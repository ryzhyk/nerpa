{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}


{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections, FlexibleContexts, LambdaCase #-}

module IR.Optimize( optimize
                  , plOptimize) where
 
import qualified Data.Graph.Inductive as G 
import qualified Data.Map as M
import Control.Monad.State
import Data.List
import Data.Maybe
--import Debug.Trace
--import System.IO.Unsafe

import Util
import IR.IR

optimize :: Int -> M.Map String Pipeline -> M.Map String Pipeline
optimize iter pls = if all (null . snd) vars then pls' else optimize (iter+1) pls''
    where
    plsvars = M.mapWithKey (\_ pl -> let (pl', (_, vars_)) = runState (plOptimize' [iter] pl) (False, [])
                                     in {-trace ("eliminating unused inputs in " ++ n ++ " " ++ show vars_) $-} (pl', vars_)) pls
    pls' = M.map fst plsvars
    vars = M.toList $ M.map snd plsvars
    pls'' = foldl' removeInputVars pls' vars

-- Unused input variables found in one of the pipelines. Remove these
-- inputs and modify all call sites.
removeInputVars :: M.Map String Pipeline -> (String, [VarName]) -> M.Map String Pipeline
removeInputVars pls (_, []) = pls
removeInputVars pls (plname, vars) = M.adjust (\pl_ -> pl_{plInputs = removeIndices (plInputs pl_) indices}) plname pls'
    where
    pl = pls M.! plname
    indices = map (\v -> fromJust $ findIndex ((==v) . exprVarName . snd) $ plInputs pl) vars
    pls' = M.map (plRemoveInputVars plname indices) pls

plRemoveInputVars :: String -> [Int] -> Pipeline -> Pipeline
plRemoveInputVars callee indices pl@Pipeline{..} = pl{plCFG = cfg'}
    where cfg' = cfgMapCtx (\_ n -> n) (Just . ctxAction plCFG) h plCFG
          h ctx = case bbNext $ ctxGetBB plCFG ctx of
                       Call x as | x == callee -> Call x $ removeIndices as indices
                       n                       -> n

type OptState = State (Bool, [VarName])

setChanged :: OptState ()
setChanged = modify (\(_, vars) -> (True, vars))

resetChanged :: OptState ()
resetChanged = modify (\(_, vars) -> (False, vars))

getChanged :: OptState Bool
getChanged = gets fst

addUnused :: [VarName] -> OptState ()
addUnused vs = modify (\(c, vars) -> (c, vars ++ vs))

plOptimize :: [Int] -> Pipeline -> Pipeline
plOptimize iter pl = evalState (plOptimize' iter pl) (False, [])


plOptimize' :: [Int] -> Pipeline -> OptState Pipeline
plOptimize' iter pl = fixpoint iter pl pass

{-
plOptimize :: Int -> Pipeline -> (Pipeline, [VarName])
plOptimize p pl | modified  = plOptimize (p+1) pl'
                | otherwise = pl'
    where (pl', (modified,)) = --trace(unsafePerformIO $ do {writeFile ("pass" ++ show p ++ ".dot") $ cfgToDot $ plCFG pl; return ""}) $
                            --trace ("******** optimizer pass " ++ show p ++ " *********") $
                            runState (pass pl) False
-}

-- one pass of the optimizer
pass :: [Int] -> Pipeline -> OptState Pipeline
pass iter pl = do
    pl1 <- fixpoint (iter ++ [0]) pl (\iter' pl_ -> do pl1_ <- {-trace "optUnusedAssigns" $-} optUnusedAssigns iter' pl_
                                                       pl2_ <- {-trace "optUnusedVars" $-} optUnusedVars iter' pl1_
                                                       {-trace "optVarSubstitute" $-}
                                                       optVarSubstitute iter' pl2_)
    -- do these last, as they may duplicate code, breaking the variable
    -- substitution optimization
    pl2 <- {-trace "optMergeCond" $-}    fixpoint (iter ++ [0]) pl1 optMergeCond
    pl3 <- {-trace "optStraightLine" $-} fixpoint (iter ++ [0]) pl2 optStraightLine
    pl4 <- {-trace "optEntryNode" $-}    fixpoint (iter ++ [0]) pl3 optEntryNode
    return pl4

fixpoint :: [Int] -> a -> ([Int] -> a -> OptState a) -> OptState a
fixpoint iter x f = do
    x' <- f iter x
    modified <- getChanged
    if modified 
       then do resetChanged
               x'' <- fixpoint (init iter ++ [last iter + 1]) x' f 
               setChanged
               return x''
       else return x'

-- Eliminate trivial entry node
optEntryNode :: [Int] -> Pipeline -> OptState Pipeline
optEntryNode _ pl@Pipeline{..} =
    case G.lab plCFG plEntryNode of
         Just (Par [BB [] (Goto n)]) -> do setChanged      
                                           let (_, cfg') = G.match plEntryNode plCFG
                                           return $ Pipeline plInputs plVars cfg' n
         --Nothing                     -> trace (unsafePerformIO $ do {cfgDump plCFG "strange.dot"; return ""}) $ error "wtf"
         _                           -> return pl

-- Merge nodes that contain straight-line code with predecessors
optStraightLine :: [Int] -> Pipeline -> OptState Pipeline
optStraightLine _ pl =
    foldM (\pl_ n -> case G.lab (plCFG pl_) n of
                          Just (Par [b]) -> do setChanged
                                               return $ merge pl_ n b
                          _              -> return pl_) pl 
          $ filter (/= plEntryNode pl) 
          $ G.nodes (plCFG pl)

merge :: Pipeline -> G.Node -> BB -> Pipeline
merge pl@Pipeline{..} n (BB as nxt) = pl{plCFG = cfg'}
    where (Just (pre, _, _, suc), cfg1) = G.match n plCFG
          -- merge n into each predecessor
          cfg' = foldl' (\cfg_ p -> let (Just (pre', _, l, suc'), cfg2) = G.match p cfg_
                                        -- rewrite predecessor's label
                                        l' = mapBB (\bb@(BB as' nxt') -> if nxt' == Goto n then BB (as' ++ as) nxt else bb) l
                                        cfg3 = (pre', p, l', suc') G.& cfg2
                                    in -- insert edges to successors of n
                                       foldl' (\cfg4 s -> G.insEdge (p, s, Edge) $ G.delLEdge (p, s, Edge) cfg4) cfg3 $ map snd suc)
                        cfg1 $ map snd pre


-- Remove assignments whose LHS is never read in the future
optUnusedAssigns :: [Int] -> Pipeline -> OptState Pipeline
optUnusedAssigns _ pl = do
    let f :: CFGCtx -> OptState (Maybe Action)
        f ctx = f' ctx (ctxAction (plCFG pl) ctx)
        f' ctx a@(ASet e1 _) | isNothing mvar = return $ Just a
                             | used           = return $ Just a
                             | otherwise      = do setChanged
                                                   return Nothing
            where mvar = var e1
                  var (EVar x _)     = Just x
                  var (ESlice e _ _) = var e
                  var _              = Nothing
                  Just v = mvar
                  match ctx' = elem v $ ctxRHSVars (plCFG pl) ctx' 
                  abort ctx' = ctxAssignsFullVar (plCFG pl) v ctx'
                  used = not $ null $ ctxSearchForward (plCFG pl) ctx match abort
        f' _   a@ABuiltin{} = return $ Just a
    cfg' <- cfgMapCtxM (\_ node -> return node) f (return . bbNext . ctxGetBB (plCFG pl)) (plCFG pl)
    return pl{plCFG = cfg'}

-- Remove unused variables
optUnusedVars :: [Int] -> Pipeline -> OptState Pipeline
optUnusedVars _ pl = do
    let used = nub $ concatMap nodeVars $ map snd $ G.labNodes $ plCFG pl
    let vars = M.keys $ plVars pl
    let unused = vars \\ used
    if null unused
       then return pl
       else do setChanged
               addUnused $ unused `intersect` (map (exprVarName . snd) $ plInputs pl)
               return $ foldl' removeVar pl unused

removeVar :: Pipeline -> VarName -> Pipeline
removeVar pl v = pl{plVars = M.delete v (plVars pl)}

-- Substitute variable values
optVarSubstitute :: [Int] -> Pipeline -> OptState Pipeline
optVarSubstitute _ pl@Pipeline{..} = do
    cfg' <- cfgMapCtxM (varSubstNode plCFG) (varSubstAction plCFG) (varSubstNext plCFG) plCFG
    return pl{plCFG = cfg'}

varSubstNode :: CFG -> NodeId -> Node -> OptState Node
varSubstNode cfg nd node = do
    let -- variables that occur in the node
        vars = case node of
                    Fork{..}   -> nodeDeps
                    Lookup{..} -> nodeDeps
                    Cond{..}   -> nub $ concatMap (exprVars . fst) nodeConds
                    Par{}      -> []
        substs = mapMaybe (\v -> fmap (v,) $ findSubstitution cfg (CtxNode nd) v) vars
        -- apply substitutions
        node' = foldl' (\node_ (v, e) -> 
                         --trace ("substitute " ++ v ++  " with " ++ show e ++ "\n         at node " ++ show node) $
                         case node_ of
                              Fork{..}   -> node_{nodeDeps = (nodeDeps \\ [v]) `union` exprVars e, nodePL = (fst nodePL, \rec -> plSubstVar v e $ (snd nodePL) rec)}
                              Lookup{..} -> node_{nodeDeps = (nodeDeps \\ [v]) `union` exprVars e, nodePL = (fst nodePL, \rec -> plSubstVar v e $ (snd nodePL) rec)}
                              Cond{..}   -> node_{nodeConds = map (\(c,b) -> (exprSubstVar v e c, b)) nodeConds}
                              Par{}      -> error "IROptimize.varSubstNode Par") 
                       node substs
    when (not $ null substs) setChanged
    return node'

varSubstAction :: CFG -> CFGCtx -> OptState (Maybe Action)
varSubstAction cfg ctx = do
    let act = ctxAction cfg ctx
        vars = actionRHSVars act
        substs = mapMaybe (\v -> fmap (v,) $ findSubstitution cfg ctx v) vars
        -- apply substitutions
        act' = foldl' (\act_ (v, e) -> 
                        --trace ("substitute " ++ v ++  " with " ++ show e ++ "\n         in action " ++ show act) $
                        case act_ of
                             ASet     l r  -> ASet l $ exprSubstVar v e r
                             ABuiltin f as -> ABuiltin f $ map (exprSubstVar v e) as
                             --APut     t es -> APut t $ map (exprSubstVar v e) es
                             --ADelete  t c  -> ADelete t $ exprSubstVar v e c
                             )
                       act substs
    when (not $ null substs) setChanged
    return $ Just act'

varSubstNext :: CFG -> CFGCtx -> OptState Next
varSubstNext cfg ctx = do
    let nxt = bbNext $ ctxGetBB cfg ctx
        substs = case nxt of
                      Send x          -> mapMaybe (\v -> fmap (v,) $ findSubstitution cfg ctx v) $ exprVars x
                      Call _ xs       -> mapMaybe (\v -> fmap (v,) $ findSubstitution cfg ctx v) $ nub $ concatMap exprVars xs
                      Controller _ xs -> -- don't substitute column names in packet-in actions
                                         filter (not . any isCol . exprAtoms . snd)
                                                $ mapMaybe (\v -> fmap (v,) $ findSubstitution cfg ctx v) $ nub $ concatMap exprVars xs
                                         where isCol ECol{} = True
                                               isCol _      = False
                      _               -> []
        -- apply substitutions
        nxt' = foldl' (\nxt_ (v, e) -> 
                        --trace ("substitute " ++ v ++  " with " ++ show e ++ "\n         in action " ++ show act) $
                        case nxt_ of
                             Send x          -> Send $ exprSubstVar v e x
                             Call f xs       -> Call f $ map (exprSubstVar v e) xs
                             Controller u xs -> Controller u $ map (exprSubstVar v e) xs
                             _               -> nxt_)
                       nxt substs
    when (not $ null substs) setChanged
    return nxt'

findSubstitution :: CFG -> CFGCtx -> String -> Maybe Expr
findSubstitution cfg ctx v = 
    -- first pass search for a unique predecessor node that assigns v
    case ctxSearchBackward cfg ctx match1 abort1 of
         [ctx'] -> let ASet _ r = ctxAction cfg ctx'
                       as = exprAtoms r 
                       iscol ECol{} = True 
                       iscol _      = False in
                   -- if as contain column names, only allow substitutions within node
                   if any iscol as && ctxNode ctx' /= ctxNode ctx
                      then Nothing
                      else -- search for intermediate assignements to variables in r
                           case ctxSearchBackward cfg ctx (match2 as) (abort2 ctx') of
                                []                      -> Just r
                                [ctx''] | ctx'' == ctx' -> Just r
                                _                       -> Nothing
         _     -> Nothing
    where
    match1 CtxNode{} = False
    match1 ctx_ = ctxAssignsFullVar cfg v ctx_

    abort1 _ = False

    match2 _  CtxNode{} = False
    match2 as ctx_ | isActCtx ctx_ = 
        case ctxAction cfg ctx_ of
             ASet l _ | (not $ null $ exprAtoms l `intersect` as) -> True
             _                                                    -> False
    match2 _ _ = False
    abort2 ctx' ctx_ = ctx' == ctx_

-- Merge cascades of cond nodes
optMergeCond :: [Int] -> Pipeline -> OptState Pipeline
optMergeCond _ pl@Pipeline{..} = do
    cfg' <- foldM (\cfg_ n -> 
                    case G.lab cfg_ n of
                         -- conditional node
                         Just (Cond cs) -> case G.match n cfg_ of
                                                -- unique predecessor that is also a conditional node with exactly one branch pointing towards n ...
                                                (Just ([(_, n')], _, _, _), _) -> 
                                                    case G.lab cfg_ n' of
                                                         Just (Cond cs') | length (filter ((==Goto n) . bbNext . snd) cs') == 1 -> do
                                                             -- and does not modify variables n depends on
                                                             let vs = concatMap (exprAtoms . fst) cs
                                                                 vs' = concatMap (bbLHSAtoms . snd) 
                                                                       $ filter ((==Goto n) . bbNext . snd) cs'
                                                             if null $ vs `intersect` vs'
                                                                then do setChanged     
                                                                        return $ mergeCond cfg_ n' n
                                                                else return cfg_
                                                         _ -> return cfg_
                                                _ -> return cfg_
                         _              -> return cfg_) plCFG
          $ G.nodes plCFG
    return $ pl{plCFG = cfg'}

bbLHSAtoms :: BB -> [Expr]
bbLHSAtoms b = nub $ concatMap (\case
                                 ASet l _   -> exprAtoms l
                                 ABuiltin{} -> []) $ bbActions b

mergeCond :: CFG -> NodeId -> NodeId -> CFG
mergeCond cfg nto n = {-trace ("merging " ++ show n ++ " into " ++ show nto) $-} (pre', nto, Cond csto', nub $ suc' ++ suc) G.& cfg2 
    where -- remove the node being merged
          (Just (_, _, Cond cs, suc), cfg1) = G.match n cfg
          (Just (pre', _, Cond csto, suc'), cfg2) = G.match nto cfg1
          csto' = concatMap (\(c', b') -> if bbNext b' /= Goto n
                                             then [(c',b')]
                                             else map (\(c,b) -> (conj[c', c], BB (bbActions b' ++ bbActions b) (bbNext b))) cs) csto
          
-- Optimizations: 
--     + eliminate unused variables (for example only a few vars returned by a query are used)
--     + variable elimination by substitution
--     * merging tables to eliminate some variables
--     + merge cascade of conditions
--     + merge sequence of basic blocks
--     * merge cascades of parallel blocks
