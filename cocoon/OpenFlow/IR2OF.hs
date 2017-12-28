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

{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, FlexibleContexts, ScopedTypeVariables, LambdaCase #-}

module OpenFlow.IR2OF( IRSwitch
                     , IRSwitches
                     , RuntimeState
                     , precompile
                     , buildSwitch
                     , updateSwitch
                     , recordField) where

import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Query.DFS as G
import qualified Data.Map                       as M
import Data.List
import Data.Maybe
import Data.Bits
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Debug.Trace
import System.FilePath.Posix
import System.IO.Unsafe

import Util
import Ops
import Name
import NS
import qualified IR.IR             as I
import qualified IR.Compile2IR     as I
import qualified IR.Registers      as I
import qualified OpenFlow.OpenFlow as O
import qualified Backend           as B
import qualified Syntax            as C -- Cocoon
import qualified Eval              as C
import qualified NS                as C

-- Uniquely identify an instance of the switch:
type SwitchId = Integer

type IRSwitch = M.Map String I.Pipeline
type IRSwitches = M.Map String IRSwitch

maxOFTables = 255

-- Runtime state maintained by the controller to keep track of OF group numbers
-- generated for any-queries.  Maps a set of columns in a relation to
-- the set of valuations of this column in the database, the number of times 
-- each valuation occurs and the group number assigned to it.
type NodeRuntimeState = M.Map [I.Expr] (O.GroupId, M.Map I.Record (O.BucketId, Integer))
type SwRuntimeState = (M.Map I.NodeId NodeRuntimeState, O.GroupId)
type Groups = M.Map SwitchId SwRuntimeState

type RuntimeState = Groups

-- For each switch table
--  Compute and compile all port roles, perform register and OF table allocation
precompile :: (MonadError String me) => B.StructReify -> FilePath -> C.Refine -> I.RegisterFile -> me IRSwitches
precompile structs workdir r rfile = do
    (liftM M.fromList)
     $ mapM (\sw -> do let ir = I.compileSwitch structs workdir r sw
                       ir' <- mapM (\(n, pl) -> do pl' <- I.allocVarsToRegisters pl rfile
                                                   let rdotname = workdir </> addExtension (addExtension n "reg") "dot"
                                                   trace (unsafePerformIO $ do {I.cfgDump (I.plCFG pl') rdotname; return ""}) $ return (n, pl')
                                                `catchError` (\e -> throwError $ "Compiling pipeline " ++ n ++ " of switch " ++ name sw ++ ":" ++ e)) 
                                   $ M.toList ir
                       let (ntables, ir'') = assignTables ir'
                       mapM_ (\(n, pl) -> do let dotname = workdir </> addExtension (addExtension n "of") "dot"
                                             trace (unsafePerformIO $ do {I.cfgDump (I.plCFG pl) dotname; return ""}) $ return ()) ir''
                       when (ntables > maxOFTables) 
                           $ throwError $ name sw ++ " requires " ++ show ntables ++ " OpenFlow tables, but only " ++ show maxOFTables ++ " tables are available"
                       return (name sw, M.fromList ir'')) $ C.refineSwitches r

-- Relabel port CFGs into openflow table numbers
assignTables :: [(String, I.Pipeline)] -> (Int, [(String, I.Pipeline)])
assignTables pls = foldl' (\(start, pls') (n,pl) -> let (start', pl') = relabel start pl
                                                    in (start', pls' ++ [(n, pl')])) (1, []) pls
    where 
    relabel :: Int -> I.Pipeline -> (Int, I.Pipeline)
    relabel start pl = (start + length ordered', pl{I.plCFG = cfg', I.plEntryNode = start})
        where
        ordered = G.topsort $ I.plCFG pl
        -- allocate extra table for nodes that send to group
        ordered' = foldl' (\ordered_ nd -> 
                            case fromJust $ G.lab (I.plCFG pl) nd of
                                 I.Fork{}                               -> ordered_ ++ [Just nd, Nothing]
                                 I.Par bbs    | length bbs > 1          -> ordered_ ++ [Just nd, Nothing]
                                 I.Lookup{..} | nodeSelection == I.Rand -> ordered_ ++ [Just nd, Nothing]
                                 _                                      -> ordered_ ++ [Just nd]) 
                   [] ordered
        rename nd = (fromJust $ findIndex ((Just nd) ==) ordered') + start
        bbrename (I.BB as (I.Goto nd)) = I.BB as $ I.Goto $ rename nd
        bbrename bb                    = bb
        cfg' = G.buildGr
               $ G.ufold (\(pre, nd, node, suc) cs -> let pre'  = map (mapSnd rename) pre
                                                          suc'  = map (mapSnd rename) suc
                                                          nd'   = rename nd 
                                                          node' = I.mapBB bbrename node
                                                      in (pre', nd', node', suc'):cs) 
                 [] (I.plCFG pl)

-- New switch event
--   Store the list of tables this switch depends on
buildSwitch :: C.Refine -> B.StructReify -> O.Field -> RuntimeState -> (String, IRSwitch) -> I.DB -> SwitchId -> ([O.Command], RuntimeState)
buildSwitch r structs idxfield s ir db swid = (table0 : (staticcmds ++ updcmds), s')
    where
    table0 = O.AddFlow 0 $ O.Flow 0 [] [O.ActionDrop]
    -- Configure static part of the pipeline
    staticcmds = let ?r = r 
                     ?structs = structs
                     ?ir = ir
                     ?idxfield = idxfield
                 in concatMap (\(plname, pl) -> concatMap (mkNode plname) $ G.labNodes $ I.plCFG pl) $ M.toList $ snd ir
    -- Configure dynamic part from primary tables
    (updcmds, s') = updateSwitch r structs idxfield (M.insert swid (M.empty,0) s) ir swid (M.map (map (True,)) db)

updateSwitch :: C.Refine -> B.StructReify -> O.Field -> RuntimeState -> (String, IRSwitch) -> SwitchId -> I.Delta -> ([O.Command], RuntimeState)
updateSwitch r structs idxfield s ir swid db = (portcmds ++ nodecmds, M.insert swid ssw' s')
    where
    s' = M.alter (Just . maybe (M.empty,0) id) swid s
    -- update table0 if ports have been added or removed
    portcmds = let ?r = r 
                   ?structs = structs
                   ?ir = ir
                   ?idxfield = idxfield
               in concatMap (\(pname, pl) -> updatePort pname pl swid db) $ filter (isJust . lookupPort r . fst) $ M.toList $ snd ir
    -- update pipeline nodes
    (nodecmds, ssw') = let ?r = r 
                           ?structs = structs 
                           ?ir = ir 
                           ?idxfield = idxfield in
                       let (cmds, ssw) = runState (mapM (\(pname, pl) -> (liftM concat) $ mapM (updateNode db pname pl swid) 
                                                                                        $ G.labNodes $ I.plCFG pl) $ M.toList $ snd ir) 
                                                  (s' M.! swid)
                       in (concat cmds, ssw)

updatePort :: (?r::C.Refine, ?structs::B.StructReify, ?idxfield::O.Field) => String -> I.Pipeline -> SwitchId -> I.Delta -> [O.Command]
updatePort pname pl i db = delcmd ++ addcmd
    where
    prel = name $ C.portRel $ C.getPort ?r pname
    (add, del) = partition fst $ filter (\(_, e) -> (C.exprIVal $ C.enode $ C.evalConstExpr ?r (C.eField e "switch")) == i) $ db M.! prel
    match f = let C.E (C.EBit _ w pnum) = C.evalConstExpr ?r (C.eField f "portnum") in
              mkSimpleCond $ I.EBinOp Eq (I.EPktField "portnum" $ I.TBit w) (I.EBit w pnum)
    delcmd = concatMap (\(_,f) -> map (O.DelFlow 0 1) $ match f) del
    addcmd = concatMap (\(_,f) -> map (\m -> O.AddFlow 0 $ O.Flow 1 m [O.ActionGoto $ I.plEntryNode pl]) $ match f) add

mkNode :: (?r::C.Refine, ?structs::B.StructReify, ?ir::(String, IRSwitch), ?idxfield::O.Field) => String -> (I.NodeId, I.Node) -> [O.Command]
mkNode plname (nd, node) = {-trace ("mkNode " ++ show nd) $-}
    case node of
         I.Par [b]                   -> [ O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB plname nd 0 b ]
         I.Par bs                    -> [ O.AddGroup 
                                          $ O.Group nd O.GroupAll 
                                          $ mapIdx (\_ i -> O.Bucket Nothing [O.ActionSet (O.EField ?idxfield $ Just (31,0)) (O.EVal $ O.Value 32 $ toInteger i), O.ActionResubmit (nd+1)]) bs 
                                        , O.AddFlow nd $ O.Flow 0 [] $ mkGroupAction nd ] ++
                                        mapIdx (\b i -> O.AddFlow (nd+1) $ O.Flow 0 [O.Match ?idxfield (Just 0xffffffff) $ toInteger i] 
                                                                                  $ mkStaticBB plname nd i b) bs
         I.Cond cs                   -> mapIdx (\(m, a) i -> O.AddFlow nd $ O.Flow i m a) 
                                               $ reverse $ mkCond $ mapIdx (\(c,b) i -> (c, mkStaticBB plname nd i b)) cs
         I.Lookup _ _ _ _ el I.First -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB plname nd 1 el]
         I.Lookup _ _ _ _ el I.Rand  -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB plname nd 1 el]
         I.Fork{}                    -> []

updateNode :: (?r::C.Refine, ?structs::B.StructReify, ?ir::(String, IRSwitch), ?idxfield::O.Field) => I.Delta -> String -> I.Pipeline -> SwitchId -> (I.NodeId, I.Node) -> State SwRuntimeState [O.Command]
updateNode db plname portpl swid (nd, node) = {-trace ("updateNode " ++ show nd) $-}
    case node of
         I.Par _                      -> return []
         I.Cond _                     -> return []
         I.Lookup t _ pl th _ I.First -> let -- First node of the pipeline? Ignore entries that do not belong to swid
                                             -- TODO: hack; remove when proper table slicing is implemented
                                             (add, del) = if (null $ G.pre (I.plCFG portpl) nd) && (isJust $ lookupPort ?r plname)
                                                             then partition fst $ filter (\(_, f) -> (C.exprIVal $ C.enode $ (C.evalConstExpr ?r (C.eField f "switch"))) == swid) $ (db M.! t)
                                                             else partition fst (db M.! t) 
                                             delcmd = concatMap (\(_,f) -> map (\O.Flow{..} -> O.DelFlow nd flowPriority flowMatch) 
                                                                               $ mkLookupFlow plname nd f (snd pl) $ Left th) del
                                             addcmd = concatMap (\(_,f) -> map (O.AddFlow nd) $ mkLookupFlow plname nd f (snd pl) $ Left th) add
                                         in return $ delcmd ++ addcmd
         I.Lookup t _ _ _ _ I.Rand    -> -- create a group for each unique combination of match columns
                                         -- create match entries in the table to forward packets to the group
                                         -- create a bucket in the group for each row in relation
                                         do let (add, del) = partition fst (db M.! t)
                                            delgrcmd <- liftM concat $ mapM (delGroup . snd) del
                                            addgrcmd <- liftM concat $ mapM (addGroup O.GroupSelect . snd) add
                                            return $ delgrcmd ++ addgrcmd
         I.Fork t _ _ _               -> do let (add, del) = partition fst (db M.! t)
                                            delgrcmd <- liftM concat $ mapM (delGroup . snd) del
                                            addgrcmd <- liftM concat $ mapM (addGroup O.GroupAll . snd) add
                                            return $ delgrcmd ++ addgrcmd
    where
    delGroup :: C.Expr -> State SwRuntimeState [O.Command]
    delGroup f = do
        s <- getNode nd
        let (cols, _) = I.nodePL node
        let f' = I.val2Record ?r ?structs (I.nodeRel node) f
        -- extract column values from f
        let vals = map (\col -> case M.lookup col f' of
                                     Nothing -> error $ "column " ++ show col ++ " not found in record " ++ show f'       
                                     Just x  -> x) cols
        let (g, bkts) = case M.lookup vals s of
                             Nothing -> error $ "entry " ++ show vals ++ " not found. node: " ++ show nd
                             Just x  -> x
        let (bid, idx) = case M.lookup f' bkts of
                              Nothing -> error $ "bucket  " ++ show f' ++ " not found" 
                              Just x  -> x
        let bkts' = M.delete f' bkts
        -- update counter in s M.! val; if the counter drops to 0, delete group and flow entries
        let s' = M.update (\(gid, _) -> Just (gid, bkts')) vals s
        let grcmds = if M.size bkts' == 0
                        then (O.DelGroup g) :
                             (map (\O.Flow{..} -> O.DelFlow nd flowPriority flowMatch)
                                  $ mkLookupFlow plname nd f (snd $ I.nodePL node) $ Right $ mkGroupAction g)
                        else []
        -- remove empty group
        s'' <- if M.size bkts' == 0
                  then do deallocGroup g
                          return $ M.delete vals s'
                  else return s'
        putNode nd s''
        let delcmd = [ O.DelBucket g bid
                     , O.DelFlow (nd+1) 1 [O.Match ?idxfield (Just 0xffffffff) idx] ]
        return $ grcmds ++ delcmd

    addGroup :: O.GroupType -> C.Expr -> State SwRuntimeState [O.Command]
    addGroup gt f = do
        let bb = case node of
                      I.Lookup _ _ _ th _ _ -> th
                      I.Fork _ _ _ b        -> b
                      _                     -> error $ "IR2OF.addGroup " ++ show node
        s <- getNode nd
        let (cols, _) = I.nodePL node
        let f' = I.val2Record ?r ?structs (I.nodeRel node) f
        -- extract column values from f
        let vals = map (f' M.!) cols
        -- update counter in s M.! val; if the counter is 1 (1st element), create group and flow entries
        s' <- case M.lookup vals s of
                   Nothing -> do newg <- allocGroup
                                 return $ M.insert vals (newg, M.empty) s
                   Just _  -> return s
        let g = fst $ s' M.! vals
        let grcmds = if M.size (snd $ s' M.! vals) == 0
                        then (O.AddGroup $ O.Group g gt []) :
                             (map (O.AddFlow nd) $ mkLookupFlow plname nd f (snd $ I.nodePL node) $ Right $ mkGroupAction g)
                        else []
        -- allocate bucket id
        let bid = case map fst $ M.elems $ snd $ s' M.! vals of
                       []    -> 0
                       bids  -> maximum bids + 1
        let idx = case map snd $ concatMap (M.elems . snd) $ M.elems s' of
                       []    -> 0
                       inds  -> maximum inds + 1
        let s'' = M.update (\(gid,bkts) -> Just (gid, M.insert f' (bid, idx) bkts)) vals s'
        let addcmd = [ O.AddBucket g $ O.Bucket (Just bid) [O.ActionSet (O.EField ?idxfield (Just (31,0))) (O.EVal $ O.Value 32 idx), O.ActionResubmit (nd+1)]
                     , O.AddFlow (nd+1) $ O.Flow 1 [O.Match ?idxfield (Just 0xffffffff) idx] $ mkBB plname nd 0 f bb]
        putNode nd s''
        return $ grcmds ++ addcmd

    -- Group id allocator -- just keep incrementing for now
    -- TODO: implement real allocator
    allocGroup :: State SwRuntimeState O.GroupId
    allocGroup = do
        lastGroup <- gets snd
        let g = lastGroup + 1
        modify (\(x, _) -> (x, g))
        return g

    deallocGroup :: O.GroupId -> State SwRuntimeState ()
    deallocGroup _ = return ()

    getNode :: I.NodeId -> State SwRuntimeState NodeRuntimeState
    getNode n = gets ((maybe M.empty id) . M.lookup n . fst)

    putNode :: I.NodeId -> NodeRuntimeState -> State SwRuntimeState ()
    putNode n s = modify (\(m, g) -> (M.insert n s m, g))

mkGroupAction :: (?idxfield::O.Field) => O.GroupId -> [O.Action]
mkGroupAction gid = [O.ActionGroup gid]

{-
getBucketId :: (?r::C.Refine) => String -> C.Expr -> O.BucketId
getBucketId rname f = fromInteger pkey
    where   
    rel = C.getRelation ?r rname
    Just [key] = C.relPrimaryKey rel
    C.E (C.EBit _ _ pkey) = recordField f key -}

recordField :: (?r::C.Refine) => C.Expr -> C.Expr -> C.Expr
recordField rec fexpr = C.evalConstExpr ?r (f fexpr)
    where
    f (C.E (C.EVar _ v))      = C.eField rec v
    f (C.E (C.EField _ e fl)) = C.eField (f e) fl
    f e                       = error $ "IR2OF.recordField.f " ++ show e

mkStaticBB :: (?r::C.Refine, ?structs::B.StructReify, ?ir::(String, IRSwitch)) => String -> I.NodeId -> Int -> I.BB -> [O.Action]
mkStaticBB plname nd i b = mkBB plname nd i (error "IR2OF.mkStaticBB requesting field value") b

mkBB :: (?r::C.Refine, ?structs::B.StructReify, ?ir::(String, IRSwitch)) => String -> I.NodeId -> Int -> C.Expr -> I.BB -> [O.Action]
mkBB plname nd i val (I.BB as n) = map (mkAction ival) as ++ mkNext plname nd i ival n
    where ival = I.val2Record ?r ?structs (C.exprConstructor $ C.enode val) val

mkAction :: I.Record -> I.Action -> O.Action
mkAction val (I.ASet e1 e2)    = O.ActionSet (mkExpr val e1) (mkExpr val e2)
mkAction val (I.ABuiltin f as) = O.ActionBuiltin f $ map (mkExpr val) as

mkExpr :: I.Record -> I.Expr -> O.Expr
mkExpr val e = {-trace ("mkExpr " ++ show val ++ " " ++ show e) $ -}
    case e of
         I.EPktField f t   -> O.EField (O.Field f $ I.typeWidth t) Nothing
         I.EVar      v t   -> O.EField (O.Field v $ I.typeWidth t) Nothing
         I.ECol      c _   -> case M.lookup c val of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown column: " ++ show c ++ " in " ++ show val
                                   Just v  -> mkExpr val v
         I.ESlice    x h l -> slice (mkExpr val x) h l
         I.EBit      w v   -> O.EVal $ O.Value w v
         I.EBool     True  -> O.EVal $ O.Value 1 1
         I.EBool     False -> O.EVal $ O.Value 1 0
         _                 -> error $ "Not implemented: IR2OF.mkExpr " ++ show e

slice :: O.Expr -> Int -> Int -> O.Expr
slice (O.EField f Nothing)       h l = O.EField f $ Just (h, l)
slice (O.EField f (Just (_,l0))) h l = O.EField f $ Just (l0+h, l0+l)
slice (O.EVal (O.Value _ v))     h l = O.EVal $ O.Value (h-l) $ bitSlice v h l

mkLookupFlow :: (?r::C.Refine, ?structs::B.StructReify, ?ir::(String, IRSwitch)) => String -> I.NodeId -> C.Expr -> I.FPipeline -> Either I.BB [O.Action] -> [O.Flow]
mkLookupFlow plname nd val lpl b = {-trace ("mkLookupFlow " ++ show val ++ " " ++ show (I.plCFG $ lpl val)) $-} map (\m -> O.Flow 1 m as) matches
    where
    matches = mkPLMatch $ lpl val
    as = case b of 
              Left bb    -> mkBB plname nd 0 val bb
              Right acts -> acts

-- compile Cond node    
-- TODO: use BDDs to find a near-optimal representation
mkCond :: [(I.Expr, [O.Action])] -> [([O.Match], [O.Action])]
mkCond []          = [([], [O.ActionDrop])]
mkCond ((c, a):cs) = let cs' = mkCond cs
                         c' = mkCond' c in
                     concatMap (\case
                                 (x, True)  -> [(x,a)]
                                 (x, False) -> mapMaybe (\(y, a') -> fmap ((,a')) $ concatMatches x y) cs') c'

mkCond' :: I.Expr -> [([O.Match], Bool)]
mkCond' c = {-trace ("mkCond " ++ show c) $-}
    case I.exprEval c of
         I.EBinOp Eq e1 e2 | I.exprIsBool e1 
                                       -> let e1s = mkCond' e1
                                              e2s = mkCond' e2 in
                                          mergeTail
                                          $ concatMap (\(e2', b2) -> mapMaybe (\(e1', b1) -> fmap ((, b1 == b2)) $ concatMatches e1' e2') e1s) e2s 
                           | I.exprIsBit e1
                                       -> let cs' = mkMatch e1 e2
                                          in map (, True) cs' ++ [([], False)]
         I.EBinOp Neq e1 e2            -> mkCond' (I.EUnOp Not (I.EBinOp Eq e1 e2))
         I.EBinOp Impl e1 e2           -> mkCond' (I.EBinOp Or (I.EUnOp Not e1) e2)
         I.EUnOp Not (I.EBinOp Eq e1 e2) | I.exprType e1 == I.TBit 1 && e2 == I.EBit 1 0 
                                       -> mkCond' $ I.EBinOp Eq e1 (I.EBit 1 1) 
         I.EUnOp Not (I.EBinOp Eq e1 e2) | I.exprType e1 == I.TBit 1 && e2 == I.EBit 1 1 
                                       -> mkCond' $ I.EBinOp Eq e1 (I.EBit 1 0) 
         I.EUnOp Not (I.EBinOp Eq e1 e2) | I.exprType e1 == I.TBit 1 && e1 == I.EBit 1 0 
                                       -> mkCond' $ I.EBinOp Eq (I.EBit 1 1) e2
         I.EUnOp Not (I.EBinOp Eq e1 e2) | I.exprType e1 == I.TBit 1 && e1 == I.EBit 1 1 
                                       -> mkCond' $ I.EBinOp Eq (I.EBit 1 0) e2
         I.EUnOp Not e                 -> map (mapSnd not) $ mkCond' e
         I.EBinOp And e1 e2            -> let e1s = mkCond' e1
                                              e2s = mkCond' e2
                                          in mergeTail $
                                             concatMap (\case
                                                         (e2', True)  -> mapMaybe (\(e1', b) -> fmap ((,b)) $ concatMatches e1' e2') e1s
                                                         (e2', False) -> [(e2', False)] ) e2s 
         I.EBinOp Or e1 e2             -> let e1s = mkCond' e1
                                              e2s = mkCond' e2
                                          in mergeTail $
                                             concatMap (\case
                                                         (e2', False)  -> mapMaybe (\(e1', b) -> fmap ((,b)) $ concatMatches e1' e2') e1s
                                                         (e2', True) -> [(e2', True)] ) e2s 
         I.EBool True                  -> [([], True)]
         I.EBool False                 -> [([], True)]
         e  | I.exprType e == I.TBit 1 -> mkCond' (I.EBinOp Eq e (I.EBit 1 1))
         --I.EPktField f I.TBool         -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches [O.Match (O.Field f 1) Nothing 1] m)) yes ++ no
         --I.EVar v I.TBool              -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches [O.Match (O.Field v 1) Nothing 1] m)) yes ++ no
         _                             -> error $ "IR2OF.mkCond': expression is not supported: " ++ show c
    where mergeTail [] = []
          mergeTail xs = let ((x,b):xs') = reverse xs
                             xs'' = dropWhile ((==b) . snd) xs'
                         in reverse $ (x,b) : xs''

{-
mkCond' :: I.Expr -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])]
mkCond' c yes no =
    case I.exprEval c of
         I.EBinOp Eq e1 e2 | I.exprIsBool e1 
                                       -> mkCond' e1 (mkCond' e2 yes no) (mkCond' e2 no yes)
                           | I.exprIsBit e1
                                       -> let cs' = mkMatch e1 e2
                                          in concatMap (\c' -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches c' m)) yes) cs' ++ no
         I.EBinOp Neq e1 e2            -> mkCond' (I.EUnOp Not (I.EBinOp Eq e1 e2)) yes no
         I.EBinOp Impl e1 e2           -> mkCond' (I.EBinOp Or (I.EUnOp Not e1) e2) yes no
         I.EUnOp Not e                 -> mkCond' e no yes
         I.EBinOp Or e1 e2             -> mkCond' e1 yes (mkCond' e2 yes no)
         I.EBinOp And e1 e2            -> mkCond' e1 (mkCond' e2 yes no) no
         I.EBool True                  -> yes
         I.EBool False                 -> no
         e  | I.exprType e == I.TBit 1 -> mkCond' (I.EBinOp Eq e (I.EBit 1 1)) yes no
         I.EPktField f I.TBool         -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches [O.Match (O.Field f 1) Nothing 1] m)) yes ++ no
         I.EVar v I.TBool              -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches [O.Match (O.Field v 1) Nothing 1] m)) yes ++ no
         _                             -> error $ "IR2OF.mkCond': expression is not supported: " ++ show c
-}

-- TODO: use BDDs to encode arbitrary pipelines
mkPLMatch :: I.Pipeline -> [[O.Match]]
mkPLMatch pl = mkSimpleCond $ fst $ mkPLMatchNode M.empty (I.plEntryNode pl) pl

mkPLMatchNode :: M.Map I.Expr I.Expr -> I.NodeId -> I.Pipeline -> (I.Expr, I.Expr)
mkPLMatchNode vars nd pl@I.Pipeline{..} = 
    case fromJust $ G.lab plCFG nd of
         I.Cond cs -> foldl' (\(yes, no) (c, b) -> 
                               let c' = I.exprSubst vars c
                               in mkPLMatchBB vars c' (yes, no) pl b) 
                             (I.EBool False, I.EBool False) cs
         I.Par [b] -> mkPLMatchBB vars (I.EBool True) (I.EBool False, I.EBool False) pl b
         I.Par []  -> (I.EBool False, I.EBool True)
         n         -> error $ "IR2OF.mkPLMatchNode " ++ show n

mkPLMatchBB :: M.Map I.Expr I.Expr -> I.Expr -> (I.Expr, I.Expr) -> I.Pipeline -> I.BB -> (I.Expr, I.Expr) 
mkPLMatchBB vars c (yes, no) pl (I.BB as nxt) = 
    let vars' = foldl' mkPLMatchAction vars as in
    case nxt of
         I.Drop     -> (I.conj [I.EUnOp Not no, c], no)
         I.Goto nd' -> let (yes', no') = mkPLMatchNode vars' nd' pl
                       in (I.disj [yes, I.conj [c, yes']], I.disj [no, I.conj [c, no']])
         _          -> error ""

mkPLMatchAction :: M.Map I.Expr I.Expr -> I.Action -> M.Map I.Expr I.Expr
mkPLMatchAction vars (I.ASet lhs rhs) = let rhs' = I.exprSubst vars rhs
                                        in M.insert lhs rhs' vars
mkPLMatchAction _    a                = error $ "IR2OF.mkPLMatchAction " ++ show a

{-
    if G.order plCFG == 2 
       then case G.lab plCFG plEntryNode of
                 Just (I.Cond cs) -> mkSimpleCond $ cs2expr cs
                 _                -> error $ "IR2OF.mkPLMatch: CFG too complicated:\n" ++ I.cfgToDot plCFG
       else error $ "IR2OF.mkPLMatch: CFG too complicated (" ++ show (G.order plCFG) ++ " nodes):\n" ++ I.cfgToDot plCFG
    -- IR compiler encodes lookup conditions with satisfying branches terminating in Drop
    where
    cs2expr ((c, I.BB [] I.Drop):cs) = I.EBinOp Or c $ cs2expr cs
    cs2expr ((c, _):cs)              = I.EBinOp And (I.EUnOp Not c) $ cs2expr cs
    cs2expr []                       = I.EBool False 
-}

mkSimpleCond :: I.Expr -> [[O.Match]]
mkSimpleCond e = {-trace ("mkSimpleCond " ++ show e) $-} mkSimpleCond' $ I.exprEval e

mkSimpleCond' :: I.Expr -> [[O.Match]]
mkSimpleCond' c = 
    case c of
         I.EBinOp Eq e1 e2 | I.exprIsBit e1
                                     -> mkMatch e1 e2
         I.EBinOp Neq e1 e2          -> mkSimpleCond' (I.EUnOp Not (I.EBinOp Eq e1 e2))
         I.EBinOp Impl e1 e2         -> mkSimpleCond' (I.EBinOp Or (I.EUnOp Not e1) e2)
         I.EBinOp Or e1 e2           -> mkSimpleCond' e1 ++ mkSimpleCond' e2
         I.EBinOp And e1 e2          -> catMaybes $ concatMatches <$> mkSimpleCond' e1 <*> mkSimpleCond' e2
         I.EUnOp Not (I.EBool b)     -> mkSimpleCond' $ I.EBool (not b)
         I.EUnOp Not (I.EUnOp Not e) -> mkSimpleCond' e
         I.EBool False               -> []
         I.EBool True                -> [[]]
         _                           -> error $ "IR2OF.mkSimpleCond': expression is not supported: " ++ show c

concatMatches :: [O.Match] -> [O.Match] -> Maybe [O.Match]
concatMatches m1 m2 = foldM (\ms m@(O.Match f msk v) -> 
                              case findIndex ((== f) . O.matchField) ms of
                                   Just i  -> do let O.Match _ msk' v' = ms !! i
                                                 m' <- combineMatches f (msk', v') (msk, v)
                                                 return $ (take i ms) ++ [m'] ++ (drop (i+1) ms)
                                   Nothing -> return $ ms ++ [m]) m1 m2 

combineMatches :: O.Field -> (Maybe O.Mask, Integer) -> (Maybe O.Mask, Integer) -> Maybe O.Match
combineMatches f (mm1, v1) (mm2, v2) = if v1' == v2' then Just (O.Match f m' v') else Nothing
    where m1 = maybe (-1) id mm1
          m2 = maybe (-1) id mm2
          v1' = v1 .&. m1 .&. m2
          v2' = v2 .&. m1 .&. m2
          m' = if m1 .|. m2 == -1 then Nothing else Just (m1 .|. m2)
          v' = (v1 .&. m1) .|. (v2 .&. m2)

mkMatch :: I.Expr -> I.Expr -> [[O.Match]]
mkMatch e1 e2 = 
    if I.exprIsConst e1 
       then mkMatch' e2' mask2 i1'
       else if I.exprIsConst e2
               then mkMatch' e1' mask1 i2'
               else error $ "IR2OF.mkMatch: cannot match two variables expressions: " ++ show e1 ++ " " ++ show e2
    where (e1', mask1, i2') = exprMask e1 (bitRange (I.typeWidth (I.exprType e1) - 1) 0) i2
          (e2', mask2, i1') = exprMask e2 (bitRange (I.typeWidth (I.exprType e2) - 1) 0) i1
          I.EBit _ i1 = e1
          I.EBit _ i2 = e2

mkMatch' :: O.Field -> Integer -> Integer -> [[O.Match]]
mkMatch' _ mask val | (val .&. (complement mask)) /= 0        = []
mkMatch' _ mask _   | mask == 0                               = [[]]
mkMatch' f mask val | mask == bitRange (O.fieldWidth f - 1) 0 = [[O.Match f Nothing val]]
mkMatch' f mask val | otherwise                               = [[O.Match f (Just mask) val]]

exprMask :: I.Expr -> Integer -> Integer -> (O.Field, Integer, Integer)
exprMask (I.EPktField f t)     m i = (O.Field f $ I.typeWidth t, m, i)
exprMask (I.EVar v t)          m i = (O.Field v $ I.typeWidth t, m, i)
exprMask (I.ESlice e h l)      m i = exprMask e ((m `shiftL` l) .&. bitRange h l) (i `shiftL` l)
exprMask (I.EBinOp BAnd e1 e2) m i | I.exprIsConst e1 
                                   = exprMask e2 (m .&. I.exprIntVal e1) i
exprMask (I.EBinOp BAnd e1 e2) m i | I.exprIsConst e2
                                   = exprMask e1 (m .&. I.exprIntVal e2) i
exprMask e                     _ _ = error $ "IR2OF.exprMask: expression too complicated " ++ show e

mkNext :: (?r::C.Refine, ?ir::(String, IRSwitch)) => String -> I.NodeId -> Int -> I.Record -> I.Next -> [O.Action]
mkNext _ _  _ _ (I.Goto nd)        = [O.ActionGoto nd]
mkNext _ _  _ r (I.Send e)         = [O.ActionOutput $ mkExpr r e]
mkNext _ _  _ _ I.Drop             = [O.ActionDrop]
mkNext _ _  _ r (I.Call f as)      = (map (\(a,_) -> O.ActionPush a) varargs) ++ 
                                     (map (\(_,i) -> O.ActionPop i) $ reverse varargs) ++
                                     (map (\(a,i) -> O.ActionSet i a) constargs) ++ 
                                     [O.ActionResubmit $ I.plEntryNode pl]
    where
    pl = (snd ?ir) M.! f
    (constargs, varargs) = partition (O.exprIsConst . fst) $ zip (map (mkExpr r) as) (map (mkExpr r) $ I.plInputs pl)
mkNext n nd i _ (I.Controller _ _) = [ O.ActionSet (O.EField (O.Field "metadata" 64) Nothing) 
                                                   (O.EVal $ O.Value 64 $ ((toInteger plnum) `shiftL` 48) + ((toInteger swnum) `shiftL` 32) + ((toInteger nd) `shiftL` 16) + toInteger i)
                                     , O.ActionController]
    where plnum = fromJust $ findIndex ((==n) . fst) $ M.toList (snd ?ir)
          swnum = fromJust $ findIndex ((== fst ?ir) . name) $ C.refineSwitches ?r

--mkGoto :: I.Pipeline -> I.NodeId -> O.Action
--mkGoto pl nd = 
--    case G.lab (I.plCFG pl) nd of
--         Just (I.Fork{}) -> O.ActionGroup nd
--         _               -> O.ActionGoto nd 
