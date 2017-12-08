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

{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, FlexibleContexts, ScopedTypeVariables #-}

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
import qualified IR.IR             as I
import qualified IR.Compile2IR     as I
import qualified IR.Registers      as I
import qualified OpenFlow.OpenFlow as O
import qualified Backend           as B
import qualified Syntax            as C -- Cocoon
import qualified Eval              as C
import qualified Relation          as C
import qualified NS                as C

-- Uniquely identify an instance of the switch:
type SwitchId = Integer

type IRSwitch = [(String, I.Pipeline)]
type IRSwitches = M.Map String IRSwitch

maxOFTables = 255

-- Runtime state maintained by the controller to keep track of OF group numbers
-- generated for any-queries.  Maps a set of columns in a relation to
-- the set of valuations of this column in the database, the number of times 
-- each valuation occurs and the group number assigned to it.
type SwRuntimeState = M.Map (I.RelName, [I.ColName]) (M.Map [I.Expr] (O.GroupId, M.Map I.Record O.BucketId))
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
                                                `catchError` (\e -> throwError $ "Compiling port " ++ n ++ " of " ++ name sw ++ ":" ++ e)) ir
                       let (ntables, ir'') = assignTables ir'
                       mapM_ (\(n, pl) -> do let dotname = workdir </> addExtension (addExtension n "of") "dot"
                                             trace (unsafePerformIO $ do {I.cfgDump (I.plCFG pl) dotname; return ""}) $ return ()) ir''
                       when (ntables > maxOFTables) 
                           $ throwError $ name sw ++ " requires " ++ show ntables ++ " OpenFlow tables, but only " ++ show maxOFTables ++ " tables are available"
                       return (name sw, ir'')) $ C.refineSwitches r

-- Relabel port CFGs into openflow table numbers
assignTables :: IRSwitch -> (Int, IRSwitch)
assignTables pls = foldl' (\(start, pls') (n,pl) -> let (start', pl') = relabel start pl
                                                    in (start', pls' ++ [(n, pl')])) (1, []) pls
    where 
    relabel :: Int -> I.Pipeline -> (Int, I.Pipeline)
    relabel start pl = (start + length ordered, pl{I.plCFG = cfg', I.plEntryNode = start})
        where
        ordered = G.topsort $ I.plCFG pl
        rename nd = (fromJust $ findIndex (nd==) ordered) + start
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
buildSwitch :: C.Refine -> B.StructReify -> RuntimeState -> IRSwitch -> I.DB -> SwitchId -> ([O.Command], RuntimeState)
buildSwitch r structs s ports db swid = (table0 : (staticcmds ++ updcmds), s')
    where
    table0 = O.AddFlow 0 $ O.Flow 0 [] [O.ActionDrop]
    -- Configure static part of the pipeline
    staticcmds = let ?r = r 
                     ?structs = structs
                 in concatMap (\(pname, pl) -> concatMap (mkNode pname pl) $ G.labNodes $ I.plCFG pl) ports
    -- Configure dynamic part from primary tables
    (updcmds, s') = updateSwitch r structs (M.insert swid M.empty s) ports swid (M.map (map (True,)) db)

updateSwitch :: C.Refine -> B.StructReify -> RuntimeState -> IRSwitch -> SwitchId -> I.Delta -> ([O.Command], RuntimeState)
updateSwitch r structs s ports swid db = (portcmds ++ nodecmds, M.insert swid ssw' s')
    where
    s' = M.alter (Just . maybe M.empty id) swid s
    -- update table0 if ports have been added or removed
    portcmds = let ?r = r 
                   ?structs = structs
               in concatMap (\(pname, pl) -> updatePort pname pl swid db) ports
    -- update pipeline nodes
    (nodecmds, ssw') = let ?r = r 
                           ?structs = structs in
                       let (cmds, ssw) = runState (mapM (\(pname, pl) -> (liftM concat) $ mapM (updateNode db pname pl swid) 
                                                                                        $ G.labNodes $ I.plCFG pl) ports) 
                                                  (s' M.! swid)
                       in (concat cmds, ssw)

updatePort :: (?r::C.Refine, ?structs::B.StructReify) => String -> I.Pipeline -> SwitchId -> I.Delta -> [O.Command]
updatePort pname pl i db = delcmd ++ addcmd
    where
    prel = name $ C.portRel $ C.getPort ?r pname
    (add, del) = partition fst $ filter (\(_, e) -> (C.exprIVal $ C.enode $ C.evalConstExpr ?r (C.eField e "switch")) == i) $ db M.! prel
    match f = let C.E (C.EBit _ w pnum) = C.evalConstExpr ?r (C.eField f "portnum") in
              mkSimpleCond $ I.EBinOp Eq (I.EPktField "portnum" $ I.TBit w) (I.EBit w pnum)
    delcmd = concatMap (\(_,f) -> map (O.DelFlow 0 1) $ match f) del
    addcmd = concatMap (\(_,f) -> map (\m -> O.AddFlow 0 $ O.Flow 1 m [mkGoto pl $ I.plEntryNode pl]) $ match f) add

mkNode :: (?r::C.Refine, ?structs::B.StructReify) => String -> I.Pipeline -> (I.NodeId, I.Node) -> [O.Command]
mkNode pname pl (nd, node) = 
    case node of
         I.Par bs                    -> [ O.AddGroup $ O.Group nd O.GroupAll $ mapIdx (\b i -> O.Bucket Nothing $ mkStaticBB pname pl nd i b) bs 
                                        , O.AddFlow nd $ O.Flow 0 [] [O.ActionGroup nd] ]
         I.Cond cs                   -> map (\(m, a) -> O.AddFlow nd $ O.Flow 0 m a) $ mkCond $ mapIdx (\(c,b) i -> (c, mkStaticBB pname pl nd i b)) cs
         I.Lookup _ _ _ _ el I.First -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB pname pl nd 1 el]
         I.Lookup _ _ _ _ el I.Rand  -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB pname pl nd 1 el]
         I.Fork{}                    -> [O.AddGroup $ O.Group nd O.GroupAll []]

updateNode :: (?r::C.Refine, ?structs::B.StructReify) => I.Delta -> String -> I.Pipeline -> SwitchId -> (I.NodeId, I.Node) -> State SwRuntimeState [O.Command]
updateNode db pname portpl swid (nd, node) = 
    case node of
         I.Par _                      -> return []
         I.Cond _                     -> return []
         I.Lookup t _ pl th _ I.First -> let -- First node of the pipeline? Ignore entries that do not belong to swid
                                             -- TODO: hack; remove when proper table slicing is implemented
                                             (add, del) = if null $ G.pre (I.plCFG portpl) nd
                                                             then partition fst $ filter (\(_, f) -> (C.exprIVal $ C.enode $ (C.evalConstExpr ?r (C.eField f "switch"))) == swid) $ (db M.! t)
                                                             else partition fst (db M.! t) 
                                             delcmd = concatMap (\(_,f) -> map (\O.Flow{..} -> O.DelFlow nd flowPriority flowMatch) 
                                                                               $ mkLookupFlow pname portpl nd f pl $ Left th) del
                                             addcmd = concatMap (\(_,f) -> map (O.AddFlow nd) $ mkLookupFlow pname portpl nd f pl $ Left th) add
                                         in return $ delcmd ++ addcmd
         I.Lookup t _ _ _ _ I.Rand    -> -- create a group for each unique combination of match columns
                                         -- create match entries in the table to forward packets to the group
                                         -- create a bucket in the group for each row in relation
                                         do let (add, del) = partition fst (db M.! t)
                                            delgrcmd <- liftM concat $ mapM (delGroup node . snd) del
                                            addgrcmd <- liftM concat $ mapM (addGroup node . snd) add
                                            return $ delgrcmd ++ addgrcmd
         I.Fork t _ _ b               -> -- TODO: re-implement Fork using the same mechanism as in Lookup Rand above
                                         -- create a bucket for each table row
                                         let (add, del) = partition fst (db M.! t) 
                                             delcmd = map (\(_,f) -> O.DelBucket nd $ getBucketId t f) del
                                             addcmd = map (\(_,f) -> O.AddBucket nd $ O.Bucket (Just $ getBucketId t f) $ mkBB pname portpl nd 0 f b) add
                                         in return $ delcmd ++ addcmd
    where
    delGroup :: I.Node -> C.Expr -> State SwRuntimeState [O.Command]
    delGroup (I.Lookup t _ fpl _ _ _) f = do
        (s::SwRuntimeState) <- get
        let (cols, _) = fpl f
        let f' = I.val2Record ?r ?structs t f
        -- extract column values from f
        let vals = map (f' M.!) cols
        let (g, bkts) = s M.! (t,cols) M.! vals
        let bid = bkts M.! f'
        let bkts' = M.delete f' bkts
        -- update counter in s M.! (rel, cols) M.! val; if the counter drops to 0, delete group and flow entries
        let s' = M.update (Just . M.update (\(gid, _) -> Just (gid, bkts')) vals) (t, cols) s
        let grcmds = if M.size bkts' == 0
                        then (O.DelGroup g) :
                             (map (\O.Flow{..} -> O.DelFlow nd flowPriority flowMatch)
                                  $ mkLookupFlow pname portpl nd f fpl $ Right [O.ActionGroup g])
                        else []
        -- remove empty group
        let s'' = M.update (\m -> let m' = M.update (\(gid,_) -> if M.size bkts' == 0 then Nothing else Just (gid, bkts')) vals m
                                  in if M.size m' == 0 then Nothing else Just m') (t, cols) s'
        put s''
        let delcmd = O.DelBucket g bid
        return $ grcmds ++ [delcmd]
    delGroup _ _ = error "IR2OF.delGroup: unexpected argument"

    addGroup :: I.Node -> C.Expr -> State SwRuntimeState [O.Command]
    addGroup (I.Lookup t _ fpl th _ _) f = do
        s <- get
        let (cols, pl) = fpl f
        let f' = I.val2Record ?r ?structs t f
        -- extract column values from f
        let vals = map (f' M.!) cols
        -- allocate group number if needed (simply increment the biggest group number by 1)
        -- TODO: proper allocator
        let newg = case concatMap (map fst . M.elems) $ M.elems s of
                        [] -> maxOFTables + 1 
                        gs -> maximum gs + 1
        -- update counter in s M.! (rel, cols) M.! val; if the counter is 1 (1st element), create group and flow entries
        let s' = M.alter (maybe (Just $ M.singleton vals (newg, M.empty)) 
                                (Just . (M.alter (maybe (Just (newg, M.empty)) (Just . id)) vals)))
                         (t, cols) s
        let g =fst $ s' M.! (t,cols) M.! vals
        let grcmds = if M.size (snd $ s' M.! (t,cols) M.! vals) == 0
                        then (O.AddGroup $ O.Group g O.GroupSelect []) :
                             (map (O.AddFlow nd) $ mkLookupFlow pname portpl nd f fpl $ Right [O.ActionGroup g])
                        else []
        -- allocate bucket id
        let bid = case M.elems $ snd $ s' M.! (t,cols) M.! vals of
                       []    -> 0
                       bids  -> maximum bids + 1
        let s'' = M.update (Just . M.update (\(gid,bkts) -> Just (gid, M.insert f' bid bkts)) vals) (t, cols) s'
        let addcmd = O.AddBucket g $ O.Bucket (Just bid) $ mkBB pname pl nd 0 f th
        put s''
        return $ grcmds ++ [addcmd]
    addGroup _ _ = error "IR2OF.addGroup: unexpected argument"

getBucketId :: (?r::C.Refine) => String -> C.Expr -> O.BucketId
getBucketId rname f = fromInteger pkey
    where   
    rel = C.getRelation ?r rname
    Just [key] = C.relPrimaryKey rel
    C.E (C.EBit _ _ pkey) = recordField f key

recordField :: (?r::C.Refine) => C.Expr -> C.Expr -> C.Expr
recordField rec fexpr = C.evalConstExpr ?r (f fexpr)
    where
    f (C.E (C.EVar _ v))      = C.eField rec v
    f (C.E (C.EField _ e fl)) = C.eField (f e) fl
    f e                       = error $ "IR2OF.recordField.f " ++ show e

mkStaticBB :: (?r::C.Refine, ?structs::B.StructReify) => String -> I.Pipeline -> I.NodeId -> Int -> I.BB -> [O.Action]
mkStaticBB pname pl nd i b = mkBB pname pl nd i (error "IR2OF.mkStaticBB requesting field value") b

mkBB :: (?r::C.Refine, ?structs::B.StructReify) => String -> I.Pipeline -> I.NodeId -> Int -> C.Expr -> I.BB -> [O.Action]
mkBB pname pl nd i val (I.BB as n) = map (mkAction ival) as ++ mkNext pname pl nd i ival n
    where ival = I.val2Record ?r ?structs (C.exprConstructor $ C.enode val) val

mkAction :: I.Record -> I.Action -> O.Action
mkAction val (I.ASet e1 e2) = O.ActionSet (mkExpr val e1) (mkExpr val e2)
mkAction _   I.ABuiltin{}   = error "not implemented: IR2OF.mkAction ABuiltin"

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

mkLookupFlow :: (?r::C.Refine, ?structs::B.StructReify) => String -> I.Pipeline -> I.NodeId -> C.Expr -> I.FPipeline -> Either I.BB [O.Action] -> [O.Flow]
mkLookupFlow pname pl nd val lpl b = map (\m -> O.Flow 1 m as) matches
    where
    matches = mkPLMatch (snd $ lpl val)
    as = case b of 
              Left bb    -> mkBB pname pl nd 0 val bb
              Right acts -> acts
    
mkCond :: [(I.Expr, [O.Action])] -> [([O.Match], [O.Action])]
mkCond []          = [([], [O.ActionDrop])]
mkCond ((c, a):cs) = mkCond' c [([], a)] $ mkCond cs

mkCond' :: I.Expr -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])]
mkCond' c yes no =
    case c of
         I.EBinOp Eq e1 e2 | I.exprIsBool e1 
                                       -> mkCond' e1 (mkCond' e2 yes no) (mkCond' e2 no yes)
                           | otherwise -> let cs' = mkMatch (mkExpr M.empty e1) (mkExpr M.empty e2)
                                          in concatMap (\c' -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches c' m)) yes) cs' ++ no
         I.EBinOp Neq e1 e2            -> mkCond' (I.EUnOp Not (I.EBinOp Eq e1 e2)) yes no
         I.EBinOp Impl e1 e2           -> mkCond' (I.EBinOp Or (I.EUnOp Not e1) e2) yes no
         I.EUnOp Not e                 -> mkCond' e no yes
         I.EBinOp Or e1 e2             -> mkCond' e1 yes (mkCond' e2 yes no)
         I.EBinOp And e1 e2            -> mkCond' e1 (mkCond' e2 yes no) no
         I.EBool True                  -> yes
         I.EBool False                 -> no
         e  | I.exprType e == I.TBit 1 -> mkCond' (I.EBinOp Eq e (I.EBit 1 1)) yes no
         _                             -> error $ "IR2OF.mkCond': expression is not supported: " ++ show c

-- TODO: use BDDs to encode arbitrary pipelines
mkPLMatch :: I.Pipeline -> [[O.Match]]
mkPLMatch I.Pipeline{..} = 
    if G.order plCFG == 2 
       then case G.lab plCFG plEntryNode of
                 Just (I.Cond cs) -> mkSimpleCond $ cs2expr cs
                 _                -> error $ "IR2OF.mkPLMatch: CFG too complicated:\n" ++ I.cfgToDot plCFG
       else error $ "IR2OF.mkPLMatch: CFG too complicated (" ++ show (G.size plCFG) ++ " nodes):\n" ++ I.cfgToDot plCFG
    -- IR compiler encodes lookup conditions with satisfying branches terminating in Drop
    where
    cs2expr ((c, I.BB [] I.Drop):cs) = I.EBinOp Or c $ cs2expr cs
    cs2expr ((c, _):cs)              = I.EBinOp And (I.EUnOp Not c) $ cs2expr cs
    cs2expr []                       = I.EBool False 

mkSimpleCond :: I.Expr -> [[O.Match]]
mkSimpleCond e = mkSimpleCond' $ I.exprEval e

mkSimpleCond' :: I.Expr -> [[O.Match]]
mkSimpleCond' c =
    case c of
         I.EBinOp Eq e1 e2 | not (I.exprIsBool e1) 
                                     -> mkMatch (mkExpr M.empty e1) (mkExpr M.empty e2)
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

mkMatch :: O.Expr -> O.Expr -> [[O.Match]]
mkMatch e1 e2 | const1 && const2 && v1 == v2 = [[]]
              | const1 && const2 && v1 /= v2 = []
              | const1                       = mkMatch e2 e1
              | const2                       = [[O.Match f (slice2mask sl) (O.valVal v2 `shiftL` l)]]
              | otherwise                    = error $ "IR2OF.mkMatch: cannot match two variables: " ++ show e1 ++ " " ++ show e2
    where
    const1 = O.exprIsConst e1
    const2 = O.exprIsConst e2
    (O.EVal v1) = e1
    (O.EVal v2) = e2
    (O.EField f sl) = e1
    l = maybe 0 snd sl
    slice2mask :: Maybe (Int, Int) -> Maybe O.Mask
    slice2mask msl = fmap (uncurry bitRange) msl

mkNext :: (?r::C.Refine) => String -> I.Pipeline -> I.NodeId -> Int -> I.Record -> I.Next -> [O.Action]
mkNext _ pl _  _ _ (I.Goto nd)        = [mkGoto pl nd]
mkNext _ _  _  _ r (I.Send e)         = [O.ActionOutput $ mkExpr r e]
mkNext _ _  _  _ _ I.Drop             = [O.ActionDrop]
mkNext n _  nd i _ (I.Controller _ _) = [ O.ActionSet (O.EField (O.Field "metadata" 64) Nothing) 
                                                      (O.EVal $ O.Value 64 $ ((toInteger portnum) `shiftL` 48) + ((toInteger nd) `shiftL` 16) + toInteger i)
                                        , O.ActionController]
    where portnum = fromJust $ findIndex ((== n) . name) $ C.refinePorts ?r
    

mkGoto :: I.Pipeline -> I.NodeId -> O.Action
mkGoto pl nd = 
    case G.lab (I.plCFG pl) nd of
         Just (I.Fork{}) -> O.ActionGroup nd
         _               -> O.ActionGoto nd 
