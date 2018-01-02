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

-- OpenFlow protocol handler for OVS based on the openflow library
-- Andreas Voellmy's openflow library for Haskell

{-# LANGUAGE RecordWildCards, FlexibleContexts, ScopedTypeVariables, LambdaCase #-}

module OpenFlow.OVSProtocol where

import qualified Data.Map as M
import Control.Monad
import Control.Exception
import Control.Concurrent
import Data.List
import Data.IORef
import Data.Bits
import Data.Word
import Data.Maybe
import Data.Binary.Get
import Data.Binary.Put
import qualified Data.ByteString      as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Graph.Inductive as G 

import Network.Data.OF13.Message 
import Network.Data.Ethernet
import qualified Network.Data.OF13.Server as OFP

import Util
import Name
import Backend
import Eval
import Syntax
import OpenFlow.OVSPacket
import OpenFlow.OVSConst
import qualified OpenFlow.IR2OF    as OF
import qualified IR.IR             as IR
import qualified IR.Compile2IR     as IR



-- index OXMs for convenient lookup
mapOXMs :: [OXM] -> M.Map OXKey OXM
mapOXMs oxms = foldl' addoxm M.empty oxms
    where
    addoxm :: M.Map OXKey OXM -> OXM -> M.Map OXKey OXM
    addoxm m oxm = M.insert
                   (case oxm of
                        OXMOther c f _ _       -> OOXMOther c f
                        InPort{}               -> OInPort
                        InPhyPort{}            -> OInPhyPort
                        Metadata{}             -> OMetadata
                        EthDst{}               -> OEthDst
                        EthSrc{}               -> OEthSrc
                        EthType{}              -> OEthType
                        IPv4Dst{}              -> OIPv4Dst
                        IPv4Src{}              -> OIPv4Src
                        NiciraRegister i _     -> ONiciraRegister i
                        PacketRegister i _     -> OPacketRegister i
                        OXM VLANID{}         _ -> OVLANID        
                        OXM VLANPCP{}        _ -> OVLANPCP       
                        OXM IPDSCP{}         _ -> OIPDSCP        
                        OXM IPECN{}          _ -> OIPECN         
                        OXM IPProto{}        _ -> OIPProto       
                        OXM TCPSrc{}         _ -> OTCPSrc        
                        OXM TCPDst{}         _ -> OTCPDst        
                        OXM UDPSrc{}         _ -> OUDPSrc        
                        OXM UDPDst{}         _ -> OUDPDst        
                        OXM SCTPSrc{}        _ -> OSCTPSrc       
                        OXM SCTPDst{}        _ -> OSCTPDst       
                        OXM ICMPv4_Type{}    _ -> OICMPv4_Type   
                        OXM ICMPv4_Code{}    _ -> OICMPv4_Code   
                        OXM ARP_OP{}         _ -> OARP_OP        
                        OXM ARP_SPA{}        _ -> OARP_SPA       
                        OXM ARP_TPA{}        _ -> OARP_TPA       
                        OXM ARP_SHA{}        _ -> OARP_SHA       
                        OXM ARP_THA{}        _ -> OARP_THA       
                        OXM IPv6Src{}        _ -> OIPv6Src       
                        OXM IPv6Dst{}        _ -> OIPv6Dst       
                        OXM IPv6_FLabel{}    _ -> OIPv6_FLabel   
                        OXM ICMPv6_Type{}    _ -> OICMPv6_Type   
                        OXM ICMPv6_Code{}    _ -> OICMPv6_Code   
                        OXM IPv6_ND_Target{} _ -> OIPv6_ND_Target
                        OXM IPv6_ND_SLL{}    _ -> OIPv6_ND_SLL   
                        OXM IPv6_ND_TLL{}    _ -> OIPv6_ND_TLL   
                        OXM MPLS_Label{}     _ -> OMPLS_Label    
                        OXM MPLS_TC{}        _ -> OMPLS_TC       
                        OXM MPLS_BOS{}       _ -> OMPLS_BOS      
                        OXM PBB_ISID{}       _ -> OPBB_ISID      
                        OXM TunnelDst{}      _ -> OTunnelDst
                        OXM TunnelID{}       _ -> OTunnelID      
                        OXM IPv6_EXTHDR{}    _ -> OIPv6_EXTHDR) oxm m

ovsStart :: Refine -> OF.IRSwitches -> PktCB -> IO ()
ovsStart r ir cb = do
    _ <- forkIO $ OFP.runServer 6633 (factory r ir cb)
    putStrLn "OF controller is running on 6633"

data SwitchCtx = SwitchCtx { swSw     :: OFP.Switch
                           , swName   :: String
                           , swId     :: SwitchID
                           , swRefine :: Refine
                           , swIR     :: OF.IRSwitches
                           , swCB     :: PktCB
                           }

sendMessage :: OFP.Switch -> [Message] -> IO ()
sendMessage sw ms = do 
    mapM_ (\m -> putStrLn $ "->OF message: " ++ show m) ms
    OFP.sendMessage sw ms

factory :: Refine -> OF.IRSwitches -> PktCB -> OFP.Switch -> IO (Maybe Message -> IO ())
factory r ir cb sw = do
    putStrLn "OF Connecting"
    sendMessage sw [ Hello { xid = 0, len = 8 }
                   , FeatureRequest { xid = 1 }]
    ref <- newIORef $ SwitchCtx sw "" 0 r ir cb
    return (messageHandler ref)

messageHandler :: IORef SwitchCtx -> Maybe Message -> IO ()
messageHandler _ Nothing = putStrLn "OF Disconnecting"
messageHandler r (Just msg) = do
    c@SwitchCtx{..} <- readIORef r
    putStrLn $ "<-OF message from " ++ swName ++ "(" ++ show swId ++ "): " ++ show msg
    case msg of 
         EchoRequest{..}  -> sendMessage swSw [EchoReply xid body]
         FeatureReply{..} -> writeIORef r $ c {swId = sid}
         PacketIn{..}     -> doPacketIn r msg 
         _                -> return ()

doPacketIn :: IORef SwitchCtx -> Message -> IO ()
doPacketIn r msg@PacketIn{..} = (do
    SwitchCtx{..} <- readIORef r
    let oxmmap = mapOXMs $ oxms match
    let inpnum = fmap inPortID $ M.lookup OInPort oxmmap
    -- locate IR node based on metadata in the packet
    (pidx,swidx, nd,i) <- case M.lookup OMetadata oxmmap of 
                               Just Metadata{..} -> let slice x h l = fromIntegral $ bitSlice x h l in
                                                    return (slice oxmMetadata 63 48, slice oxmMetadata 47 32, slice oxmMetadata 31 16, slice oxmMetadata 15 0)
                               _                 -> error "message does not contain metadata value"
    when (swidx >= (length $ refineSwitches swRefine)) $ error $ "invalid switch number " ++ show swidx
    let switch = refineSwitches swRefine !! swidx
    let swir = swIR M.! (name switch)
    when (pidx >= (M.size swir)) $ error $ "invalid pipeline number " ++ show pidx
    let pl = snd $ M.toList swir !! pidx
    node <- case G.lab (IR.plCFG pl) nd of
                 Nothing -> error $ "invalid node number " ++ show nd
                 Just x  -> return x
    -- extract function name and arguments from IR
    nxt <- case node of
                IR.Fork   {..} -> return $ IR.bbNext nodeBB
                IR.Lookup {..} -> case i of
                                       0 -> return $ IR.bbNext nodeThen 
                                       1 -> return $ IR.bbNext nodeElse
                                       _ -> error $ "invalid index " ++ show i ++ " in Lookup node " ++ show node
                IR.Cond   {..} -> do when (i >= length nodeConds) $ error $ "invalid index " ++ show i ++ " in Cond node " ++ show node
                                     return $ IR.bbNext $ snd $ nodeConds !! i
                IR.Par    {..} -> do when (i >= length nodeBBs) $ error $ "invalid index " ++ show i ++ " in Par node " ++ show node
                                     return $ IR.bbNext $ nodeBBs !! i
    (f, as) <- case nxt of
                    IR.Controller f' as' -> return (f', as')
                    _                    -> error $ "invalid Next action: " ++ show nxt
    --putStrLn $ "action: " ++ f ++ "(" ++ (intercalate ", " $ map show as') ++ ")"
    -- parse packet
    (pkt, rest) <- parsePkt oxmmap payload
    let irpkt = IR.struct2Record swRefine ovsStructReify "" pkt
    putStrLn $ "packet-in: " ++ show pkt
    -- evaluate arguments
    let as' = map (eval oxmmap irpkt) as
    --putStrLn $ "payload: " ++ show rest
    -- call swCB
    outpkts <- swCB f as' pkt 
    -- send packets
    mapM_ (\case 
           (pkt', (E (ESend _ (E (ELocation _ _ key _))))) -> do 
                putStrLn $ "packet-out: " ++ show pkt'
                let E (EBit _ _ pnum) = evalConstExpr swRefine $ eField key "portnum"
                    (b, acts) = unparsePkt pkt' rest
                    acts' = acts ++ [Output (fromInteger pnum) Nothing]
                sendMessage swSw [PacketOut xid Nothing inpnum acts' b]
           (pkt', (E (EApply _ fun fas))) -> do
                putStrLn $ "packet-out (recirculate): " ++ show pkt'
                let -- find fun's pipeline
                    fpl = swir M.! fun
                    fidx = fromJust $ M.lookupIndex fun swir
                    -- convert as to IR
                    fas' = concatMap (IR.val2Scalars swRefine ovsStructReify) fas
                    -- filter inputs to the function
                    fas'' = map (\(idx,reg) -> (fas' !! idx, reg)) $ IR.plInputs fpl
                    -- create output message
                    (b, acts) = unparsePkt pkt' rest
                    regacts = concatMap (\(v,reg) -> case v of
                                                          IR.EBool True  -> setRegAction reg 1
                                                          IR.EBool False -> setRegAction reg 0
                                                          IR.EBit  _ x   -> setRegAction reg x
                                                          _              -> error $ "OVSPacket.doPacketIn: unexpected value: " ++ show v) fas''
                    meta = SetField $ Metadata (fromIntegral fidx) (-1) False 
                    acts' = acts ++ [meta] ++ regacts ++  [Output oFPP_TABLE Nothing]
                sendMessage swSw [PacketOut xid Nothing Nothing acts' b]
           (_,x) -> error $ "OVSPacket.doPacketIn: unexpected result: " ++ show x
           ) 
           outpkts 
    ) `catch` (\(e::SomeException) -> do 
                            putStrLn $ "error handling packet-in message: " ++ show e ++ "\nmessage content: " ++ show msg
                            return ())
doPacketIn _ _ = return ()

parsePkt :: M.Map OXKey OXM -> B.ByteString -> IO (Expr, B.ByteString)
parsePkt oxmmap buf = do
    pkt <- case runGetOrFail getEthernetFrame (BL.fromStrict buf) of
                Left  (_,_,e) -> error $ "failed to parse packet: " ++ e
                Right (_,_,p) -> return p
    return $ packet2Expr oxmmap pkt

unparsePkt :: Expr -> B.ByteString -> (B.ByteString, [Action])
unparsePkt e pl = ( BL.toStrict $ runPut $ putEthFrame pkt
                  , if tunid == 0 
                       then [] 
                       else [ {-SetField $ OXM (TunnelDst tundst 0xffffffff) False
                            , -}SetField $ OXM (TunnelID tunid 0xffffffffffffffff) False])
    where 
    (pkt, tunid, tundst) = expr2Packet e pl

eval :: M.Map OXKey OXM -> IR.Record -> IR.Expr -> Expr
eval oxms pkt e = 
    case e of
         IR.EBool     b             -> eBool b
         IR.EBit      w v           -> eBit w v
         IR.EVar      "reg0"    _   -> eBit 32 $ getreg 0
         IR.EVar      "reg1"    _   -> eBit 32 $ getreg 1
         IR.EVar      "reg2"    _   -> eBit 32 $ getreg 2
         IR.EVar      "reg3"    _   -> eBit 32 $ getreg 3
         IR.EVar      "reg4"    _   -> eBit 32 $ getreg 4
         IR.EVar      "reg5"    _   -> eBit 32 $ getreg 5
         IR.EVar      "reg6"    _   -> eBit 32 $ getreg 6
         IR.EVar      "reg7"    _   -> eBit 32 $ getreg 7
         IR.EVar      "reg8"    _   -> eBit 32 $ getreg 8
         IR.EVar      "reg9"    _   -> eBit 32 $ getreg 9
         IR.EVar      "reg10"   _   -> eBit 32 $ getreg 10
         IR.EVar      "reg11"   _   -> eBit 32 $ getreg 11
         IR.EVar      "reg12"   _   -> eBit 32 $ getreg 12
         IR.EVar      "reg13"   _   -> eBit 32 $ getreg 13
         IR.EVar      "reg14"   _   -> eBit 32 $ getreg 14
         IR.EVar      "reg15"   _   -> eBit 32 $ getreg 15
         IR.EVar      "xreg0"   _   -> eBit 64 $ getxreg 0
         IR.EVar      "xreg1"   _   -> eBit 64 $ getxreg 1
         IR.EVar      "xreg2"   _   -> eBit 64 $ getxreg 2
         IR.EVar      "xreg3"   _   -> eBit 64 $ getxreg 3
         IR.EVar      "xreg4"   _   -> eBit 64 $ getxreg 4
         IR.EVar      "xreg5"   _   -> eBit 64 $ getxreg 5
         IR.EVar      "xreg6"   _   -> eBit 64 $ getxreg 6
         IR.EVar      "xreg7"   _   -> eBit 64 $ getxreg 7
         IR.EVar      "xxreg0"  _   -> eBit 128 $ getxxreg 0
         IR.EVar      "xxreg1"  _   -> eBit 128 $ getxxreg 1
         IR.EVar      "xxreg2"  _   -> eBit 128 $ getxxreg 2
         IR.EVar      "xxreg3"  _   -> eBit 128 $ getxxreg 3
         IR.ESlice    x h l         -> eSlice (eval oxms pkt x) h l
         IR.EBinOp    op x1 x2      -> eBinOp op (eval oxms pkt x1) (eval oxms pkt x2)
         IR.EUnOp     op x          -> eUnOp op $ eval oxms pkt x
         IR.EPktField f         _   -> case M.lookup f pkt of
                                            Nothing -> error $ "Packet does not contain field " ++ show f
                                            Just x  -> eval oxms pkt x
         _                          -> error $ "Not implemented: OVSProtocol.eval " ++ show e
    where
    getreg i   = case getofreg (i `div` 2) of
                      Just v | testBit i 0 -> bitSlice v 31 0
                             | otherwise   -> bitSlice v 63 32
                      Nothing -> fromIntegral $ maybe 0 (\(NiciraRegister _ v) -> v) $ M.lookup (ONiciraRegister i) oxms
    getofreg i = fmap (\(PacketRegister _ v) -> fromIntegral v) $ M.lookup (OPacketRegister i) oxms
    getxreg i  = case getofreg i of
                      Just v  -> v
                      Nothing -> (getreg (2*i) `shiftL` 32) + getreg (2*i + 1)
    getxxreg i = (getxreg (2*i) `shiftL` 64) + getxreg (2*i + 1)

setReg :: Int -> Int -> Int -> Word32 -> Action
setReg reg off nbits val = SetNiciraRegister reg (fromIntegral off) (fromIntegral nbits) val

setXReg :: Int -> Int -> Int -> Word64 -> [Action]
setXReg reg off nbits val = a0 ++ a1
    where
    off0    = max 0 (off - 32)
    nbits0  = nbits - (max 0 (32 - off))
    val0    = fromIntegral $ bitSlice val (nbits - 1) (nbits - nbits0)
    off1    = off
    nbits1  = min (32 - off1) nbits
    val1    = fromIntegral $ bitSlice val (nbits1 - 1) 0
    a0      = if nbits0 >= 0
                 then [setReg (2*reg) off0 nbits0 val0]
                 else []
    a1      = if nbits1 >= 0
                 then [setReg (2*reg+1) off1 nbits1 val1]
                 else []

setXXReg :: Int -> Int -> Int -> Integer -> [Action]
setXXReg reg off nbits val = a0 ++ a1
    where
    off0    = max 0 (off - 64)
    nbits0  = nbits - (max 0 (64 - off))
    val0    = fromInteger $ bitSlice val (nbits - 1) (nbits - nbits0)
    off1    = off
    nbits1  = min (64 - off1) nbits
    val1    = fromInteger $ bitSlice val (nbits1 - 1) 0
    a0      = if nbits0 >= 0
                 then setXReg (2*reg) off0 nbits0 val0
                 else []
    a1      = if nbits1 >= 0
                 then setXReg (2*reg+1) off1 nbits1 val1
                 else []

setRegAction :: IR.Expr -> Integer -> [Action]
setRegAction (IR.EVar reg _) v | isPrefixOf "reg" reg   = setRegAction' reg 0 32  v
setRegAction (IR.EVar reg _) v | isPrefixOf "xreg" reg  = setRegAction' reg 0 64  v
setRegAction (IR.EVar reg _) v | isPrefixOf "xxreg" reg = setRegAction' reg 0 128 v
setRegAction (IR.ESlice (IR.EVar reg _) h l) v          = setRegAction' reg l (h-l+1) v
setRegAction e  _                                       = error $ "OVSProtocol.setRegAction: unexpected expression " ++ show e

setRegAction' :: String -> Int -> Int -> Integer -> [Action]
setRegAction' reg off nbits val = 
    case reg of
         "reg0"   -> [setReg 0  off nbits val32]
         "reg1"   -> [setReg 1  off nbits val32]
         "reg2"   -> [setReg 2  off nbits val32]
         "reg3"   -> [setReg 3  off nbits val32]
         "reg4"   -> [setReg 4  off nbits val32]
         "reg5"   -> [setReg 5  off nbits val32]
         "reg6"   -> [setReg 6  off nbits val32]
         "reg7"   -> [setReg 7  off nbits val32]
         "reg8"   -> [setReg 8  off nbits val32]
         "reg9"   -> [setReg 9  off nbits val32]
         "reg10"  -> [setReg 10 off nbits val32]
         "reg11"  -> [setReg 11 off nbits val32]
         "xreg0"  -> setXReg 0 off nbits val64
         "xreg1"  -> setXReg 1 off nbits val64
         "xreg2"  -> setXReg 2 off nbits val64
         "xreg3"  -> setXReg 3 off nbits val64
         "xreg4"  -> setXReg 4 off nbits val64
         "xreg5"  -> setXReg 5 off nbits val64
         "xreg6"  -> setXReg 6 off nbits val64
         "xreg7"  -> setXReg 7 off nbits val64
         "xxreg0" -> setXXReg 0 off nbits val
         "xxreg1" -> setXXReg 1 off nbits val
         "xxreg2" -> setXXReg 2 off nbits val
         "xxreg3" -> setXXReg 3 off nbits val
         _        -> error $ "OVSProtocol.setRegAction': unknown register " ++ reg
    where val32 = fromInteger val
          val64 = fromInteger val

ovsStop :: IO ()
ovsStop = return ()

