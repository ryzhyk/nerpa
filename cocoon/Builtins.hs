{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

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

{-# LANGUAGE RankNTypes, FlexibleContexts, ImplicitParams #-}

-- Interface to SMT2 format

module Builtins( Builtin(..)
               , builtins) where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe
import qualified Data.Map as M

import Syntax
import Name
import Util
import Eval
import Validate
import Backend
import Type
import Pos
import qualified IR.Compile2IR as IR
import qualified IR.IR         as IR

data Builtin = Builtin { bfuncName          :: String
                       , bfuncValidate1     :: forall me . (MonadError String me) => Refine -> ECtx -> Expr -> me ()
                       , bfuncValidate2     :: forall me . (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
                       , bfuncType          :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
                       , bfuncCompileExprAt :: StructReify -> Refine -> (M.Map String String) -> ECtx -> IR.NodeId -> Maybe IR.NodeId -> ENode -> State IR.Pipeline (M.Map String String)
                       , bfuncMkExpr        :: StructReify -> Refine -> (M.Map String String) -> ECtx -> ExprNode (IR.ExprTree IR.Expr) -> IR.ExprTree IR.Expr
                       --, bfuncPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       --, bfuncPrintP4     :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       --, bfuncToSMT       :: [SMT.Expr] -> SMT.Expr
                       , bfuncEval          :: Expr -> EvalState Expr
                       }

instance WithName Builtin where
    name = bfuncName

builtins :: [Builtin]
builtins = [ bprint
           , bct
           --, bctField "ct_inv"   IR.TBool
           --, bctField "ct_rel"   IR.TBool
           --, bctField "ct_rpl"   IR.TBool
           --, bctField "ct_new"   IR.TBool
           --, bctField "ct_est"   IR.TBool
           , bctField "ct_state" (IR.TBit 32)
           , bctField "ct_label" (IR.TBit 128)
           , bctCommit
           , bctLB
           ]

{- Some reusable implementations -}

notImplemented bin meth = error $ "Builtins: method " ++ meth ++ " is not supported for builtin function " ++ bin
skipValidate2 _ _ _ = return ()

compileExprAt :: StructReify -> Refine -> (M.Map String String) -> ECtx -> IR.NodeId -> Maybe IR.NodeId -> ENode -> State IR.Pipeline (M.Map String String)
compileExprAt structs r vars ctx entrynd exitnd e@(EBuiltin _ f as) = do
    let as' = concat $ mapIdx (\a i -> let ?r = r
                                           ?s = structs
                                       in IR.mkExpr vars (CtxBuiltin e ctx i) a) as
    IR.updateNode entrynd (IR.Par [IR.BB [IR.ABuiltin f as'] $ maybe IR.Drop IR.Goto exitnd]) $ maybeToList exitnd
    return vars
compileExprAt _ _ _ _ _ _ e = error $ "Builtins.compileExprAt " ++ show e



{- print(expr) -}

bprint = Builtin "print" 
                 printValidate1
                 skipValidate2
                 printType
                 (\_ _ _ _ _ _ _ -> notImplemented "print" "bfuncCompileExprAt")
                 (\_ _ _ _ _     -> notImplemented "print" "bfuncMkExpr")
                 printEval

printValidate1 :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
printValidate1 r ctx (E e@(EBuiltin _ _ as)) = mapIdxM_ (\a i -> exprValidate r (CtxBuiltin e ctx i) a) as
printValidate1 _ _ e = error $ "Builtins.printValidate1 " ++ show e

printType :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
printType _ _ _ = tTuple []

printEval :: Expr -> EvalState Expr
printEval (E (EBuiltin _ _ es)) = do mapM_ eyield es
                                     return $ eTuple []
printEval e = error $ "Builtins.printEval " ++ show e

{- ct() -}

bct = Builtin "ct" 
              ctValidate1
              ctValidate2
              ctType
              compileExprAt
              (\_ _ _ _ _ -> notImplemented "ct" "bfuncMkExpr")
              ctEval

ctValidate1 :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
ctValidate1 _ _   (E (EBuiltin _ _ [_])) = return()                                         
ctValidate1 r _   (E (EBuiltin p _ _))   = errR r p $ "ct() takes one argument"
ctValidate1 _ _   e                      = error $ "Builtins.ctValidate1 " ++ show e

ctValidate2 :: (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
ctValidate2 r _   (EBuiltin _ _ [z]) = matchType (pos z) r (tBit 16) z
ctValidate2 _ _   e                  = error $ "Builtins.ctValidate2 " ++ show e

ctType :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
ctType _ _ _ = tTuple []

ctEval :: Expr -> EvalState Expr
ctEval (E (EBuiltin _ _ _)) = return $ eTuple []
ctEval e = error $ "Builtins.ctEval " ++ show e

{- ct_inv(), ct_rel(), ct_rpl(), ct_new(), ct_est(), ct_label() -}

bctField f t = Builtin f
                       (ctfValidate1 f t)
                       skipValidate2
                       (ctfType f t)
                       (ctfCompileExprAt f t)
                       (ctfMkExpr f t)
                       (\_ -> notImplemented f "bfuncEval")

ctfValidate1 :: (MonadError String me) => String -> IR.Type ->  Refine -> ECtx -> Expr -> me ()
ctfValidate1 _ _ _ _ (E (EBuiltin _ _ [])) = return()
ctfValidate1 f _ r _ (E (EBuiltin p _ _))  = errR r p $ f ++ "() does not take arguments"
ctfValidate1 _ _ _ _ e                     = error $ "Builtins.ctfValidate1 " ++ show e

ctfType :: String -> IR.Type -> Refine -> ECtx -> ExprNode (Maybe Type) -> Type
ctfType _ IR.TBool    _ _ _ = tBool
ctfType _ (IR.TBit w) _ _ _ = tBit w
ctfType _ IR.TString  _ _ _ = tString

ctfCompileExprAt :: String -> IR.Type -> StructReify -> Refine -> (M.Map String String) -> ECtx -> IR.NodeId -> Maybe IR.NodeId -> ENode -> State IR.Pipeline (M.Map String String)
ctfCompileExprAt _ _ _ _ vars _ entrynd exitnd _ = IR.ignore vars entrynd exitnd

ctfMkExpr :: String -> IR.Type -> StructReify -> Refine -> (M.Map String String) -> ECtx -> ExprNode (IR.ExprTree IR.Expr) -> IR.ExprTree IR.Expr
ctfMkExpr f t _ _ _ _ _ = IR.ETLeaf $ IR.EPktField f t


{- ct_commit(zone), ct_commit(zone, label) -}

bctCommit = Builtin "ct_commit" 
                    ctCommitValidate1
                    ctCommitValidate2
                    ctCommitType
                    compileExprAt
                    (\_ _ _ _ _ -> notImplemented "ct_commit" "bfuncMkExpr")
                    (\_ -> notImplemented "ct_commit" "bfuncEval")

ctCommitValidate1 :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
ctCommitValidate1 _ _   (E (EBuiltin _ _ [_]))   = return()                                         
ctCommitValidate1 _ _   (E (EBuiltin _ _ [_,_])) = return()                                         
ctCommitValidate1 r _   (E (EBuiltin p _ _))     = errR r p $ "ct_commit() takes one or two arguments"
ctCommitValidate1 _ _   e                        = error $ "Builtins.ctCommitValidate1 " ++ show e

ctCommitValidate2 :: (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
ctCommitValidate2 r _   (EBuiltin _ _ [z])   = matchType (pos z) r (tBit 16) z
ctCommitValidate2 r _   (EBuiltin _ _ [z,l]) = do matchType (pos z) r (tBit 16) z
                                                  matchType (pos z) r (tBit 128) l
ctCommitValidate2 _ _   e                    = error $ "Builtins.ctValidate2 " ++ show e

ctCommitType :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
ctCommitType _ _ _ = tTuple []

{- ct_lb(zone), ct_lb(zone, ip, port), ct_lb(zone, ip) -}
bctLB = Builtin "ct_lb" 
                ctLBValidate1
                ctLBValidate2
                ctLBType
                compileExprAt
                (\_ _ _ _ _ -> notImplemented "ct_lb" "bfuncMkExpr")
                (\_ -> notImplemented "ct_lb" "bfuncEval")

ctLBValidate1 :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
ctLBValidate1 _ _   (E (EBuiltin _ _ [_]))     = return()                                         
ctLBValidate1 _ _   (E (EBuiltin _ _ [_,_]))   = return()                                         
ctLBValidate1 _ _   (E (EBuiltin _ _ [_,_,_])) = return()                                         
ctLBValidate1 r _   (E (EBuiltin p _ _))       = errR r p $ "ct_lb() takes one, two, or three arguments"
ctLBValidate1 _ _   e                          = error $ "Builtins.ctLBValidate1 " ++ show e

ctLBValidate2 :: (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
ctLBValidate2 r _   (EBuiltin _ _ as)   = do matchType (pos $ head as) r (tBit 16) (head as)
                                             when (length as >= 2) 
                                                $ matchType (pos $ as !! 1) r (tUser "ip_addr_t") (as !! 1)
                                             when (length as >= 3) 
                                                $ matchType (pos $ as !! 2) r (tBit 16) (as !! 2)
ctLBValidate2 _ _   e                   = error $ "Builtins.ctLBValidate2 " ++ show e

ctLBType :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
ctLBType _ _ _ = tTuple []


-- {- select!(array, index) -}
-- 
-- arraySelectValidate :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
-- arraySelectValidate r ctx p args = do
--     assertR r (length args == 2) p "select! requires two arguments"
--     let [arr, idx] = args
--     assertR r (isArray r ctx arr) (pos $ head args) "the first argument of select! must be an array"
--     assertR r (isUInt r ctx idx) (pos $ head args) "the second argument of select! must be a uint"
-- 
-- arraySelectType :: Refine -> ECtx -> [Expr] -> Type
-- arraySelectType r ctx args = t
--     where (a:_) = args
--           TArray _ t _ = typ' r ctx a
-- 
-- arraySelectPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
-- arraySelectPrintBoogie _ _ _ args = arr <> (brackets idx)
--     where [arr, idx] = args
-- 
-- arraySelectPrintP4 :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
-- arraySelectPrintP4 r ctx args p4args = 
--     let [arr, _]  = args
--         [p4arr, p4idx] = p4args
--         TArray _ t _ = typ' r ctx arr in
--     case typ' r ctx t of
--          TBool _ -> parens $ (parens $ (parens $ p4arr <+> pp ">>" <+> p4idx) <+> pp "&" <+> pp "0x1") <+> pp "==" <+> pp "0x1"
--          _       -> error "Builtins.arraySelectPrintP4 not implemented"
-- 
-- arraySelectToSMT :: [SMT.Expr] -> SMT.Expr
-- arraySelectToSMT args = SMT.EApply "select" args
-- 
-- arraySelectEval :: [Expr] -> Expr
-- arraySelectEval args = 
--     let [arr, idx] = args in
--     case arr of
--          EBuiltin _ "array" elems -> case idx of
--                                           EInt _ _ i -> elems !! fromInteger i
--                                           _          -> EBuiltin nopos "select" [arr, idx]
--          _                        -> EBuiltin nopos "select" [arr, idx]
-- 
-- arraySelect = Builtin "select" 
--                       arraySelectValidate
--                       arraySelectType
--                       arraySelectPrintBoogie
--                       arraySelectPrintP4
--                       arraySelectToSMT
--                       arraySelectEval
-- 
-- 
-- {- array!(x1, x2, ...) -}
-- 
-- arrayArrayValidate :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
-- arrayArrayValidate r ctx p args = do
--     assertR r (length args > 0) p "select! requires at least one argument"
--     mapM_ (\a -> matchType r ctx a (head args)) $ tail args
--         
-- arrayArrayType :: Refine -> ECtx -> [Expr] -> Type
-- arrayArrayType r ctx args = TArray nopos (typ' r ctx $ head args) (length args) 
-- 
-- arrayArrayPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
-- arrayArrayPrintBoogie r ctx args bgargs = 
--     foldIdx (\e a i -> parens $ e <> (brackets $ pp i <+> pp ":=" <+> a)) (apply (emptyTypeFuncName r $ arrayArrayType r ctx args) []) bgargs
-- 
-- arrayArrayPrintP4 :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
-- arrayArrayPrintP4 r ctx args p4args = 
--     case typ' r ctx $ head args of
--          TBool _ -> parens $ hsep $ punctuate (pp " |") $ mapIdx mkBit p4args
--          _       -> error "Builtins.arrayArrayPrintP4 not implemented"
--     where mkBit a i = parens $ (parens $ pp "(bit<" <> pp len <> pp ">)" <> (parens $ pp "(bit<1>)" <> a)) <+> pp "<<" <+> pp i
--           len = length p4args
-- 
-- arrayArrayToSMT :: [SMT.Expr] -> SMT.Expr
-- arrayArrayToSMT _ = error "Not implemented: arrayArrayToSMT"
-- --parens $ (parens $ pp "as const" <+> (parens $ pp "Array Int" <+> t)) <+> defval
-- 
-- 
-- arrayArrayEval :: [Expr] -> Expr
-- arrayArrayEval args = EBuiltin nopos "array" args
-- 
-- arrayArray = Builtin "array" 
--                       arrayArrayValidate
--                       arrayArrayType
--                       arrayArrayPrintBoogie
--                       arrayArrayPrintP4
--                       arrayArrayToSMT
--                       arrayArrayEval
