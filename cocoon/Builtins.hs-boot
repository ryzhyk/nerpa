{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Builtins where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

import Syntax
import Name
import Backend
import {-# SOURCE #-} Eval
import qualified IR.IR as IR

data Builtin = Builtin { bfuncName          :: String
                       , bfuncValidate1     :: forall me . (MonadError String me) => Refine -> ECtx -> Expr -> me ()
                       , bfuncValidate2     :: forall me . (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
                       , bfuncType          :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
                       , bfuncCompileExprAt :: StructReify -> Refine -> (M.Map String String) -> ECtx -> IR.NodeId -> Maybe IR.NodeId -> ENode -> State IR.Pipeline (M.Map String String)
                       , bfuncMkExpr        :: StructReify -> Refine -> (M.Map String String) -> ECtx -> ExprNode (IR.ExprTree IR.Expr) -> IR.ExprTree IR.Expr
                       , bfuncEval          :: Expr -> EvalState Expr
                       }

instance WithName Builtin 

builtins :: [Builtin]
