{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Syntax where

open import Data.Empty
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit
open import Dijkstra.AST.Core
open import Function
open import Haskell.Prelude
import      Level
import      Level.Literals as Level using (#_)

instance
  MonadAST : ∀ {OP : ASTOps} → Monad (AST OP)
  Monad.return MonadAST = ASTreturn
  Monad._>>=_ MonadAST = ASTbind