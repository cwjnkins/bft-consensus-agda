{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.Liveness.ProposerElection where

open RWST-do

postulate
  isValidProposerM : Author → Round → LBFT Bool
  getValidProposer : ProposerElection → Round → Author

isValidProposalM : Block → LBFT Bool
isValidProposalM b = maybeS (b ^∙ bAuthor) (pure false) (λ a → isValidProposerM a (b ^∙ bRound))