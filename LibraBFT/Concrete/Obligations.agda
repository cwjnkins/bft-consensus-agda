{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
import LibraBFT.Concrete.Properties.VotesOnce as VO
import LibraBFT.Concrete.Properties.LockedRound as LR

open import LibraBFT.Impl.Base.Types
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open EpochConfig

open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Yasm.Yasm NodeId (ℓ+1 0ℓ) EpochConfig epochId authorsN getPubKey ConcSysParms

-- This module collects in one place the obligations an
-- implementation must meet in order to enjoy the properties
-- proved in Abstract.Properties.

module LibraBFT.Concrete.Obligations where
  record ImplObligations : Set₁ where
    field
      -- Structural obligations:
      sps-cor : StepPeerState-AllValidParts

      -- Semantic obligations:
      --
      -- VotesOnce:
      vo₁ : VO.ImplObligation₁
      vo₂ : VO.ImplObligation₂

      -- LockedRound:
      lr₁ : LR.ImplObligation₁
