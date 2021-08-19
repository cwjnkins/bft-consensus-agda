{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

------------------------------------------------------------------------------
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block                as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert           as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote                 as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData             as VoteData
import      LibraBFT.Impl.Consensus.SafetyRules.PersistentSafetyStorage as PersistentSafetyStorage
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules             as SafetyRules
import      LibraBFT.Impl.OBM.Crypto                                    as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Types.BlockInfo                               as BlockInfo
open import LibraBFT.Impl.Types.ValidatorSigner                         as ValidatorSigner
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto                             as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                       as String
------------------------------------------------------------------------------

module LibraBFT.Impl.Consensus.SafetyRules.SafetyRulesManager where

storage
  : SafetyRulesConfig -> Author -> SK
  → Either ErrLog PersistentSafetyStorage
storage config obmMe obmSK = do
  pure $ PersistentSafetyStorage.new  -- internalStorage
           obmMe
           (config ^∙ srcObmGenesisWaypoint)
           obmSK

newLocal : PersistentSafetyStorage → Bool → Either ErrLog SafetyRulesManager

new
  : SafetyRulesConfig → Author → SK
  → Either ErrLog SafetyRulesManager
new config obmMe obmSK = do
  storage0               ← storage config obmMe obmSK
  let exportConsensusKey = config ^∙ srcExportConsensusKey
  case config ^∙ srcService of λ where
    SRSLocal → newLocal storage0 exportConsensusKey

newLocal storage0 exportConsensusKey = do
  safetyRules ← SafetyRules.new storage0 exportConsensusKey
  pure (mkSafetyRulesManager (SRWLocal safetyRules))

client : SafetyRulesManager → SafetyRules
client self = case self ^∙ srmInternalSafetyRules of λ where
  (SRWLocal safetyRules) → safetyRules

