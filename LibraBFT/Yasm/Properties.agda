{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Yasm.Base   as LYB
import      LibraBFT.Yasm.System as LYS

-- This module provides some definitions and properties that facilitate
-- proofs of properties about a distributed system modeled by Yasm.System
-- paramaterized by some SystemParameters.

module LibraBFT.Yasm.Properties
   (ℓ-PeerState : Level)
   (ℓ-VSFP : Level)
   (parms       : LYB.SystemParameters ℓ-PeerState)
   -- In addition to the parameters used by the rest of the system model, this module
   -- needs to relate Members to PKs and PeerIds, so that StepPeerState-AllValidParts
   -- can be defined.  This enables the application to prove that honest peers sign
   -- new messages only for their own public key.  The system model does not know that
   -- directly.
 -- A ValidPartForPK collects the assumptions about what a /part/ in the outputs of an honest verifier
 -- satisfies: (i) the epoch field is consistent with the existent epochs and (ii) the verifier is
 -- a member of the associated epoch config, and (iii) has the given PK in that epoch.

   (ValidSenderForPK        : LYS.ValidSenderForPK-type        ℓ-PeerState ℓ-VSFP parms)
 -- A valid part remains valid across peer steps
   (ValidSenderForPK-stable : LYS.ValidSenderForPK-stable-type ℓ-PeerState ℓ-VSFP parms ValidSenderForPK)
  where
 open LYB.SystemParameters parms
 open import LibraBFT.Yasm.Base
 open import LibraBFT.Yasm.System ℓ-PeerState ℓ-VSFP parms
 open import Util.FunctionOverride PeerId _≟PeerId_

 ¬cheatForgeNew : ∀ {pid pk vsig mst outs m}{st : SystemState}
                → (sp : StepPeer st pid mst outs)
                → outs ≡ m ∷ []
                → (ic : isCheat sp)
                → Meta-Honest-PK pk
                → MsgWithSig∈ pk vsig ((pid , m) ∷ msgPool st)
                → MsgWithSig∈ pk vsig (msgPool st)
 ¬cheatForgeNew sc@(step-cheat isch) refl _ hpk mws
    with msg∈pool mws
 ...| there m∈pool = mkMsgWithSig∈ (msgWhole mws) (msgPart mws) (msg⊆ mws) (msgSender mws) m∈pool (msgSigned mws) (msgSameSig mws)
 ...| here m∈pool
    with isch (subst (msgPart mws ⊂Msg_) (cong proj₂ m∈pool) (msg⊆ mws)) (msgSigned mws)
 ...| inj₁ dis = ⊥-elim (hpk dis)
 ...| inj₂ mws' rewrite msgSameSig mws = mws'

 ValidSenderForPK-stable-sys : ∀{st : SystemState}{st' : SystemState}
                             → ReachableSystemState st
                             → Step* st st' → ∀{part α pk}
                             → initialised st α ≡ initd
                             → ValidSenderForPK (peerStates st  α) part α pk
                             → ValidSenderForPK (peerStates st' α) part α pk
 ValidSenderForPK-stable-sys _ step-0 _ v = v
 ValidSenderForPK-stable-sys {pre} r (step-s {pre = st''} st''reach (step-peer {pid} {st' = st'} (step-honest sps))) {part} {α} {pk} ini v
    with pid ≟PeerId α
 ...| yes refl rewrite sym (StepPeer-post-lemma {pre = st''} (step-honest sps)) =
               ValidSenderForPK-stable {part = part} {pk}
                                       (Step*-trans r st''reach) sps (Step*-initdStable st''reach ini)
                                       (ValidSenderForPK-stable-sys r st''reach ini v)
 ...| no  neq  rewrite override-target-≢ {b = st'} {f = peerStates st''} neq = ValidSenderForPK-stable-sys r st''reach ini v
 ValidSenderForPK-stable-sys {pre} r (step-s {pre = st''} st''reach (step-peer {pid} {st' = st'} (step-cheat {m = m} isch))) {α = α} ini v =
                             subst (λ ps → ValidSenderForPK (ps α) _ _ _)
                                   (sym (cheatStepDNMPeerStates {pre = st''} (step-cheat {m = m} isch) unit))
                                   (ValidSenderForPK-stable-sys r st''reach ini v)

 override-elim-ValidSenderForPK : ∀ {ps part pid pk f}
                                → ValidSenderForPK ps part pid pk
                                → ValidSenderForPK (⟦ f , pid ← ps ⟧ pid) part pid pk
 override-elim-ValidSenderForPK vsfp = subst (λ ps → ValidSenderForPK ps _ _ _) (sym override-target-≡) vsfp  

 -- We say that an implementation produces only valid parts iff all parts of every message in the
 -- output of a 'StepPeerState' are either: (i) a valid new part (i.e., the part is valid and no
 -- message with the same signature has been sent previously), or (ii) a message has been sent
 -- with the same signature.
 StepPeerState-AllValidParts : Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
 StepPeerState-AllValidParts = ∀{s m part pk initd' outs}{α}{st : SystemState}
   → (r : ReachableSystemState st)
   → Meta-Honest-PK pk
   → StepPeerState α (msgPool st) (initialised st) (peerStates st α) initd' (s , outs)
   → m ∈ outs → part ⊂Msg m → (ver : WithVerSig pk part)
     -- Note that we require that α can send for the PK according to the α's *new* state.  This
     -- allows sufficient generality to ensure that a peer can sign and send a message for an epoch
     -- even if it changed to the epoch in the same step.  If this is too painful, we could require
     -- that the epoch config is already available in the (initialised) prestate, which would
     -- require, for example, initialising a peer to be a separate step from sending its first
     -- signed message, which in turn could preclude some valid implementations.
   → (ValidSenderForPK s part α pk × ¬ (MsgWithSig∈ pk (ver-signature ver) (msgPool st)))
   ⊎ MsgWithSig∈ pk (ver-signature ver) (msgPool st)

 -- A /part/ was introduced by a specific step when:
 IsValidNewPart : ∀{pre : SystemState}{post : SystemState} → Signature → PK → Step pre post → Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
 -- said step is a /step-peer/ and
 IsValidNewPart {pre} {post} sig pk (step-peer {pid = pid} pstep)
    -- the part has never been seen before
    = ReachableSystemState pre
    × ¬ (MsgWithSig∈ pk sig (msgPool pre))
    × Σ (MsgWithSig∈ pk sig (msgPool (StepPeer-post pstep)))
        (λ m → msgSender m ≡ pid × initialised post pid ≡ initd × ValidSenderForPK (peerStates post pid) (msgPart m) (msgSender m) pk)


 mwsAndVspk-stable : ∀{st : SystemState}{st' : SystemState}
                   → ReachableSystemState st
                   → Step* st st'
                   → ∀ {pk sig}
                   → (mws : MsgWithSig∈ pk sig (msgPool st))
                   → initialised st (msgSender mws) ≡ initd
                   → ValidSenderForPK (peerStates st (msgSender mws)) (msgPart mws) (msgSender mws) pk
                   → Σ (MsgWithSig∈ pk sig (msgPool st')) λ mws' →
                       ValidSenderForPK (peerStates st' (msgSender mws')) (msgPart mws') (msgSender mws') pk
 mwsAndVspk-stable {_} {st'} r tr {pk} {sig} mws ini vpk = MsgWithSig∈-Step* tr mws
                                                     , subst₂ (λ p s → ValidSenderForPK (peerStates st' s) p s pk)
                                                              (MsgWithSig∈-Step*-part tr mws)
                                                              (MsgWithSig∈-Step*-sender tr mws)
                                                              (ValidSenderForPK-stable-sys r tr ini vpk)

 -- When we can prove that the implementation provided by 'parms' at the
 -- top of this module satisfies 'StepPeerState-AllValidParts', we can
 -- prove a number of useful structural properties:

 -- TODO-2: Refactor into a file (LibraBFT.Yasm.Properties.Structural) later on
 -- if this grows too large.
 module Structural (sps-avp      : StepPeerState-AllValidParts) where

     -- We can unwind the state and highlight the step where a part was
     -- originally sent. This 'unwind' function combined with Any-Step-elim
     -- enables a powerful form of reasoning. The 'honestVoteEpoch' below
     -- exemplifies this well.
     unwind : ∀{st : SystemState}(tr : ReachableSystemState st)
            → ∀{p m σ pk} → Meta-Honest-PK pk
            → p ⊂Msg m → (σ , m) ∈ msgPool st → (ver : WithVerSig pk p)
            → Any-Step (IsValidNewPart (ver-signature ver) pk) tr
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) hpk p⊂m m∈sm sig
       with Any-++⁻ (List-map (β ,_) outs) {msgPool pre} m∈sm
     ...| inj₂ furtherBack = step-there (unwind tr hpk p⊂m furtherBack sig)
     ...| inj₁ thisStep
       with sp
     ...| step-cheat isCheat
       with thisStep
     ...| here refl
       with isCheat p⊂m sig
     ...| inj₁ abs    = ⊥-elim (hpk abs)
     ...| inj₂ sentb4
       with unwind tr {p = msgPart sentb4} hpk (msg⊆ sentb4) (msg∈pool sentb4) (msgSigned sentb4)
     ...| res rewrite msgSameSig sentb4 = step-there res
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) hpk p⊂m m∈sm sig
        | inj₁ thisStep
        | step-honest x
       with Any-satisfied-∈ (Any-map⁻ thisStep)
     ...| (m , refl , m∈outs)
       with sps-avp tr hpk x m∈outs p⊂m sig
     ...| inj₂ sentb4 with unwind tr {p = msgPart sentb4} hpk (msg⊆ sentb4) (msg∈pool sentb4) (msgSigned sentb4)
     ...| res rewrite msgSameSig sentb4 = step-there res
     unwind (step-s tr (step-peer {pid = β} {outs = outs} {pre = pre} sp)) {p} hpk p⊂m m∈sm sig
        | inj₁ thisStep
        | step-honest x
        | (m , refl , m∈outs)
        | inj₁ (valid-part , notBefore) = step-here tr (tr , notBefore , MsgWithSig∈-++ˡ (mkMsgWithSig∈ _ _ p⊂m β thisStep sig refl) , refl , override-target-≡  , override-elim-ValidSenderForPK valid-part )

     -- Unwind is inconvenient to use by itself because we have to do
     -- induction on Any-Step-elim. The 'honestPartValid' property below
     -- provides a fairly general result conveniently: for every part
     -- verifiable with an honest PK, there is a msg with the same
     -- signature that is valid for some pid.

     honestPartValid : ∀ {st} → ReachableSystemState st → ∀ {pk nm v sender}
                     → Meta-Honest-PK pk
                     → v ⊂Msg nm → (sender , nm) ∈ msgPool st → (ver : WithVerSig pk v)
                     → Σ (MsgWithSig∈ pk (ver-signature ver) (msgPool st))
                         (λ msg → (ValidSenderForPK (peerStates st (msgSender msg)) (msgPart msg) (msgSender msg) pk))
     honestPartValid {st} r {pk = pk} hpk v⊂m m∈pool ver
     -- We extract two pieces of important information from the place where the part 'v'
     -- was first sent: (a) there is a message with the same signature /in the current pool/
     -- and (b) its epoch is less than e.
        = Any-Step-elim (λ { {st = step-peer {pid = pid} (step-honest sps)} (preReach , ¬sentb4 , new , refl , ini , valid) tr
                             → mwsAndVspk-stable (step-s preReach (step-peer (step-honest sps))) tr new ini valid
                           ; {st = step-peer {pid = pid} {pre = pre} (step-cheat {pid} sps)} (preReach , ¬sentb4 , new , refl , valid) tr
                            → ⊥-elim (¬sentb4 (¬cheatForgeNew {st = pre} (step-cheat sps) refl unit hpk new))
                        })
                        (unwind r hpk v⊂m m∈pool ver)

     newMsg⊎msgSentB4 :  ∀ {pk v m pid sndr st' outs} {st : SystemState}
                   → (r : ReachableSystemState st)
                   → (stP : StepPeer st pid st' outs)
                   → Meta-Honest-PK pk → (sig : WithVerSig pk v)
                   → v ⊂Msg m → (sndr , m) ∈ msgPool (StepPeer-post stP)
                   → (m ∈ outs × ValidSenderForPK st' v pid pk
                      × ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool st)))
                     ⊎ MsgWithSig∈ pk (ver-signature sig) (msgPool st)
     newMsg⊎msgSentB4 {pk} {v} {m} {pid} {sndr} {_} {outs} {st} r stP pkH sig v⊂m m∈post
        with Any-++⁻ (List-map (pid ,_) outs) m∈post
     ...| inj₂ m∈preSt = inj₂ (mkMsgWithSig∈ m v v⊂m sndr m∈preSt sig refl)
     ...| inj₁ nm∈outs
        with Any-map (cong proj₂) (Any-map⁻ nm∈outs)
     ...| m∈outs
        with stP
     ...| step-honest stH
        with sps-avp r pkH stH m∈outs v⊂m sig
     ...| inj₁ newVote = inj₁ (m∈outs , newVote)
     ...| inj₂ msb4    = inj₂ msb4
     newMsg⊎msgSentB4 {pk} {v} {m} {pid} {sndr} {_} {outs} {st} r stP pkH sig v⊂m m∈post
        | inj₁ nm∈outs
        | here refl
        | step-cheat ic
          = let mws = mkMsgWithSig∈ m v v⊂m pid (here refl) sig refl
            in inj₂ (¬cheatForgeNew {st = st} (step-cheat ic) refl unit pkH mws)

 -- This could potentially be more general, for example covering the whole SystemState, rather than
  -- just one peer's state.  However, this would put more burden on the user and is not required so
 -- far.
 CarrierProp : Set (1ℓ ℓ⊔ ℓ-PeerState)
 CarrierProp = Part → PeerState → Set

 module _ (P   : CarrierProp) where

  record PropCarrier (pk : PK) (sig : Signature) (st : SystemState) : Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState) where
    constructor mkCarrier
    field
      carrStReach : ReachableSystemState st -- Enables use of invariants when proving that steps preserve carrProp
      carrSent    : MsgWithSig∈ pk sig (msgPool st)
      carrInitd   : initialised st (msgSender carrSent) ≡ initd
      carrValid   : ValidSenderForPK (peerStates st (msgSender carrSent)) (msgPart carrSent) (msgSender carrSent) pk
      carrProp    : P (msgPart carrSent) (peerStates st (msgSender carrSent))
  open PropCarrier public

  PeerStepPreserves : Set (ℓ-VSFP ℓ⊔ ℓ+1 ℓ-PeerState)
  PeerStepPreserves = ∀ {initd' ps' outs pk sig}{pre : SystemState}
                      → (r : ReachableSystemState pre)
                      → (pc : PropCarrier pk sig pre)
                      → (sps : StepPeerState     (msgSender (carrSent pc))
                                                 (msgPool pre)
                                                 (initialised pre)
                                                 (peerStates pre (msgSender (carrSent pc)))
                                                 initd'
                                                 (ps' , outs))
                      → P (msgPart (carrSent pc)) ps'

  module _ (PSP : PeerStepPreserves) where

    Carrier-transp : ∀ {pk sig} {pre : SystemState}{post : SystemState}
                   → (theStep : Step pre post)
                   → PropCarrier pk sig pre
                   → PropCarrier pk sig post
    Carrier-transp {pk} {pre = pre} {post} theStep@(step-peer {pid = pid} {st'} {pre = .pre} sps) pc@(mkCarrier r mws ini vpk prop)
       with step-s r theStep
    ...| postReach
       with sps
    ...| sch@(step-cheat isch) = mkCarrier postReach (MsgWithSig∈-++ʳ mws) (trans (cong (λ f → f (msgSender mws)) (cheatStepDNMInitialised sch unit)) ini)      -- PeerStates not changed by cheat steps
           (subst (λ ps → ValidSenderForPK ps _ _ _) (cong (λ f → f (msgSender mws)) (sym (cheatStepDNMPeerStates {pre = pre} (step-cheat isch) unit))) vpk)
           (subst (λ ps → P (msgPart mws) (ps (msgSender mws))) (sym (cheatStepDNMPeerStates {pre = pre} (step-cheat isch) unit)) prop)
    ...| step-honest {st = st} sps'
       with msgSender mws ≟PeerId pid
    ...| no neq   = mkCarrier postReach (MsgWithSig∈-++ʳ mws) (trans (sym (override-target-≢ neq)) ini)
                              (subst (λ ps → ValidSenderForPK ps _ _ _) (override-target-≢ {f = peerStates pre} neq) vpk)
                              (subst (λ ps → P (msgPart mws) ps) (override-target-≢ {f = peerStates pre} neq) prop)
    ...| yes refl = mkCarrier postReach (MsgWithSig∈-++ʳ mws) override-target-≡
                              (override-elim-ValidSenderForPK (ValidSenderForPK-stable {part = msgPart mws} {pk} r sps' ini vpk))
                              (subst (λ ps → P (msgPart mws) ps) (sym override-target-≡) (PSP r pc sps'))
