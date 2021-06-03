{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Concrete.System
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

-- This module contains placeholders for the future analog of the
-- corresponding VotesOnce property.  Defining the implementation
-- obligation and proving that it is an invariant of an implementation
-- is a substantial undertaking.  We are working first on proving the
-- simpler VotesOnce property to settle down the structural aspects
-- before tackling the harder semantic issues.
module LibraBFT.Concrete.Properties.PreferredRound (𝓔 : EpochConfig) where
 import      LibraBFT.Abstract.Records UID _≟UID_ NodeId 𝓔 as Abs
 open import LibraBFT.Concrete.Obligations.PreferredRound 𝓔 (ConcreteVoteEvidence 𝓔)
 open WithAbsVote 𝓔
 open PeerCanSignForPK
 open PeerCanSignForPKinEpoch

 -- As with VotesOnce, we will have two implementation obligations, one for when v is sent by the
 -- step and v' has been sent before, and one for when both are sent by the step.

 ImplObligation₁ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₁ =
   ∀{pid pid' s' outs pk}{pre : SystemState}
   → (r : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → let post = StepPeer-post {pre = pre} (step-honest sps) in
     ∀{mbr v vabs m v' v'abs m'}
   → (𝓔∈Sys : EpochConfig∈Sys post 𝓔)
   → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre)
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound < v' ^∙ vRound
   → toNodeId 𝓔 mbr ≡ pid
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → let intSys = PerState.PerEpoch.intSystemState pre r 𝓔 in
     (c2 : Cand-3-chain-vote intSys vabs)
   → Σ (VoteParentData intSys v'abs)
           (λ vp → Cand-3-chain-head-round intSys c2
                   ≤ Abs.round (ConcreteVoteEvidence 𝓔) (vpParent vp))

 ImplObligation₂ : Set (ℓ+1 ℓ-RoundManager)
 ImplObligation₂ =
   ∀{pid s' outs pk}{pre : SystemState}
   → (r  : ReachableSystemState pre)
   -- For any honest call to /handle/ or /init/,
   → (sps : StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) (s' , outs))
   → let post = StepPeer-post {pre = pre} (step-honest sps) in
     ∀{mbr v vabs m v' v'abs m'}
   → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → send m ∈ outs
   → (sig : WithVerSig pk v) → ¬ (∈GenInfo (ver-signature sig))
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre))

   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → send m' ∈ outs
   → (sig' : WithVerSig pk v') → ¬ (∈GenInfo (ver-signature sig'))
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre))
   -- If v and v' share the same epoch and round
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → v ^∙ vRound < v' ^∙ vRound
   → toNodeId 𝓔 mbr ≡ pid
   → α-ValidVote 𝓔 v  mbr ≡ vabs
   → α-ValidVote 𝓔 v' mbr ≡ v'abs
   → let intSys = PerState.PerEpoch.intSystemState pre r 𝓔 in
     (c2 : Cand-3-chain-vote intSys vabs)
   → Σ (VoteParentData intSys v'abs)
           (λ vp → Cand-3-chain-head-round intSys c2
                   ≤ Abs.round (ConcreteVoteEvidence 𝓔) (vpParent vp))

  -- Next, we prove that given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-PR1 : ImplObligation₁)
   (Impl-PR2 : ImplObligation₂)
   where
  -- Any reachable state satisfies the PR rule for any epoch in the system.
  module _ (st : SystemState)(r : ReachableSystemState st) where
   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr
   -- Bring in intSystemState
   open        PerState st r
   open        PerEpoch 𝓔
   open import LibraBFT.Concrete.Obligations.PreferredRound 𝓔 (ConcreteVoteEvidence 𝓔) as PR

   postulate
     prr : PR.Type intSystemState
   -- prr honα refl sv refl sv' c2 round< = {!c2!}
