{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.Common    as Common
import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open RoundManagerInvariants
open RoundManagerTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK

open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

-- This module contains definitions and lemmas used by proofs of the
-- implementation obligations for VotesOnce and PreferredRoundRule.

module LibraBFT.Impl.Properties.Common where

handleProposalRequirements : ∀ {inst st sndr pm pid}
                             → ReachableSystemState st
                             → (sndr , P pm) ∈ msgPool st
                             → initialised st pid ≡ initd
                             → handleProposalSpec.Requirements inst pm (msgPool st) (peerStates st pid)

postulate -- TODO-3: prove (note: advanced; waiting on: `handle`)
  -- This will require updates to the existing proofs for the peer handlers. We
  -- will need to show that honest peers sign things only for their only PK, and
  -- that they either resend messages signed before or if sending a new one,
  -- that signature hasn't been sent before
  impl-sps-avp : StepPeerState-AllValidParts

open Structural impl-sps-avp

-- We can prove this easily for the Agda model because (unlike the Haskell
-- prototype) it does not yet do epoch changes, so only the initial EC is
-- relevant. Later, this will require us to use the fact that epoch changes
-- require proof of committing an epoch-changing transaction.
availEpochsConsistent :
   ∀{pid pid' v v' pk}{st : SystemState}
   → (pkvpf  : PeerCanSignForPK st v  pid  pk)
   → (pkvpf' : PeerCanSignForPK st v' pid' pk)
   → v ^∙ vEpoch ≡ v' ^∙ vEpoch
   → pcs4𝓔 pkvpf ≡ pcs4𝓔 pkvpf'
availEpochsConsistent (mkPCS4PK _ (inGenInfo refl) _) (mkPCS4PK _ (inGenInfo refl) _) refl = refl

postulate
  uninitQcs∈Gen -- TODO-1: Prove (waiting on: complete definition of `initRM`)
    : ∀ {pid qc vs}{st : SystemState}
      → ReachableSystemState st
      → initialised st pid ≡ uninitd
      → qc QC.∈RoundManager (peerStates st pid)
      → vs ∈ qcVotes qc
      → ∈GenInfo-impl genesisInfo (proj₂ vs)

-- postulate -- TODO-2: prove (waiting on: `handle`, refinements to handler contracts)
  -- This will be proved for the implementation, confirming that honest
  -- participants only store QCs comprising votes that have actually been sent.
  -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
  -- Note that some implementations might not ensure this, but LibraBFT does
  -- because even the leader of the next round sends its own vote to itself,
  -- as opposed to using it to construct a QC using its own unsent vote.
qcVoteSigsSentB4
  : ∀ {pid qc vs pk}{st : SystemState}
    → ReachableSystemState st
    → initialised st pid ≡ initd
    → qc QC.∈RoundManager (peerStates st pid)
    → vs ∈ qcVotes qc
    → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
    → MsgWithSig∈ pk (proj₂ vs) (msgPool st)
qcVoteSigsSentB4{pid}{qc}{st = st} rss'@(step-s{pre = pre} rss (step-peer sp@(step-cheat _))) ini qc∈rm vs∈qcvs ¬gen
  = MsgWithSig∈-++ʳ{pool = msgPool pre} (qcVoteSigsSentB4 rss iniPre qc∈rmPre vs∈qcvs ¬gen)
  where
  pre≡ : peerStates (StepPeer-post{pre = pre} sp) pid ≡ peerStates pre pid
  pre≡ = cheatStepDNMPeerStates₁ sp unit

  qc∈rmPre : qc QC.∈RoundManager peerStates pre pid
  qc∈rmPre = subst (λ rm → qc QC.∈RoundManager rm) pre≡ qc∈rm

  iniPre : initialised pre pid ≡ initd
  iniPre = trans (sym (cheatStepDNMInitialised₁ sp unit)) ini

qcVoteSigsSentB4{pid}{qc}{_ , sig}{pk} (step-s{pre = pre} rss (step-peer sp@(step-honest{pid'} sps))) ini qc∈rm vs∈qcvs ¬gen
  with pid ≟ pid'
...| no  pid≢ = MsgWithSig∈-++ʳ{pool = msgPool pre} $ qcVoteSigsSentB4 rss iniPre qc∈rmPre vs∈qcvs ¬gen
  where
  pre≡ : peerStates (StepPeer-post{pre = pre} sp) pid ≡ peerStates pre pid
  pre≡ = sym $ pids≢StepDNMPeerStates sps pid≢

  qc∈rmPre : qc QC.∈RoundManager peerStates pre pid
  qc∈rmPre = subst (λ rm → qc QC.∈RoundManager rm) pre≡ qc∈rm

  iniPre : initialised pre pid ≡ initd
  iniPre = trans (pids≢StepDNMInitialised{pre = pre} sps pid≢) ini

...| yes refl
  with sps
... | step-init uni = ⊥-elim (¬gen (uninitQcs∈Gen rss uni qc∈rmPre vs∈qcvs))
  where
  pre≡ : peerStates (StepPeer-post{pre = pre} sp) pid ≡ peerStates pre pid
  pre≡ = sym $ trans (peerUninitState rss uni) (StepPeer-post-lemma sp)

  qc∈rmPre : qc QC.∈RoundManager peerStates pre pid'
  qc∈rmPre rewrite pre≡ = qc∈rm

...| step-msg{sndr , V pm} m∈pool ini' =  obm-dangerous-magic' "waiting on : handleVoteSpec"
...| step-msg{sndr , C pm} m∈pool ini' =  obm-dangerous-magic' "waiting on : handleCommitSpec"

-- Will need to relate the QCs in the outs to the msgPool of the prestate.
-- Either they come from pm, or from the previous roundstate.
-- In the first case, we can construct the MsgWithsig∈ with that knowledge.
-- In the second case, they come from the RoundManager of the pre-state, and we will rely on the system inv.
...| step-msg{sndr , P pm} m∈pool ini' = mws
       where
       hpPre      = peerStates pre pid'
       hpPoolPre  = msgPool pre
       hpOuts     = outputsToActions {hpPre} $ LBFT-outs (handle pid' (P pm) 0) hpPre
       hpPoolPost = actionsToSentMessages pid hpOuts ++ msgPool pre

       open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPoolPre hpPre $ handleProposalRequirements rss m∈pool ini')

       mws : MsgWithSig∈ pk sig hpPoolPost
       mws = obm-dangerous-magic' "TODO: use handleProposalSpec.Contract.qcs∈RM∈Pool"


module ∈GenInfoProps where
  sameSig∉ : ∀ {pk} {v v' : Vote}
             → (sig : WithVerSig pk v) (sig' : WithVerSig pk v')
             → ¬ ∈GenInfo-impl genesisInfo (ver-signature sig)
             → ver-signature sig' ≡ ver-signature sig
             → ¬ ∈GenInfo-impl genesisInfo (ver-signature sig')
  sameSig∉ _ _ ¬gen ≡sig rewrite ≡sig = ¬gen

-- Lemmas for `PeerCanSignForPK`
module PeerCanSignForPKProps where
  msb4 -- NOTE: This proof requires updating when we model epoch changes.
    : ∀ {pid v pk}{pre post : SystemState}
      → ReachableSystemState pre
      → Step pre post
      → PeerCanSignForPK post v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk
  msb4 preach step (mkPCS4PK 𝓔@._ (inGenInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)) hpk sig mws∈pool =
    mkPCS4PK 𝓔 (inGenInfo refl) (mkPCS4PKin𝓔 𝓔id≡ mbr nid≡ pk≡)

  msb4-eid≡
    : ∀ {pre post : SystemState} {v v' pid pk}
      → ReachableSystemState pre
      → Step pre post
      → Meta-Honest-PK pk
      → PeerCanSignForPK post v pid pk
      → v ≡L v' at vEpoch
      → (sig' : WithVerSig pk v')
      → MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
      → PeerCanSignForPK pre v pid pk
  msb4-eid≡ rss step hpk pcsfpk ≡eid sig' mws' =
    peerCanSignEp≡ (msb4 rss step (peerCanSignEp≡ pcsfpk ≡eid) hpk sig' mws') (sym ≡eid)

  pidInjective
    : ∀ {pid pid' pk v v'}{st : SystemState}
      → PeerCanSignForPK st v  pid  pk
      → PeerCanSignForPK st v' pid' pk
      → v ^∙ vEpoch ≡ v' ^∙ vEpoch
      → pid ≡ pid'
  pidInjective{pid}{pid'}{pk} pcsfpk₁ pcsfpk₂ ≡epoch = begin
    pid         ≡⟨ sym (nid≡ (pcs4in𝓔 pcsfpk₁)) ⟩
    pcsfpk₁∙pid ≡⟨ PK-inj-same-ECs{pcs4𝓔 pcsfpk₁}{pcs4𝓔 pcsfpk₂}
                     (availEpochsConsistent pcsfpk₁ pcsfpk₂ ≡epoch) pcsfpk∙pk≡ ⟩
    pcsfpk₂∙pid ≡⟨ nid≡ (pcs4in𝓔 pcsfpk₂) ⟩
    pid'        ∎
    where
    open ≡-Reasoning
    open PeerCanSignForPKinEpoch
    open PeerCanSignForPK

    pcsfpk₁∙pid  = EpochConfig.toNodeId  (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁))
    pcsfpk₂∙pid  = EpochConfig.toNodeId  (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂))
    pcsfpk₁∙pk   = EpochConfig.getPubKey (pcs4𝓔 pcsfpk₁) (mbr (pcs4in𝓔 pcsfpk₁))
    pcsfpk₂∙pk   = EpochConfig.getPubKey (pcs4𝓔 pcsfpk₂) (mbr (pcs4in𝓔 pcsfpk₂))

    pcsfpk∙pk≡ : pcsfpk₁∙pk ≡ pcsfpk₂∙pk
    pcsfpk∙pk≡ = begin
      pcsfpk₁∙pk ≡⟨ pk≡ (pcs4in𝓔 pcsfpk₁) ⟩
      pk         ≡⟨ sym (pk≡ (pcs4in𝓔 pcsfpk₂)) ⟩
      pcsfpk₂∙pk ∎

module ReachableSystemStateProps where
  postulate --TODO-2: Prove by induction using handler contracts
    systemInvariants
      : ∀ {st}
        → ReachableSystemState st
        → SystemInv st

  mws∈pool⇒initd
    : ∀ {pid pk v}{st : SystemState}
      → ReachableSystemState st
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → initialised st pid ≡ initd
  mws∈pool⇒initd{pk = pk}{v} (step-s{pre = pre} rss step@(step-peer sp@(step-cheat cmc))) pcsfpk hpk sig ¬gen mws∈pool =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre) hpk sig ¬gen mws∈poolPre)
    where
    ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)

    mws∈poolPre : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre = ¬cheatForgeNew sp refl unit hpk mws∈pool ¬gen'
  mws∈pool⇒initd{pid₁}{pk = pk} (step-s{pre = pre} rss step@(step-peer sp@(step-honest{pid₂} sps@(step-init ini)))) pcsfpk hpk sig ¬gen mws∈pool
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬gen' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)
  ... | Right mws∈poolPre = peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬gen mws∈poolPre')
    where
    mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre
  mws∈pool⇒initd{pid₁}{pk}{v} (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬gen mws∈pool
     with newMsg⊎msgSentB4 rss sps hpk (msgSigned mws∈pool) ¬gen' (msg⊆ mws∈pool) (msg∈pool mws∈pool)
     where
     ¬gen' = ∈GenInfoProps.sameSig∉ sig (msgSigned mws∈pool) ¬gen (msgSameSig mws∈pool)
  ... | Left (m∈outs , pcsfpk' , ¬msb4)
     with pid≡
     where
     vd₁≡vd₂ : v ≡L msgPart mws∈pool at vVoteData
     vd₁≡vd₂ = either (⊥-elim ∘ PerReachableState.meta-sha256-cr rss) id (sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool))

     pid≡ : pid₁ ≡ pid₂
     pid≡ = PeerCanSignForPKProps.pidInjective pcsfpk pcsfpk' (cong (_^∙ vdProposed ∙ biEpoch) vd₁≡vd₂)
  ... | refl rewrite StepPeer-post-lemma2{pid₂}{pre = pre} sps = refl
  mws∈pool⇒initd{pid₁}{pk}  (step-s{pre = pre} rss step@(step-peer{pid₂} sp@(step-honest sps@(step-msg _ ini)))) pcsfpk hpk sig ¬gen mws∈pool | Right mws∈poolPre =
    peersRemainInitialized step (mws∈pool⇒initd rss (PeerCanSignForPKProps.msb4 rss step pcsfpk hpk sig mws∈poolPre') hpk sig ¬gen mws∈poolPre')
    where
    mws∈poolPre' : MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    mws∈poolPre' rewrite msgSameSig mws∈pool = mws∈poolPre

  mws∈pool⇒epoch≡
    : ∀ {pid v s' outs pk}{st : SystemState}
      → ReachableSystemState st
      → (sps : StepPeerState pid (msgPool st) (initialised st) (peerStates st pid) (s' , outs))
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → s' ^∙ rmEpoch ≡ v ^∙ vEpoch
      → peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch
  mws∈pool⇒epoch≡ rss (step-init uni) pcsfpk hpk sig ¬gen mws∈pool epoch≡ =
    absurd (uninitd ≡ initd) case (trans (sym uni) ini) of λ ()
    where
    ini = mws∈pool⇒initd rss pcsfpk hpk sig ¬gen mws∈pool
  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{_ , P pm} m∈pool ini) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = begin
    hpPre ^∙ rmEpoch ≡⟨ noEpochChange ⟩
    hpPos ^∙ rmEpoch ≡⟨ epoch≡ ⟩
    v ^∙ vEpoch      ∎
    where
    hpPool = msgPool st
    hpPre  = peerStates st pid
    hpPos  = LBFT-post (handleProposal 0 pm) hpPre
    open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre $
                                       handleProposalRequirements rss m∈pool ini)
    open ≡-Reasoning

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , V vm} _ _) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = TODO
    where
    postulate -- TODO-3: prove (waiting on: epoch config changes)
      TODO : peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch

  mws∈pool⇒epoch≡{pid}{v}{st = st} rss (step-msg{sndr , C cm} _ _) pcsfpk hpk sig ¬gen mws∈pool epoch≡ = TODO
    where
    postulate -- TODO-3: prove (waiting on: epoch config changes)
      TODO : peerStates st pid ^∙ rmEpoch ≡ v ^∙ vEpoch

-- TODO-2: This should probably go somewhere else.  One possibility is
-- Properties.InputOutputHandlers but it can't easily go there without creating cyclic imports
open ReachableSystemStateProps
handleProposalRequirements {st = st} {sndr} {pm} {pid} reach m∈pool ini =
  record { mSndr = sndr
         ; m∈pool = m∈pool
         ; qcs∈RmSigsSentB4 = qcs∈RMSigSentB4 (systemInvariants reach) ini
         }

