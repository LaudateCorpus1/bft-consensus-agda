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
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module proves the two "VotesOnce" proof obligations for our fake handler. Unlike the
-- LibraBFT.ImplFake.Properties.VotesOnce, which is based on unwind, this proof is done
-- inductively on the ReachableSystemState.

module LibraBFT.Impl.Properties.VotesOnce (𝓔 : EpochConfig) where

newVote⇒lvr≡
  : ∀ {pre : SystemState}{pid s' outs v m pk}
    → ReachableSystemState pre
    → StepPeerState pid (msgPool pre) (initialised pre)
        (peerStates pre pid) (s' , outs)
    → v ⊂Msg m → send m ∈ outs → (sig : WithVerSig pk v)
    → Meta-Honest-PK pk → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
    → ¬ MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → v ^∙ vRound ≡ metaRMGetRealLastVotedRound s'
newVote⇒lvr≡{pre}{pid}{v = v} preach (step-msg{sndr , P pm} m∈pool ini) vote∈vm m∈outs sig hpk ¬gen ¬msb4
  with handleProposalSpec.contract! 0 pm (peerStates pre pid)
... | handleProposalSpec.mkContract _ _ (Voting.mkVoteAttemptCorrectWithEpochReq (inj₁ (_ , voteUnsent)) sdEpoch≡?) =
  ⊥-elim (unsentVoteSent voteUnsent)
  where
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  unsentVoteSent : ¬ Voting.VoteUnsentCorrect (peerStates pre pid) _ _ _ _
  unsentVoteSent (Voting.mkVoteUnsentCorrect noVoteMsgOuts _) =
    sendVote∉actions{outs = handleOuts}{st = peerStates pre pid}
      (sym noVoteMsgOuts) m∈outs
... | handleProposalSpec.mkContract _ _ (Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect (VoteMsg∙new v' _) rcvr voteMsgOuts vgCorrect)) sdEpoch≡?) =
  sentVoteIsPostLVR
  where
  handlePost = LBFT-post (handle pid (P pm) 0) (peerStates pre pid)
  handleOuts = LBFT-outs (handle pid (P pm) 0) (peerStates pre pid)

  sentVoteIsPostLVR : v ^∙ vRound ≡ metaRMGetRealLastVotedRound handlePost
  sentVoteIsPostLVR with Voting.VoteGeneratedCorrect.state vgCorrect
  ... | StateTransProps.mkVoteGenerated lv≡v _ rewrite sym lv≡v =
    cong (_^∙ vmVote ∙ vRound) (sendVote∈actions{outs = handleOuts}{st = peerStates pre pid} (sym voteMsgOuts) m∈outs)
-- TODO-1: prove (note: no votes sent from processing a vote message) (waiting on: handle)
newVote⇒lvr≡ preach (step-msg{sndr , V vm} m∈pool ini) vote∈vm m∈outs sig hpk ¬gen ¬msb4 = {!!}
-- TODO-2: prove (note: qc votes have been sent before)
newVote⇒lvr≡ preach sps (vote∈qc vs∈qc v≈rbld qc∈m) m∈outs sig hpk ¬gen ¬msb4 = {!!}

postulate -- TODO-3: prove
  peerCanSign-Msb4
    : ∀ {pid v pk}{pre post : SystemState}
      → ReachableSystemState pre
      → Step pre post
      → PeerCanSignForPK post v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
      → PeerCanSignForPK pre v pid pk

  msg∈pool⇒initd
    : ∀ {pid pk v}{st : SystemState}
      → ReachableSystemState st
      → PeerCanSignForPK st v pid pk
      → Meta-Honest-PK pk → (sig : WithVerSig pk v)
      → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
      → MsgWithSig∈ pk (ver-signature sig) (msgPool st)
      → initialised st pid ≡ initd

  peerCanSignPK-Inj
    : ∀ {pid pid' pk v v'}{st : SystemState}
      → ReachableSystemState st
      → Meta-Honest-PK pk
      → PeerCanSignForPK st v' pid' pk
      → PeerCanSignForPK st v pid pk
      → v ^∙ vEpoch ≡ v' ^∙ vEpoch
      → pid ≡ pid'

oldVoteRound≤lvr
  : ∀ {pid pk v}{pre : SystemState}
    → (r : ReachableSystemState pre)
    → Meta-Honest-PK pk → (sig : WithVerSig pk v)
    → ¬ (∈GenInfo-impl genesisInfo (ver-signature sig))
    → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
    → PeerCanSignForPK pre v pid pk
    → (peerStates pre pid) ^∙ rmEpoch ≡ (v ^∙ vEpoch)
    → v ^∙ vRound ≤ metaRMGetRealLastVotedRound (peerStates pre pid)
oldVoteRound≤lvr{pid} (step-s preach step@(step-peer{pid'} sp@(step-cheat  cmc))) hpk sig ¬gen mws∈pool pcsfpk epoch≡
  -- `pid`'s state is untouched by this step
  rewrite cheatStepDNMPeerStates₁{pid = pid'}{pid' = pid} sp unit
  = oldVoteRound≤lvr preach hpk sig ¬gen mws∈prePool pcsfpkPre epoch≡
  where
  -- The cheat step could not have been where the signed message was introduced,
  -- so there must be a signed message in the pool prior to this
  mws∈prePool = ¬cheatForgeNew sp refl unit hpk mws∈pool (¬subst ¬gen (msgSameSig mws∈pool))
  -- `pid` can sign for the message in the previous system state
  pcsfpkPre   = peerCanSign-Msb4 preach step pcsfpk hpk sig mws∈prePool
oldVoteRound≤lvr{pid}{v = v} step*@(step-s{pre = pre}{post = post@._} preach step@(step-peer{pid'} sp@(step-honest{st = ppost} sps))) hpk sig ¬gen mws∈pool pcsfpk epoch≡
   with msgSameSig mws∈pool
...| refl
   with newMsg⊎msgSentB4 preach sps hpk (msgSigned mws∈pool) ¬gen (msg⊆ mws∈pool) (msg∈pool mws∈pool)
...| inj₂ msb4 = helpSentB4
   where
   pcsfpkPre : PeerCanSignForPK pre v pid _
   pcsfpkPre = peerCanSign-Msb4 preach step pcsfpk hpk sig msb4

   ovrIH : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch → v ^∙ vRound ≤ metaRMGetRealLastVotedRound (peerStates pre pid)
   ovrIH ep≡ = oldVoteRound≤lvr{pre = pre} preach hpk sig ¬gen msb4 pcsfpkPre ep≡

   helpSentB4 : v ^∙ vRound ≤ metaRMGetRealLastVotedRound (peerStates post pid)
   helpSentB4
      with pid ≟ pid'
   -- A step by `pid'` step cannot affect `pid`'s state
   ...| no  pid≢
      rewrite sym (pids≢StepDNMPeerStates{pre = pre} sps pid≢)
      = ovrIH epoch≡
   ...| yes pid≡ = ≤-trans (ovrIH epoch≡') lvr≤
     where
     -- If a vote signed by a peer exists in the past, and that vote has an
     -- epoch id associated to it that is the same as the peer's post-state
     -- epoch, then the peer has that same epoch id in its immediately preceding
     -- pre-state.
     epoch≡' : peerStates pre pid ^∙ rmEpoch ≡ v ^∙ vEpoch
     epoch≡' = {!!}

     ini : initialised pre pid' ≡ initd
     ini rewrite sym pid≡ = msg∈pool⇒initd preach pcsfpkPre hpk sig ¬gen msb4

     lvr≤ : metaRMGetRealLastVotedRound (peerStates pre pid) ≤ metaRMGetRealLastVotedRound (peerStates post pid)
     lvr≤
       rewrite pid≡
       |       sym (StepPeer-post-lemma{pre = pre} sp)
       = lastVotedRound-mono pid' pre preach ini sps
           (trans (subst (λ x → peerStates pre x ^∙ rmEpoch ≡ v ^∙ vEpoch) pid≡ epoch≡') (sym epoch≡))
-- The vote was newly sent this round
...| inj₁ (m∈outs , pcsfpkPost , ¬msb4)
-- ... and it really is the same vote, because there has not been a hash collision
   with sameSig⇒sameVoteData (msgSigned mws∈pool) sig (msgSameSig mws∈pool)
... | inj₁ nonInjSHA256 = ⊥-elim (PerReachableState.meta-sha256-cr step* nonInjSHA256)
... | inj₂ refl
   with pid ≟ pid'
... | no  pid≢ = ⊥-elim (pid≢ (peerCanSignPK-Inj step* hpk pcsfpkPost pcsfpk refl))
... | yes refl = ≡⇒≤ vr≡lvrPost
  where
    vr≡lvrPost : v ^∙ vRound ≡ metaRMGetRealLastVotedRound (peerStates (StepPeer-post sp) pid)
    vr≡lvrPost
      rewrite sym (StepPeer-post-lemma sp)
      -- TODO-2: Once `newVote⇒lvr≡` is strengthened, do we have enough
      -- information to prove `VoteForRound∈`?
      = newVote⇒lvr≡{pre = pre}{pid = pid} preach sps (msg⊆ mws∈pool) m∈outs (msgSigned mws∈pool) hpk ¬gen ¬msb4

  {-
  -- NOTE: A vote being stored in `sdLastVote` does /not/ mean the vote has been
  -- sent, since the peer could have failed to save that vote in its persistent
  -- storage, leading it to drop the vote. We must additionally require that a
  -- vote for the same round as the `sdLastVote`, sent by the same peer, already
  -- exists in the pool.
  peerLastVoteSentB4
    : ∀ {pre pid v m' v' pk}
      → ReachableSystemState pre
      → just v ≡ (peerStates pre pid ^∙ (lSafetyData ∙ sdLastVote))
      → Meta-Honest-PK pk
      → (sig : WithVerSig pk v) 
      → v' ⊂Msg m' → (pid , m') ∈ msgPool pre
      → v ≡L v' at vEpoch v ≡L v' at vRound
      → MsgWithSig∈ pk (ver-signature sig) (msgPool pre)
  -}

votesOnce₁ : Common.IncreasingRoundObligation InitAndHandlers 𝓔
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {m} {v'} {m'} hpk (vote∈qc x x₁ x₂) m∈outs sig ¬gen ¬msb pcspkv v'⊂m' m'∈pool sig' ¬gen' eid≡ = {!!}
votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , P pm} m∈pool ini) {v} {.(V (VoteMsg∙new v _))} {v'} {m'} hpk vote∈vm m∈outs sig ¬gen ¬msb pcspkv v'⊂m' m'∈pool sig' ¬gen' eid≡
  with handleProposalSpec.contract! 0 pm (peerStates pre pid)
... | handleProposalSpec.mkContract rmInv noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts nvg⊎vgusc)) sdEpoch≡?) =
  ⊥-elim (sendVote∉actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym noVoteMsgOuts) m∈outs)
... | handleProposalSpec.mkContract rmInv noEpochChange (Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid₁ voteMsgOuts vgCorrect)) sdEpoch≡?)
  with sendVote∈actions{outs = LBFT-outs (handleProposal 0 pm) (peerStates pre pid)} (sym voteMsgOuts) m∈outs
... | refl = ret
  where
  -- Some definitions
  step = step-peer (step-honest sps)
  rmPre  = peerStates pre pid

  -- State invariants
  open StateInvariants
  rmInvs      = invariantsCorrect pid pre preach
  epochsMatch = RoundManagerInv.epochsMatch rmInvs
  sdInvs      = RoundManagerInv.sdCorrect   rmInvs

  -- The proof
  m'mwsb : MsgWithSig∈ pk (ver-signature sig') (msgPool pre)
  m'mwsb = mkMsgWithSig∈ m' v' v'⊂m' pid' m'∈pool sig' refl

  pcspkv'-pre : PeerCanSignForPK pre v' pid pk
  pcspkv'-pre = peerCanSign-Msb4 preach step (peerCanSignEp≡{v' = v'} pcspkv eid≡) hpk sig' m'mwsb

  rv'≤rv : v' ^∙ vRound ≤ v ^∙ vRound
  rv'≤rv =
    ≤-trans
      (oldVoteRound≤lvr preach hpk sig' ¬gen' m'mwsb pcspkv'-pre (trans rmPreEsEpoch≡ eid≡))
      realLVR≤rv
    where
    open ≡-Reasoning
    -- TODO-1 : `rmPreSdEpoch≡` can be factored out into a lemma.
    -- Something like: for any reachable state where a peer sends a vote, the
    -- epoch for that vote is the peer's sdEpoch / esEpoch.
    rmPreSdEpoch≡ : rmPre ^∙ lSafetyData ∙ sdEpoch ≡ v ^∙ vEpoch
    rmPreSdEpoch≡
       with Voting.VoteGeneratedCorrect.state vgCorrect
       |    Voting.VoteGeneratedCorrect.blockTriggered vgCorrect
    ...| StateTransProps.mkVoteGenerated lv≡v (Left (StateTransProps.mkVoteOldGenerated lvr≡ lv≡)) | _
       with SDLastVote.epoch≡ ∘ SafetyDataInv.lastVote $ sdInvs
    ...| sdEpochInv rewrite trans lv≡ (sym lv≡v) = sym sdEpochInv
    rmPreSdEpoch≡
       | StateTransProps.mkVoteGenerated lv≡v (Right (StateTransProps.mkVoteNewGenerated lvr< lvr≡)) | bt =
      trans sdEpoch≡? (sym ∘ proj₁ ∘ Voting.VoteMadeFromBlock⇒VoteEpochRoundIs $ bt)

    rmPreEsEpoch≡ : rmPre ^∙ rmEpochState ∙ esEpoch ≡ v ^∙ vEpoch
    rmPreEsEpoch≡ =
      begin rmPre ^∙ rmEpochState ∙ esEpoch ≡⟨ epochsMatch   ⟩
            rmPre ^∙ lSafetyData ∙ sdEpoch  ≡⟨ rmPreSdEpoch≡ ⟩
            v ^∙ vEpoch                     ∎

    realLVR≤rv : metaRMGetRealLastVotedRound rmPre ≤ v ^∙ vRound
    realLVR≤rv
      with Voting.VoteGeneratedCorrect.state vgCorrect
    ...| StateTransProps.mkVoteGenerated lv≡v (Left (StateTransProps.mkVoteOldGenerated lvr≡ lv≡))
      rewrite trans lv≡ (sym lv≡v)
        = ≤-refl
    ...| StateTransProps.mkVoteGenerated lv≡v (Right (StateTransProps.mkVoteNewGenerated lvr< lvr≡))
      with rmPre ^∙ lSafetyData ∙ sdLastVote
        |    SDLastVote.round≤ ∘ SafetyDataInv.lastVote $ sdInvs
    ...| nothing | _ = z≤n
    ...| just lv | round≤ = ≤-trans (≤-trans round≤ (<⇒≤ lvr<)) (≡⇒≤ (sym lvr≡))

  ret : v' [ _<_ ]L v at vRound ⊎ Common.VoteForRound∈ InitAndHandlers 𝓔 pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
  ret
    with <-cmp (v' ^∙ vRound) (v ^∙ vRound)
  ... | tri< rv'<rv _ _ = inj₁ rv'<rv
  ... | tri≈ _ rv'≡rv _
    = inj₂ (Common.mkVoteForRound∈ _ v' v'⊂m' pid' m'∈pool sig' (sym eid≡) rv'≡rv {!!})
  ... | tri> _ _ rv'>rv = ⊥-elim (≤⇒≯ rv'≤rv rv'>rv)


votesOnce₁ {pid = pid} {pid'} {pk = pk} {pre = pre} preach sps@(step-msg {sndr , V x} m∈pool ini) {v} {m} {v'} {m'} hpk v⊂m m∈outs sig ¬gen ¬msb vspk v'⊂m' m'∈pool sig' ¬gen' eid≡ = {!!}
