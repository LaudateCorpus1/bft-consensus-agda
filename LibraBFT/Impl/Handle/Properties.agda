{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

-- This module provides some scaffolding to define the handlers for our
-- implementation and connect them to the interface of the SystemModel.

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
-- open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open        ParamsWithInitAndHandlers InitAndHandlers
open        PeerCanSignForPK

open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

open StateProps

module LibraBFT.Impl.Handle.Properties where

-- TODO-2: Prove these once `initRM` in `LibraBFT.Impl.Handle` is sufficiently implemented
postulate
  initRM-correct           : RoundManager-correct initRM
  initRM-blockTree-correct : StateInvariants.BlockTreeInv initRM

initRMSatisfiesInv : StateInvariants.RoundManagerInv initRM
initRMSatisfiesInv = StateInvariants.mkRoundManagerInv initRM-correct initRM-blockTree-correct refl

invariantsCorrect
  : ∀ pid (pre : SystemState)
    → ReachableSystemState pre → StateInvariants.RoundManagerInv (peerStates pre pid)
invariantsCorrect pid pre@._ step-0 = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-cheat{pid'} cheatMsgConstraint)))
  rewrite cheatStepDNMPeerStates₁{pid'}{pid}{pre = pre'} step unit
  = invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer step@(step-honest{pid'} sps)))
  with pid ≟ pid'
...| no pid≢pid'
  rewrite sym (pids≢StepDNMPeerStates{pre = pre'} sps pid≢pid')
  = invariantsCorrect pid pre' preach
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-init ini)))) | yes refl
  rewrite override-target-≡{a = pid}{b = initRM}{f = peerStates pre'}
  = initRMSatisfiesInv
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{m = sndr , P pm} m∈pool ini)))) | yes refl
  with handleProposalSpec.contract!-RoundManagerInv 0 pm (peerStates pre' pid)
... | invPres
  rewrite override-target-≡{a = pid}{b = LBFT-post (handleProposal 0 pm) (peerStates pre' pid)}{f = peerStates pre'}
  = invPres (invariantsCorrect pid pre' preach)
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{m = sndr , V x} m∈pool ini)))) | yes refl = {!!}
invariantsCorrect pid pre@._ (step-s{pre = pre'} preach (step-peer (step-honest (step-msg{m = sndr , C x} m∈pool ini)))) | yes refl = {!!}

-- TODO-3: Prove this
postulate
  impl-sps-avp : StepPeerState-AllValidParts
