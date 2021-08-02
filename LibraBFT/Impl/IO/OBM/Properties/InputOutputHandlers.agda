{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager       as RoundManager
open import LibraBFT.Impl.Consensus.RoundManager.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.NetworkMsg
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers where

module epvvSpec where

  contract
    : ∀ pre Post
      → let ep = pre ^∙ pssSafetyData-rm ∙ sdEpoch
            vv = pre ^∙ rmEpochState ∙ esVerifier in
        (Post (ep , vv) pre [])
      → LBFT-weakestPre epvv Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl = pf

module handleProposalSpec (now : Instant) (pm : ProposalMsg) where

  open handleProposal now pm

  record Requirements (pool : SentMessages) (pre : RoundManager) : Set where
    field
      mSndr            : NodeId
      m∈pool           : (mSndr , P pm) ∈ pool
      qcs∈RmSigsSentB4 : QC.SigsForVotes∈Qc∈Rm-SentB4 pre pool

  module _ (pool : SentMessages) (pre : RoundManager) (reqs : Requirements pool pre) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General properties / invariants
        rmInv              : Preserves RoundManagerInv pre post
        noEpochChange      : NoEpochChange pre post
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrectWithEpochReq pre post outs (pm ^∙ pmProposal)
        -- Signatures
        qcs∈RM∈Pool        : QC.SigsForVotes∈Qc∈Rm-SentB4 post pool
        outQcs∈RM          : QC.OutputQc∈RoundManager outs pre

    contract : LBFT-weakestPre (handleProposal now pm) Contract pre
    contract =
      epvvSpec.contract pre
        (RWST-weakestPre-bindPost unit (λ where (myEpoch , vv) → step₁ myEpoch vv) Contract)
        contract-step₁
      where
      contractBail : ∀ outs → OutputProps.NoVotes outs → Contract unit pre outs
      contractBail outs noVotes =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          (Voting.mkVoteAttemptCorrectWithEpochReq (Voting.voteAttemptBailed outs noVotes) tt)
          qc∈post⇒SigsSentB4
          outqcs∈pre
        where
        postulate -- TODO-1: Prove this (waiting on: updates to RoundManager contracts)
          outqcs∈pre : QC.OutputQc∈RoundManager outs pre
        postulate -- TODO-1: Prove this (waiting on: updates to RoundManager contracts)
          qc∈post⇒SigsSentB4 : QC.SigsForVotes∈Qc∈Rm-SentB4 pre pool

      contract-step₁ : _  -- Post condition
      proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₁ e) pp≡Left =
        contractBail _ refl
      proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₂ i) pp≡Left =
        contractBail _ refl
      proj₂ (contract-step₁ (myEpoch@._ , vv@._) refl) unit pp≡Right =
        processProposalMsgMSpec.contract now pm pre Contract pf
        where
        module PPM = processProposalMsgMSpec now pm

        sdEpoch≡ : pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ pm ^∙ pmProposal ∙ bEpoch
        sdEpoch≡
          with processProposalSpec.contract pm myEpoch vv
        ...| con rewrite pp≡Right = sym con

        pf : RWST-Post-⇒ (PPM.Contract pre) Contract
        pf unit st outs (processProposalMsgMSpec.mkContract rmInv noEpochChange voteAttemptCorrect) =
          mkContract rmInv noEpochChange
            (Voting.mkVoteAttemptCorrectWithEpochReq voteAttemptCorrect
              (Voting.voteAttemptEpochReq! voteAttemptCorrect sdEpoch≡))
            (obm-dangerous-magic' "waiting on processProposalMsgMSpec extension")
            obm-dangerous-magic! -- TODO-2: prove it, ...

    contract! : LBFT-Post-True Contract (handleProposal now pm) pre
    contract! = LBFT-contract (handleProposal now pm) Contract pre contract

    contract!-RoundManagerInv : LBFT-Post-True (λ r st outs → Preserves RoundManagerInv pre st) (handleProposal now pm) pre
    contract!-RoundManagerInv = Contract.rmInv contract!
