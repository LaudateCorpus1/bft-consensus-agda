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

  module OutQcs where
    record Requirements (pool : SentMessages) (pre : RoundManager) : Set where
      constructor mkRequirements
      field
        mSndr            : NodeId
        m∈pool           : (mSndr , P pm) ∈ pool

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General properties / invariants
        rmInv              : Preserves (RoundManagerInv pool) pre post
        noEpochChange      : NoEpochChange pre post
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrectWithEpochReq pre post outs (pm ^∙ pmProposal)
        -- Signatures
        outQcs∈RM          : OutQcs.Requirements pool pre → QCProps.OutputQc∈RoundManager outs post

    contract : LBFT-weakestPre (handleProposal now pm) Contract pre
    contract =
      epvvSpec.contract pre Post-epvv contract-step₁
      where
      Post-epvv : LBFT-Post (Epoch × ValidatorVerifier)
      Post-epvv = RWST-weakestPre-bindPost unit (λ where (myEpoch , vv) → step₁ myEpoch vv) Contract

      myEpoch = pre ^∙ pssSafetyData-rm ∙ sdEpoch
      vv      = pre ^∙ rmEpochState ∙ esVerifier

      contractBail : ∀ outs → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail outs noMsgs =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          vac outQcs∈RM
        where
        vac : Voting.VoteAttemptCorrectWithEpochReq pre pre outs (pm ^∙ pmProposal)
        vac = Voting.mkVoteAttemptCorrectWithEpochReq
                (Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs noMsgs)) tt

        outQcs∈RM : OutQcs.Requirements pool pre → QCProps.OutputQc∈RoundManager outs pre
        outQcs∈RM _ = QCProps.NoMsgs⇒OutputQc∈RoundManager outs pre noMsgs

      contract-step₁ : Post-epvv (myEpoch , vv) pre []
      proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₁ e) pp≡Left =
        contractBail _ refl
      proj₁ (contract-step₁ (myEpoch@._ , vv@._) refl) (inj₂ i) pp≡Left =
        contractBail _ refl
      proj₂ (contract-step₁ (myEpoch@._ , vv@._) refl) unit pp≡Right =
        processProposalMsgMSpec.contract now pm pool pre Contract pf
        where
        module PPM = processProposalMsgMSpec now pm

        sdEpoch≡ : pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ pm ^∙ pmProposal ∙ bEpoch
        sdEpoch≡
          with processProposalSpec.contract pm myEpoch vv
        ...| con rewrite pp≡Right = sym con

        pf : RWST-Post-⇒ (PPM.Contract pool pre) Contract
        pf unit st outs (processProposalMsgMSpec.mkContract rmInv noEpochChange voteAttemptCorrect outQcs∈RM) =
          mkContract rmInv noEpochChange vac
            outQcs∈RM'
          where
          vac : Voting.VoteAttemptCorrectWithEpochReq pre st outs (pm ^∙ pmProposal)
          vac = Voting.mkVoteAttemptCorrectWithEpochReq voteAttemptCorrect
                  (Voting.voteAttemptEpochReq! voteAttemptCorrect sdEpoch≡)

          outQcs∈RM' : OutQcs.Requirements pool pre → QCProps.OutputQc∈RoundManager outs st
          outQcs∈RM' (OutQcs.mkRequirements mSndr m∈pool) =
            outQcs∈RM (PPM.OutQcs.mkRequirements mSndr m∈pool)

    contract! : LBFT-Post-True Contract (handleProposal now pm) pre
    contract! = LBFT-contract (handleProposal now pm) Contract pre contract

    contract!-RoundManagerInv : LBFT-Post-True (λ r st outs → Preserves (RoundManagerInv pool) pre st) (handleProposal now pm) pre
    contract!-RoundManagerInv rmInv = Contract.rmInv contract! rmInv

module handleVoteSpec (now : Instant) (vm : VoteMsg) where
  open handleVote now vm

  module OutQcs where
    record Requirements (pool : SentMessages) : Set where
      constructor mkRequirements
      field
        mSndr  : NodeId
        m∈pool : (mSndr , V vm) ∈ pool

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General properties / invariants
        rmInv         : Preserves (RoundManagerInv pool) pre post
        noEpochChange : NoEpochChange pre post
        noSDChange    : NoSafetyDataChange pre post
        -- Output
        noVotes       : OutputProps.NoVotes outs
        outQcs∈RM     : OutQcs.Requirements pool → QCProps.OutputQc∈RoundManager outs post

    postulate -- TODO-2: prove (waiting on: refinement of `Contract`)
      contract : LBFT-weakestPre (handleVote now vm) Contract pre

    contract! : LBFT-Post-True Contract (handleVote now vm) pre
    contract! = LBFT-contract (handleVote now vm) Contract pre contract
