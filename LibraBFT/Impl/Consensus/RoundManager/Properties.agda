{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.BlockStorage.BlockStore            as BlockStore
import      LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore as BlockStoreProps
import      LibraBFT.Impl.Consensus.BlockStorage.Properties.SyncManager as SyncManagerProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock       as ExecutedBlock
import      LibraBFT.Impl.Consensus.Liveness.RoundState                as RoundState
import      LibraBFT.Impl.Consensus.Liveness.ProposerElection          as ProposerElection
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage          as PersistentLivenessStorage
import      LibraBFT.Impl.Consensus.PersistentLivenessStorage.Properties as PersistentLivenessStorageProps
open import LibraBFT.Impl.Consensus.RoundManager
import      LibraBFT.Impl.Consensus.SafetyRules.SafetyRules            as SafetyRules
import      LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules as SafetyRulesProps
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open OutputProps
open RoundManagerInvariants
open RoundManagerTransProps

-- This module contains properties that are only about the behavior of the handlers, nothing to do
-- with system state

module LibraBFT.Impl.Consensus.RoundManager.Properties where

module executeAndVoteMSpec (b : Block) where

  open executeAndVoteM b
  open SafetyRulesProps
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore

  VoteResultCorrect : (pre post : RoundManager) (lvr≡? : Bool) (r : Either ErrLog Vote) → Set
  VoteResultCorrect pre post lvr≡? (Left _) =
    VoteNotGenerated pre post lvr≡? ⊎ Voting.VoteGeneratedUnsavedCorrect pre post b
  VoteResultCorrect pre post lvr≡? (Right vote) =
    Voting.VoteGeneratedCorrect pre post vote b

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General properties / invariants
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noMsgOuts     : OutputProps.NoMsgs outs
        -- Voting
        lvr≡?             : Bool
        voteResultCorrect : VoteResultCorrect pre post lvr≡? r

    contract'
      : LBFT-weakestPre (executeAndVoteM b) Contract pre
    contract' =
      executeAndInsertBlockMSpec.contract b pre
        (RWST-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ [])) (RWST-weakestPre-ebindPost unit step₁ Contract))
          (λ where e e≡ ._ refl → contractBail [] refl)
          contract-step₁
      where
      contractBail : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) pre outs
      contractBail outs noMsgOuts =
        mkContract
          reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          noMsgOuts true (inj₁ reflVoteNotGenerated)

      module _
        (bs' : BlockStore) (eb : ExecutedBlock)
        (eaibRight : Right (bs' , eb) ≡ BlockStore.executeAndInsertBlockE (pre ^∙ lBlockStore) b) where

        preUpdateBS = pre & lBlockStore ∙~ bs'

        eb≡b = (BlockStoreProps.executeAndInsertBlockESpec.ebBlock≡ (pre ^∙ lBlockStore) b (sym eaibRight))

        eb≡b-epoch : (eb ^∙ ebBlock) ≡L b at bEpoch
        eb≡b-epoch rewrite eb≡b = refl

        eb≡b-round : (eb ^∙ ebBlock) ≡L b at bRound
        eb≡b-round rewrite eb≡b = refl

        -- State invariants
        module _  where
          qcP : Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre preUpdateBS
          qcP = obm-dangerous-magic' "TODO-2: contract for `executeAndInsertBlockE` should guarantee this if `b` came from pool"

          bsP : Preserves BlockStoreInv pre preUpdateBS
          bsP = executeAndInsertBlockESpec.bs'BlockInv (pre ^∙ rmBlockStore) b (sym eaibRight) refl

          srP : Preserves SafetyRulesInv pre preUpdateBS
          srP = mkPreservesSafetyRulesInv (substSafetyDataInv refl)

          invP₁ : Preserves RoundManagerInv pre preUpdateBS
          invP₁ = mkPreservesRoundManagerInv id id bsP srP

        contractBailSetBS : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) preUpdateBS outs
        contractBailSetBS outs noMsgOuts =
          mkContract invP₁ refl
            noMsgOuts true (inj₁ (mkVoteNotGenerated refl refl))

        contract-step₁
          : RWST-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ []))
              (RWST-weakestPre-ebindPost unit step₁ Contract) (Right eb) preUpdateBS []
        contract-step₂
          : RWST-weakestPre (step₂ eb) Contract unit preUpdateBS

        proj₁ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡just = contractBailSetBS [] refl
        proj₁ (proj₂ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡none) so≡true = contractBailSetBS [] refl
        proj₂ (proj₂ (contract-step₁ ._ refl ._ refl ._ refl ._ refl ._ refl) vs≡none) so≡false = contract-step₂

        maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb

        contract-step₂ =
          constructAndSignVoteMSpec.contract maybeSignedVoteProposal' preUpdateBS pool
            (RWST-weakestPre-ebindPost unit step₃ Contract) pf
          where
          pf : RWST-Post-⇒
                 (constructAndSignVoteMSpec.Contract preUpdateBS pool _)
                 (RWST-weakestPre-ebindPost unit step₃ Contract)
          pf r st outs (constructAndSignVoteMSpec.mkContract rmInv noEpochChange noMsgOuts lvr≡? voteResCorrect) = pf' r voteResCorrect
            where
            module CASV = constructAndSignVoteMSpec
            invP₂ = transPreservesRoundManagerInv invP₁ rmInv

            pf' : (r : Either ErrLog Vote) (vrc : CASV.VoteResultCorrect preUpdateBS st (CASV.proposedBlock maybeSignedVoteProposal') lvr≡? r)
                  → (RWST-weakestPre-ebindPost unit step₃ Contract) r st outs
            pf' (Left _) vc =
              mkContract invP₂ noEpochChange noMsgOuts lvr≡?
                (inj₁ (transVoteNotGenerated (mkVoteNotGenerated refl refl) vc))
            pf' (Right vote) vc ._ refl rewrite eb≡b =
              PersistentLivenessStorageProps.saveVoteMSpec.contract vote
                (RWST-weakestPre-ebindPost unit (const (ok vote)) (RWST-Post++ Contract outs)) st
                onSaveFailed onSaveSucceeded

                where
                vgc : Voting.VoteGeneratedCorrect pre st vote _
                vgc = Voting.glue-VoteNotGenerated-VoteGeneratedCorrect
                        (mkVoteNotGenerated refl refl) vc

                onSaveFailed : _
                onSaveFailed outs₁ noMsgOuts₁ noErrOuts₁ =
                  mkContract invP₂ noEpochChange
                    (OutputProps.++-NoMsgs outs _ noMsgOuts noMsgOuts₁)
                    lvr≡?
                    (inj₂ (Voting.mkVoteGeneratedUnsavedCorrect vote vgc))

                onSaveSucceeded : _
                onSaveSucceeded outs₁ noMsgOuts₁ noErrOuts₁ .unit refl =
                  mkContract invP₂ noEpochChange
                    (OutputProps.++-NoMsgs outs _ noMsgOuts (OutputProps.++-NoMsgs outs₁ _ noMsgOuts₁ refl))
                    lvr≡? vgc

    contract
      : ∀ Post
        → (∀ r st outs → Contract r st outs → Post r st outs)
        → LBFT-weakestPre (executeAndVoteM b) Post pre
    contract Post pf =
      RWST-⇒ Contract Post pf (executeAndVoteM b) unit pre contract'

module processProposalMSpec (proposal : Block) where

  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore
  open import LibraBFT.Impl.Consensus.Liveness.Properties.ProposerElection
  open        LibraBFT.Impl.Consensus.RoundManager.processProposalM proposal

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
         -- General properties / invariants
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noProposals   : OutputProps.NoProposals outs
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrect pre post outs proposal

    contract' : LBFT-weakestPre (processProposalM proposal) Contract pre
    contract' ._ refl =
      isValidProposalMSpec.contract proposal pre
        (RWST-weakestPre-bindPost unit (step₁ (pre ^∙ lBlockStore)) Contract)
        (λ where
          mAuthor≡nothing ._ refl → (λ _ → contractBail refl) , (λ where ()))
        (λ where
          notValid ._ refl → (λ _ → contractBail refl) , (λ where ()))
        λ where
          vp ._ refl →
            (λ where ())
            , (λ _ →
                 (λ _ → contractBail refl)
                 , (λ _ →
                      (λ _ → contractBail refl)
                      , (λ _ → contract-step₂)))
      where
      contractBail : ∀ {outs} → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail{outs} nmo =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          (OutputProps.NoMsgs⇒NoProposals outs nmo)
          (Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo))

      contract-step₂ : RWST-weakestPre (executeAndVoteM proposal >>= step₂) Contract unit pre
      contract-step₂ =
        executeAndVoteMSpec.contract proposal pool pre
          (RWST-weakestPre-bindPost unit step₂ Contract) pf-step₂
        where
        module EAV = executeAndVoteMSpec proposal

        pf-step₂ : RWST-Post-⇒ (EAV.Contract pool pre) (RWST-weakestPre-bindPost unit step₂ Contract)
        pf-step₂ r st outs (executeAndVoteMSpec.mkContract rmInv noEpochChange noMsgOuts lvr≡? voteResultCorrect) = pf r voteResultCorrect
          where
            rmInv₂ = transPreservesRoundManagerInv reflPreservesRoundManagerInv rmInv

            pf : (r : Either ErrLog Vote) (vrc : EAV.VoteResultCorrect pre st lvr≡? r) → RWST-weakestPre-bindPost unit step₂ Contract r st outs
            pf (Left _) vrc ._ refl =
              mkContract rmInv₂ noEpochChange
                (OutputProps.++-NoProposals outs _ (OutputProps.NoMsgs⇒NoProposals outs noMsgOuts) refl)
                (inj₁ (lvr≡? , Voting.mkVoteUnsentCorrect
                                 (OutputProps.++-NoVotes outs _ (OutputProps.NoMsgs⇒NoVotes outs noMsgOuts) refl) vrc))
            pf (Right vote) vrc ._ refl ._ refl ._ refl =
              syncInfoMSpec.contract (st & rsVoteSent-rm ?~ vote)
                (RWST-weakestPre-bindPost unit (step₃ vote) (RWST-Post++ Contract outs))
                contract-step₃
              where
              stUpdateRS = st & rsVoteSent-rm ?~ vote

              module _
                (si : SyncInfo)
                (si≡ : si ≡ SyncInfo∙new
                              (st ^∙ lBlockStore ∙ bsHighestQuorumCert)
                              (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                              (st ^∙ lBlockStore ∙ bsHighestTimeoutCert))
                where
                contract-step₃ : RWST-weakestPre (step₃ vote si) (RWST-Post++ Contract outs) unit stUpdateRS
                contract-step₃ ._ refl ._ refl ._ refl ._ refl recipient@._ refl =
                  mkContract rmInv₃
                    (transNoEpochChange{i = pre}{j = st}{k = stUpdateRS} noEpochChange refl)
                    (OutputProps.++-NoProposals outs _ (OutputProps.NoMsgs⇒NoProposals outs noMsgOuts) refl)
                    (inj₂ (Voting.mkVoteSentCorrect vm recipient
                            (OutputProps.++-NoVotes-OneVote outs _ (OutputProps.NoMsgs⇒NoVotes outs noMsgOuts) refl)
                            (Voting.glue-VoteGeneratedCorrect-VoteNotGenerated{s₂ = st}
                              vrc (mkVoteNotGenerated refl refl))))
                  where
                  vm = VoteMsg∙new vote si

                  -- state invariants
                  module _ where
                    qcP : Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) st stUpdateRS
                    qcP = substSigsForVotes∈Rm-SentB4 refl

                    postulate -- TODO-1: prove (waiting on: `α-RM`)
                      bsP : Preserves BlockStoreInv st stUpdateRS
                   -- bsP = id

                    srP : Preserves SafetyRulesInv st stUpdateRS
                    srP = mkPreservesSafetyRulesInv (substSafetyDataInv refl)

                    rmInv₃ : Preserves RoundManagerInv pre stUpdateRS
                    rmInv₃ = transPreservesRoundManagerInv rmInv₂
                             (mkPreservesRoundManagerInv id id bsP srP)

    contract : ∀ Post → RWST-Post-⇒ Contract Post → LBFT-weakestPre (processProposalM proposal) Post pre
    contract Post pf = LBFT-⇒ Contract Post pf (processProposalM proposal) pre contract'

module syncUpMSpec
  (now : Instant) (syncInfo : SyncInfo) (author : Author) (_helpRemote : Bool) where

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        outQcs∈RMor   : QCProps.OutputQc∈RmOr outs pre post (_QC∈SyncInfo syncInfo)

    postulate -- TODO-3: prove (waiting on: `syncUpM`)
      -- This is expected to be quite challenging, since syncing up can cause
      -- significant state changes, and currently (in the Haskell implementation)
      -- requires backdoor communications with other peers.
      contract' : LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Contract pre

    contract
      : ∀ Post → (∀ r st outs → Contract r st outs → Post r st outs)
        → LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Post pre
    contract Post pf =
      LBFT-⇒ Contract Post pf (syncUpM now syncInfo author _helpRemote) pre
        contract'

module ensureRoundAndSyncUpMSpec
  (now : Instant) (messageRound : Round) (syncInfo : SyncInfo)
  (author : Author) (helpRemote : Bool) where

  open ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (r : Either ErrLog Bool) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        outQcs∈RMor   : QCProps.OutputQc∈RmOr outs pre post (_QC∈SyncInfo syncInfo)

    contract'
      : LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Contract pre
    proj₁ (contract' ._ refl) _         =
      mkContract id refl refl (mkVoteNotGenerated refl refl) []
    proj₂ (contract' ._ refl) mrnd≥crnd = contract-step₁
      where
      contract-step₁
        : RWST-weakestPre (syncUpM now syncInfo author helpRemote)
            (RWST-weakestPre-ebindPost unit (const step₂) Contract)
            unit pre
      contract-step₁ = syncUpMSpec.contract now syncInfo author helpRemote pool pre Post contract-step₁'
        where
        Post = RWST-weakestPre-ebindPost unit (const step₂) Contract

        contract-step₁' : _
        contract-step₁' (Left  _   ) st outs (syncUpMSpec.mkContract rmInv noEpochChange noVoteOuts noVote outQcs∈) =
          mkContract rmInv noEpochChange noVoteOuts noVote
            (obm-dangerous-magic' "TODO: waiting on contract for `syncUpM")
        contract-step₁' (Right unit) st outs (syncUpMSpec.mkContract rmInv noEpochChange noVoteOuts noVote outQcs∈) = contract-step₂
          where

          noVoteOuts' : NoVotes (outs ++ [] ++ [])
          noVoteOuts' = ++-NoneOfKind outs ([] ++ []) isSendVote? noVoteOuts refl

          contract-step₂ : _
          proj₁ (contract-step₂ ._ refl ._ refl) _ =
            mkContract rmInv noEpochChange noVoteOuts' noVote (obm-dangerous-magic' "TODO: waiting on contract for `syncUpM`")
          proj₂ (contract-step₂ ._ refl ._ refl) _ =
            mkContract rmInv noEpochChange noVoteOuts' noVote (obm-dangerous-magic' "TODO: waiting on contract for `syncUpM`")

    contract : ∀ Post → RWST-Post-⇒ Contract Post → LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Post pre
    contract Post pf =
      LBFT-⇒ Contract Post pf (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) pre contract'

module processProposalMsgMSpec
  (now : Instant) (pm : ProposalMsg) where

  proposal = pm ^∙ pmProposal

  open processProposalMsgM now pm

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrect pre post outs proposal
        -- Signatures
        outQcs∈RM : QCProps.OutputQc∈RmOr outs pre post (_QC∈NM P pm)
        qcSigsB4  : QCProps.MsgRequirements pool (P pm) → Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre post

    contract' : LBFT-weakestPre (processProposalMsgM now pm) Contract pre
    contract' rewrite processProposalMsgM≡ = contract
      where
      contractBail : ∀ outs → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail outs nmo = {!!}
        -- mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre})
        --   (Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo))
        --   (const $ QCProps.NoMsgs⇒OutputQc∈RmOrMsg outs pre nmo)

      contract : LBFT-weakestPre step₀ Contract pre
      proj₁ contract ≡nothing = contractBail _ refl
      proj₂ contract = contract-step₁
        where
        module _ (pAuthor : Author) (pAuthor≡ : pm ^∙ pmProposer ≡ just pAuthor) where
          pf-step₂ : RWST-Post-⇒ _ (RWST-weakestPre-bindPost unit step₂ Contract)

          contract-step₁ : LBFT-weakestPre (step₁ pAuthor) Contract pre
          contract-step₁ =
            ensureRoundAndSyncUpMSpec.contract now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo) pAuthor true pool pre
              (RWST-weakestPre-bindPost unit step₂ Contract) pf-step₂

          pf-step₂ r st outs (ensureRoundAndSyncUpMSpec.mkContract rmInv noEpochChange noVoteOuts noVote outQcs∈RM) = pf-step₂' r
            where
            contractBailAfterSync : ∀ outs' → OutputProps.NoMsgs outs' → RWST-Post++ Contract outs unit st outs'
            contractBailAfterSync outs' noMsgs' =
              mkContract rmInv noEpochChange vac {!!} {!!} -- outQcs∈RM'
              where
              vac : Voting.VoteAttemptCorrect pre st (outs ++ outs') proposal
              vac = Left (true , (Voting.mkVoteUnsentCorrect
                                   (OutputProps.++-NoVotes outs _ noVoteOuts (OutputProps.NoMsgs⇒NoVotes outs' noMsgs'))
                                   (Left noVote)))

              outQcs∈RM' : QCProps.MsgRequirements pool (P pm) → QCProps.OutputQc∈RmOrMsg (outs ++ outs') st (P pm)
              outQcs∈RM' msgReq = {!!}
                -- QCProps.++-OutputQc∈RmOrMsg
                --   (outQcs∈RM (QCProps.mkSyncInfoRequirements (P pm) msgReq inP))
                --   (QCProps.NoMsgs⇒OutputQc∈RmOrMsg outs' st noMsgs')

            pf-step₂' : (r : Either ErrLog Bool) → RWST-weakestPre-bindPost unit step₂ Contract r st outs
            pf-step₂' (Left e) ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right false) ._ refl ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right true) ._ refl =
              processProposalMSpec.contract (pm ^∙ pmProposal) pool st (RWST-Post++ Contract outs) pf-step₃
              where
              pf-step₃ : RWST-Post-⇒ _ (RWST-Post++ Contract outs)
              pf-step₃ unit st' outs' (processProposalMSpec.mkContract rmInv' noEpochChange' NoProposals' voteAttemptCorrect') =
                mkContract
                  (transPreservesRoundManagerInv rmInv rmInv')
                  (transNoEpochChange{i = pre}{j = st}{k = st'} noEpochChange noEpochChange')
                  (Voting.glue-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs}
                    noVote noVoteOuts voteAttemptCorrect')
                  (obm-dangerous-magic' "TODO")
                  {!!}

    contract : ∀ Post → RWST-Post-⇒ Contract Post → LBFT-weakestPre (processProposalMsgM now pm) Post pre
    contract Post pf =
      LBFT-⇒ Contract Post pf (processProposalMsgM now pm) pre contract'
