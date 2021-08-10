{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

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

  module _ (pre : RoundManager) where

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
        -- QCs
        qcPost : QCProps.∈Post⇒∈PreOr pre post (_≡ b ^∙ bQuorumCert)
        qcPres : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre post

    contract' :
      LBFT-weakestPre (executeAndVoteM b) Contract pre
    contract' =
      executeAndInsertBlockMSpec.contract b pre Post₀
        (λ where e ._ refl → contractBail [] refl)
        contract₁
      where
      Post₀ : LBFT-Post (Either ErrLog ExecutedBlock)
      Post₀ = RWST-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ []))
                (RWST-weakestPre-ebindPost unit step₁ Contract)

      contractBail : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) pre outs
      contractBail{e} outs noMsgOuts =
        mkContract
          reflPreservesRoundManagerInv (reflNoEpochChange{pre})
          noMsgOuts true vrc
          qcPost qcPres
        where
        vrc : VoteResultCorrect pre pre true (Left e)
        vrc = inj₁ reflVoteNotGenerated

        qcPost : QCProps.∈Post⇒∈PreOr pre pre (_≡ b ^∙ bQuorumCert)
        qcPost qc = Left

        qcPres : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre pre
        qcPres qc = id

      module EAIBM = executeAndInsertBlockMSpec b
      module EAIBE = executeAndInsertBlockESpec (EAIBM.bs pre) b
      module _ (isOk : EAIBE.Ok) (con : EAIBE.ContractOk (proj₁ isOk) (proj₁ (proj₂ isOk))) where

        module EAIBECon = EAIBE.ContractOk con

        bs' = proj₁ isOk
        eb  = proj₁ (proj₂ isOk)

        pre₁ = pre & rmBlockStore ∙~ bs'

        -- State invariants
        module _  where
          bsP : Preserves BlockStoreInv pre pre₁
          bsP = EAIBECon.bsInv pre refl

          srP : Preserves SafetyRulesInv pre pre₁
          srP = mkPreservesSafetyRulesInv (substSafetyDataInv refl)

        invP₁ : Preserves RoundManagerInv pre pre₁
        invP₁ = mkPreservesRoundManagerInv id id bsP srP

        qcPost₁ : QCProps.∈Post⇒∈PreOr pre pre₁ (_≡ b ^∙ bQuorumCert)
        qcPost₁ = EAIBECon.qcPost

        qcPres₁ : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre pre₁
        qcPres₁ = EAIBECon.qcPres pre refl

        -- For the case any of the checks in `step₁` fails
        contractBail₁ : ∀ {e} outs → OutputProps.NoMsgs outs → Contract (Left e) pre₁ outs
        contractBail₁ outs noMsgOuts =
          mkContract invP₁ refl
            noMsgOuts true (inj₁ (mkVoteNotGenerated refl refl))
            qcPost₁ qcPres₁

        contract₁ : Post₀ (Right eb) pre₁ []
        proj₁ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _ = contractBail₁ [] refl
        proj₁ (proj₂ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _) _ = contractBail₁ [] refl
        proj₂ (proj₂ (contract₁ ._ refl ._ refl ._ refl ._ refl ._ refl) _) _ = contract₂
          where
          maybeSignedVoteProposal' = ExecutedBlock.maybeSignedVoteProposal eb

          module CASV = constructAndSignVoteMSpec

          proposedBlock = CASV.proposedBlock maybeSignedVoteProposal'

          Post₂ : LBFT-Post (Either ErrLog Vote)
          Post₂ = RWST-weakestPre-ebindPost unit step₃ Contract

          contract₂ : RWST-weakestPre (step₂ eb) Contract unit pre₁

          contract₂⇒ : RWST-Post-⇒ (CASV.Contract pre₁ proposedBlock) Post₂
          contract₂⇒ r pre₃ outs con = contract₂⇒-help r CASVCon.voteResCorrect
            where
            module CASVCon = CASV.Contract con
            CASVouts = outs

            invP₂ = transPreservesRoundManagerInv invP₁ CASVCon.rmInv

            qcPost₂ : QCProps.∈Post⇒∈PreOr pre pre₃ (_≡ b ^∙ bQuorumCert)
            qcPost₂ = obm-dangerous-magic' "TODO: waiting on `constructAndSignVoteM` contract"

            qcPres₂ : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre pre₃
            qcPres₂ = obm-dangerous-magic' "TODO: waiting on `constructAndSignVoteM` contract"

            contract₂⇒-help :
              (r : Either ErrLog Vote) (vrc : CASV.VoteResultCorrect pre₁ pre₃ proposedBlock CASVCon.lvr≡? r)
              → RWST-weakestPre-ebindPost unit step₃ Contract r pre₃ outs
            contract₂⇒-help (Left _) vrc =
              mkContract invP₂ CASVCon.noEpochChange CASVCon.noMsgOuts
                CASVCon.lvr≡? (Left (transVoteNotGenerated (mkVoteNotGenerated refl refl) vrc))
                qcPost₂ qcPres₂
            contract₂⇒-help (Right vote) vrc ._ refl = contract₃
              where
              contract₃ : RWST-weakestPre (step₃ vote) (RWST-Post++ Contract CASVouts) unit pre₃
              contract₃ =
                PersistentLivenessStorageProps.saveVoteMSpec.contract vote
                  Post₃ pre₃
                  contractBail₃ contractOk₃
                where
                Post₃ : LBFT-Post (Either ErrLog Unit)
                Post₃ = RWST-weakestPre-ebindPost unit (const $ ok vote) (RWST-Post++ Contract CASVouts)

                vgc₃ : Voting.VoteGeneratedCorrect pre pre₃ vote b {- proposedBlock -}
                vgc₃ =
                  Voting.glue-VoteNotGenerated-VoteGeneratedCorrect
                    (mkVoteNotGenerated refl refl)
                    (Voting.substVoteGeneratedCorrect proposedBlock b
                      EAIBECon.ebBlock≈ vrc)

                noMsgOutsBail₃ : ∀ outs → NoMsgs outs → NoMsgs (CASVouts ++ outs)
                noMsgOutsBail₃ outs noMsgs = ++-NoMsgs CASVouts outs CASVCon.noMsgOuts noMsgs

                noMsgOutsOk₃ : ∀ outs → NoMsgs outs → NoMsgs (CASVouts ++ outs ++ [])
                noMsgOutsOk₃ outs noMsgs rewrite ++-identityʳ outs = noMsgOutsBail₃ outs noMsgs

                contractBail₃ : ∀ outs → NoMsgs outs → NoErrors outs → Post₃ (Left fakeErr) pre₃ outs
                contractBail₃ outs noMsgOuts noErrOuts =
                  mkContract invP₂ CASVCon.noEpochChange (noMsgOutsBail₃ outs noMsgOuts)
                    CASVCon.lvr≡? (Right (Voting.mkVoteGeneratedUnsavedCorrect vote vgc₃))
                    qcPost₂ qcPres₂

                contractOk₃ : ∀ outs → NoMsgs outs → NoErrors outs → Post₃ (Right unit) pre₃ outs
                contractOk₃ outs noMsgs noErrs unit refl =
                  mkContract invP₂ CASVCon.noEpochChange (noMsgOutsOk₃ outs noMsgs)
                    CASVCon.lvr≡? vgc₃
                    qcPost₂ qcPres₂

          contract₂ = constructAndSignVoteMSpec.contract maybeSignedVoteProposal' pre₁ Post₂ contract₂⇒

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

  module _ (pre : RoundManager) where

    record Contract (u : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
         -- General properties / invariants
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noProposals   : OutputProps.NoProposals outs
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrect pre post outs proposal
        -- QCs
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost    : QCProps.∈Post⇒∈PreOr pre post (_≡ proposal ^∙ bQuorumCert)
        qcsPres   : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre post

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
          noProposals vac outQcs qcPost qcPres
        where
          noProposals : NoProposals outs
          noProposals = OutputProps.NoMsgs⇒NoProposals outs nmo

          vac : Voting.VoteAttemptCorrect pre pre outs proposal
          vac = Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo)

          outQcs : QCProps.OutputQc∈RoundManager outs pre
          outQcs = QCProps.NoMsgs⇒OutputQc∈RoundManager outs pre nmo

          qcPost : QCProps.∈Post⇒∈PreOr pre pre _
          qcPost qc = Left

          qcPres : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre pre
          qcPres qc = id

      contract-step₂ : RWST-weakestPre (executeAndVoteM proposal >>= step₂) Contract unit pre
      contract-step₂ =
        executeAndVoteMSpec.contract proposal pre
          (RWST-weakestPre-bindPost unit step₂ Contract) pf-step₂
        where
        module EAV = executeAndVoteMSpec proposal

        pf-step₂ : RWST-Post-⇒ (EAV.Contract pre) (RWST-weakestPre-bindPost unit step₂ Contract)
        pf-step₂ r st outs con = pf r EAVSpec.voteResultCorrect
          where
          module EAVSpec = executeAndVoteMSpec.Contract con
          rmInv₂ = transPreservesRoundManagerInv reflPreservesRoundManagerInv EAVSpec.rmInv

          pf : (r : Either ErrLog Vote) (vrc : EAV.VoteResultCorrect pre st EAVSpec.lvr≡? r) → RWST-weakestPre-bindPost unit step₂ Contract r st outs
          pf (Left _) vrc ._ refl =
            mkContract rmInv₂ EAVSpec.noEpochChange noProposals
              vac
              (obm-dangerous-magic' "TODO: waiting on contract for executeAndVoteM")
              (obm-dangerous-magic' "TODO: waiting on contract for executeAndVoteM")
              (obm-dangerous-magic' "TODO: waiting on contract for executeAndVoteM")
            where
            noProposals : NoProposals (outs ++ LogErr _ ∷ [])
            noProposals = ++-NoProposals outs _ (NoMsgs⇒NoProposals outs EAVSpec.noMsgOuts) refl

            vac : Voting.VoteAttemptCorrect pre st (outs ++ LogErr _ ∷ []) proposal
            vac = inj₁ (EAVSpec.lvr≡?
                       , Voting.mkVoteUnsentCorrect
                           (OutputProps.++-NoVotes outs _ (OutputProps.NoMsgs⇒NoVotes outs EAVSpec.noMsgOuts) refl) vrc)
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
                  (transNoEpochChange{i = pre}{j = st}{k = stUpdateRS} EAVSpec.noEpochChange refl)
                  (OutputProps.++-NoProposals outs _ (OutputProps.NoMsgs⇒NoProposals outs EAVSpec.noMsgOuts) refl)
                  vac outQcs qcPost qcPres
                where
                vm = VoteMsg∙new vote si

                vac : Voting.VoteAttemptCorrect pre stUpdateRS (outs ++ SendVote vm _ ∷ []) proposal
                vac =
                  inj₂ (Voting.mkVoteSentCorrect vm recipient
                         (OutputProps.++-NoVotes-OneVote outs _ (OutputProps.NoMsgs⇒NoVotes outs EAVSpec.noMsgOuts) refl)
                         (Voting.glue-VoteGeneratedCorrect-VoteNotGenerated{s₂ = st}
                           vrc (mkVoteNotGenerated refl refl)))

                outQcs : QCProps.OutputQc∈RoundManager (outs ++ SendVote vm _ ∷ []) stUpdateRS
                outQcs =
                  QCProps.++-OutputQc∈RoundManager{stUpdateRS}{outs}
                    (QCProps.NoMsgs⇒OutputQc∈RoundManager outs stUpdateRS EAVSpec.noMsgOuts)
                    (outQcSendVote ∷ [])
                  where
                  outQcSendVote : ∀ qc nm → qc QC∈NM nm → nm Msg∈Out (SendVote vm _) → qc QCProps.∈RoundManager stUpdateRS
                  outQcSendVote qc .(V (VoteMsg∙new vote si)) (inSI inV (withVoteSIHighQC qc≡)) inSV rewrite si≡ =
                    QCProps.inHQC (sym qc≡)
                  outQcSendVote qc .(V (VoteMsg∙new vote si)) (inSI inV (withVoteSIHighCC qc≡)) inSV =
                    QCProps.inHCC (just-injective $
                      begin
                        just qc ≡⟨ lem₁ ⟩
                        sixxx   ≡⟨ lem₂ (cong is-just (sym lem₁)) ⟩
                        just (stUpdateRS ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert) ∎)
                    where
                    open ≡-Reasoning
                    sixxx = if (st ^∙ lBlockStore ∙ bsHighestQuorumCert) QCBoolEq (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                            then nothing
                            else (just $ (st ^∙ lBlockStore ∙ bsHighestCommitCert))

                    lem₁ : just qc ≡ sixxx
                    lem₁ = begin
                      just qc ≡⟨ sym qc≡ ⟩
                      vm ^∙ vmSyncInfo ∙ sixxxHighestCommitCert ≡⟨ cong (_^∙ sixxxHighestCommitCert) si≡ ⟩
                      sixxx ∎

                    lem₂ : is-just sixxx ≡ true
                           → sixxx ≡ just (stUpdateRS ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert)
                    lem₂ isj
                        with (st ^∙ lBlockStore ∙ bsHighestQuorumCert) QCBoolEq (st ^∙ lBlockStore ∙ bsHighestCommitCert)
                    ... | false = refl
                    ... | true = absurd false ≡ true case isj of λ ()

                qcPost : QCProps.∈Post⇒∈PreOr pre stUpdateRS (_≡ proposal ^∙ bQuorumCert)
                qcPost qc qc∈st = obm-dangerous-magic' "TODO: waiting on contract for executeAndVoteM"

                qcPres : ∀ qc → Preserves (qc QCProps.∈RoundManager_) pre stUpdateRS
                qcPres qc = obm-dangerous-magic' "TODO: waiting on contract for executeAndVoteM"

                -- state invariants
                module _ where
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

  open syncUpM now syncInfo author _helpRemote
  open import LibraBFT.Impl.Consensus.ConsensusTypes.Properties.SyncInfo
  open import LibraBFT.Impl.Consensus.BlockStorage.Properties.SyncManager

  module _ (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noVoteOuts    : OutputProps.NoVotes outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- QCs
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost    : QCProps.∈Post⇒∈PreOr pre post (_QC∈SyncInfo syncInfo)

    contract' : LBFT-weakestPre (syncUpM now syncInfo author _helpRemote) Contract pre
    contract' =
      BlockStoreProps.syncInfoMSpec.contract pre
        (RWST-weakestPre-bindPost unit step₁ Contract)
        contract₁
      where
      localSyncInfo = BlockStoreProps.syncInfoMSpec.syncInfo pre

      contract₁ : RWST-weakestPre-bindPost unit step₁ Contract (BlockStoreProps.syncInfoMSpec.syncInfo pre) pre []
      proj₂ (contract₁ localSyncInfo lsi≡) hnc≡false =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre}) refl
          (reflVoteNotGenerated{pre})
          outQcs qcPost
        where
        outQcs : QCProps.OutputQc∈RoundManager [] pre
        outQcs = QCProps.NoMsgs⇒OutputQc∈RoundManager [] pre refl

        qcPost : QCProps.∈Post⇒∈PreOr pre pre _
        qcPost qc = Left
      proj₁ (contract₁ localSyncInfo lsi≡) hcn≡true vv@._ refl =
        verifyMSpec.contract syncInfo vv pre Post₁
          contract₃
        where
        Post₁ : LBFT-Post (Either ErrLog Unit)
        Post₁ = (RWST-weakestPre-∙^∙Post unit (withErrCtx (here' []))
                  (RWST-weakestPre-ebindPost unit (λ _ → step₃ localSyncInfo vv) Contract))

        contract₃ : RWST-Post-⇒ (verifyMSpec.Contract syncInfo vv pre) Post₁
        contract₃ r st outs con ._ refl
           with VSpec.noStateChange
           where module VSpec = verifyMSpec.Contract con
        contract₃ (Left x) st outs con ._ refl
           | refl
           = mkContract VSpec.rmInv (reflNoEpochChange{st})
               (++-NoVotes outs [] (NoMsgs⇒NoVotes outs VSpec.noMsgOuts) refl)
               (reflVoteNotGenerated{st})
               outQcs qcPost -- (const id)
           where
           module VSpec = verifyMSpec.Contract con
           outQcs : QCProps.OutputQc∈RoundManager (outs ++ []) st
           outQcs = QCProps.++-OutputQc∈RoundManager{rm = st}
                      (QCProps.NoMsgs⇒OutputQc∈RoundManager outs st VSpec.noMsgOuts)
                      (QCProps.NoMsgs⇒OutputQc∈RoundManager [] st refl)

           qcPost : QCProps.∈Post⇒∈PreOr st st _
           qcPost qc = Left
        contract₃ (Right y) st₃ outs₃ con₃ ._ refl
           | refl = λ where
             unit refl →
               addCertsMSpec.contract syncInfo retriever st₃
                 Post₃ contract₄
           where
           Post₃ : LBFT-Post (Either ErrLog Unit)
           Post₃ = (RWST-weakestPre-∙^∙Post unit (withErrCtx (here' []))
                     (RWST-weakestPre-ebindPost unit (λ _ → step₄ localSyncInfo vv)
                       (RWST-Post++ Contract (outs₃ ++ []))))

           retriever = BlockRetriever∙new now author

           contract₄ : RWST-Post-⇒ (addCertsMSpec.Contract syncInfo retriever st₃) Post₃
           contract₄ (Left  _) st₄ outs₄ con₄ ._ refl =
             mkContract AC.rmInv AC.noEpochChange noVotes₄ AC.noVote outqcs AC.qcPost
             where
             module AC    = addCertsMSpec.Contract con₄
             module VSpec = verifyMSpec.Contract con₃

             noVotes₄ : NoVotes $ (outs₃ ++ []) ++ outs₄ ++ []
             noVotes₄ =
               ++-NoVotes (outs₃ ++ []) (outs₄ ++ [])
                 (++-NoVotes outs₃ [] (NoMsgs⇒NoVotes outs₃ VSpec.noMsgOuts) refl)
                 (++-NoVotes outs₄ [] AC.noVoteOuts refl)

             outqcs : QCProps.OutputQc∈RoundManager ((outs₃ ++ []) ++ outs₄ ++ []) st₄
             outqcs =
               QCProps.++-OutputQc∈RoundManager{st₄}{outs₃ ++ []}{outs₄ ++ []}
                 (QCProps.++-OutputQc∈RoundManager{st₄}{outs₃}{[]}
                   (QCProps.NoMsgs⇒OutputQc∈RoundManager outs₃ st₄ VSpec.noMsgOuts)
                   (QCProps.NoMsgs⇒OutputQc∈RoundManager [] st₄ refl))
                 (QCProps.++-OutputQc∈RoundManager{st₄}{outs₄}{[]}
                   AC.outQcs∈RM
                   (QCProps.NoMsgs⇒OutputQc∈RoundManager [] st₄ refl))

           contract₄ (Right _) st₄ outs₄ con₄ ._ refl =
             obm-dangerous-magic' "TODO: waiting on contract for `processCertificatesM`"

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

  module _ (pre : RoundManager) where

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
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost   : QCProps.∈Post⇒∈PreOr pre post (_QC∈SyncInfo syncInfo)

    contract'
      : LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Contract pre
    proj₁ (contract' ._ refl) _         =
      mkContract id refl refl vng outqcs qcPost
      where
        vng : VoteNotGenerated pre pre true
        vng = mkVoteNotGenerated refl refl

        outqcs : QCProps.OutputQc∈RoundManager [] pre
        outqcs = QCProps.NoMsgs⇒OutputQc∈RoundManager [] pre refl

        qcPost : QCProps.∈Post⇒∈PreOr pre pre _
        qcPost qc = Left

    proj₂ (contract' ._ refl) mrnd≥crnd = contract-step₁
      where
      contract-step₁
        : RWST-weakestPre (syncUpM now syncInfo author helpRemote)
            (RWST-weakestPre-ebindPost unit (const step₂) Contract)
            unit pre
      contract-step₁ = syncUpMSpec.contract now syncInfo author helpRemote pre Post contract-step₁'
        where
        Post = RWST-weakestPre-ebindPost unit (const step₂) Contract

        contract-step₁' : _
        contract-step₁' (Left  _   ) st outs con =
          mkContract SU.rmInv SU.noEpochChange SU.noVoteOuts SU.noVote SU.outQcs∈RM SU.qcPost
          where
          module SU = syncUpMSpec.Contract con
        contract-step₁' (Right unit) st outs con = contract-step₂
          where
          module SU = syncUpMSpec.Contract con

          noVoteOuts' : NoVotes (outs ++ [] ++ [])
          noVoteOuts' = ++-NoneOfKind outs ([] ++ []) isSendVote? SU.noVoteOuts refl

          outqcs : QCProps.OutputQc∈RoundManager (outs ++ []) st
          outqcs = QCProps.++-OutputQc∈RoundManager{rm = st} SU.outQcs∈RM
                     (QCProps.NoMsgs⇒OutputQc∈RoundManager [] st refl)

          contract-step₂ : _
          proj₁ (contract-step₂ ._ refl ._ refl) _ =
            mkContract SU.rmInv SU.noEpochChange noVoteOuts' SU.noVote
              outqcs SU.qcPost
          proj₂ (contract-step₂ ._ refl ._ refl) _ =
            mkContract SU.rmInv SU.noEpochChange noVoteOuts' SU.noVote
              outqcs SU.qcPost

    contract : ∀ Post → RWST-Post-⇒ Contract Post → LBFT-weakestPre (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) Post pre
    contract Post pf =
      LBFT-⇒ Contract Post pf (ensureRoundAndSyncUpM now messageRound syncInfo author helpRemote) pre contract'

module processProposalMsgMSpec
  (now : Instant) (pm : ProposalMsg) where

  proposal = pm ^∙ pmProposal

  open processProposalMsgM now pm

  module _ (pre : RoundManager) where

    record Contract (_ : Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        -- Voting
        voteAttemptCorrect : Voting.VoteAttemptCorrect pre post outs proposal
        -- QCs
        outQcs∈RM : QCProps.OutputQc∈RoundManager outs post
        qcPost    : QCProps.∈Post⇒∈PreOr pre post (_QC∈NM (P pm))

    contract' : LBFT-weakestPre (processProposalMsgM now pm) Contract pre
    contract' rewrite processProposalMsgM≡ = contract
      where
      contractBail : ∀ outs → OutputProps.NoMsgs outs → Contract unit pre outs
      contractBail outs nmo =
        mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre}) vac outqcs qcPost
        where
        vac : Voting.VoteAttemptCorrect pre pre outs proposal
        vac = Voting.voteAttemptBailed outs (OutputProps.NoMsgs⇒NoVotes outs nmo)

        outqcs : QCProps.OutputQc∈RoundManager outs pre
        outqcs = QCProps.NoMsgs⇒OutputQc∈RoundManager outs pre nmo

        qcPost : QCProps.∈Post⇒∈PreOr pre pre _
        qcPost qc = Left

      contract : LBFT-weakestPre step₀ Contract pre
      proj₁ contract ≡nothing = contractBail _ refl
      proj₂ contract = contract-step₁
        where
        module _ (pAuthor : Author) (pAuthor≡ : pm ^∙ pmProposer ≡ just pAuthor) where
          pf-step₂ : RWST-Post-⇒ _ (RWST-weakestPre-bindPost unit step₂ Contract)

          contract-step₁ : LBFT-weakestPre (step₁ pAuthor) Contract pre
          contract-step₁ =
            ensureRoundAndSyncUpMSpec.contract now (pm ^∙ pmProposal ∙ bRound) (pm ^∙ pmSyncInfo) pAuthor true pre
              (RWST-weakestPre-bindPost unit step₂ Contract) pf-step₂

          pf-step₂ r st outs con = pf-step₂' r
            where
            module ERASU = ensureRoundAndSyncUpMSpec.Contract con
            contractBailAfterSync : ∀ outs' → OutputProps.NoMsgs outs' → RWST-Post++ Contract outs unit st outs'
            contractBailAfterSync outs' noMsgs' =
              mkContract ERASU.rmInv ERASU.noEpochChange vac outqcs qcPost
              where
              vac : Voting.VoteAttemptCorrect pre st (outs ++ outs') proposal
              vac = Left (true , (Voting.mkVoteUnsentCorrect
                                   (OutputProps.++-NoVotes outs _ ERASU.noVoteOuts (OutputProps.NoMsgs⇒NoVotes outs' noMsgs'))
                                   (Left ERASU.noVote)))

              outqcs : QCProps.OutputQc∈RoundManager (outs ++ outs') st
              outqcs = QCProps.++-OutputQc∈RoundManager{rm = st}
                         ERASU.outQcs∈RM
                         (QCProps.NoMsgs⇒OutputQc∈RoundManager outs' st noMsgs')

              qcPost : QCProps.∈Post⇒∈PreOr pre st (_QC∈NM (P pm))
              qcPost qc qc∈st
                 with ERASU.qcPost qc qc∈st
              ... | Left qc∈pre = Left qc∈pre
              ... | Right qc∈si = Right (inSI inP qc∈si)

            pf-step₂' : (r : Either ErrLog Bool) → RWST-weakestPre-bindPost unit step₂ Contract r st outs
            pf-step₂' (Left e) ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right false) ._ refl ._ refl =
              contractBailAfterSync _ refl
            pf-step₂' (Right true) ._ refl =
              processProposalMSpec.contract (pm ^∙ pmProposal) st (RWST-Post++ Contract outs) pf-step₃
              where
              pf-step₃ : RWST-Post-⇒ _ (RWST-Post++ Contract outs)
              pf-step₃ unit st' outs' con =
                mkContract
                  (transPreservesRoundManagerInv ERASU.rmInv (PP.rmInv con))
                  (transNoEpochChange{i = pre}{j = st}{k = st'} ERASU.noEpochChange (PP.noEpochChange con))
                  vac outqcs qcPost
                where
                module PP = processProposalMSpec.Contract
                vac : Voting.VoteAttemptCorrect pre st' (outs ++ outs') proposal
                vac = Voting.glue-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs}
                        ERASU.noVote ERASU.noVoteOuts (PP.voteAttemptCorrect con)

                outqcs : QCProps.OutputQc∈RoundManager (outs ++ outs') st'
                outqcs = QCProps.++-OutputQc∈RoundManager{rm = st'}
                           (All-map
                             (λ ∈rm qc nm qc∈nm nm∈out → PP.qcsPres con qc (∈rm qc nm qc∈nm nm∈out))
                             ERASU.outQcs∈RM)
                           (PP.outQcs∈RM con)

                qcPost : QCProps.∈Post⇒∈PreOr pre st' (_QC∈NM (P pm))
                qcPost qc qc∈st'
                   with PP.qcPost con qc qc∈st'
                ...| Right refl = Right inP
                ...| Left qc∈st
                   with ERASU.qcPost qc qc∈st
                ... | Right qc∈si = Right (inSI inP qc∈si)
                ... | Left qc∈pre = Left qc∈pre

    contract : ∀ Post → RWST-Post-⇒ Contract Post → LBFT-weakestPre (processProposalMsgM now pm) Post pre
    contract Post pf =
      LBFT-⇒ Contract Post pf (processProposalMsgM now pm) pre contract'
