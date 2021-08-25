{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.BlockStorage.BlockTree
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Consensus.ConsensusTypes.ExecutedBlock as ExecutedBlock
open import LibraBFT.Impl.OBM.Prelude
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Prelude
open import Optics.All

open QCProps
open Invariants

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockTree where


module insertBlockESpec (block : ExecutedBlock) (bt : BlockTree) where

  record ContractOk (bt“ : BlockTree) (b : ExecutedBlock) : Set where
    constructor mkContractOk
    field
      block≈ : b [ _≈Block_ ]L block at ebBlock
      -- TODO-1: the returned block tree is the same as the previous block tree at all values not equal to b ^∙ ebId

  Contract : Either ErrLog (BlockTree × ExecutedBlock) → Set
  Contract (Left _) = ⊤
  Contract (Right (bt' , b)) = ContractOk bt' b

  postulate -- TODO-1: prove, (waiting on: refinement of `ContractOk`)
    contract : Contract (insertBlockE.E block bt)

  module _ (bt“ : BlockTree) (b : ExecutedBlock) (con : ContractOk bt“ b) where

    postulate -- TODO-1: prove (waiting on: refinement of assumption)
      preservesBlockStoreInv
        : ∀ rm → rm ^∙ rmBlockStore ∙ bsInner ≡ bt
          → Preserves BlockStoreInv rm (rm & rmBlockStore ∙ bsInner ∙~ bt“)
            ⊎ ⊥ -- NOTE: This disjunct is for when there is a hash collision
                -- between b ^∙ ebBlock ∙ bBlockData and block ^∙ ebBlock ∙
                -- bBlockdata

      qcPost : QCProps.∈Post⇒∈PreOrBT (_≡ block ^∙ ebBlock ∙ bQuorumCert) bt bt“

module insertQuorumCertESpec
  (qc : QuorumCert) (bt0  : BlockTree) where
  open insertQuorumCertE qc bt0

  Ok : Set
  Ok = ∃₂ λ bt1 il → insertQuorumCertE qc bt0 ≡ Right (bt1 , il)

  private
    Ok' : BlockTree → List InfoLog → Either ErrLog (BlockTree × List InfoLog) → Set
    Ok' bt il m = m ≡ Right (bt , il)

  record ContractOk (btPre btPost : BlockTree) (ilPre ilPost : List InfoLog) : Set where
    constructor mkContractOk
    field
      noNewQCs : ∈Post⇒∈PreOrBT (_≡ qc) btPre btPost

  ContractOk-trans : ∀ {btPre btInt btPost ilPre ilInt ilPost}
                   → ContractOk btPre btInt  ilPre ilInt
                   → ContractOk btInt btPost ilInt ilPost
                   → ContractOk btPre btPost ilPre ilPost
  ContractOk-trans (mkContractOk noNewQCs) (mkContractOk noNewQCs₁) =
                    mkContractOk (∈Post⇒∈PreOr'-trans _∈BlockTree_ (_≡ qc) noNewQCs noNewQCs₁)

  Contract : EitherD-Post ErrLog (BlockTree × List InfoLog)
  Contract (Left _) = ⊤
  Contract (Right (bt1 , il)) = ContractOk bt0 bt1 [] il

  contract' : EitherD-weakestPre step₀ Contract
  contract'
     with safetyInvariant
  ...| Left e     = tt
  ...| Right unit = contract-step₁'
    where
    contract-step₁' : EitherD-weakestPre (step₁ blockId) Contract
    proj₁ contract-step₁' _ = tt
    proj₂ contract-step₁' block _ = contract-step₂'
      where
      contract-step₂' : EitherD-weakestPre (step₂ blockId block) Contract
      proj₁ contract-step₂' _ = tt
      proj₂ contract-step₂' hcb _ =
        contract-step₃'
        where
        contract-cont2' : ∀ (bt : BlockTree) (info : List InfoLog)
                         → let (bt' , info') = continue2 bt info
                           in ContractOk bt bt' info info'
        contract-cont2' bt info
           with (bt ^∙ btHighestCommitCert ∙ qcCommitInfo ∙ biRound) <? (qc ^∙ qcCommitInfo ∙ biRound)
        ...| yes hqcR<qcR = mkContractOk (∈BlockTree-upd-hcc refl refl)
        ...| no  hqcR≥qcR = mkContractOk (λ _ x → inj₁ x)

        cont1-update-bt : BlockTree → BlockTree
        cont1-update-bt bt = bt & btIdToQuorumCert ∙~ Map.insert blockId qc (bt ^∙ btIdToQuorumCert)

        info' : List InfoLog → Bool → List InfoLog
        info' il b = (fakeInfo ∷ il) ++ (if b then (fakeInfo ∷ []) else [])

        contract-cont1' : ∀ (btPre : BlockTree) (infoPre : List InfoLog)
                        → let (btPost , infoPost) = continue1 btPre blockId block infoPre
                          in  ContractOk btPre btPost infoPre infoPost
        contract-cont1' btPre infoPre
           with Map.kvm-member blockId (btPre ^∙ btIdToQuorumCert)
        ...| true  = mkContractOk (ContractOk.noNewQCs (contract-cont2' btPre (info' infoPre $ ExecutedBlock.isNilBlock block )))
        ...| false = ContractOk-trans {btInt = cont1-update-bt btPre} {ilInt = info' infoPre $ ExecutedBlock.isNilBlock block }
                               (mkContractOk (∈Post⇒∈PreOrBT-QCs≡ _ refl refl))
                               (mkContractOk (ContractOk.noNewQCs (contract-cont2'
                                                                     (cont1-update-bt btPre)
                                                                     (info' infoPre $ ExecutedBlock.isNilBlock block))))

        bt' = bt0 & btHighestCertifiedBlockId ∙~ block ^∙ ebId
                  & btHighestQuorumCert       ∙~ qc

        contract-step₃' : EitherD-weakestPre (step₃ blockId block hcb) Contract
        proj₁ contract-step₃' _ = ContractOk-trans
                                    (mkContractOk (∈BlockTree-upd-hqc refl refl))
                                    (contract-cont1' bt' (fakeInfo ∷ []))
        proj₂ contract-step₃' _ = ContractOk-trans
                                    (mkContractOk (∈Post⇒∈PreOr'-refl _∈BlockTree_ _))
                                    (contract-cont1' bt0 [])
