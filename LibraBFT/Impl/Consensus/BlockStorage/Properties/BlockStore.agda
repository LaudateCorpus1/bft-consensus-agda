{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Prelude
open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms
open import Optics.All

open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module executeAndInsertBlockESpec (bs : BlockStore) (b : Block) where
  postulate -- TODO-2: prove
    -- More properties are likely going to required in the future, as well.
    ebBlock≡ : ∀ {bs' eb} → executeAndInsertBlockE bs b ≡ Right (bs' , eb) → eb ^∙ ebBlock ≡ b
    bs'BlockInv
      : ∀ {bs' eb pre}
        → executeAndInsertBlockE bs b ≡ Right (bs' , eb)
        → bs ≡ pre ^∙ lBlockStore
        → Preserves BlockStoreInv pre (pre & lBlockStore ∙~ bs')

module executeAndInsertBlockMSpec (b : Block) where
  -- NOTE: This function returns any errors, rather than producing them as output.
  contract
    : ∀ pre Post
      → (∀ e → Left e ≡ executeAndInsertBlockE (pre ^∙ lBlockStore) b → Post (Left e) pre [])
      → (∀ bs' eb → Right (bs' , eb) ≡ executeAndInsertBlockE (pre ^∙ lBlockStore) b
         → Post (Right eb) (pre & lBlockStore ∙~ bs') [])
      → LBFT-weakestPre (executeAndInsertBlockM b) Post pre
  proj₁ (contract pre Post pfBail pfOk ._ refl) e eaibLeft = pfBail e (sym eaibLeft)
  proj₂ (contract pre Post pfBail pfOk ._ refl) (bs' , eb) eaibRight ._ refl ._ refl =
    pfOk bs' eb (sym eaibRight)

module insertSingleQuorumCertMSpec
  (qc : QuorumCert) where

  module _ (pool : SentMessages) (pre : RoundManager) where

    record Contract (r : Either ErrLog Unit) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        -- General invariants / properties
        rmInv         : Preserves RoundManagerInv pre post
        noEpochChange : NoEpochChange pre post
        noMsgOuts     : OutputProps.NoMsgs outs
        -- Voting
        noVote        : VoteNotGenerated pre post true
        -- Signatures
        qcSigsB4 : QCProps.QCRequirements pool qc
                   → Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre post


    postulate -- TODO-2: prove
      contract' : LBFT-weakestPre (insertSingleQuorumCertM qc) Contract pre

    contract : ∀ Q → RWST-Post-⇒ Contract Q → LBFT-weakestPre (insertSingleQuorumCertM qc) Q pre
    contract Q pf = LBFT-⇒ Contract Q pf (insertSingleQuorumCertM qc) pre contract'

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new (pre ^∙ lBlockStore ∙ bsHighestQuorumCert)
                 (pre ^∙ lBlockStore ∙ bsHighestCommitCert)
                 (pre ^∙ lBlockStore ∙ bsHighestTimeoutCert)

  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf ._ refl ._ refl ._ refl ._ refl ._ refl ._ refl = pf
