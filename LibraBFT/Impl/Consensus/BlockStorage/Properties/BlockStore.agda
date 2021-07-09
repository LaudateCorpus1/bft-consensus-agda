{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module executeAndInsertBlockESpec {𝓔 : EpochConfig} (bs : BlockStore 𝓔) (b : Block) where
  postulate
    ebBlock≡ : ∀ {bs' eb} → executeAndInsertBlockE bs b ≡ Right (bs' , eb) → eb ^∙ ebBlock ≡ b

module executeAndInsertBlockMSpec (b : Block) where
  -- NOTE: This function returns any errors, rather than producing them as output.
  contract
    : ∀ pre Post
      → (∀ e → Left e ≡ executeAndInsertBlockE (rmGetBlockStore pre) b → Post (Left e) pre [])
      → (∀ bs' eb → Right (bs' , eb) ≡ executeAndInsertBlockE (rmGetBlockStore pre) b
         → Post (Right eb) (rmSetBlockStore pre bs') [])
      → LBFT-weakestPre (executeAndInsertBlockM b) Post pre
  proj₁ (contract pre Post pfBail pfOk ._ refl) e eaibLeft = pfBail e (sym eaibLeft)
  proj₂ (contract pre Post pfBail pfOk ._ refl) (bs' , eb) eaibRight ._ refl =
    pfOk bs' eb (sym eaibRight)

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new   (rmGetBlockStore pre ^∙ bsHighestQuorumCert _)
                 $ (rmGetBlockStore pre ^∙ bsHighestCommitCert _)

  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf ._ refl .unit refl .unit refl = pf
