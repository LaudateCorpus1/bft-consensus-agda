{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.ConsensusTypes.BlockData where

newProposal : TX → Author → Round → {-Instant →-} QuorumCert → BlockData
newProposal payload author round {-timestamp-} quorumCert = BlockData∙new
  (quorumCert ^∙ qcCertifiedBlock ∙ biEpoch) round {-timestamp-} quorumCert (Proposal payload author)

isGenesisBlock : BlockData → Bool
isGenesisBlock bd = bd ^∙ bdBlockType == Genesis

isNilBlock : BlockData → Bool
isNilBlock bd = bd ^∙ bdBlockType == NilBlock
