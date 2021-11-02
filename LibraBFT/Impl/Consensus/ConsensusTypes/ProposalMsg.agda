{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block              as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.TimeoutCertificate as TimeoutCertificate
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                               using (String)

module LibraBFT.Impl.Consensus.ConsensusTypes.ProposalMsg where

verifyWellFormed : ProposalMsg → EitherD ErrLog Unit
verifyWellFormed self = do
  lcheckD (not (Block.isNilBlock (self ^∙ pmProposal)))
          (here' ("Proposal for a NIL block" ∷ []))
  withErrCtxD' ("Failed to verify ProposalMsg's block" ∷ [])
               (Block.verifyWellFormed (self ^∙ pmProposal))
  lcheckD (self ^∙ pmProposal ∙ bRound >? 0)
          (here' ("Proposal for has round <= 0" ∷ []))
  lcheckD (self ^∙ pmProposal ∙ bEpoch == self ^∙ pmSyncInfo ∙ siEpoch)
          (here' ("ProposalMsg has different epoch than SyncInfo" ∷ [])) -- lsSI (self ^∙ pmSyncInfo)

  lcheckD (self ^∙ pmProposal ∙ bParentId == self ^∙ pmSyncInfo ∙ siHighestQuorumCert ∙ qcCertifiedBlock ∙ biId)
          (here' ( "Proposal SyncInfo HQC CertifiedBlock id not eq to block parent id" ∷ []))
                -- lsSI (self ^∙ pmSyncInfo)
  let previousRound = self ^∙ pmProposal ∙ bRound ∸ 1 -- NOTE: monus usage
  let highestCertifiedRound =
        max (self ^∙ pmProposal ∙ bQuorumCert ∙ qcCertifiedBlock ∙ biRound)
            (maybeHsk 0 (_^∙ tcRound) (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert))
  lcheckD (previousRound == highestCertifiedRound)
          (here' ("Proposal does not have a certified round" ∷ []))
                -- lsMTC (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert)
  lcheckD (is-just (self ^∙ pmProposal ∙ bAuthor))
          (here' ("Proposal does not have an author" ∷ []))
  -- LBFT-DIFF : this check used to live in EventProcessor ∙ processProposedBlockM
  -- TODO: is it needed?
  -- Safety invariant: For any valid proposed block
  -- , its parent block == the block pointed to by its QC.
  lcheckD (self ^∙ pmProposal ∙ bParentId == self ^∙ pmProposal ∙ bQuorumCert ∙ qcCertifiedBlock ∙ biId)
          (here' ("parent id /= qcCB" ∷ [])) -- show (self ^∙ pmProposal)
 where
  here' : List String → List String
  here' t = "ProposalMsg" ∷ "verifyWellFormed" {-∷ lsPM self-} ∷ t


verify : ProposalMsg → ValidatorVerifier → EitherD ErrLog Unit
verify self validator = do
  Block.validateSignature    (self ^∙ pmProposal)                        validator
  TimeoutCertificate.verify' (self ^∙ pmSyncInfo ∙ siHighestTimeoutCert) validator
  verifyWellFormed self

