{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

-- Here we establish the properties necessary to achieve consensus
-- just like we see them on paper: stating facts about the state of
-- the system and reasoning about which QC's exist in the system.
-- This module is a stepping stone to the properties we want;
-- you should probably not be importing it directly, see 'LibraBFT.Abstract.Properties'
-- instead.
--
-- The module 'LibraBFT.Abstract.Properties' proves that the invariants
-- presented here can be obtained from reasoning about sent votes,
-- which provides a much easier-to-prove interface to an implementation.
module LibraBFT.Abstract.RecordChain.Invariants
    (𝓔      : EpochConfig)(valid : ValidEpoch 𝓔)
    (UID    : Set)
    (_≟UID_ : (u₀ u₁ : UID) → Dec (u₀ ≡ u₁))
    (𝓥      : VoteEvidence 𝓔 UID)
  where

  open import LibraBFT.Abstract.System           𝓔 UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.Records          𝓔 UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.Records.Extends  𝓔 UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.BFT              𝓔 valid UID _≟UID_ 𝓥
  open import LibraBFT.Abstract.RecordChain      𝓔 UID _≟UID_ 𝓥

  open EpochConfig 𝓔

  module _ {ℓ}(𝓢 : AbsSystemState ℓ) where
   open AbsSystemState 𝓢

   -- Another important predicate of a "valid" RecordStoreState is the fact
   -- that α's n-th vote is always the same.
   VotesOnlyOnceRule : Set ℓ
   VotesOnlyOnceRule
      -- Given an honest α
      = (α : Member) → (hpk : Meta-Honest-Member 𝓔 α)
      -- For all system states where q and q' exist,
      → ∀{q q'} → (q∈𝓢 : InSys (Q q)) → (q'∈𝓢 : InSys (Q q'))
      -- such that α voted for q and q'; if α says it's the same vote, then it's the same vote.
      → (va  : α ∈QC q)(va' : α ∈QC q')
      → abs-vRound (∈QC-Vote q va) ≡ abs-vRound (∈QC-Vote q' va')
      -----------------
      → ∈QC-Vote q va ≡ ∈QC-Vote q' va'


  module _ {ℓ}(𝓢 : AbsSystemState ℓ) where
   open AbsSystemState 𝓢

   -- The locked-round-rule, or preferred-round rule (from V3 onwards) is a critical
   -- aspect of LibraBFT's correctness. It states that an honest node α will cast
   -- votes for blocks b only if prevRound(b) ≥ locked_round(α), where locked_round(α)
   -- is defined as $max { round b | b is the head of a 2-chain }$.
   --
   -- Operationally, α can ensure it obeys this rule as follows: it keeps a counter
   -- locked_round, initialized at 0 and, whenever α receives a QC q that forms a
   -- 2-chain:
   --
   --  Fig1
   --
   --    I ← ⋯ ← b₁ ← q₁ ← b ← q
   --        ⌞₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋₋⌟
   --                2-chain
   --
   -- it checks whether round(b₁) , which is the head of the 2-chain above,
   -- is greater than its previously known locked_round; if so, α updates
   -- it.  Note that α doesn't need to cast a vote in q, above, to have its
   -- locked_round updated.  All that matters is that α has seen q.
   --
   -- We are encoding the rules governing Libra nodes as invariants in the
   -- state of other nodes. Hence, the LockedRoundRule below states an invariant
   -- on the state of β, if α respects the locked-round-rule.
   --
   -- Let the state of β be as below, such that α did cast votes for q
   -- and q' in that order (α is honest here!):
   --
   --
   --  Fig2
   --                            3-chain
   --        ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
   --        |        2-chain            |          α knows of the 2-chain because
   --        ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝        |          it voted at the 3-chain.
   --    I ← ⋯ ← b₂ ← q₂ ← b₁ ← q₁ ← b ← q
   --         ↖
   --           ⋯ ← b₁' ← q₁' ← b' ← q'
   --
   -- Then, since α is honest and follows the locked-round rule, we know that
   -- round(b₂) ≤ round(b₁') because, by seeing that α voted on q, we know that α
   -- has seen the 2-chain above, hence, α's locked_round was at least round(b₂) at
   -- the time α cast its vote for b.
   --
   -- After casting a vote for b, α cast a vote for b', which means that α must have
   -- checked that round(b₂) ≤ prevRound(b'), as stated by the locked round rule.
   --
   -- The invariant below states that, since α is honest, we can trust that these
   -- checks have been performed and we can infer this information solely
   -- by seeing α has knowledge of the 2-chain in Fig2 above.
   --
   LockedRoundRule : Set (ℓ+1 ℓ0 ℓ⊔ ℓ)
   LockedRoundRule
     = ∀{R}(α : Member)(hpk : Meta-Honest-Member 𝓔 α)
     → ∀{q q'}(q∈𝓢 : InSys (Q q))(q'∈𝓢 : InSys (Q q'))
     → {rc : RecordChain (Q q)}{n : ℕ}(c3 : 𝕂-chain R (3 + n) rc)
     → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail of the 3-chain!
     → (rc' : RecordChain (Q q'))
     → (vα' : α ∈QC q')
     → abs-vRound (∈QC-Vote q vα) < abs-vRound (∈QC-Vote q' vα')
     → NonInjective-≡ bId ⊎ (getRound (kchainBlock (suc (suc zero)) c3) ≤ prevRound rc')
