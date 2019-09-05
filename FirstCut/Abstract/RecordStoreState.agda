open import Hash
open import BasicTypes
open import Prelude

open import Data.Nat.Properties

module Abstract.RecordStoreState {f : ℕ} (ec : EpochConfig f) 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open WithCryptoHash                 hash hash-cr
  open import Abstract.Records     ec hash hash-cr
  open import Abstract.RecordChain ec hash hash-cr
  
  -- VCM: There's a TRAP!
  --
  -- We must be sure to never add repeated records to our record store. 
  -- Note that, as is, these postulates allows me to prove bottom.
  -- That's because we are using a 'List' as the recordStoreState intead
  -- of an abstract interface.
  -- 
  postulate _∈_          : ∀{a}{A : Set a} → A → List A → Set
  postulate ∈-irrelevant : ∀{a}{A : Set a}{x : A}{l : List A}(p₀ p₁ : x ∈ l) → p₀ ≡ p₁ 

  -- TODO: Abstract away from lists and let the implemnter choose!
  record RecordStoreState : Set₁ where
    constructor rss
    field
      pool       : List Record
      correct    : (r : Record) → r ∈ pool → WithPool.RecordChain (_∈ pool) ∈-irrelevant r
  open RecordStoreState public

  -- Now, we need to state the invariants over the system that we seek to:
  --
  --  1) Guarantee when implementing the algo
  --  2) Use on the proofs
  --
  module Invariants (curr : RecordStoreState) where

    open WithPool (_∈ pool curr) ∈-irrelevant

    -- The increasing round rule says that a current RecordStoreState
    -- that contains two votes from α is guaranteed to have the order of
    -- votes respect the rounds
    IncreasingRoundRule : Set₁
    IncreasingRoundRule 
       = (α : Author ec) → Honest {ec = ec} α
       → ∀{q q'}(va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → vOrder (∈QC-Vote {q} α va) < vOrder (∈QC-Vote {q'} α va')
       → qRound q < qRound q' 

    -- Another important predicate of a "valid" RecordStoreState is the fact
    -- that α's n-th vote is always the same.
    VotesOnlyOnceRule : Set₁
    VotesOnlyOnceRule 
       = (α : Author ec) → Honest {ec = ec} α
       → ∀{q q'}(va  : α ∈QC q)(va' : α ∈QC q') -- α has voted for q and q'
       → vOrder (∈QC-Vote {q} α va) ≡ vOrder (∈QC-Vote {q'} α va')
       → ∈QC-Vote {q} α va ≡ ∈QC-Vote {q'} α va'

    -- TODO: change parameters to ∈QC-Vote; author can be implicit; QC has to be explicit.
    -- TOEXPLAIN: prevRound is defined for blocks only on the paper; however,
    --            it is cumbersome to open rc' to expose the block that comes
    --            before (Q q'). Yet, (Q q') is valid so said block has the same round,
    --            so, the prevRound (Q q') is the prevRound of the block preceding (Q q').
    LockedRoundRule : Set₁
    LockedRoundRule 
      = (α : Author ec) → Honest {ec = ec} α
      → ∀{q}{rc : RecordChain (Q q)}{n : ℕ}(c2 : 𝕂-chain (2 + n) rc)
      → (vα : α ∈QC q) -- α knows of the 2-chain because it voted on the tail.
      → ∀{q'}(rc' : RecordChain (Q q'))
      → (vα' : α ∈QC q')
      → vOrder (∈QC-Vote {q} _ vα) < vOrder (∈QC-Vote {q'} _ vα')
      → bRound (kchainBlock (suc zero) c2) ≤ prevRound rc'
