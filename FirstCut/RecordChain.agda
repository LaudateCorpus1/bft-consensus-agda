open import Hash
open import BasicTypes
open import Prelude

module RecordChain {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open WithCryptoHash hash hash-cr
  open import Records ec

  -- Hash Functions ----------------------------------------------
  postulate
    encodeR     : Record → ByteString
    encodeR-inj : ∀ {r₀ r₁ : Record} → (encodeR r₀ ≡ encodeR r₁) → (r₀ ≡ r₁)

  HashR : Record → Hash
  HashR = hash ∘ encodeR

  data _←_ : Record → Record → Set where
    I←B : {i : Initial} {b : Block}
          → HashR (I i) ≡  bPrevQCHash b
          → I i ← B b
    Q←B : {q : QC} {b : Block}
          → HashR (Q q) ≡  bPrevQCHash b
          → Q q ← B b
    B←Q : {b : Block} {q : QC}
          → HashR (B b) ≡ qBlockHash q
          → B b ← Q q
    B←V : {b : Block} {v : Vote}
          → HashR (B b) ≡ vBlockHash v
          → B b ← V v

  -- This is the reflexive-transitive closure of _←_, as defined in
  -- section 4.7 in the paper.
  data _←⋆_ (r₁ : Record) : Record → Set₁ where
    ssRefl : r₁ ←⋆ r₁
    ssStep : ∀ {r r₂ : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂

  -- A record chain is a slice of the reflexive transitive closure with
  -- valid records only. Validity, in turn, is defined by recursion on the
  -- chain.
  mutual
    data RecordChain : Record → Set₁ where
      empty : ∀ {hᵢ} → RecordChain (I hᵢ)
      step  : ∀ {r r'} → (rc : RecordChain r) → r ← r' → Valid rc r' → RecordChain r'

    data Valid : ∀ {r} → RecordChain r → Record → Set₁ where
      ValidBlockInit : {b : Block} {hᵢ : Initial} → 1 ≤ bRound b → Valid (empty {hᵢ}) (B b)
      ValidBlockStep : {b : Block} {q : QC}
                     → (rc : RecordChain (Q q))
                     → qRound q < bRound b
                     → Valid rc (B b)
      -- It's the leader that proposes the Block that sends the QC therefore we enforce it
      -- by asking just one author
      ValidQC        : {q : QC} {b : Block}
                     → (rc : RecordChain (B b))
                     → qRound q ≡ bRound b
                     → Valid rc (Q q)

  ------------------------
  -- Lemma 1

  -- LemmaS1-1 states that a record that has been flagged as 'valid' (paper section 4.2)
  -- depends upon the initial record.
  lemmaS1-1 : {i : Initial}{r : Record}
            → RecordChain r
            → (I i) ←⋆ r
  lemmaS1-1 = {!!}

  lemmaS1-2 : ∀{r₀ r₁ r₂}
            → r₀ ← r₂ → r₁ ← r₂
            → HashBroke ⊎ (r₀ ≡ r₁)
  lemmaS1-2 {i₀} {i₁} {b} (I←B i₀←b) (I←B i₁←b)
    with hash-cr (trans i₀←b (sym i₁←b))
  ... | inj₁ (i₀≢i₁ , hi₀≡hi₁) = inj₁ ( ( encodeR i₀ , encodeR i₁ ) , ( i₀≢i₁ , hi₀≡hi₁ ) )
  ... | inj₂ i₀≡i₁             = inj₂ (encodeR-inj i₀≡i₁)
  lemmaS1-2 {i} {q} {b} (I←B i←b) (Q←B q←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ i≡q               = contradiction (encodeR-inj i≡q) λ ()
  lemmaS1-2 {q} {i} {b} (Q←B q←b) (I←B i←b)
    with hash-cr (trans i←b (sym q←b))
  ... | inj₁ (i≢q , hi≡hq)     = inj₁ ( ( encodeR i , encodeR q ) , ( i≢q , hi≡hq ) )
  ... | inj₂ i≡q               = contradiction (encodeR-inj i≡q) λ ()
  lemmaS1-2 {q₀} {q₁} {b} (Q←B q₀←b) (Q←B q₁←b)
     with hash-cr (trans q₀←b (sym q₁←b))
  ... | inj₁ (q₀≢q₁ , hq₀≡hq₁) = inj₁ ( ( encodeR q₀ , encodeR q₁ ) , ( q₀≢q₁ , hq₀≡hq₁ ) )
  ... | inj₂ q₁≡q₂             = inj₂ (encodeR-inj q₁≡q₂)
  lemmaS1-2 {b₀} {b₁} {q} (B←Q b₀←q) (B←Q b₁←q)
     with hash-cr (trans b₀←q (sym b₁←q))
  ... | inj₁ (b₀≢b₁ , hb₀←hb₁) = inj₁ ( ( encodeR b₀ , encodeR b₁ ), ( b₀≢b₁ , hb₀←hb₁ ) )
  ... | inj₂ b₀≡b₁             = inj₂ (encodeR-inj b₀≡b₁)
  lemmaS1-2 {b₀} {b₁} {v} (B←V b₀←v) (B←V b₁←v)
     with hash-cr (trans b₀←v (sym b₁←v))
  ... | inj₁ (b₀≢b₁ , hb₀←hb₁) = inj₁ ( (encodeR b₀ , encodeR b₁ ) , ( b₀≢b₁ , hb₀←hb₁ ) )
  ... | inj₂ b₀≡b₁             = inj₂ (encodeR-inj b₀≡b₁)


  -- Better name for our lemma
  ←-inj : ∀{r₀ r₁ r₂}
        → r₀ ← r₂ → r₁ ← r₂
        → HashBroke ⊎ (r₀ ≡ r₁)
  ←-inj = lemmaS1-2

  lemmaS1-3 : ∀{r₀ r₁ r₂}
            → r₀ ←⋆ r₂ → r₁ ←⋆ r₂
            → round r₀ < round r₁
            → r₀ ←⋆ r₂
  lemmaS1-3 = {!!}

  ----------------------
  -- Lemma 2

  module Lemma2-WithBFT 
     (lemmaB1 : (q₁ : QC)(q₂ : QC) 
              → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a))
    where

   postulate
    increasing-round 
      : (ha : Author ec) → Honest {ec = ec} ha
      → {b₀ : Block}{q₀ : QC}
      → {b₁ : Block}{q₁ : QC}
      → ha ∈QC q₀ → (B b₀ ← Q q₀) -- a voted for q₀, which extends b₀
      → ha ∈QC q₁ → (B b₁ ← Q q₁) -- a voted for q₁, which extends b₁
      → q₀ ≢ q₁
      → bRound b₀ ≢ bRound b₁

   lemmaS2 : {b₀ : Block}{q₀ : QC}
           → {b₁ : Block}{q₁ : QC}
           → {rc₀ : RecordChain (B b₀)} → Valid rc₀ (Q q₀)
           → {rc₁ : RecordChain (B b₁)} → Valid rc₁ (Q q₁)
           → (B b₀) ← (Q q₀)
           → (B b₁) ← (Q q₁)
           → bRound b₀ ≡ bRound b₁
           → HashBroke ⊎ b₀ ≡ b₁ -- × qState q₀ ≡ qState q₁
   lemmaS2 {q₀ = q₀} {q₁ = q₁} (ValidQC rc0 p0) (ValidQC rc1 p1) b0q0 b1q1 rnd 
     with q₀ ≟QC q₁
   ...| yes refl with lemmaS1-2 b0q0 b1q1 
   ...| inj₁ hb   = inj₁ hb
   ...| inj₂ refl = inj₂ refl
   lemmaS2 {q₀ = q₀} {q₁ = q₁} (ValidQC rc0 p0) (ValidQC rc1 p1) b0q0 b1q1 rnd 
      | no  imp
     with lemmaB1 q₀ q₁
   ...|  (a , (a∈q₀ , a∈q₁ , honest)) 
     with increasing-round a honest a∈q₀ b0q0 a∈q₁ b1q1 imp
   ...| r = ⊥-elim (r rnd)
