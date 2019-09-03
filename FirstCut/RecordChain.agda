open import Hash
open import BasicTypes
open import Prelude

open import Data.Nat.Properties

module RecordChain {f : ℕ} (ec : EpochConfig f)
  -- A Hash function maps a bytestring into a hash.
  (hash    : ByteString → Hash)
  -- And is colission resistant
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open WithCryptoHash hash hash-cr
  open import Records ec

  -- We need to encode records into bytestrings in order to hash them.
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
    -- B←V : {b : Block} {v : Vote}
    --       → HashR (B b) ≡ vBlockHash v
    --       → B b ← V v

  -- A record chain is a slice of the reflexive transitive closure with
  -- valid records only. Validity, in turn, is defined by recursion on the
  -- chain.
  mutual
    -- One way of looking at a 'RecordChain r' is to think of it as 
    -- one path from the epoch's initial record to r.
    data RecordChain : Record → Set₁ where
      empty : ∀ {hᵢ} → RecordChain (I hᵢ)
      step  : ∀ {r r'} → (rc : RecordChain r) → r ← r' → Valid rc r' → RecordChain r'

    data Valid : ∀ {r} → RecordChain r → Record → Set₁ where
      ValidBlockInit : {b : Block} {hᵢ : Initial} → 1 ≤ bRound b → Valid (empty {hᵢ}) (B b)
      ValidBlockStep : {b : Block} {q : QC}
                     → (rc : RecordChain (Q q))
                     → qRound q < bRound b
                     → Valid rc (B b)
      ValidQC        : {q : QC} {b : Block}
                     → (rc : RecordChain (B b))
                     → qRound q ≡ bRound b
                     → Valid rc (Q q)

  prevBlock : ∀{q} → RecordChain (Q q) → Block
  prevBlock (step {r = B b} _ (B←Q _) _) = b

  -- Defition of 'previous_round' as in Paper Section 5.5
  currRound : ∀{r} → RecordChain r → Round
  currRound empty = 0
  currRound (step {r = r} _ _ _) = round r

  prevRound : ∀{r} → RecordChain r → Round
  prevRound empty = 0
  prevRound (step rc _ _) = currRound rc

  -- A k-chain (paper Section 5.2) is a sequence of
  -- blocks and quorum certificates for said blocks:
  --
  --  B₀ ← C₀ ← B₁ ← C₁ ← ⋯ ← Bₖ ← Cₖ
  --
  -- Our datatype 𝕂-chain captures exactly that structure.
  --
  data 𝕂-chain : (k : ℕ){r : Record} → RecordChain r → Set₁ where
    0-chain : ∀{r}{rc : RecordChain r} → 𝕂-chain 0 rc
    s-chain : ∀{k r}{rc : RecordChain r}{b : Block}{q : QC}
            → (r←b : r   ← B b)
            → (vb  : Valid rc (B b))
            → (b←q : B b ← Q q)
            → (vq  : Valid (step rc r←b vb) (Q q))
            → 𝕂-chain k rc
            → 𝕂-chain (suc k) (step (step rc r←b vb) b←q vq)

  -- Returns the round of the block heading the k-chain.
  kchainHeadRound : ∀{k r}{rc : RecordChain r} → 𝕂-chain k rc → Round
  kchainHeadRound (0-chain {r = r})          = round r
  kchainHeadRound (s-chain r←b vb b←q vq kk) = kchainHeadRound kk

  -- States that a given record belongs in a record chain.
  data _∈RC_ (r₀ : Record) : ∀{r₁} → RecordChain r₁ → Set where
    here   : ∀{rc : RecordChain r₀} → r₀ ∈RC rc
    there  : ∀{r₁ r₂}{rc : RecordChain r₁}(p : r₁ ← r₂)(pv : Valid rc r₂)
           → r₀ ∈RC rc
           → r₀ ∈RC (step rc p pv)

  -- This is the reflexive-transitive closure of _←_, as defined in 
  -- section 4.7 in the paper. Note it is different than the previous
  -- definition in the code. We must consider the 'reflexive' aspect as
  -- we can see in the paper's proof of S4.
  data _←⋆_ (r₁ : Record) : Record → Set₁ where
    ssRefl : r₁ ←⋆ r₁
    ssStep : ∀ {r r₂ : Record} → (r₁ ←⋆ r) → (r ← r₂) → r₁ ←⋆ r₂

  ------------------------
  -- Lemma 1

  InitialIrrel : (i j : Initial) → i ≡ j
  InitialIrrel mkInitial mkInitial = refl

  -- LemmaS1-1 states that a record that has been flagged as 'valid' (paper section 4.2)
  -- depends upon the initial record.
  lemmaS1-1 : {i : Initial}{r : Record}
            → RecordChain r
            → (I i) ←⋆ r
  lemmaS1-1 {i} {i₀} (empty {hᵢ}) rewrite InitialIrrel i hᵢ = ssRefl
  lemmaS1-1 {i} {r} (step rc r'←r vR)
    with vR
  ... | ValidBlockInit x = ssStep (lemmaS1-1 rc) r'←r
  ... | ValidBlockStep rc x = ssStep (lemmaS1-1 rc) r'←r
  ... | ValidQC rc x = ssStep (lemmaS1-1 rc) r'←r


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
  -- lemmaS1-2 {b₀} {b₁} {v} (B←V b₀←v) (B←V b₁←v)
  --    with hash-cr (trans b₀←v (sym b₁←v))
  -- ... | inj₁ (b₀≢b₁ , hb₀←hb₁) = inj₁ ( (encodeR b₀ , encodeR b₁ ) , ( b₀≢b₁ , hb₀←hb₁ ) )
  -- ... | inj₂ b₀≡b₁             = inj₂ (encodeR-inj b₀≡b₁)


  -- Better name for our lemma
  ←-inj : ∀{r₀ r₁ r₂}
        → r₀ ← r₂ → r₁ ← r₂
        → HashBroke ⊎ (r₀ ≡ r₁)
  ←-inj = lemmaS1-2


  Valid-round-< : ∀{r₀ r₁}
            → (rc : RecordChain r₀)
            → Valid rc r₁
            → round r₀ ≤ round r₁
  Valid-round-< empty (ValidBlockInit x) = z≤n
  Valid-round-< rc (ValidBlockStep rc x) = <⇒≤ x
  Valid-round-< rc (ValidQC rc refl)     = ≤-refl


  ←⋆-round-< : ∀{r₀ r₁}
             → RecordChain r₁
             → r₀ ←⋆ r₁
             → HashBroke ⊎ (round r₀ ≤ round r₁)
  ←⋆-round-< empty ssRefl                   = inj₂ z≤n
  ←⋆-round-< (step path x x₁) ssRefl        = inj₂ ≤-refl
  ←⋆-round-< (step path x vr₁) (ssStep r x₂)
    with lemmaS1-2 x₂ x
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ refl
    with ←⋆-round-< path r
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ rec = inj₂ (≤-trans rec (Valid-round-< path vr₁))

  lemmaS1-3 : ∀{r₀ r₁ r₂}
            → RecordChain r₀
            → RecordChain r₁
            → r₀ ←⋆ r₂ → r₁ ←⋆ r₂
            → round r₀ < round r₁
            → HashBroke ⊎ r₀ ←⋆ r₁
  lemmaS1-3 rc₀ rc₁ ssRefl ssRefl rr₀<rr₁ = inj₂ ssRefl
  lemmaS1-3 rc₀ rc₁ ssRefl (ssStep r₁←⋆r r←r₀) rr₀<rr₁
    with ←⋆-round-< rc₀ (ssStep r₁←⋆r r←r₀)
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ r₁≤r₀ = contradiction r₁≤r₀ (<⇒≱ rr₀<rr₁)
  lemmaS1-3 rc₀ rc₁ (ssStep r₀←⋆r r←r₁) ssRefl rr₀<rr₁ = inj₂ (ssStep r₀←⋆r r←r₁)
  lemmaS1-3 rc₀ rc₁ (ssStep r₀←⋆r r←r₂) (ssStep r₁←⋆rₓ rₓ←r₂) rr₀<rr₁
    with ←-inj r←r₂ rₓ←r₂
  ... | inj₁ hb = inj₁ hb
  ... | inj₂ refl = lemmaS1-3 rc₀ rc₁ r₀←⋆r r₁←⋆rₓ rr₀<rr₁


  postulate
    increasing-round-rule
      : (ha : Author ec) → Honest {ec = ec} ha
      → ∀{q} (rc  : RecordChain (Q q))  (va  : ha ∈QC q)  -- ha has voted for q
      → ∀{q'}(rc' : RecordChain (Q q')) (va' : ha ∈QC q') -- ha has voted for q'
      → vOrder (∈QC-Vote {q} ha va) < vOrder (∈QC-Vote {q'} ha va')
      → qRound q < qRound q' 

    votes-only-once-rule
      : (ha : Author ec) → Honest {ec = ec} ha
      → ∀{q} (rc  : RecordChain (Q q))  (va  : ha ∈QC q)  -- ha has voted for q
      → ∀{q'}(rc' : RecordChain (Q q')) (va' : ha ∈QC q') -- ha has voted for q'
      → vOrder (∈QC-Vote {q} ha va) ≡ vOrder (∈QC-Vote {q'} ha va')
      → ∈QC-Vote {q} ha va ≡ ∈QC-Vote {q'} ha va'

  ----------------------
  -- Lemma 2

  B-inj : ∀{b₀ b₁} → B b₀ ≡ B b₁ → b₀ ≡ b₁
  B-inj refl = refl

  module Lemma2-WithBFT 
     (lemmaB1 : (q₁ : QC)(q₂ : QC) 
              → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a))
    where

   -- TODO: When we bring in the state everywhere; this will remain very similar.
   --       We will add another check for st₀ ≟State st₁ after checking the block
   --       equality in (***); Naturally, if blocks are equal so is the state.
   --       We will need some command-application-injective lemma.
   --
   --         1) when st₀ ≟State st₁ returns yes, we done.
   --         2) when it returns no, and the blocks are different, no problem.
   --         3) when it returns no and the blocks are equal, its impossible! HashBroke!
   lemmaS2 : {q₀ q₁ : QC}
           → (rc₀ : RecordChain (Q q₀)) 
           → (rc₁ : RecordChain (Q q₁)) 
           → bRound (prevBlock rc₀) ≡ bRound (prevBlock rc₁)
           → HashBroke ⊎ prevBlock rc₀ ≡ prevBlock rc₁ -- × qState q₀ ≡ qState q₁
   lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                     (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
     with b₀ ≟Block b₁ -- (***)
   ...| yes done = inj₂ done
   ...| no  imp  
     with lemmaB1 q₀ q₁
   ...|  (a , (a∈q₀ , a∈q₁ , honest)) 
     with <-cmp (vOrder (∈QC-Vote {q₀} a a∈q₀)) (vOrder (∈QC-Vote {q₁} a a∈q₁))
   ...| tri< va<va' _ _ 
     with increasing-round-rule a honest {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀ 
                                         {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁ 
                                         va<va'
   ...| res = ⊥-elim (<⇒≢ res hyp)
   lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                     (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest)) 
      | tri> _ _ va'<va 
     with increasing-round-rule a honest {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁  
                                         {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀  
                                         va'<va
   ...| res = ⊥-elim (<⇒≢ res (sym hyp))
   lemmaS2 {q₀} {q₁} (step {r = B b₀} rc₀ (B←Q h₀) (ValidQC .rc₀ refl)) 
                     (step {r = B b₁} rc₁ (B←Q h₁) (ValidQC .rc₁ refl)) hyp 
      | no imp
      |  (a , (a∈q₀ , a∈q₁ , honest)) 
      | tri≈ _ va≡va' _ 
     with votes-only-once-rule a honest {q₀} (step rc₀ (B←Q h₀) (ValidQC rc₀ refl)) a∈q₀  
                                        {q₁} (step rc₁ (B←Q h₁) (ValidQC rc₁ refl)) a∈q₁ 
                                        va≡va'
   ...| res = inj₁ ((encodeR (B b₀) , encodeR (B b₁)) , (imp ∘ B-inj ∘ encodeR-inj) 
                    , trans h₀ {!!}) -- extract from h₁, res and qVotes-C3!

-- ################
-- ## WE ARE HERE

-- Below is scratchpad

{-
  
  {- TODO: We could think of gathering evidence that a node
           knows about a record in a more expressive way.

  data KnowsOf (α : Author ec) : Record → Set where
    seenEvidence : ∀{q} → α ∈QC q → KnowsOf α (Q q)
    isInMyRecordStore : ∀{r} → ⊥ {- r is in my record store and I'm α -} 
                      → KnowsOf α r
  -}

  data KnowsOf (α : Author ec) : Record → Set where
    seenEvidence : ∀{q} → α ∈QC q → KnowsOf α (Q q)

  -- For the locked-round-rule (Sect 5.5), we observe its breakage
  -- in a more intricate fashion;
  --
  -- If there exists a two chain as follows, call it c2,
  --
  --   ⋯ ← B₀ ← Q₀ ← B₁ ← Q₁ 
  --
  -- Such that we seen evidence that α knowsOf Q₁,
  -- then, the following never happens as long as α is honest:
  --
  --   ⋯ ← B' ← Q' with α knowingOf Q' with prevRound B' < round B₀
  --
  -- That's because wince we know α knowsOf Q₁, it's locked_round is
  -- at least round B₀. Therefore, since α is honest, it would never vote
  -- for a node B' that extends something from before the 2-chain, after α
  -- has seen the 2-chain.
  data LockedRoundBroke (ha : Author ec) {r} {rc : RecordChain r} 
                        (c2 : 𝕂-chain 2 rc) (hyp : KnowsOf ha r) (b' : Block) 
      : Set₁ where
    lrh : {q' : QC}(rc' : RecordChain (B b'))
        → Valid rc' (Q q')
        → B b' ← Q q'
        → ha ∈QC q'
        → prevRound rc' < kchainHeadRound c2
        → LockedRoundBroke ha c2 hyp b'

  -- TODO: (FOR MARK) Eagles eye needed here!
  postulate
    locked-round-rule
      : (ha : Author ec) → Honest {ec = ec} ha
      → ∀{r}{rc : RecordChain r}(c2 : 𝕂-chain 2 rc)
      → (hyp : KnowsOf ha r)
      → {b' : Block} 
      → ¬ (LockedRoundBroke ha c2 hyp b')


  module Lemma3-WithBFT 
     (lemmaB1 : (q₁ : QC)(q₂ : QC) 
              → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a))
    where
  
   -- We just noted that when the paper mentions 'certified' or ' verified'
   -- block, we encode it as a 'RecordChain' ending in said block.   
   lemmaS3 : ∀{r}{rc : RecordChain r}
           → (c3 : 𝕂-chain 3 rc)
           → {b' : Block}{q' : QC}
           → (certB : RecordChain (B b'))
           → (b←q   : B b' ← Q q') → Valid certB (Q q')
           → round r < bRound b'
           → kchainHeadRound c3 ≤ prevRound certB 
   lemmaS3 {r} (s-chain {rc = rc} {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
     with lemmaB1 q₂ q'
   ...| (a , (a∈q₂ , a∈q' , honest)) 
     with bRound b₂ ≤?ℕ bRound b'
   ...| no imp 
     with increasing-round-rule a honest (step _ b₂←q₂ vq₂) a∈q₂ 
   ...| abs = ⊥-elim (abs (irh (step certB b←q' vq') a∈q' {!!} {!!}))
   lemmaS3 {r} (s-chain {b = b₂} {q₂} r←b₂ vb₂ b₂←q₂ vq₂ c2) {b'} {q'} certB b←q' vq' hyp 
      | (a , (a∈q₂ , a∈q' , honest)) 
      | yes prf = {!!}
-}
