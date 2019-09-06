{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.EpochConfig
open import LibraBFT.Concrete.Util.HashMap

module LibraBFT.Concrete.RecordStoreState
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  -- VCM: We'll be having the mutable bit of the record store state 
  --      separate from the immutable one.
  record RecordStoreStateMut (authors : Set) : Set where
    constructor mkRecordStoreState
    field
      -- rssInitiaState       : State
      rssBlocks               : HashMap BlockHash Block
      rssQCs                  : HashMap QCHash QC
      rssRoundToQChash        : HashMap Round QCHash
      rssCurrentProposedBlock : Maybe BlockHash
      rssHighestQCRound       : Round
      -- rssHighestTCRound    : Round
      rssCurrentRound         : Round
      -- rssHighest2ChainRound       : Round
      -- rssHighestCommittedRound    : Round
      -- rssHighestTimoutCertificate : Maybe (List Timeout)
      -- rssCurrentTimeouts      : HashMap authors Timeout
      rssCurrentVotes         : HashMap authors Vote
      -- rssCurrentTimeoutWeight     : ℕ  -- LIBRA-DIFF: assume equal weights for now
      -- rssCurrentElection          : ?

  record RecordStoreState : Set where
    constructor mkRecordStoreState
    field
      rssEpochId              : EpochId
      rssConfig               : EpochConfig
      -- VCM: think about initial later
      -- rssInitial              : Initial  -- LIBRA-DIFF, we store the Initial structure;
      --                                    -- Libra say QuorumCertificateHash, but it's not really one.
      rssMutablePart          : RecordStoreStateMut (Author rssConfig)
  open RecordStoreState public



  module _ (rss : RecordStoreState) where

   import LibraBFT.Abstract.Records          (ecAbstract (rssConfig rss)) 
     as AbstractR
   import LibraBFT.Abstract.RecordStoreState (ecAbstract (rssConfig rss)) hash hash-cr 
     as AbstractRSS
   
   -- The abstract interface to RecordStoreState is
   -- to look at it from a 'Pool of Records' point of view.
   -- 
   -- Calling 'AbstractRSS rss' gives us the abstract interpretation 
   -- of a record store state and enables us to instantiate
   -- the invariants.
   abstractRSS : AbstractRSS.isRecordStoreState 
                   (RecordStoreStateMut (Author (rssConfig rss)))
   abstractRSS = AbstractRSS.rss (_∈Mut (rssMutablePart rss)) 
                              ∈Mut-irrelevant
     where
       postulate _∈Mut_ : AbstractR.Record 
                        → RecordStoreStateMut (Author (rssConfig rss)) 
                        → Set

       postulate ∈Mut-irrelevant : ∀{r}(p₀ p₁ : r ∈Mut (rssMutablePart rss))
                                 → p₀ ≡ p₁
                

  emptyRSS : EpochId → EpochConfig → RecordStoreState
  emptyRSS eid ecfg = record {
      rssEpochId              = eid
    ; rssConfig               = ecfg
    ; rssMutablePart = record {
     -- ; rssInitial              = init
       -- rssInitiaState   : State
       rssBlocks               = emptyHM
     ; rssQCs                  = emptyHM
     ; rssRoundToQChash        = proj₁ (emptyHM [ 0 := just (ecInitialState ecfg) , _≟ℕ_ ])
     ; rssCurrentProposedBlock = nothing
     ; rssHighestQCRound       = 0
       -- rssHighestTCRound    = 0
     ; rssCurrentRound         = 1
       -- rssHighest2ChainRound   : Round
       -- rssHighestCommittedRound : Round
       -- rssHighestTimoutCertificate : Maybe (List Timeout)
     -- ; rssCurrentTimeouts      = emptyHM
     ; rssCurrentVotes         = emptyHM
       -- rssCurrentTimeoutWeight : ℕ  -- LIBRA-DIFF: assume equal weights for now
       -- rssCurrentElection : ?
    }}

  module _ (rss : RecordStoreState) where

    import LibraBFT.Abstract.Records          
      (ecAbstract (rssConfig rss))              as AbstractR

    import LibraBFT.Abstract.RecordStoreState 
      (ecAbstract (rssConfig rss)) hash hash-cr as AbstractRSS

    import LibraBFT.Abstract.RecordStoreState.Invariants
      (ecAbstract (rssConfig rss)) hash hash-cr as AbstractI

    ValidRSS : Set₁
    ValidRSS = AbstractI.Correct (abstractRSS rss)

    NoIncreasingRoundBroke : Set₁
    NoIncreasingRoundBroke = AbstractI.IncreasingRoundRule (abstractRSS rss)

    -- ... same for the others
    


  -- Now we can prove things about the empty state; for example,
  -- that is is valid. That is, for all records there exists a record chain
  -- that ends with it.
  -- 
  -- Once its all said and done, this proof should be trivial for there
  -- are no records in the pool of the empty state.
  emptyRSS-is-valid : (eid : EpochId)(ecfg : EpochConfig) 
                    → ValidRSS (emptyRSS eid ecfg)
  emptyRSS-is-valid eid ecfg {r} r∈pool = {!!} 
                                               
