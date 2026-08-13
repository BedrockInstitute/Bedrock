{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.52] probe B: THE GRAPH AGREEMENT, DECOMPOSED AND ASSEMBLED.
--
-- The class-carrier half of piece 2: graphBndAt implies the machine
-- LsetGraphAt at the same env.  The decomposition is:
--   StepAgree    -- the bounded step implies the machine step
--   ApproxAgree  -- the bounded approximation implies the machine one
--   SiteFacts    -- the LEG D site facts bundle
-- The assembly from StepAgree + ApproxAgree + SiteFacts is proved
-- here; StepAgree and ApproxAgree are hypotheses.  With Probe A's
-- decode, the chain graphBndAt -> LsetGraphAt -> ride-only ->
-- "w = Lset gamma" is fully pinned at the class carrier.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ152B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Sequence {ℓ} lem
  using ( LsetGraphAt; LsetGraph-in; StepAt; ApproxAt )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The site facts of the twelve-row agreement at the graph env: the
-- tag slots hold the numerals, the recorded values lie in K, the
-- satisfiers lie in K.  One opaque bundle for this probe.
module _ (SF : (h x w v γ K : S) → Type (ℓ-suc ℓ)) where
  
  -- The bounded step implies the machine step at the graph env.
  -- S.stepBndAt at [h x w v γ K] says "w = the step of h at γ".
  -- The machine StepAt (suc (suc zero)) (suc (suc (suc (suc zero)))) zero at the
  -- same env says the same thing.
  StepAgree : Type (ℓ-suc ℓ)
  StepAgree = (h x w v γ K : S) (sf : SF h x w v γ K)
            → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.LH.G.S.stepBndAt ⟩
            → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                 StepAt (suc (suc zero)) (suc (suc (suc (suc zero)))) zero ⟩
  
  -- The bounded approximation implies the machine approximation.
  ApproxAgree : Type (ℓ-suc ℓ)
  ApproxAgree = (h x w v γ K : S) (sf : SF h x w v γ K)
              → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.LH.G.A.approxBndAt ⟩
              → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                   ApproxAt zero (suc (suc (suc (suc zero)))) ⟩
  
  -- The assembly: the bounded graph implies the machine graph.
  -- The graph's satisfaction unpacks to h ∈ γ with the approximation
  -- and the step at the extended env; the agreements hand back the
  -- machine pieces; LsetGraph-in packages them.
  graph-assembly : (step : StepAgree) (approx : ApproxAgree)
                 → (x w v γ K : S) (sf : (h' : S) → SF h' x w v γ K)
                 → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.LH.G.graphBndAt ⟩
                 → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                      LsetGraphAt {5} (suc zero) (suc (suc (suc zero))) ⟩
  graph-assembly step approx x w v γ K sf h =
    PT.rec squash₁ go h
    where
    go : Σ[ h' ∈ S ]
           (⟨ h' ∈ˢ γ ⟩
          × ⟨ (h' ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
               (LH0.LH.G.A.approxBndAt ∧̇ LH0.LH.G.S.stepBndAt) ⟩)
       → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
            LsetGraphAt {5} (suc zero) (suc (suc (suc zero))) ⟩
    go (h' , h∈γ , hahs) =
      LsetGraph-in {5} (suc zero) (suc (suc (suc zero)))
        (x ∷ w ∷ v ∷ γ ∷ K ∷ []) h'
        (approx h' x w v γ K (sf h') (fst hahs))
        (step h' x w v γ K (sf h') (snd hahs))
  