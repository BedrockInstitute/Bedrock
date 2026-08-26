{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.673] PROBE.  The hull-membership of the bound at
-- [LJ-1.667]'s matrix₃.  Lands nothing in src/.  This is NOT a
-- second formula: inBound is matrix₃ with the value slot and the
-- parameter slot pinned to hull codes, the shape [LJ-1.651]'s inF
-- used (Probe651.agda:149-150).
--
--   W3              Formula Code 1 from matrix₃, then hull-closed
--                   at that formula.  No new matrix.
--   THE OBLIGATION  lset-grounded.  Not lifted until the term
--                   inhabits LsetGrounded at matrix₃.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-673.Probe673 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667

open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- W3.  THE FORMULA hull-closed TAKES, FROM matrix₃, NOT A SECOND
-- MATRIX.  countFo matrix₃ is 0, so mapFo never reads the slide
-- (same dummy-slide as Probe651.agda:125-142).  Pinning uses ≐ con,
-- the inF pattern, because CloseSyntax.close demands
-- K : Type (ℓ-suc ℓ) and Code is Type ℓ (measured at
-- agents/tasks/LJ-1-664/runs/close-1.out:5-7).
-- =====================================================================

count-matrix₃ : countFo P667.matrix₃ ≡ 0
count-matrix₃ = refl

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ
  module I = F.Instances elem

  M : S
  M = F.HS.M

  open F.HS.H.T using ( Code; val )
  open F.HS.H using ( hull-closed; hull-member )

  slide : ⊥* {ℓ-suc ℓ} → Code
  slide b = Empty.rec* b

  -- matrix₃ over the hull's alphabet.  Not a new formula.
  matrix₃-Code : Formula Code 3
  matrix₃-Code = mapFo slide P667.matrix₃

  -- Slot order of matrix₃ is value, parameter, witness
  -- (Probe667.agda:70-73; Probe652.agda:87-91).  Two existentials
  -- bind value then parameter; the remaining free slot is the
  -- witness.  The two ≐ conjuncts pin those binders to the codes.
  inBound : (ca cp : Code) → Formula Code 1
  inBound ca cp =
    ∃̇ (∃̇ (matrix₃-Code
         ∧̇ (var zero ≐ con ca)
         ∧̇ (var (suc zero) ≐ con cp)))

  -- THE STAGE EXISTENTIAL hull-closed demands
  -- (src/L/Hull.lagda.md:415).  For ca coding Lset δ and cp coding
  -- δ this is Devlin 5.2 (b) at matrix₃
  -- (dev/literature/devlin-II5.md:95-99).  Named, not inhabited.
  BoundInStage : (ca cp : Code) → Type (ℓ-suc ℓ)
  BoundInStage ca cp =
    ⟨ [] F.HS.ASt.AbsL.⊨ᵐ (∃̇ (mapFo val (inBound ca cp))) ⟩

  -- THE CONSUMER.  W2: hull-closed, not a second search.  Given the
  -- stage existential, a bound is a hull member.  The ambient
  -- reading of matrix₃ at that bound is a conversion, named below.
  bound-from-stage : (ca cp : Code) → BoundInStage ca cp
                   → ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ M ⟩ ∥₁
  bound-from-stage ca cp h =
    PT.map (λ { (a , a∈H , _) → fst a , a∈H })
           (hull-closed (inBound ca cp) h)

  -- What LsetGrounded still asks after hull membership: the ambient
  -- 3-slot reading at (Lset δ, δ, z).
  AmbientAt : (δ z : S) → Type (ℓ-suc ℓ)
  AmbientAt δ z = ⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

  -- AbsL satisfaction of inBound to the ambient 3-slot reading.
  -- Named, not inhabited.  The path is unpack of two ∃̇ and two ≐,
  -- then Frame652.AtTrans.read at Δ₀-matrix₃ (Probe652.agda:114-124),
  -- which does not use elem.
  Convert : Type (ℓ-suc ℓ)
  Convert =
    (ca cp : Code) (a : F.HS.ASt.SL)
    → ⟨ (a ∷ []) F.HS.ASt.AbsL.⊨ᵐ (mapFo val (inBound ca cp)) ⟩
    → ⟨ (fst (val ca) ∷ fst (val cp) ∷ fst a ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

  -- Completeness of matrix₃ at hull codes: if the value code names
  -- Lset of the parameter code, the stage satisfies the existential
  -- hull-closed takes.  Named, not inhabited.  Devlin 5.2 (b)
  -- (dev/literature/devlin-II5.md:98-99) is this at L_α, and it
  -- asks γ to be an ordinal.  LsetGrounded has no IsOrd.
  Completeness : Type (ℓ-suc ℓ)
  Completeness =
    (ca cp : Code)
    → fst (val ca) ≡ Lset (fst (val cp))
    → BoundInStage ca cp

  -- Witnessed at matrix₃, given the sibling's soundness.
  WitnessedAt :
      ((a p z : S)
       → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
       → a ≡ Lset p)
    → P652.Witnessed Lset
  WitnessedAt sound = P667.matrix₃ , P667.Δ₀-matrix₃ , sound

  -- THE CORRECTED TARGET, D-10.  Same conclusion as LsetGrounded at
  -- matrix₃, two named hypotheses.  A term that SUBSTITUTES along
  -- the ambient reading of matrix₃ was started as grounded-from-complete
  -- (runs/p-4.out: still Checking, no ended line).  That term is not
  -- in this file.  Completeness and Convert remain types.
