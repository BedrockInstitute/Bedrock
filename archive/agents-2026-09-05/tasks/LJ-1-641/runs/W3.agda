{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-641]  W3 SLICE.  THE WIDEST UNMEASURED TERM, ALONE.
--
-- The brief names W3: "Whether the two computation laws join once the
-- collapse is an ordinal."  This slice states exactly that and nothing
-- else, and it is typechecked ALONE before any other row of the probe
-- is written.
--
-- The two laws are the ones [LJ-1.477] spent
-- (agents/tasks/LJ-1-477/lj-1.477-report.md, STEP TWO):
--   HS.C.π-compute (Lset δ) : π (Lset δ) ≡ step (Lset δ) (λ z _ → π z)
--   Lset-compute (HS.C.π δ) : Lset (π δ) ≡ LsetStep (π δ) (λ β _ → Lset β)
-- and the join is the equation between the two right-hand sides.  THE
-- DIFFERENCE FROM [LJ-1.477] IS THE HYPOTHESIS: `IsOrd (HS.C.π δ)` and
-- `⟨ Lset δ ∈ˢ HS.M ⟩` are IN SCOPE here and were not there.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-641.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-compute; LsetStep )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- LAW ONE, at the collapse, spent at `Lset δ`.  The seal on π does
  -- not open: the exported computation law carries its own type.
  law-π : (δ : SV.S)
        → HS.C.π (Lset δ) ≡ HS.C.step (Lset δ) (λ z _ → HS.C.π z)
  law-π δ = HS.C.π-compute (Lset δ)

  -- LAW TWO, at the tower, spent at `HS.C.π δ`.
  law-L : (δ : SV.S)
        → Lset (HS.C.π δ) ≡ LsetStep (HS.C.π δ) (λ β _ → Lset β)
  law-L δ = Lset-compute (HS.C.π δ)

  -- THE JOIN, AT THE ORDINAL COLLAPSE.  This is [LJ-1.477]'s
  -- `JoinSteps` (agents/tasks/LJ-1-477/Probe477.agda:90-93) with THIS
  -- obligation's two hypotheses added.  Unbuilt here; the question W3
  -- asks is whether the hypotheses close it.
  JoinStepsAtOrd : Type (ℓ-suc ℓ)
  JoinStepsAtOrd =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.step (Lset δ) (λ z _ → HS.C.π z)
      ≡ LsetStep (HS.C.π δ) (λ β _ → Lset β)

  -- and the obligation IS that join, once both laws are spent: this
  -- row is the reduction, and it is the only thing W3 delivers as a
  -- TERM.  It says the join is not a detour but the whole remainder.
  join-gives-commute
    : JoinStepsAtOrd
    → (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)
  join-gives-commute j δ δ∈M oπδ Lδ∈M =
    law-π δ ∙ j δ δ∈M oπδ Lδ∈M ∙ sym (law-L δ)
