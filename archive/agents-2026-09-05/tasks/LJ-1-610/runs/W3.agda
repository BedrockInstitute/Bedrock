{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.610]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "the Sigma-one closure of
-- the graph matrix, stated alone, TYPE ONLY, capped".  The graph matrix
-- is the tree's own: the body of `LsetGraphAt`
-- (src/L/Coding/Sequence.lagda.md:291-292), an approximation `z` on the
-- index and the value as the step at the index from `z`, at the three
-- slots (z, v, gamma).  Its Sigma-one closure is `∃̇` over that matrix,
-- and at the stage's inner world the `∃̇` ranges over the STAGE's
-- members: the witness must be inside the carrier.  That is Devlin's
-- (b) (dev/literature/devlin-II5.md:219-223), and this type is the
-- statement of its forward half, with no inhabitant claimed.
--
-- The carrier: the tree's graph formulas live at the constructible-class
-- carrier `CS.S` (src/L/Coding/Model.lagda.md:70 opens
-- `hPropStructure 𝒮ʟ using ( S )`), and the only constants the machine
-- matrix carries are the L-numerals (they enter at `tagAtL`,
-- src/L/Coding/Model.lagda.md:585-586).  `numSL` below carries every
-- numeral into the stage (Bound.num∈λ, src/L/Coding/Bound.lagda.md:139,
-- from the frame's own four hypotheses) and sends everything else to the
-- stage's empty member, so the relabelled matrix reads the numerals it
-- actually carries.  No total correct relabelling exists: not every
-- constructible set is a stage member.  This slide is itself one of the
-- task's findings; see the report.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-610.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Sequence {ℓ} lem using ( ApproxAt; StepAt )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.BoundedSubset {ℓ} lem using ( module DownReflect )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Foundations.HLevels using ( isProp→isSet; isSetΣ )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module DR = DownReflect lam ordλ X X⊆Lλ ∅∈λ
  module B = Bound lam ordλ succλ ∅∈λ

  -- numerals into the stage, junk elsewhere; correct on every constant
  -- the machine matrix carries
  isSetSL : isSet DR.ASt.SL
  isSetSL = isSetΣ SV.isSetS (λ x → isProp→isSet ((x ∈ˢ Lset lam) .snd))

  numSL : CS.S → DR.ASt.SL
  numSL c =
    Sum.rec
      (λ h → PT.rec→Set isSetSL numf numk h)
      (λ _ → ∅ , DR.H.∅∈Lsetα)
      (lem ((∥ Σ[ k ∈ ℕ ] (c ≡ numeralL k) ∥₁) , squash₁))
    where
    numf : Σ[ k ∈ ℕ ] (c ≡ numeralL k) → DR.ASt.SL
    numf (k , ck) =
      fst c , subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (cong fst ck)) (B.num∈λ k)
    numk : (u v : Σ[ k ∈ ℕ ] (c ≡ numeralL k)) → numf u ≡ numf v
    numk _ _ = cong₂ _,_ refl ((fst c ∈ˢ Lset lam) .snd _ _)

  -- THE GRAPH MATRIX, at the three slots (z, v, gamma): z is an
  -- approximation on gamma and v is the step at gamma from z.  This is
  -- the body of `LsetGraphAt` at (suc zero, suc (suc zero))
  -- (src/L/Coding/Sequence.lagda.md:291-292).
  matrixCS : Formula CS.S 3
  matrixCS = ApproxAt zero (suc (suc zero))
           ∧̇ StepAt (suc zero) (suc (suc zero)) zero

  matrixSL : Formula DR.ASt.SL 3
  matrixSL = mapFo numSL matrixCS

  -- THE SIGMA-ONE CLOSURE, STATED ALONE, TYPE ONLY.  At every stage pair
  -- whose value IS the tower's value at the index, the stage's inner
  -- world satisfies the existential closure of the graph matrix, the
  -- witness inside the carrier.
  Σ₁Closure : Type (ℓ-suc ℓ)
  Σ₁Closure =
    (q γ : DR.ASt.SL) → fst q ≡ Lset (fst γ)
    → ⟨ (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ (∃̇ matrixSL) ⟩
