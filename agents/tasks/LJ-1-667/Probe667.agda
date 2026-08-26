{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.667] PROBE.  The witnessed matrix clause (iii) actually wants.
-- It runs in agents/tasks/LJ-1-667/ and lands nothing in src/.
--
--   THE OBLIGATION  witnessed-lset.  Witnessed Lset together with
--                   LsetGrounded, at the shape [LJ-1.652] measured and
--                   [LJ-1.665] assembled.  DO NOT FUND Matrix₂.
--
--   W3              the witness slot's content: [LJ-1.520]'s Matrix
--                   with the twelve tag slots bounded by the witness,
--                   erased onto ⊥*.  Green in runs/W3.agda.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-667.Probe667 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∀∈; δ-∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.runs.W3 {ℓ} lem as W3
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE WITNESS SLOT, AS SYNTAX.  W3 delivered the erased 3-slot Δ₀
-- matrix.  Slot order is Witnessed's: value, parameter, witness
-- (Probe652.agda:87-91).  The twelve tag numerals live inside the
-- witness by bounded existentials over it (runs/W3.agda, `three`).
-- transK and pins are already inside [LJ-1.520]'s Matrix.
-- =====================================================================

φ₃ : Formula (⊥* {ℓ-suc ℓ}) 3
φ₃ = W3.erased

Δ₀-φ₃ : Δ₀ φ₃
Δ₀-φ₃ = W3.Δ₀-erased

count-φ₃ : countFo φ₃ ≡ 0
count-φ₃ = refl

-- Ordinality of the parameter, as a 3-slot conjunct, p at slot 1.
-- isOrdAt (src/L/BoundedSubset.lagda.md:795-798) is arity 1 at slot 0.
-- Written at arity 3 rather than renamed, so the parameter is p and
-- not a.
isOrd-at-p : Formula (⊥* {ℓ-suc ℓ}) 3
isOrd-at-p =
    (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc zero))))))
  ∧̇ (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero)
        (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrd-at-p : Δ₀ isOrd-at-p
Δ₀-isOrd-at-p = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- The matrix the literature has: Devlin 5.2 (a), Φ(z, v, γ), with the
-- consumer's slot order (v, γ, z) = (a, p, z).
matrix₃ : Formula (⊥* {ℓ-suc ℓ}) 3
matrix₃ = isOrd-at-p ∧̇ φ₃

Δ₀-matrix₃ : Δ₀ matrix₃
Δ₀-matrix₃ = δ-∧ Δ₀-isOrd-at-p Δ₀-φ₃

-- =====================================================================
-- THE SOUNDNESS RESIDUE.  Witnessed asks
--   (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ matrix₃ ⟩ → a ≡ Lset p
-- (Probe652.agda:87-91).  Lset-only
-- (src/L/Hierarchy.lagda.md:334-335) discharges that conclusion FROM
-- LsetGraphAt AT 𝒮ʟ WITH IsOrd.  Three bridges sit between matrix₃
-- and that lemma, and they are types, not prose.
-- =====================================================================

-- BRIDGE 1.  The ambient V reading of an erased Δ₀ formula, at
-- arbitrary sets, is not the 𝒮ʟ reading Lset-only takes.  EraseTransfer
-- (src/L/Condensation.lagda.md:287-305) moves 𝒮ʟ UP to V, at a
-- constructible environment.  It does not move V DOWN to 𝒮ʟ, and it
-- does not apply when a, p, z fail isL.
module SoundnessBridges where

  -- BRIDGE 2.  graphBndAt (with transK and pins, which Matrix already
  -- carries) to LsetGraphAt.  [LJ-1.520] named this SameAsGraph and
  -- did not inhabit it (Probe520.agda:192-195).  No module GraphAgree
  -- exists under src/.  The story-to-machine leaf chain that would
  -- feed it is commented as unplaced
  -- (src/L/Condensation.lagda.md:5477-5480).

  -- BRIDGE 3.  Witnessed's soundness has no IsOrd hypothesis.
  -- isOrd-at-p is in the formula so that, IF the two bridges above
  -- close, Amb.isOrdAt-out plus Lset-only fire.  It is not itself
  -- the missing conversion.

-- THE TYPE THE OBLIGATION OWES, restated from the predecessor, so a
-- next brief does not have to open 652 to see it.
WitnessedLset : Type (ℓ-suc ℓ)
WitnessedLset = P652.Witnessed Lset

-- =====================================================================
-- ELEMENTARITY AT THIS FRAME.  Premise 4 of the brief: take `elem`
-- from src/L/BoundedSubset.lagda.md:759 and report if it does not
-- reach.  [LJ-1.655] measured that it lives in WithCode and costs a
-- code pair (lj-1.655-report.md:64-79).  Re-measured here: LsetGrounded
-- is at Frame652.Instances, whose telescope is HullStage's, which does
-- not carry that pair.
-- =====================================================================

module ElemReach
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ

  -- The type LsetGrounded lives at.  elem is a hypothesis of
  -- Instances, not a field of HullStage.
  ElementaryAt : Type (ℓ-suc (ℓ-suc ℓ))
  ElementaryAt = F.A.Elementary

  -- [LJ-1.655] already closed elem-at-collapse at the CHAPTER
  -- telescope (Probe655.agda:300), which carries κ, a cardinal, a
  -- square, and absorbs.  That pair is not in THIS telescope, so
  -- BoundedSubset:759 does not reach Frame652.  The name below is
  -- the type a next brief would inhabit if it funds the code pair
  -- at this frame; it is not inhabited here.
  CodePair : Type (ℓ-suc ℓ)
  CodePair =
    Σ[ f ∈ (F.A.SM → F.HS.H.T.Code) ]
      ((q : F.A.SM) → fst (F.HS.H.T.val (f q)) ≡ fst q)

-- =====================================================================
-- LSETGROUNDED'S OWN RESIDUE, ONCE A Witnessed IS IN HAND.
-- The consumer commute-from-witnessed (Probe652.agda:266-268) is
-- green.  What it still asks of the hull is a member z such that
-- the ambient 3-slot formula holds of (Lset δ, δ, z).  For matrix₃
-- that z is a bound containing the twelve numerals and the
-- approximation table.  Putting that bound in the hull is a
-- hull-closure fact, and it is not a reading of the ambient formula.
-- =====================================================================

LsetGroundedAt :
  (w : P652.Witnessed Lset)
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
  → Type (ℓ-suc ℓ)
LsetGroundedAt w lam ordλ succλ X X⊆Lλ ∅∈λ elem =
  P652.Frame652.Instances.LsetGrounded lam ordλ succλ X X⊆Lλ ∅∈λ elem w

-- The obligation name is NOT defined.  The witness meter must read
-- UNRESOLVED.  The syntax of the witness slot is `matrix₃` / `Δ₀-matrix₃`.
-- The three soundness bridges and the hull-membership of the bound
-- are the stop.  See review-of-witnessed-lset.md.
