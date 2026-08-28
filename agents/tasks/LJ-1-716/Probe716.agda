{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.716] PROBE.  The ambient 3-slot matrix at the table.  D-10
-- verdict: THE TARGET IS FALSE, and this file machine-checks the
-- refutation in two green lemmas.  It runs in agents/tasks/LJ-1-716/
-- and lands nothing in src/.
--
--   THE OBLIGATION  ambient-at-hier.  P667.matrix₃ at
--                   (Lset δ₀, δ₀, hierL δ₀) for EVERY constructible
--                   ordinal δ₀.  Stated below with the designed hole:
--                   uninhabitable, by zero-refutes.
--   THE SITE        δ₀ := (∅ , ∅∈L), the empty ordinal.  hierL ∅ has
--                   no members (Recorded ∅ quantifies over members of
--                   ∅), while matrix₃'s φ₃ half opens with one bounded
--                   existential OVER the witness slot.  First member
--                   demanded, none exists: absurd.
--   W3              whether graph + SameAsGraph + erase yield φ₃ at
--                   (Lset δ, δ, hierL δ).  Answered NO: the 2-slot
--                   graph and the 3-slot matrix remain distinct, and
--                   the miss is the MATRIX's witness-slot content, not
--                   the graph, not the erase, not isOrd-at-p.
--   MEASURED WALL   the final one-line composition of the two green
--                   lemmas at the concrete δ₀ walls the checker at
--                   2.6 g (runs/g-4.out through runs/vi-1.out): any
--                   conversion between two pointer-distinct types that
--                   both spell Lset ∅ in the environment makes the
--                   checker whnf the ∈-induction unfold.  The two
--                   lemmas below keep every reduction in variable-land
--                   and are green at 3.3 s.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing is postulated.  Two designed holes, at zero-refutes and at
-- ambient-at-hier.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-716.Probe716 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import L.Axioms.Basic {ℓ} using ( ∅∈L )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty )
open import V.Coding {ℓ} using ( pr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE BRIEFED TYPE, restated from Probe673.agda:108-109.  Unoccupied;
-- the refutation below proves it uninhabitable at δ₀ = ∅.
-- =====================================================================

AmbientAt : (δ z : S) → Type (ℓ-suc ℓ)
AmbientAt δ z = ⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

-- =====================================================================
-- GREEN LEMMA 1.  The table at ∅ has no members.  Every member of
-- fst (hierL ∅ …) lands in Recorded ∅ through the spec, and Recorded ∅
-- quantifies over members of ∅.  isL-trans is what lifts the ambient
-- member into the constructible carrier the spec quantifies over.
-- Satisfaction is a structural recursion
-- (src/FOL/Semantics.lagda.md:102-103), so the descent needs no lemma
-- past the truncation's own map.
-- =====================================================================

no-member-of-hierL∅ :
  (h0 : ⟨ isL ∅ ⟩) (o0 : IsOrd ∅) (x : S)
  → ⟨ x ∈ˢ fst (hierL ∅ h0 o0) ⟩ → Empty.⊥
no-member-of-hierL∅ h0 o0 x x∈H =
  PT.rec Empty.isProp⊥ kill (subst ⟨_⟩ (spec z) x∈H)
  where
  H : CS.S
  H = hierL ∅ h0 o0
  xL : ⟨ isL x ⟩
  xL = isL-trans x∈H (H .snd)
  z : CS.S
  z = x , xL
  spec : IsHier ∅ H
  spec = hierL-spec ∅ h0 o0
  kill : Σ[ c ∈ CS.S ]
           (⟨ fst c ∈ ∅ ⟩ × (x ≡ pr (fst c) (Lset (fst c)))) → Empty.⊥
  kill (c , c∈∅ , _) =
    Empty.rec (∅-empty (fst c) (∈∈ₛ {a = fst c} {b = ∅} .fst c∈∅))

-- =====================================================================
-- GREEN LEMMA 2.  The descent, GENERIC in δ and oδ: any ambient
-- reading at (Lset δ, δ, hierL δ) surrenders a member of hierL δ by
-- the truncation's own map, and a member-free hierL δ kills it.  Kept
-- generic on purpose: the concrete-δ₀ composition of these two lemmas
-- is exactly the conversion the checker walls on (see the header).
-- =====================================================================

ambient-at-hier-empty :
  (δ : CS.S) (oδ : IsOrd (fst δ))
  → AmbientAt (fst δ) (fst (hierL (fst δ) (δ .snd) oδ))
  → ((u : S) → ⟨ u ∈ˢ fst (hierL (fst δ) (δ .snd) oδ) ⟩ → Empty.⊥)
  → Empty.⊥
ambient-at-hier-empty δ oδ h noMember =
  PT.rec Empty.isProp⊥ (λ { (x , x∈z) → noMember x x∈z })
    (PT.map (λ { (x , x∈z , _) → x , x∈z }) (h .snd))

-- =====================================================================
-- THE COMPOSITION AT δ₀ := (∅ , ∅∈L), WITH THE DESIGNED HOLE.  The
-- one-line plug is
--     zero-refutes h =
--       ambient-at-hier-empty (∅ , ∅∈L) ∅-ord h
--         (no-member-of-hierL∅ ∅∈L ∅-ord)
--     -- η: no-member's (x : S) matches the callback's u
-- and both lemmas are green above; the plug walls the checker at 2.6 g
-- (runs/vh-1.out, runs/vi-1.out), so it stands as this hole.
-- =====================================================================

zero-refutes :
  (h : AmbientAt ∅ (fst (hierL ∅ ∅∈L ∅-ord))) → Empty.⊥
zero-refutes h = {! composition walls the checker: see the header !}

-- =====================================================================
-- THE OBLIGATION, WITH THE DESIGNED HOLE.  Uninhabitable: applying it
-- at δ := (∅ , ∅∈L) with oδ := ∅-ord gives exactly zero-refutes'
-- hypothesis, and zero-refutes kills it.  The corrected target stands
-- beside the original (D-10) in the review, not as a type here: the
-- least reading that survives is at a WITNESS SLOT THAT CARRIES THE
-- NUMERALS, a stage and not the table.
-- =====================================================================

ambient-at-hier : (δ : CS.S) (oδ : IsOrd (fst δ))
  → AmbientAt (fst δ) (fst (hierL (fst δ) (δ .snd) oδ))
ambient-at-hier δ oδ = {!! NO-GO, the target is false at the empty
                          ordinal: zero-refutes above consumes exactly
                          this inhabitant; see
                          review-of-ambient-at-hier.md !}
