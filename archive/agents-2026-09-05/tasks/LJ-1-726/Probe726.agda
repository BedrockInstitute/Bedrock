{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.726] PROBE.  The ambient 3-slot matrix at the numeral-carrying
-- witness slot Lset (omega).  D-10 verdict: THE TARGET IS FALSE, and
-- this file machine-checks the refutation in green lemmas.  It runs in
-- agents/tasks/LJ-1-726/ and lands nothing in src/.
--
--   THE OBLIGATION  ambient-at-Lw.  P667.matrix3 at
--                   (Lset d, d, Lset omega) for EVERY constructible
--                   ordinal d.  Stated below with the designed hole:
--                   uninhabitable, by the refutation chain.
--   THE SITE        d := omega.  The graph half of matrix3 bounds the
--                   approximation table by the witness slot
--                   (graphBndAt = EXIST-IN (var K) ..., and its domB
--                   conjunct (src/L/Condensation.lagda.md:1749-1761)
--                   forces the table to answer EXACTLY the members of
--                   the parameter that lie in the witness.  At
--                   p := omega and z := Lset omega the numerals all lie
--                   in both, so any table c would carry a pair with
--                   first component # k for EVERY k.  But c sits in
--                   Lset omega, so rank c sits in omega, so rank c is a
--                   numeral # j; the entry at # j drags # j inside
--                   rank c = # j, and no set is a member of itself.
--                   One counterexample kills the Pi.
--   WHAT IS NEW     nothing.  Every link is a delivered lemma: the kill
--                   lives in runs/TablePerp.agda (this file imports it),
--                   built on rank-Lset (src/L/Ordinal/Stages.lagda.md:
--                   190), rank-mono and rank-fix (src/L/Rank.lagda.md:
--                   117, :191), the pair components (SingletonPackage
--                   and pairing-ax, Cubical.HITs.CumulativeHierarchy.
--                   Constructions.agda:133-160), the omega-members
--                   decode behind ω-mem-ord (src/L/Ordinal.lagda.md:
--                   258), and ord∈Lset-suc with Lset-mono.
--   W3 ANSWER       NO-GO for general d: the pin that still needs the
--                   table is graphBndAt's domB conjunct, whose right
--                   half demands an entry for EVERY member of p that
--                   lies in z.  At a FIXED witness stage Lset w the
--                   obligation dies for every d whose numeral content
--                   outranks w; at d := omega, z := Lset omega dies.
--                   The readings that survive keep the witness growing
--                   with d (z := Lset (suc^k d) for small fixed k, the
--                   table's rank being d + finite), or drop the table
--                   bound.  That is the mathematician's call; see
--                   review-of-ambient-at-Lw.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing is postulated.  Two designed holes: matrix3-table (the
-- extraction's final application, parked; see its hole note and
-- runs/p-45 and p-50 to p-83) and ambient-at-Lw (the obligation,
-- uninhabitable).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-726.Probe726 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
import FOL.Semantics
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import V.Coding {ℓ} using ( pr )
open import LJ-1-667.Probe667 {ℓ} lem as P667
open import LJ-1-726.runs.TablePerp {ℓ} lem using ( #∈Lω; table-⊥ )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open PT using ( ∥_∥₁ )
open import Cubical.Foundations.Prelude using ( cong )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
module At∅ = SemV.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b)

_⊨ₚ_ : ∀ {n} → V ℓ ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = At∅._⊨_

-- The parameter-free reading of the obligation.  This is Probe652's
-- own _⊨ₚ_ (Probe652.agda:50-51), spelled locally: same algebra, same
-- structure, same empty constant domain, so the obligation type below
-- is the briefed type.

-- =====================================================================
-- THE OBLIGATION, restated.  Uninhabitable; the refutation is below.
-- =====================================================================

AmbientAtLω : Type (ℓ-suc ℓ)
AmbientAtLω =
  (δ : CS.S) (oδ : IsOrd (fst δ))
  → ⟨ (Lset (fst δ) ∷ fst δ ∷ Lset ω ∷ []) ⊨ₚ P667.matrix₃ ⟩

-- =====================================================================
-- THE EXTRACTION, PARKED.  From any ambient reading of the matrix at
-- (a, p, z) the route is: transport the erased reading to the landing
-- reading SemV.At CS.S fst (by Count.erase-inv, src/FOL/Count.lagda.md:
-- 617, and embed-⊨, src/FOL/Manipulation/Relabelling.lagda.md:188, both
-- delivered), peel the twelve bounded existentials one step at a time
-- (each level a one-line PT.rec; every level's shape was measured
-- green in runs/exp-12.out), then from the matrix satisfaction take
-- the graph half (m .snd .snd): a truncated pair of the approximation
-- table c in Lset (omega) and its conjunct pair.  The domB half of the
-- conjunct (src/L/Condensation.lagda.md:1749-1761) answers, for every
-- x in the parameter that lies in the witness, with a truncated pair
-- y and pr x y in c, which is exactly the entry type table-perp (in
-- runs/TablePerp.agda, green) consumes.  The assembly was written and
-- elaborated to within one application (runs/p-45.out): the
-- application of the projected domB satisfaction left the satisfaction
-- coercion unreduced at the application check, and every restructuring
-- of the deep peel crashed Agda 2.8.0 itself (runs/p-50 to p-66: four
-- shapes, all abnormal terminations with no Agda message).  The next
-- brief should reach this step through the delivered reading-lemmas
-- (Sequence's ApproxAt-value / StepAt-back at variable slots,
-- src/L/Coding/Sequence.lagda.md:294-330) instead of raw peeling, or
-- price a satisfactions-level domAt-out analogue.

matrix₃-table :
  (a p z : V ℓ)
  (h : ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ P667.matrix₃ ⟩)
  → ∥ Σ[ c ∈ V ℓ ] ( ⟨ c ∈ˢ z ⟩
    × ((x : V ℓ) → ⟨ x ∈ˢ z ⟩ → ⟨ x ∈ˢ p ⟩
        → ∥ Σ[ y ∈ V ℓ ] ( ⟨ y ∈ˢ z ⟩ × ⟨ pr x y ∈ˢ c ⟩ ) ∥₁ ) ) ∥₁
matrix₃-table a p z h = {! THE ONE PARKED STEP of the extraction.  The
  route above is green to within one application (runs/p-45.out); the
  application of the projected domB satisfaction left the satisfaction
  coercion unreduced at the application check, and every restructuring
  of the deep peel crashed Agda 2.8.0 itself (runs/p-50 to p-66: four
  shapes, all abnormal terminations).  !}

-- =====================================================================
-- THE REFUTATION, and the obligation with the designed hole.  Applying
-- the obligation at d := (omega , its constructibility) gives exactly
-- the hypothesis the chain kills.
-- =====================================================================

ω∈Lˡ : ⟨ isL ω ⟩
ω∈Lˡ = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

ambient-at-Lω-refutes : AmbientAtLω → Empty.⊥
ambient-at-Lω-refutes h =
  PT.rec Empty.isProp⊥
    (λ { (c , (c∈ , ents)) → table-⊥ c c∈ ents })
    (matrix₃-table (Lset ω) ω (Lset ω) (h (ω , ω∈Lˡ) ω-ord))

ambient-at-Lω : AmbientAtLω
ambient-at-Lω δ oδ = {!! NO-GO, the target is false at the ordinal omega:
                          ambient-at-Lω-refutes above consumes exactly this
                          inhabitant; the graph half's domB conjunct forces a
                          table in Lset omega answering every numeral, and
                          the rank chain kills it; see
                          review-of-ambient-at-Lw.md !}
