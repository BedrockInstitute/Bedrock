{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.710] PROBE.  bound2-in-limit, in a frame trimmed to ordinals.
-- Lands nothing in src/.
--
--   THE OBLIGATION  <a limit that contains sigma1 and sigma2 contains
--                   fst (bound2 sigma1 sigma2 o1 o2)>.
--                   NOT INHABITED HERE.
--                   review-of-bound2-in-limit.md states the stop.
--
--   FRAME           src/L/Ordinal.lagda.md only.  Import NOTHING from
--                   LJ-1.698 / LJ-1.705 / LJ-1.706, no LEM, no FOL, no
--                   condensation.  Cold floor measured:
--                   runs/t-small.out, EXIT=0, 1.37 s, 278 MB.
--
--   THE DESIGN      IsLimit below carries ordinality, successor closure,
--                   and small-family union closure, so its union clause
--                   accepts ANY presentation.  The goal set never needs
--                   a judgmental match against bound2's internals ON THE
--                   INSTANCE SIDE; SECTION 3 closes at my own written
--                   family in two lines.
--
--   WHY THE GOAL SIDE STILL STANDS OPEN (W3, answered by measurement)
--     t-e1.out      The closure clause INSTANCED at my written family
--                   fails against fst (bound2 ...): "L.Ordinal.f
--                   sigma1 sigma2 o1 o2 x != mf x" [UnequalTerms].
--                   This is elaboration-time unification, not a refl
--                   check, so p-26's lesson does not cover it; it fails
--                   anyway, on the variable position again.
--     t-paths2.out  bound2's where-bound family is not referenceable:
--                   L.Ordinal.bound2.f -- [NotInScope].  The symbol only
--                   prints inside error messages.
--   SECTION 3 therefore closes the merge at an own-name presentation,
--   whose statement coincides with the obligation up to that name;
--   SECTION 4 types the gap.  The review file names what reopens it.
--
-- ONE Agda process per run, GHCRTS wide caliber (-A64m -I0 -M2g),
-- set on the pane by the program and untouched here.  Nothing is
-- postulated; no hole survives; this file typechecks green (exit 0)
-- BY DESIGN: the obligation itself appears only as a well-formed Type,
-- which is what the predecessor floor pattern measured green too.

open import Base.Prelude
open import Base.Truth

module LJ-1-710.Probe710 {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; bound2 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ

-- =====================================================================
-- SECTION 1.  THE LIMIT PREDICATE.
--
-- Presentation-honest on purpose: the union clause quantifies over the
-- family, so the instance side is whatever the prover writes.  This is
-- the restructured shape the predecessor's heap wall demanded; the
-- trimmed frame loads it cold in 1.37 s (runs/t-small.out).
-- =====================================================================

IsLimit : S → Type (ℓ-suc ℓ)
IsLimit α =
    IsOrd α
  × ((x : S) → ⟨ x ∈ₛ α ⟩ → ⟨ sucV x ∈ₛ α ⟩)
  × ((X : Type ℓ) (h : X → S)
      → ((i : X) → ⟨ h i ∈ₛ α ⟩)
      → ⟨ ⋃ (sett X h) ∈ₛ α ⟩)

-- =====================================================================
-- SECTION 2.  THE OBLIGATION, AS A WELL-FORMED TYPE.
--
-- Verbatim the brief's bracketed statement with IsLimit above.
-- Well-formedness here is the trimmed-frame floor, precedent
-- lj-1.705-report.md section 3.  A body would be dishonest: every
-- route to it needs the internal name measured inaccessible at
-- runs/t-paths2.out and unconvertible at runs/t-e1.out.
-- =====================================================================

the-obligation : Type (ℓ-suc ℓ)
the-obligation =
    (α : S) (Lim : IsLimit α)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ₛ α ⟩) (h₂ : ⟨ σ₂ ∈ₛ α ⟩)
  → ⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩

-- =====================================================================
-- SECTION 3.  WHAT CLOSES GREEN AT MY OWN PRESENTATION.
--
-- bound2OwnLimit merges two members of a limit exactly the way
-- boundingOrd does, with the family written out loud.  Two lines: the
-- successor clause lifts both members, the union clause takes the
-- merge.  This theorem is what the obligation reduces TO once the
-- family parity gap is closed on the src side.
-- =====================================================================

-- The merge family, written out loud ONCE, named, so every mention of
-- it below (type side, instance side, ordinality side) cites the same
-- symbol and nothing ever converts at a variable position.

succFam : S → S → Lift {ℓ-zero} {ℓ} Bool → S
succFam σ₁ σ₂ (lift true)  = sucV σ₁
succFam σ₁ σ₂ (lift false) = sucV σ₂

bound2OwnLimit :
    (α : S) (Lim : IsLimit α)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ₛ α ⟩) (h₂ : ⟨ σ₂ ∈ₛ α ⟩)
  → ⟨ ⋃ (sett (Lift {ℓ-zero} {ℓ} Bool) (succFam σ₁ σ₂)) ∈ₛ α ⟩
bound2OwnLimit α (_ , succCl , unionCl) σ₁ σ₂ o₁ o₂ h₁ h₂ =
  unionCl (Lift {ℓ-zero} {ℓ} Bool) (succFam σ₁ σ₂) mm
  where
  mm : (b : Lift {ℓ-zero} {ℓ} Bool) → ⟨ succFam σ₁ σ₂ b ∈ₛ α ⟩
  mm (lift true)  = succCl σ₁ h₁
  mm (lift false) = succCl σ₂ h₂


-- Its ordinality comes free from L.Ordinal's already-green pieces,
-- witnessing that the merge really is the same KIND of object the
-- obligation speaks about (bound2's fst carries an IsOrd by
-- src/L/Ordinal.lagda.md:185).

ownMerged : (α : S) (Lim : IsLimit α)
           (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
         → S
ownMerged α Lim σ₁ σ₂ o₁ o₂ = ⋃ (sett (Lift {ℓ-zero} {ℓ} Bool) (succFam σ₁ σ₂))

ownMergedOrd : (α : S) (Lim : IsLimit α)
               (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
             → IsOrd (ownMerged α Lim σ₁ σ₂ o₁ o₂)
ownMergedOrd α Lim σ₁ σ₂ o₁ o₂ =
  setUnion-ord (Lift {ℓ-zero} {ℓ} Bool) (succFam σ₁ σ₂) ordFam
  where
  ordFam : (b : Lift {ℓ-zero} {ℓ} Bool) → IsOrd (succFam σ₁ σ₂ b)
  ordFam (lift true)  = suc-ord o₁
  ordFam (lift false) = suc-ord o₂

ownMergedInLimit :
    (α : S) (Lim : IsLimit α)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ₛ α ⟩) (h₂ : ⟨ σ₂ ∈ₛ α ⟩)
  → ⟨ ownMerged α Lim σ₁ σ₂ o₁ o₂ ∈ₛ α ⟩
ownMergedInLimit α Lim σ₁ σ₂ o₁ o₂ h₁ h₂ =
  bound2OwnLimit α Lim σ₁ σ₂ o₁ o₂ h₁ h₂

-- =====================================================================
-- SECTION 4.  THE GAP, WRITTEN DOWN IN TYPES.
--
-- The only missing link is one equality-shaped fact about a symbol
-- this file cannot reference (runs/t-paths.out):
--
--   eqOfPresentations :
--       (b : Lift {\ell-zero} {\ell} Bool)
--     -> succFam sigma1 sigma2 b ~ bound2's internal family at b
--
-- after which subst along cong-U (seteq ...) closes the obligation.
-- Neither refl (predecessor runs/p-26.out, this dispatch
-- runs/t-e1.out) nor name-reference closes it today.  The review file
-- names the minimal src-side cure.
-- =====================================================================
