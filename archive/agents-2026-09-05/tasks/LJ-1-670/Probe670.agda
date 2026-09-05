{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.670] PROBE.  Can [LJ-1.665]'s Elementary slot be filled from
-- what [LJ-1.655] and the chapter already delivered?  Lands nothing
-- in src/.  Does not re-prove elementarity.
--
--   PART 0   W3.  [LJ-1.655]'s AtCollapse and [LJ-1.652]'s Frame652
--            (the frame [LJ-1.665] assembled in) share one HullStage
--            telescope.  The hull, the code type, and the Elementary
--            type itself agree by refl.
--
--   PART 1   THE OBLIGATION.  `elem-is-paid` fills Frame652.A.Elementary
--            with AtCollapse.WithCode.elem.  The remaining price is the
--            code pair [LJ-1.655] named, and nothing else.  That pair
--            is NOT Elementary; Elementary leaves the certificate's
--            remaining debt.  The chapter already spends the pair at
--            BoundedSubsetAt (Probe655.agda:283-300); this file does
--            not re-elaborate that spend.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.  No heap event.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-670.Probe670 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- THE PREDECESSORS, BY THE TYPE EACH ONE DELIVERED (coder clause,
-- owner 2026-08-20).  665 closed GO on certificate-remainder
-- (lj-1.665-report.md:8).  655 closed GO on elem-at-collapse
-- (lj-1.655-report.md:1).  Neither names Elementary FALSE.
import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-655.Probe655 {ℓ} lem as P655

-- =====================================================================
-- PART 0.  W3: DO THE TWO FRAMES SHARE A TELESCOPE?
--
--   [LJ-1.665] assembled at HullStage
--   (src/L/BoundedSubset.lagda.md:903-914; Probe665.agda:65-69).
--   [LJ-1.655] instantiated HullElemDown at that telescope minus
--   succλ (Probe655.agda:75-100).  AtCollapse still takes succλ.
--   The join is definitional.
-- =====================================================================

module At665 (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ
  module AC = P655.AtCollapse lam ordλ succλ X X⊆Lλ ∅∈λ

  hull-agree : AC.HED.M ≡ F.HS.M
  hull-agree = refl

  code-agree : AC.HED.H.T.Code ≡ F.HS.H.T.Code
  code-agree = refl

  -- THE SLOT AND THE SUPPLIER ARE ONE TYPE.
  elem-type-agree : AC.HED.A.Elementary ≡ F.A.Elementary
  elem-type-agree = refl

  -- ===================================================================
  -- PART 1.  THE OBLIGATION, AT THE FRAME [LJ-1.665] ASSEMBLED IN.
  --
  --   665's hypothesis is `F.A.Elementary` (Probe665.agda:236).
  --   655's `elem` (Probe655.agda:144-145) inhabits `HED.A.Elementary`.
  --   Those are the same type, so the slot fills.  The remaining
  --   arguments are the code pair 655 priced
  --   (lj-1.655-report.md:84-85), which is a SELECTION problem, not
  --   a second proof of elementarity.
  --
  --   `elem-at-collapse` (Probe655.agda:153-158) is NOT this type:
  --   it is elem composed with iso-invariance.  Clause (iii) spends
  --   Elementary (Probe652.agda:155, :174).  This term spends that.
  -- ===================================================================

  elem-is-paid :
      (f : AC.HED.A.SM → AC.H.T.Code)
      (f-spec : (q : AC.HED.A.SM) → fst (AC.H.T.val (f q)) ≡ fst q)
    → F.A.Elementary
  elem-is-paid f f-spec = AC.WithCode.elem f f-spec

-- THE OBLIGATION, at this module's own top level, so the witness
-- reaches it by the bare name the brief declares.
elem-is-paid = At665.elem-is-paid
