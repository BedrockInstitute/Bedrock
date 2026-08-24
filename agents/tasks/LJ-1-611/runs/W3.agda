{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.611]  W3 SLICE.  crossOut, RE-ASCRIPTED AT G-'s FRAME, TYPE
-- ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "`crossOut`, re-ascribed
-- at Probe606.agda:168-172's frame, TYPE ONLY, capped".
--
-- [LJ-1.160]'s crossOut, at an ABSTRACT belief
-- (agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72):
--
--   (v b : S) -> < v in P > -> < b in P > -> IsOrd b -> Bel v b
--              -> v == Lset b
--
-- The re-ascription at face G- ([LJ-1.606]'s GraphAmbient,
-- agents/tasks/LJ-1-606/Probe606.agda:168-172):
--   P becomes the collapse image piX;  Bel v b becomes the AMBIENT
--   reading of the relabelled matrix at (x, v, b), the witness x a
--   fresh first slot (the one the kit's existential binds);  the two
--   containment hypotheses are DROPPED, because the face quantifies
--   over arbitrary ambient values;  and psi stays a PARAMETER, because
--   the abstract crossOut never chose a formula.  That last point is
--   the whole residue: a supplier of G- is a supplier of psi.
--
-- No formula is chosen and no inhabitant is claimed: this slice is a
-- TYPE.  Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-611.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ
                 (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans

  -- FACE G-, crossOut RE-ASCRIPTED, TYPE ONLY.  Letter for letter
  -- [LJ-1.606]'s GraphAmbient (Probe606.agda:168-172).
  W3 : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  W3 ψ = (x v γ : SV.S) → IsOrd γ
       → ⟨ (x ∷ v ∷ γ ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩
       → v ≡ Lset γ
