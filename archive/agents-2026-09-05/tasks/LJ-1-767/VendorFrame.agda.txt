{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.765] VENDORED INTERFACE, THE FRAME.  This file is
-- LJ-1-728-SPLIT-SPLIT-SPLIT/runs/Frame728SSS.agda transcribed into
-- this worktree (which carries no LJ-1-728-SPLIT* directory), with
-- the module renamed to this task's namespace and this header
-- rewritten.  Every import and every declaration below the module
-- line is byte-identical to the original (runs/vendor-frame.diff):
-- the repaired telescope, the named interface types, the
-- obligation's type, and codeOf, exactly as the split measured them
-- green at -M4g (SSS runs/frame-1.out 15.08 s RSS 2.06 GB,
-- runs/frame-2.out 14.41 s; re-measured here at this dispatch).
--
--   THE TYPE       Completeness is [LJ-1.718]'s repaired statement
--                  taken as a HYPOTHESIS, never inhabited;
--                  hull-convert-at-matrix is [LJ-1.692]'s CONSTRUCTED
--                  term, opened plainly, never hypothesised.
--   NO HOLE, NO POSTULATE.  One Agda process per run, caliber from
-- the pane, never set here.  Lands nothing in src/.


open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-765.runs.Frame765 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ
open import FOL.Manipulation.Relabelling using ( mapFo )

open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
open import LJ-1-673.Probe673 {ℓ} lem as P673
-- plain import: the unqualified alias hull-convert-at-matrix of
-- Probe692.agda:66 must NOT enter short scope beside the Spend-opened
-- name of the same spelling (measured: AmbiguousName, 728's si-1).
import LJ-1-692.Probe692 {ℓ} lem as P692

open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

-- =====================================================================
-- THE FRAME, AS [LJ-1.718] HAD IT.  One hull stage, the telescope of
-- Probe692's Spend (Probe692.agda:46-51).
-- =====================================================================

module Build (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module F = A.F
  module HS = F.HS

  open F.HS.H.T using ( Code; val ) public
  open F.HS.H using ( hull-member; hull-closed ) public

  -- THE SUPPLIER.  [LJ-1.692]'s constructed Convert, opened once as
  -- a module alias over this frame, never hypothesised.
  open P692.Spend lam ordλ succλ X X⊆Lλ ∅∈λ elem
    using ( hull-convert-at-matrix ) public

  -- Completeness: [LJ-1.718]'s repaired statement, Completeness
  -- carrying IsOrd on the parameter code (Probe718.agda:81-86).
  -- Taken as a HYPOTHESIS, never inhabited here.
  Completeness : Type (ℓ-suc ℓ)
  Completeness =
    (ca cp : Code) → IsOrd (fst (val cp))
    → fst (val ca) ≡ Lset (fst (val cp))
    → A.BoundInStage ca cp

  -- The ambient matrix3 reading, named once (heap protocol: every
  -- later occurrence is a neutral application of this name, so the
  -- FOL elaboration is paid here and shared).
  AmbientAt : (v p w : S) → Type (ℓ-suc ℓ)
  AmbientAt v p w = ⟨ (v ∷ p ∷ w ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

  -- The hull's reading of inBound at a witness, named once (shape 4:
  -- no ascription restates this unfolding inline).
  SatIn : (a : F.HS.ASt.SL) (ca cp : Code) → Type (ℓ-suc ℓ)
  SatIn a ca cp =
    ⟨ (a ∷ []) F.HS.ASt.AbsL.⊨ᵐ (mapFo val (A.inBound ca cp)) ⟩

  -- Hull membership at a witness, named once (shape 4).
  HullM : F.HS.ASt.SL → Type (ℓ-suc ℓ)
  HullM a = ⟨ fst a ∈ˢ F.HS.H.T.Hull ⟩

  -- THE OBLIGATION'S TYPE: Probe718.agda:93-101 with its Convert
  -- line dropped, everything else verbatim.
  GroundedFromComplete : Type (ℓ-suc ℓ)
  GroundedFromComplete =
    Completeness
    → ((a p z : S)
       → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ → IsOrd p → a ≡ Lset p)
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
    → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ Lset δ ∈ˢ HS.M ⟩
                  × ⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩) ∥₁

  -- Hull membership read as the code search
  -- (src/L/Hull.lagda.md:337-339).
  codeOf : (x : S) → ⟨ x ∈ˢ HS.M ⟩
         → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
  codeOf x x∈M = hull-member x x∈M
