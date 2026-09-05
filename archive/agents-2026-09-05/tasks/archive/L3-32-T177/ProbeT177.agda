{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.32-T177] Adversarial review, heavy-arm extension: the pin frame
-- at op8 (slice collection) and op15 (relativization slot).  Untracked
-- probe, never committed (D-1).  The frame under audit is
-- ProbeT175.PinFrame, imported and reused unchanged.  The measured
-- claim: each heavy arm is one application and one composition, in
-- Bridge's Arm shape (the caller's subset certificate is passed
-- through).  Report: _build/l3.32-t177-report.md (incremental, C-22).
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT177 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isTransV )
open import L.Rud.StepGraph {ℓ} lem A using ( module Layer; module Desc )
open import L.Rud.Step {ℓ} lem A using ( op8; op15; Fof; Fof-f8; Fof-f15; F15A )
open import L.Rud.Images {ℓ} using ( F8 )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

import ProbeT175 {ℓ} lem A as P175

-- The heavy arms at the frame's own telescope, in Bridge's Arm shape.
-- Each arm is Fof-defSet≡ at its op, composed with the delivered
-- Fof-fk reshape.  The caller's subset certificate enters unchanged;
-- no per-op membership analysis enters the arm, exactly as F1.
module HeavyArms (C : S) (Ctr : isTransV C)
  (mA : ⟪ C ⟫) (qA : ⟪ C ⟫↪ mA ≡ A) (∅∈C : ⟨ ∅ ∈ˢ C ⟩)
  (a b : S) (a∈ : ⟨ a ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) where

  module P = P175.PinFrame C Ctr mA qA ∅∈C a b a∈ b∈

  F8-defSet≡ : (sub : (v : S) → ⟨ v ∈ˢ F8 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → P.defSet (P.pinned op8) ≡ F8 a b
  F8-defSet≡ sub = P.Fof-defSet≡ op8 sub8 ∙ Fof-f8 a b
    where
    sub8 : (v : S) → ⟨ v ∈ˢ Fof op8 a b ⟩ → ⟨ v ∈ˢ C ⟩
    sub8 v h = sub v (subst (λ t → ⟨ v ∈ˢ t ⟩) (Fof-f8 a b) h)

  F15-defSet≡ : (sub : (v : S) → ⟨ v ∈ˢ F15A a ⟩ → ⟨ v ∈ˢ C ⟩)
              → P.defSet (P.pinned op15) ≡ F15A a
  F15-defSet≡ sub = P.Fof-defSet≡ op15 sub15 ∙ Fof-f15 a b
    where
    sub15 : (v : S) → ⟨ v ∈ˢ Fof op15 a b ⟩ → ⟨ v ∈ˢ C ⟩
    sub15 v h = sub v (subst (λ t → ⟨ v ∈ˢ t ⟩) (Fof-f15 a b) h)
