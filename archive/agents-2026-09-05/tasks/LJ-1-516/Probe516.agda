{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.516] PROBE.  Transport the SATISFACTION, not only the formula.
-- It runs in agents/tasks/LJ-1-516/ and lands nothing in src/.
--
--   W3, FIRST      the seam: liftFo-correct fed to the ⊨-map law at this
--                  frame.  Written with the obligation OMITTED and
--                  typechecked ALONE, so a failure to compose costs one
--                  file and not a task.  IT COMPOSES.
--   DELIVERED      transports-Δ₀, the briefed statement for EVERY Δ₀
--                  formula over CS.S, unconditional in the stage.
--   NOT DELIVERED  graphSat-transports.  NO-GO.  The seam is not the
--                  obstruction; the Levy grade of LsetGraphAt is, and
--                  no-Δ₀, no-Σ₁ and no-Π₁ below REFUTE all three grades.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-516.Probe516 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∧; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀ )
import FOL.Semantics
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; Lset; IsOrd; isL; isL-trans; Lset→isL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Axioms.Separation {ℓ} lem using ( Below′ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.Data.Vec using ( map )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module CS = hPropStructure 𝒮ʟ

-- THE FRAME.  Three satisfactions are in play and they must be kept apart.
--   _⊨ᵥ_   the hierarchy, constants ARE sets            (Formula (V ℓ) n)
--   _⊨ʟᵛ_  the hierarchy, constants read through fst    (Formula CS.S n)
--   AbsL.⊨ᵛ the hierarchy, constants read through fst    (Formula SL n)
-- The two ⊨-map instances below move between the first and each of the
-- other two.  NONE of the three is satisfaction in an inner model.
module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id  using () renaming ( _⊨_ to _⊨ᵥ_ )
open SemV.At CS.S fst using () renaming ( _⊨_ to _⊨ʟᵛ_ )

-- W3.  THE SEAM, AND IT COMES FIRST.
--
-- liftFo-correct (src/FOL/Manipulation/Bounding.lagda.md:198) equates two
-- mapFo images, both of them Formula (V ℓ) n.  ⊨-map
-- (src/FOL/Manipulation/Relabelling.lagda.md:154) turns each of those into
-- a satisfaction IN 𝒮ᵥ.  Put end to end they give ONE equation, and the
-- statement below is exactly what they give: outer against outer.
module Seam (α : V ℓ) (ordα : IsOrd α) where

  module ASt  = AtStage α ordα
  module AbsL = ASt.AbsL
  open ASt public using ( SL )

  -- The instance is [LJ-1.514]'s, restated because a probe may not import
  -- a probe.  down-correct is refl for the reason that task measured:
  -- both carriers project into V ℓ and the projections agree on the nose.
  module RL = Relabel {K = CS.S} {K' = SL} {W = V ℓ}
                fst fst (Below′ α)
                (λ c h → fst c , h)
                (λ c h → refl)

  seam : ∀ {n} (φ : Formula CS.S n) (h : BoundedFo (Below′ α) φ) (γ : SL ^ n)
       → ((map fst γ) AbsL.⊨ᵛ RL.liftFo φ h) ≡ ((map fst γ) ⊨ʟᵛ φ)
  seam φ h γ =
      sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id (RL.liftFo φ h) (map fst γ))
    ∙ cong (λ ψ → (map fst γ) ⊨ᵥ ψ) (RL.liftFo-correct φ h)
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id φ (map fst γ)

-- THE OTHER SIDE OF THE FRAME.  𝒮ʟ IS 𝒮ᵥ ↾ isL, on the nose
-- (src/L/Constructible.lagda.md:411), and _↾_ takes the carrier
-- Σ[ x ∈ S ] (x ∈ᶜ M) (src/FOL/ZFStructure.lagda.md:145-146).  So the
-- Single instance below has SM = CS.S definitionally, its _⊨ᵛ_ IS the
-- _⊨ʟᵛ_ opened above, and its _⊨ᵐ_ IS satisfaction at 𝒮ʟ.
module AbsLʟ = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

open AbsLʟ using () renaming ( _⊨ᵐ_ to _⊨ʟᵐ_ )

module Gap (α : V ℓ) (ordα : IsOrd α) where

  open Seam α ordα public

  -- The environment correspondence.  A member of the stage is
  -- constructible, by Lset→isL (src/L/Constructible.lagda.md:395), so
  -- SL lands in CS.S and the underlying set never moves.
  intoL : SL → CS.S
  intoL c = fst c , Lset→isL α ordα (fst c) (snd c)

  map-intoL : ∀ {n} (γ : SL ^ n) → map fst (map intoL γ) ≡ map fst γ
  map-intoL [] = refl
  map-intoL (c ∷ γ) = cong (fst c ∷_) (map-intoL γ)

  -- THE BRIEFED STATEMENT, AS A TYPE.  The certificate is a parameter
  -- rather than a rebuild: [LJ-1.514] delivered one
  -- (agents/tasks/LJ-1-514/Probe514.agda:153-154), and this task must not
  -- rebuild graphFo-at-SL.  The type FORMS.  That is all it does.
  Transports : ∀ {n} (φ : Formula CS.S n) → BoundedFo (Below′ α) φ
             → Type (ℓ-suc (ℓ-suc ℓ))
  Transports {n} φ h = (γ : SL ^ n)
                     → (γ AbsL.⊨ᵐ RL.liftFo φ h) ≡ ((map intoL γ) ⊨ʟᵐ φ)

  -- WHAT THE TWO NAMED LAWS BUY, ONCE ABSOLUTENESS IS ADDED.  Stated at
  -- the generic carrier and for EVERY formula of the Δ₀ family, so the
  -- mathematics is written once (W2).  Four steps: abs₀ inward at the
  -- stage, the seam, abs₀ outward at L.
  transports-Δ₀ : ∀ {n} (φ : Formula CS.S n) → Δ₀ φ
                → (h : BoundedFo (Below′ α) φ) → Transports φ h
  transports-Δ₀ φ dφ h γ =
      AbsL.abs₀ (RL.Δ₀-liftFo h dφ) γ
    ∙ seam φ h γ
    ∙ sym (subst (λ δ → ((map intoL γ) ⊨ʟᵐ φ) ≡ (δ ⊨ʟᵛ φ))
                 (map-intoL γ)
                 (AbsLʟ.abs₀ dφ (map intoL γ)))

  -- AND THE ONE-DIRECTION FALLBACKS, for the same reason.
  transports-Σ₁ : ∀ {n} (φ : Formula CS.S n) → Σ₁ φ
                → (h : BoundedFo (Below′ α) φ) (γ : SL ^ n)
                → ⟨ (map intoL γ) ⊨ʟᵐ φ ⟩ → ⟨ (map fst γ) ⊨ʟᵛ φ ⟩
  transports-Σ₁ φ sφ h γ hm =
    subst (λ δ → ⟨ δ ⊨ʟᵛ φ ⟩) (map-intoL γ)
          (AbsLʟ.σ₁-up sφ (map intoL γ) hm)

-- THE GAP, MEASURED AND NOT READ.
--
-- Every route above is gated on a Levy witness for the formula, because
-- abs₀ is (src/FOL/Absoluteness.lagda.md:122) and so are σ₁-up and
-- π₁-down (src/FOL/Absoluteness.lagda.md:182,187).  Δ₀ has no constructor
-- for ∃̇ or ∀̇ (src/FOL/LevyHierarchy.lagda.md:47-57), and
-- LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ StepAt (suc w) (suc b) zero)
-- (src/L/Coding/Sequence.lagda.md:292 through :349).  So the three
-- witnesses are not merely unbuilt.  They are REFUTED, by absurd pattern,
-- and Agda checks the refutation.
no-Δ₀ : {n : ℕ} (w b : Fin n) → Δ₀ (LsetGraphAt w b) → ⊥* {ℓ}
no-Δ₀ w b ()

-- The lifted formula keeps the shape, so the stage side is refuted too.
-- This is the witness AbsL.abs₀ would need, and it is the one that blocks.
no-Δ₀-lifted : (α : V ℓ) (ordα : IsOrd α) {n : ℕ} (w b : Fin n)
             → (h : BoundedFo (Below′ α) (LsetGraphAt w b))
             → Δ₀ (Gap.RL.liftFo α ordα (LsetGraphAt w b) h) → ⊥* {ℓ}
no-Δ₀-lifted α ordα w b h ()

-- The Σ₁ prefix does not reach it either.  σ-∃ strips the one existential
-- LsetGraphAt starts with, and then the core must be Δ₀; but the core is
-- ApproxAt ∧̇ StepAt, and ApproxAt is domAt ∧̇ ∀̇ (∀̇ …)
-- (src/L/Coding/Sequence.lagda.md:286-289).  That ∀̇ is unbounded, so the
-- one-direction fallback transports-Σ₁ is unavailable at this formula.
no-Σ₁ : {n : ℕ} (w b : Fin n) → Σ₁ (LsetGraphAt w b) → ⊥* {ℓ}
no-Σ₁ w b (σ-Δ₀ ())
no-Σ₁ w b (σ-∃ (σ-Δ₀ (δ-∧ (δ-∧ _ ()) _)))

-- Π₁ prefixes universals, and LsetGraphAt begins with an existential, so
-- π-∀ never applies and the Δ₀ core is refuted above.  π₁-down is out too.
no-Π₁ : {n : ℕ} (w b : Fin n) → Π₁ (LsetGraphAt w b) → ⊥* {ℓ}
no-Π₁ w b (π-Δ₀ ())

-- THE BRIEFED OBLIGATION, AS A TYPE.  It FORMS, at any stage and for any
-- certificate.  It is NOT INHABITED HERE, and this probe writes no term
-- called graphSat-transports.  Every route the tree delivers from
-- AbsL.⊨ᵐ to _⊨ʟᵐ_ passes through a Levy witness for this formula, and
-- the three refutations above say there is none.
GraphSatTransports : (α : V ℓ) (ordα : IsOrd α) {n : ℕ} (w b : Fin n)
                   → BoundedFo (Below′ α) (LsetGraphAt w b)
                   → Type (ℓ-suc (ℓ-suc ℓ))
GraphSatTransports α ordα w b h =
  Gap.Transports α ordα (LsetGraphAt w b) h
