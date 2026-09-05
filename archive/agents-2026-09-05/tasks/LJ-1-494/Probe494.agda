{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.494] PROBE.  GraphSatAtStage, the defines direction of the
-- level graph at AbsL.𝒮M.  It runs in agents/tasks/LJ-1-494/ and
-- lands nothing in src/.
--
--   STEP ONE, W3 FIRST  hier-in-stage.  Obligation omitted.
--                       Stage membership of the approximation.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-494.Probe494 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; IsOrd )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- Telescope: one stage. AtStage is opened so SL is in scope. W3
-- does not use it. The obligation type does not form at AbsL.𝒮M
-- (Formula CS.S against Formula SL).

module StageWorld (α : S) (ordα : IsOrd α) where

  module ASt = AtStage α ordα
  -- AbsL is a nested module, not an export of AtStage.
  -- SL = AbsL.SM (src/L/Hull.lagda.md:153-156).
  open ASt using ( SL )

  -- W3. The brief's spelling
  --   ⟨ hierL (fst δ) _ _ ∈ˢ Lset α ⟩
  -- does not form: hierL returns CS.S (src/L/Hierarchy.lagda.md:621)
  -- and 𝒮ᵥ's ∈ˢ takes S (src/FOL/ZFStructure.lagda.md:48). The
  -- intended membership is the first projection. The isL witness
  -- is δ .snd, which CS.S carries. No postulate. No term.

  hier-in-stage : Type (ℓ-suc ℓ)
  hier-in-stage =
      (δ : CS.S) (oδ : IsOrd (fst δ))
    → ⟨ fst δ ∈ˢ Lset α ⟩
    → ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset α ⟩

  -- The brief's GraphSatAtStage does not form as a type:
  --   Lset-at is not a name in src/ (grep: the brief only).
  --   LsetGraphAt : Formula CS.S n
  --     (src/L/Coding/Sequence.lagda.md:349).
  --   AbsL.⊨ᵐ takes Formula SL n, with
  --     SL = Σ[ x ∈ S ] ⟨ x ∈ˢ Lset α ⟩
  --     (src/L/Hull.lagda.md:153-156, src/FOL/ZFStructure.lagda.md:146).
  --   mapFo from CS.S to SL is a total map from L into Lset α.
  --   No such map. The brief forbids a reflection hypothesis.
  -- The existential of GraphAt still needs hier-in-stage even if
  -- the formula were rewritten. UNBUILT. Not a hypothesis.

  GraphSatAtStage : Type (ℓ-suc ℓ)
  GraphSatAtStage = hier-in-stage

  -- LsetGraphAt is in scope so the carrier mismatch is a checked
  -- import, not a comment. It is not applied. SL is the stage
  -- carrier AbsL.𝒮M would interpret into. Formula CS.S is not
  -- Formula SL.
  private
    graphAtArity2 : Formula CS.S 2
    graphAtArity2 = LsetGraphAt zero (suc zero)
    stageCarrier : Type (ℓ-suc ℓ)
    stageCarrier = SL
