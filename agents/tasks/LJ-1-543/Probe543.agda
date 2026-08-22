{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.543]  B6, and whether it is the theorem or something cheaper.
--
-- SECTION 1 is W3: what `z` IS, from `z ∈ y` and `y ∈ 𝒫 κ`, at its
-- strongest delivered characterisation.  The brief ordered it written
-- first and typechecked ALONE.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-543.Probe543 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
import FOL.ZFModel
open import Cubical.Data.Sigma using ( _×_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier, the conclusion's carrier.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier.  `𝒮ʟ = 𝒮ᵥ ↾ isL` (src/L/Constructible.lagda.md:410-411), so
-- SL.S is Σ[ x ∈ SV.S ] ⟨ isL x ⟩ and SL._∈ˢ_ a b is DEFINITIONALLY
-- fst a ∈ˢ fst b (src/FOL/ZFStructure.lagda.md:149).
module SL = hPropStructure 𝒮ʟ

-- The same instance `src/L/GCH.lagda.md:29` names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  WHAT z IS.
--
--   The row hands `z` in through two doors and neither one is ambient:
--
--     `y ∈ˢ 𝒫 κ`   the L-model's power set (src/FOL/ZFModel.lagda.md:287-288)
--     `z ∈ˢ fst y` an AMBIENT membership, at the V-carrier
--
--   `𝒫 κ = ℩ (hasPower κ)` and `hasPower` realizes the class
--   `λ x → x ⊆ˢ κ` (src/FOL/ZFModel.lagda.md:199), where `⊆ˢ` is the
--   INTERNAL subset relation: it quantifies over SL.S and over nothing
--   else (src/FOL/ZFModel.lagda.md:141-142).  So the power-set hypothesis
--   only speaks about CONSTRUCTIBLE members of `y`, and `z` arrives
--   ambient.  The bridge between the two is transitivity of the class
--   `isL` (src/L/Constructible.lagda.md:379), and it is the ONE step
--   this section needs that is not a projection.
-- =====================================================================

-- THE CHARACTERISATION.  Everything the two hypotheses deliver about z.
zStrongest : ModelL.isZFModel → Type (ℓ-suc ℓ)
zStrongest zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩
  → (⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z)
  where open ModelL.isZFModel zf using ( 𝒫 )

z-strongest : (zf : ModelL.isZFModel) → zStrongest zf
z-strongest zf κ y ordκ y∈𝒫κ z z∈y = isLz , z∈κ , mem-ord {A = fst κ} ordκ z z∈κ
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )

  -- Door 1.  z is constructible, because y is and L is transitive.
  isLz : ⟨ isL z ⟩
  isLz = isL-trans z∈y (snd y)

  -- Door 2.  The power-set specification, read off `℩-spec`
  -- (src/FOL/ZFModel.lagda.md:123-124).  `𝒫 κ` IS `℩ (hasPower κ)` by
  -- definition, so no transport of the operation is needed.
  y⊆κ : ⟨ y ModelL.⊆ˢ κ ⟩
  y⊆κ = subst ⟨_⟩ (ModelL.℩-spec (hasPower κ) y) y∈𝒫κ

  -- And the two doors meet: z re-enters the internal subset relation
  -- as the L-element (z , isLz).
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = y⊆κ (z , isLz) z∈y

-- =====================================================================
-- SECTION 2.  THE WHOLE MATHEMATICAL CONTENT OF B6, AND IT IS A TOWER
-- LOOKUP.
--
--   W3 says `z` is an ORDINAL and a member of `fst κ`.  For such a `z`
--   the conclusion is the tower's own cumulation lemma and nothing
--   else.  This section takes NO model, NO power set, NO carrier of L
--   and NO cardinal: it is a statement about V and the stage function.
--
--   The two facts it spends:
--     `ord∈Lset-suc`  an ordinal is in the stage after it
--                     (src/L/Ordinal/Stages.lagda.md:434)
--     `Lset-cumul`    and then in every stage above
--                     (src/L/Ordinal/Stages.lagda.md:164-165)
-- =====================================================================

ord-below-lands : (κ : SV.S) → IsOrd κ → (z : SV.S) → ⟨ z ∈ˢ κ ⟩
                → ⟨ z ∈ˢ Lset κ ⟩
ord-below-lands κ ordκ z z∈κ =
  Lset-cumul z κ ordz ordκ z∈κ (ord∈Lset-suc z ordz)
  where
  ordz : IsOrd z
  ordz = mem-ord {A = κ} ordκ z z∈κ

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
--   `SubsetIntoStageAt` is `[LJ-1.523]`'s type, letter for letter
--   (agents/tasks/LJ-1-523/Probe523.agda:224-228).  The brief displays
--   the same Π-type with `𝒫` free; `𝒫` is a field of the model
--   (src/FOL/ZFModel.lagda.md:287-288), so the model must be bound, and
--   `[LJ-1.523]` binds it exactly here.  The term below is the brief's
--   ONE term and it inhabits that type at every model.
-- =====================================================================

SubsetIntoStageAt : ModelL.isZFModel → Type (ℓ-suc ℓ)
SubsetIntoStageAt zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

SubsetIntoStage : (zf : ModelL.isZFModel) → SubsetIntoStageAt zf
SubsetIntoStage zf κ y ordκ y∈𝒫κ z z∈y =
  ord-below-lands (fst κ) ordκ z z∈κ
  where
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = z-strongest zf κ y ordκ y∈𝒫κ z z∈y .snd .fst

-- =====================================================================
-- SECTION 4.  WHAT THE ROW DOES NOT NEED, MEASURED BY THE ELABORATOR
-- AND NOT CLAIMED IN A SENTENCE.
-- =====================================================================

-- 4.1  THE MODEL IS SURPLUS.  Replace the power-set membership by the
-- internal subset relation it realizes (src/FOL/ZFModel.lagda.md:199)
-- and `isZFModel` leaves the statement entirely.  So the row consumes
-- exactly one projection of the model and no axiom of it.
subset-is-all-the-power-set-gives :
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ y ModelL.⊆ˢ κ ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
subset-is-all-the-power-set-gives κ y ordκ y⊆κ z z∈y =
  ord-below-lands (fst κ) ordκ z (y⊆κ (z , isL-trans z∈y (snd y)) z∈y)

-- 4.2  AND `y` IS SURPLUS TOO, ONCE THE SUBSET FACT IS AMBIENT.  The
-- only work `y` does is to carry `⟨ isL (fst y) ⟩` into the internal
-- quantifier of `⊆ˢ`.  Hand the subset fact at the V-carrier and the
-- L-carrier disappears with it: this is `ord-below-lands` composed
-- with the hypothesis, and it is the row with every L-side term gone.
no-L-side-left :
    (κ : SV.S) → IsOrd κ → (y : SV.S)
  → ((w : SV.S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ κ ⟩)
  → (z : SV.S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ Lset κ ⟩
no-L-side-left κ ordκ y y⊆κ z z∈y = ord-below-lands κ ordκ z (y⊆κ z z∈y)

-- 4.3  NOTHING FROM `L.BoundedSubset` ENTERS.  The import list of this
-- file is the whole evidence: `L.BoundedSubset` is not imported, so
-- neither `Devlin55.BoundedSubsetAt` (src/L/BoundedSubset.lagda.md:
-- 1385-1395) nor its `levelIn` and `cover` (:1555-1557) can be behind
-- any line above.  `IsCardinal` does not appear either.

-- 4.4  THE ROW WRITTEN FRESH, AS ONE DECLARATION.  Clause W4 asks for
-- the price of the ideal form.  This is it: the same proof with every
-- intermediate name of sections 1 to 3 inlined, so the line count has
-- ONE site to be read off and no section boundary inflates it.  It
-- imports nothing that sections 1 to 3 did not already import.
b6-written-fresh : (zf : ModelL.isZFModel) → SubsetIntoStageAt zf
b6-written-fresh zf κ y ordκ y∈𝒫κ z z∈y =
  Lset-cumul z (fst κ) ordz ordκ z∈κ (ord∈Lset-suc z ordz)
  where
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = subst ⟨_⟩ (ModelL.℩-spec (ModelL.isZFModel.hasPower zf κ) y) y∈𝒫κ
          (z , isL-trans z∈y (snd y)) z∈y

  ordz : IsOrd z
  ordz = mem-ord {A = fst κ} ordκ z z∈κ
