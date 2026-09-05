{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.432] PROBE.  Does case four close when d is an ordinal whose
-- arrow is data by construction, rather than the ambient least
-- cardinal?
--
--   W3 FIRST  `kappaC-not-fin`.  Infinitude of κC from the DATA
--              arrow.  Typechecked ALONE, obligation omitted.
--
--   TERM      `descent-case4-coded`.  Case four of the 421 split,
--              with d := κC.  Membership is a hypothesis.  The arrow
--              is κC-arrow.  sq at κC is the IH plus W3.
--
--   MODULE HYPOTHESES.  κC, κC-ord, κC∈suc, κC-arrow.  Sealed in the
--              shape [LJ-1.421] seals κL at Probe421.agda:125-135.
--              The arrow is data, not truncated.  Nothing inhabited.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-432.Probe432 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import Cubical.Data.Sigma using ( ΣPathP )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SMALL DELIVERED-FACT HELPERS, rebuilt from src/ primitives.
-- Same as [LJ-1.421] Probe421.agda:62-82.  Not imported.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

mem-incl : (d k : V ℓ) → IsOrd d → ⟨ k ∈ d ⟩ → ⟪ k ⟫ ↪ ⟪ d ⟫
mem-incl d k od k∈d = ι , ι-inj
  where
  raise : (m : ⟪ k ⟫) → ⟨ ⟪ k ⟫↪ m ∈ d ⟩
  raise m = fst od (member k m) k∈d

  ι : ⟪ k ⟫ → ⟪ d ⟫
  ι m = fst (fiber d (raise m))

  ι-inj : (m n : ⟪ k ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = k}
    (sym (snd (fiber d (raise m)))
     ∙ cong (⟪ d ⟫↪) e
     ∙ snd (fiber d (raise n)))

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- =====================================================================
-- PART 1.  descent-data, rebuilt from Probe421.agda:89-118.
-- Generic in d.  Nothing in its type names a least cardinal.
-- =====================================================================

descent-core : (δ κ : S)
             → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
             → sq (fst κ)
             → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫
             → sq (fst δ)
descent-core δ κ incl (g , g-inj) down = f , f-inj
  where
  f : ⟪ fst δ ⟫ × ⟪ fst δ ⟫ → ⟪ fst δ ⟫
  f (x , y) = fst incl (g (fst down x , fst down y))

  f-inj : (p q : ⟪ fst δ ⟫ × ⟪ fst δ ⟫) → f p ≡ f q → p ≡ q
  f-inj (x₁ , y₁) (x₂ , y₂) e = ΣPathP (ex , ey)
    where
    step : (fst down x₁ , fst down y₁) ≡ (fst down x₂ , fst down y₂)
    step = g-inj _ _ (snd incl _ _ e)

    ex : x₁ ≡ x₂
    ex = snd down x₁ x₂ (cong fst step)

    ey : y₁ ≡ y₂
    ey = snd down y₁ y₂ (cong snd step)

descent-data : (x d : S) (ox : IsOrd (fst x))
             → ⟨ fst d ∈ˢ fst x ⟩
             → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
             → sq (fst d)
             → sq (fst x)
descent-data x d ox d∈x down sqd =
  descent-core x d (mem-incl (fst x) (fst d) ox d∈x) sqd down

-- =====================================================================
-- The coded selection, sealed as a module hypothesis in the shape
-- [LJ-1.421] seals κL at Probe421.agda:125-135.  The arrow is DATA.
-- κC, κC-ord, κC∈suc, κC-arrow are owed.  None is inhabited here.
-- =====================================================================

module _
  (κC       : (a : S) (oa : IsOrd (fst a)) → S)
  (κC-ord   : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κC a oa)))
  (κC∈suc   : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κC a oa) ∈ sucV (fst a) ⟩)
  (κC-arrow : (a : S) (oa : IsOrd (fst a)) → ⟪ fst a ⟫ ↪ ⟪ fst (κC a oa) ⟫)
  where

  -- =====================================================================
  -- W3.  kappaC-not-fin.  Infinitude of κC from the DATA arrow.
  -- Probe421.agda:164-180 spends the truncated κ-injL through PT.rec.
  -- The data arrow skips the truncation.  Typechecked ALONE before
  -- the obligation was added.
  -- =====================================================================

  kappaC-not-fin :
      (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
    → (⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ ω ⟩ → Empty.⊥)
  kappaC-not-fin x ox ω∈x κ∈ω =
    finite-excl-ω (fst κ) oκ κ∈ω
      (λ t → fst ω↪κ t , fst ω↪κ t)
      (λ t u e → snd ω↪κ t u (cong fst e))
    where
    a : S
    a = x , isL-ord x ox
    κ : S
    κ = κC a ox
    oκ : IsOrd (fst κ)
    oκ = κC-ord a ox
    ω↪κ : ⟪ ω ⟫ ↪ ⟪ fst κ ⟫
    ω↪κ = comp-inj (mem-incl x ω ox ω∈x) (κC-arrow a ox)

  -- =====================================================================
  -- THE OBLIGATION.  Case four only.  d := κC.  Membership is the
  -- hypothesis.  The arrow is κC-arrow.  sq at κC is the IH at
  -- κC-ord and kappaC-not-fin.  Case three is not written.
  -- =====================================================================

  descent-case4-coded :
      (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
    → ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x
  descent-case4-coded x ox ω∈x κ∈x ih =
    descent-data a κ ox κ∈x (κC-arrow a ox) sqκ
    where
    a : S
    a = x , isL-ord x ox
    κ : S
    κ = κC a ox
    sqκ : sq (fst κ)
    sqκ = ih (fst κ) κ∈x (κC-ord a ox) (kappaC-not-fin x ox ω∈x)
