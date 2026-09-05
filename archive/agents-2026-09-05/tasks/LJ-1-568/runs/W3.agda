{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.568]  W3.  THE `g` AT [LJ-1.561]'s `w→B9` CALL SITE, ITS TYPE
--                  WRITTEN OUT.  TYPE ONLY.
--
-- THE BRIEF'S W3, VERBATIM: "the g at [LJ-1.561]'s w→B9 call site, its
-- type written out, TYPE ONLY".  Written FIRST and typechecked ALONE,
-- before any other Agda of this task, because the restriction has to be
-- true OF THAT `g` and there is no point inventing one before looking
-- at it.
--
-- NO TERM BELOW IS A PROOF OF ANYTHING MISSING.  Every declaration is
-- an ASCRIPTION of a term already delivered in src/, or a type.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-568.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( _↪_ )
import L.StageCardinal

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- [LJ-1.536]'s one-liner, re-typed the way Probe561.agda:110-111 does.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- ===================================================================
-- 1.  THE TWO L-SETS `w→B9` HANDS TO `w→code`.
--     Probe561.agda:379-381 applies `w→code w (LsetS δ oδ) (δ , isL-ord
--     δ oδ)`, so `a` and `b` are these two and nothing else.
-- ===================================================================

B9-a : (δ : V ℓ) → IsOrd δ → S
B9-a δ oδ = LsetS δ oδ

B9-b : (δ : V ℓ) → IsOrd δ → S
B9-b δ oδ = δ , isL-ord δ oδ

-- ===================================================================
-- 2.  THE `g` ITSELF.  `w→code`'s third argument is a `⟪ fst a ⟫ ↪
--     ⟪ fst b ⟫`, and at this site it is `SC.Upper.stage-card-upper`
--     applied to the site's four arguments (Probe561.agda:381).
--
--     THE TYPE WRITTEN OUT.  `fst (B9-a δ oδ)` is `Lset δ` and
--     `fst (B9-b δ oδ)` is `δ`, so the function is
--
--         ⟪ Lset δ ⟫ → ⟪ δ ⟫
--
--     from the members of the δ-th stage of L to the members of the
--     ordinal δ, injective, with TWO SIDE CONDITIONS on δ and no
--     condition of any kind on the function.
-- ===================================================================

B9-g-type : Type (ℓ-suc ℓ)
B9-g-type =
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
  → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ g ∈ (⟪ Lset δ ⟫ → ⟪ δ ⟫) ]
      ((k k' : ⟪ Lset δ ⟫) → g k ≡ g k' → k ≡ k')

-- AND IT IS INHABITED BY THE DELIVERED TERM, NOT BY ME.
-- src/L/StageCardinal.lagda.md:564-566.
B9-g : B9-g-type
B9-g = SC.Upper.stage-card-upper

-- THE SAME TERM AT THE CARRIERS `w→code` NAMES, so that the two
-- readings are checked to be one and not quoted to be one.
B9-g-at-site :
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
  → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → ⟪ fst (B9-a δ oδ) ⟫ ↪ ⟪ fst (B9-b δ oδ) ⟫
B9-g-at-site = SC.Upper.stage-card-upper

-- ===================================================================
-- 3.  WHAT THE SITE CARRIES BESIDE THE FUNCTION.  This is the whole
--     list, and it is the list any restriction must be discharged
--     from.  `w→B9` (Probe561.agda:376-381) binds exactly these.
-- ===================================================================

B9-side-conditions : (δ : V ℓ) → IsOrd δ → Type (ℓ-suc ℓ)
B9-side-conditions δ oδ =
    ⟨ δ SV.∈ˢ sucV α₀ ⟩                    -- δ is at most α₀
  × (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)              -- δ is infinite

-- ===================================================================
-- 4.  AND THE ONE FACT THIS SLICE WAS WRITTEN TO SEE.
--
--     `stage-card-upper` IS A TERM OF THIS MODULE, AND THIS MODULE
--     TAKES `sq` AS A PARAMETER.  `sq` is an ARBITRARY ambient pairing
--     injection on every infinite δ ≤ α₀ (src/L/StageCardinal.lagda.md:15-19,
--     and the module header of this file repeats it).  So the `g` at
--     the B9 site is not one function: it is a function OF `sq`, and
--     `sq` carries no formula, no stage and no `isL`.
--
--     The row below says that in a type: the site's `g` is available
--     for EVERY `sq` the module admits, because `sq` is a parameter.
-- ===================================================================

B9-g-depends-on-sq : Type (ℓ-suc ℓ)
B9-g-depends-on-sq = B9-g-type   -- inhabited, above, once `sq` is fixed
