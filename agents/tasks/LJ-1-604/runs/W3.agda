{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-604]  W3.  THE WIDEST UNMEASURED TERM: can ingredient (iii) and
-- `sq` be written in one file at all.  TYPE ONLY, and nothing else.
--
-- The brief: "Write it FIRST, typecheck it ALONE, cap it."  Estimated
-- about 15 lines under a two-minute cap.
--
-- OBJECT ONE is `sq` itself, the module parameter, and it is IMPORTED
-- and not restated: `SqParam` is [LJ-1.594]'s green transcription
-- (agents/tasks/LJ-1-594/runs/W3.agda:26-31) of
-- src/L/StageCardinal.lagda.md:17-19, and importing that file
-- re-elaborates its own check that `L.StageCardinal` accepts the type.
--
-- OBJECT TWO is ingredient (iii) at ONE site.  [LJ-1.594]'s table row
-- (iii) names `fst (sq α α∈suc infα)`
-- (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:42); the site
-- also spends the injectivity half through `B.pair-inj`
-- (src/L/StageCardinal.lagda.md:382), so the ingredient is the whole
-- package below.  The tree already carries this type under its own name
-- `sq` at src/L/Ordinal/SquareLaw.lagda.md:685-688; the probe ties the
-- two names together by `refl`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-604.runs.W3 {ℓ : Level} where

open import Cubical.Data.Sigma using ( _×_ )
open import LJ-1-594.runs.W3 using ( SqParam )
open InfinitySet {ℓ} using ( sucV; ω )

-- W3.1  OBJECT TWO: the ingredient at one site.  `sq` applied at α has
--       exactly this type, and nothing narrower: one binary function on
--       the members of α, with its injectivity.
Ing3 : V ℓ → Type ℓ
Ing3 α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
           ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- W3.2  THE FIRST CONVERSION ROW.  The parameter DELIVERS the
--       ingredient at every site of its band.  If `Ing3` drifted by one
--       character from what `sq`'s codomain is at α, this ascription
--       would not elaborate.
site-gets : (α₀ : V ℓ) (sq : SqParam α₀) (α : V ℓ)
          → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥) → Ing3 α
site-gets α₀ sq α α∈suc infα = sq α α∈suc infα

-- W3.3  THE SECOND CONVERSION ROW.  The parameter IS the product of the
--       ingredient over the whole band, and it carries NOTHING else: no
--       coherence between two sites, no uniformity, no definability.
sq-is-product : (α₀ : V ℓ)
              → SqParam α₀
                ≡ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩
                    → (⟨ δ ∈ ω ⟩ → Empty.⊥) → Ing3 δ)
sq-is-product α₀ = refl
