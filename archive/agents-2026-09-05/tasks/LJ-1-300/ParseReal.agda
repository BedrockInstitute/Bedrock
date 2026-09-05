{-# OPTIONS --cubical --safe --guardedness #-}
-- [LJ-1.300] DD25 review probe.  It tests the REAL `SqShape`, imported
-- from `L.GCH` under `L.GCH`'s own imports and module telescope.  It
-- does not restate the type and it does not define its own `_↪_`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-300.ParseReal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.GCH {ℓ} lem using ( SqShape )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- TEST 1.  The REAL `SqShape`, applied and projected with `.snd`.
-- This typechecks only if `↪` binds tighter than `×` at the real site,
-- so that the body is `⟪ fst α ⟫ × (⟪ fst α ⟫ ↪ ⟪ fst α ⟫)`.
realSnd : SqShape → (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
        → ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
realSnd sq α oα h = sq α oα h .snd

-- TEST 2.  The REAL `SqShape`, applied and projected with `.fst`.
-- This typechecks only if the first component is one carrier element,
-- and not the pair type `⟪ fst α ⟫ × ⟪ fst α ⟫` the reader expects.
realFst : SqShape → (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
        → ⟪ fst α ⟫
realFst sq α oα h = sq α oα h .fst

-- An ordinal outside omega holds a member, by trichotomy.
mem : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ (# 0) ∈ˢ α ⟩
mem α oα nfin = go (ord-tri α oα ω (ω-ord))
  where
  go : (⟨ α ∈ˢ ω ⟩ ⊎ ((α ≡ ω) ⊎ ⟨ ω ∈ˢ α ⟩)) → ⟨ (# 0) ∈ˢ α ⟩
  go (inl a∈ω) = Empty.rec (nfin a∈ω)
  go (inr (inl e)) = subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) (sym e) (#∈ω 0)
  go (inr (inr ω∈α)) = oα .fst (#∈ω 0) ω∈α

-- TEST 3.  THE REAL `SqShape` IS INHABITED OUTRIGHT.  No square law is
-- used.  The witness is one carrier element paired with the identity.
-- The trophy's one remaining hypothesis, as it stands in `src/` today,
-- gates nothing.
realTrivial : SqShape
realTrivial α oα nfin =
  (fiber (fst α) (mem (fst α) oα nfin) .fst , ((λ x → x) , (λ x y e → e)))

-- TEST 4.  WHAT THE FIX WOULD SAY.  With the parentheses in place, the
-- body of `SqShape` is JUDGMENTALLY the tree's own delivered square law
-- `L.Ordinal.SquareLaw.sq` (src/L/Ordinal/SquareLaw.lagda.md:685-687).
-- `refl` typechecks, so no `subst` and no wrapper stand between them.
-- The intended statement is already in the tree, one file away.
sq-same : (α : S) → ((⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫) ≡ sq (fst α)
sq-same α = refl
