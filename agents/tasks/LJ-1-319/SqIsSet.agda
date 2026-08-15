{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.319] RULING PROBE.  One measurement: `sq alpha` is a SET.
--
-- [LJ-1.316] section 2.5 names the `rec→Set` door and marks its
-- precondition INFERRED: "`sq α` is a set ... INFERRED, not typechecked".
-- This file upgrades that precondition to MEASURED.  With it, the maps
-- `∥ Wat α ∥₁ → sq α` are exactly the `2-Constant` maps `Wat α → sq α`
-- (`trunc→Set≃`, cubical library
-- Cubical/HITs/PropositionalTruncation/Properties.agda:225).
--
-- Tracked probe.  ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-319.SqIsSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; _∈ₛ_; presentation )
open import Cubical.Foundations.HLevels
  using ( isSetΣ; isSetΣSndProp; isSetΠ; isPropΠ3; isSet×;
          isOfHLevelRespectEquiv )

-- The carrier of a V-set is a set: `presentation` exhibits it as a
-- subtype of V, and V is a set.
carrier-set : (a : V ℓ) → isSet ⟪ a ⟫
carrier-set a = isOfHLevelRespectEquiv 2 (presentation a)
  (isSetΣSndProp setIsSet (λ v → snd (v ∈ₛ a)))

-- The door's precondition, MEASURED by this file: `sq alpha` is a set.
-- The first component is a function into a set; the second is a
-- proposition, because paths in a set are propositions.
sq-set : (α : V ℓ) → isSet (sq α)
sq-set α = isSetΣ
  (isSetΠ (λ _ → carrier-set α))
  (λ f → isProp→isSet (isPropΠ3 (λ x y _ →
    isSet× (carrier-set α) (carrier-set α) x y)))
