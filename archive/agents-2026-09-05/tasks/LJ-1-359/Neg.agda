{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.359] NEGATIVE CONTROL.  The master's content verbatim
-- (src/L/CantorBernstein.lagda.md), with ONE corruption: in readL the
-- second and third components of the InjCode tuple are passed to the
-- Small readback in swapped order (dm where sv is expected).  A green
-- run of the master proves nothing until this file has gone red naming
-- the two satisfaction types.

open import Base.Prelude
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-359.Neg {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.CantorBernstein {ℓ} (lowerLEM lem)
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import L.GCH {ℓ} lem using ( InjL )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

setPL : (a : S) → isSet (⟪ fst a ⟫)
setPL a = small-set (fst a)

readL : (a b : S) → Σ[ F ∈ S ] InjCode F a b
      → Σ[ f ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
          ((x y : ⟪ fst a ⟫) → f x ≡ f y → x ≡ y)
readL a b (F , sv , dm , ij , ran) = SM.small , SM.small-inj
  where
  module SM = Small F a b dm sv ij ran

module MutualInjL = MutualInj S (λ a → ⟪ fst a ⟫)
  (λ a b → Σ[ F ∈ S ] InjCode F a b) setPL readL

mutual-inj→bijection : (a b : S) → InjL a b → InjL b a
  → ∥ Σ[ h ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
       (((x y : ⟪ fst a ⟫) → h x ≡ h y → x ≡ y)
     × ((y : ⟪ fst b ⟫) → ∥ Σ[ x ∈ ⟪ fst a ⟫ ] (h x ≡ y) ∥₁)) ∥₁
mutual-inj→bijection = MutualInjL.∃bijection
