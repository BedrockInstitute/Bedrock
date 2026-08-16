{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.355] NEGATIVE CONTROL B.  The corollary's conclusion carries a
-- truncation.  This control measures that the truncation is FORCED: it
-- claims the same conclusion untruncated, from the same truncated
-- hypotheses.  Expected: rejection, a truncation cannot be eliminated
-- into the data a function is.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-355.NegB {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.CantorBernstein {ℓ} (lowerLEM lem)
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import L.GCH {ℓ} lem using ( InjL )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
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
  module SM = Small F a b sv dm ij ran

module MI = MutualInj S (λ a → ⟪ fst a ⟫) (λ a b → Σ[ F ∈ S ] InjCode F a b)
  setPL readL

-- The untruncated claim.  It must fail: the hypotheses are truncations,
-- and their elimination target would not be a proposition.
bad : (a b : S) → InjL a b → InjL b a
    → Σ[ h ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
         (((x y : ⟪ fst a ⟫) → h x ≡ h y → x ≡ y)
       × ((y : ⟪ fst b ⟫) → ∥ Σ[ x ∈ ⟪ fst a ⟫ ] (h x ≡ y) ∥₁))
bad = MI.∃bijection
