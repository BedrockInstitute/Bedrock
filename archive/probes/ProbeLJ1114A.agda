{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.114] probe A: the count is NOT injective across two honest
-- injections of the same carrier.
--
-- The threading of [LJ-1.111] makes LimitStep's per-step induction
-- hypothesis truncated:  ih : (m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫
-- ↪ ⟪ α ⟫ ∥₁.  The honest least-code construction (LimitStep.h /
-- h-inj) compares two witnesses of the code class, and each witness
-- carries its own honest injection extracted from its own truncation.
-- The count of a formula's constants through the injection (Bound's
-- tuple-g) is injective PER INJECTION, but NOT across two different
-- injections:  with K = Fin 2, α = ω, and g₁, g₂ two injections of K
-- into ⟪ ω ⟫ that swap the two elements, the tuples
--   tuple-g g₁ 2 (a ∷ a ∷ [])   and   tuple-g g₂ 2 (b ∷ b ∷ [])
-- are EQUAL while (a ∷ a ∷ []) ≠ (b ∷ b ∷ []).  The code value
-- therefore does not determine the formula across independently
-- chosen honest injections, and the injectivity step of LimitStep's
-- h-inj (cnt-inj m₁ on two witnesses) cannot be written.  The master
-- refusal is at src/L/StageCardinal.lagda.md:412 (g₂' != g₁), and
-- this probe shows the mathematical fact behind it.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1114A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ1106A {ℓ} lem as P106
open P106 using ( module NumeralPresentation )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.FinData.Base using ( Fin; zero; suc; toℕ )
open import Cubical.Data.FinData.Properties using ( inj-toℕ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Properties using ( znots )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty

open NumeralPresentation

-- The carrier: two elements.
K : Type
K = Fin 2

a : K
a = zero

b : K
b = suc zero

a≠b : a ≡ b → Empty.⊥
a≠b p = znots (cong toℕ p)

-- The two honest injections into ⟪ ω ⟫, swapping the two elements.
g₁ : K → ⟪ ω ⟫
g₁ i = numeralω (toℕ i)

g₁-inj : (i j : K) → g₁ i ≡ g₁ j → i ≡ j
g₁-inj i j e = inj-toℕ {k = i} {l = j} (numeralω-inj (toℕ i) (toℕ j) e)

sw : Fin 2 → ℕ
sw zero = 1
sw (suc zero) = 0

g₂ : K → ⟪ ω ⟫
g₂ i = numeralω (sw i)

g₂-inj : (i j : K) → g₂ i ≡ g₂ j → i ≡ j
g₂-inj zero zero _ = refl
g₂-inj zero (suc zero) e = Empty.rec (znots (sym (numeralω-inj 1 0 e)))
g₂-inj (suc zero) zero e = Empty.rec (znots (numeralω-inj 0 1 e))
g₂-inj (suc zero) (suc zero) _ = refl

inj₁ : Σ[ f ∈ (K → ⟪ ω ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y)
inj₁ = g₁ , g₁-inj

inj₂ : Σ[ f ∈ (K → ⟪ ω ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y)
inj₂ = g₂ , g₂-inj

-- The g-dependent tuple code, exactly Bound's tuple-g at β = ω.
pairω2 : ⟪ ω ⟫ → ⟪ ω ⟫ → ⟪ ω ⟫
pairω2 x y = NumeralPresentation.pairω (x , y)

tuple-g : (g : Σ[ f ∈ (K → ⟪ ω ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
        → (k : ℕ) → Vec K k → ⟪ ω ⟫
tuple-g g zero [] = numeralω 0
tuple-g g (suc k) (x ∷ xs) = pairω2 (fst g x) (tuple-g g k xs)

-- The collision: the tuple of (a ∷ a ∷ []) under g₁ equals the tuple
-- of (b ∷ b ∷ []) under g₂, while the tuples differ.
collision : tuple-g inj₁ 2 (a ∷ a ∷ []) ≡ tuple-g inj₂ 2 (b ∷ b ∷ [])
collision = refl

tuples-differ : (a ∷ a ∷ []) ≡ (b ∷ b ∷ []) → Empty.⊥
tuples-differ p = a≠b (cong head p)
  where
  head : Vec K 2 → K
  head (x ∷ _) = x

-- So the honest code is not injective across independently chosen
-- injections:  cnt g₁ φ₁ ≡ cnt g₂ φ₂ does not imply φ₁ ≡ φ₂, and
-- LimitStep's h-inj cannot be written with per-witness honest data.
