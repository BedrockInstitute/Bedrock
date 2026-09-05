# The coded shift

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.CodedShift {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Absorption {ℓ} lem using ( module ShiftGraph )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import Cubical.Data.Sigma using ( Σ≡Prop )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

-- Four conjuncts are ShiftGraph exports
-- (src/L/Absorption.lagda.md:452-498, opened publicly at :604-605).
-- Domain D is sucV (fst γ) with a transported isL; sucʟ γ agrees on
-- fst by sucʟ-fst.  InjCode sees the assignment, so the tuple moves
-- by Σ≡Prop.  No extra hypothesis.  No postulate.

shift-coded :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁
shift-coded γ oγ γ∉ω numerals = ∣ SG.G , code ∣₁
  where
  module SG = ShiftGraph γ oγ γ∉ω numerals

  codeD : InjCode SG.G SG.D γ
  codeD = SG.sv , SG.dm , SG.ij , SG.ran

  D≡suc : SG.D ≡ sucʟ γ
  D≡suc = Σ≡Prop (λ x → snd (isL x)) (sym (sucʟ-fst γ))

  code : InjCode SG.G (sucʟ γ) γ
  code = subst (λ a → InjCode SG.G a γ) D≡suc codeD
```
