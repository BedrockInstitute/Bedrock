{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import K7.ForcedFunctionValues

module Controls.Negative.MissingValueFunction
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (Cond Name : Type ℓ)
  (order : Cond → Cond → hProp ℓ)
  (R : ∀ {n} → Cond → Formula (⊥* {ℓ}) n → Vec Name n → hProp ℓ)
  (M E : Cond → Name → Name → hProp ℓ)
  where

open TruthAlgebra (hPropAlgebra ℓ)
module Values = K7.ForcedFunctionValues 𝒮 Cond Name order R M E

module AtClauses (C : Values.Clauses) where
  module Proof = Values.AtClauses C

  module AtOrder
    (order-refl : (p : Cond) → ⟨ order p p ⟩)
    (order-trans : (r q p : Cond)
      → ⟨ order r q ⟩ → ⟨ order q p ⟩ → ⟨ order r p ⟩)
    (mono : ∀ {n} (p q : Cond) (φ : Values.Src n) (ν : Vec Name n)
      → ⟨ order q p ⟩ → ⟨ R p φ ν ⟩ → ⟨ R q φ ν ⟩)
    (regular : ∀ {n} (p : Cond) (φ : Values.Src n) (ν : Vec Name n)
      → ⟨ Values.Dense p (λ r → R r φ ν) ⟩ → ⟨ R p φ ν ⟩)
    where

    module Result = Proof.AtOrder order-refl order-trans mono regular

    with-function : (p : Cond) (f x y z : Name)
      → ⟨ R p Proof.functionFo (f ∷ []) ⟩
      → ⟨ R p Proof.valueFo (x ∷ y ∷ f ∷ []) ⟩
      → ⟨ R p Proof.valueFo (x ∷ z ∷ f ∷ []) ⟩
      → ⟨ E p y z ⟩
    with-function = Result.forced-function-values

    -- Deliberately rejected: a forced graph value cannot fill the theorem's
    -- forced-function premise. All primitive clauses and order laws remain.
    missing-value-function : (p : Cond) (f x y z : Name)
      → ⟨ R p Proof.valueFo (x ∷ y ∷ f ∷ []) ⟩
      → ⟨ R p Proof.valueFo (x ∷ z ∷ f ∷ []) ⟩
      → ⟨ E p y z ⟩
    missing-value-function p f x y z hy hz =
      Result.forced-function-values p f x y z hy hy hz
