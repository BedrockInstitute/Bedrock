{-# OPTIONS --cubical --safe --guardedness #-}
module SameLevel where

open import Cubical.Foundations.Prelude
open import Boundary using (LargeSheaf)

same-level : ∀ {ℓ} → Type ℓ → Type ℓ
same-level X = LargeSheaf X
