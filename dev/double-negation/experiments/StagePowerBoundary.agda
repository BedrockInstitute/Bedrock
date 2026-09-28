{-# OPTIONS --cubical --safe --guardedness #-}
module StagePowerBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import ModalTrees using (NN; mapNN; bindNN)

module StageSystem {s b p : Level}
  (S : Type s) (B : Type b) (Mem : S → S → Type p) (stage : B → S)
  (stage-transitive : (β : B) (x y : S) → Mem x y → Mem y (stage β) → Mem x (stage β))
  (stage-cover : (x : S) → NN (Σ[ β ∈ B ] Mem x (stage β))) where

  Subset : S → S → Type (ℓ-max s p)
  Subset x a = (z : S) → Mem z x → Mem z a

  Power : S → Type (ℓ-max s p)
  Power a = Σ[ power ∈ S ] ((x : S) →
    (Mem x power → Subset x a) × (Subset x a → Mem x power))

  StageBound : S → Type (ℓ-max (ℓ-max s p) b)
  StageBound a = Σ[ β ∈ B ] ((x : S) → Subset x a → Mem x (stage β))

  StageSeparation : Type (ℓ-max (ℓ-max s p) b)
  StageSeparation = (a : S) (β : B) → NN (Σ[ power ∈ S ] ((x : S) →
    (Mem x power → Mem x (stage β) × Subset x a) ×
    (Mem x (stage β) × Subset x a → Mem x power)))

  power-to-bound : (a : S) → Power a → NN (StageBound a)
  power-to-bound a (power , spec) = mapNN
    (λ { (β , contains-power) → β , λ x sub →
      stage-transitive β x power (spec x .snd sub) contains-power })
    (stage-cover power)

  bound-to-power : StageSeparation → (a : S) → StageBound a → NN (Power a)
  bound-to-power separate a (β , bound) = mapNN
    (λ { (power , spec) → power , λ x →
      (λ member → spec x .fst member .snd) ,
      (λ sub → spec x .snd (bound x sub , sub)) }) (separate a β)

  negative-power-to-bound : (a : S) → NN (Power a) → NN (StageBound a)
  negative-power-to-bound a n = bindNN n (power-to-bound a)

  negative-bound-to-power : StageSeparation → (a : S)
    → NN (StageBound a) → NN (Power a)
  negative-bound-to-power separate a n = bindNN n (bound-to-power separate a)

  pointwise-to-common-stage : ∀ {q}
    → (stable : (x : S) (β : B) → NN (Mem x (stage β)) → Mem x (stage β))
    → (Small : B → Type q) → (δ : B)
    → ((β : B) → Small β → (x : S) → Mem x (stage β) → Mem x (stage δ))
    → (a : S)
    → ((x : S) → Subset x a → NN (Σ[ β ∈ B ] (Small β × Mem x (stage β))))
    → StageBound a
  pointwise-to-common-stage stable Small δ upper a each = δ , λ x sub →
    stable x δ (mapNN (λ { (β , small , member) → upper β small x member })
      (each x sub))
