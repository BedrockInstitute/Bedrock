# The stage-arithmetic kit

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.StageArith {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Pointwise inclusion at the big membership, as the ordinal chapters read it.
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

-- The finite successor chain above a stage.
sucIter : ℕ → S → S
sucIter zero u = u
sucIter (suc n) u = sucV (sucIter n u)

-- The ω-block above a stage: the union of the finitely iterated successors.
-- The union representation is sealed at birth (R-38). Consumers see an atom.
opaque
  +ω : S → S
  +ω u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u))

opaque
  unfolding +ω

  -- One direction: a member of a finite iterate is a member of the block.
  +ω-in : (u x : S) → (n : ℕ) → ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω u ⟩
  +ω-in u x n x∈ = ∈∈ₛ {a = x} {b = +ω u} .snd
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .snd
      ∣ sucIter (suc n) u , (memb , x∈ₛ) ∣₁)
    where
    F : Lift {ℓ-zero} {ℓ} ℕ → S
    F m = sucIter (suc (lower m)) u
    memb : ⟨ sucIter (suc n) u ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩
    memb = ∈∈ₛ {a = sucIter (suc n) u} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .fst
      ∣ lift n , refl ∣₁
    x∈ₛ : ⟨ x ∈ₛ sucIter (suc n) u ⟩
    x∈ₛ = ∈∈ₛ {a = x} {b = sucIter (suc n) u} .fst x∈

  -- The base and every finite iterate lie in the block.
  +ω-mem : (u : S) → ⟨ u ∈ˢ +ω u ⟩
  +ω-mem u = +ω-in u u 0 (self∈sucV u)

  +ω-sup : (u : S) → u ⊆ +ω u
  +ω-sup u x x∈u = +ω-in u x 0 (∈sucV-inl x∈u)

  +ω-iter : (n : ℕ) → (u : S) → ⟨ sucIter n u ∈ˢ +ω u ⟩
  +ω-iter n u = +ω-in u (sucIter n u) n (self∈sucV (sucIter n u))

  -- Ordinality: each iterate is an ordinal, and the block is an ordinal.
  sucIter-ord : {u : S} → (n : ℕ) → IsOrd u → IsOrd (sucIter n u)
  sucIter-ord zero ou = ou
  sucIter-ord (suc n) ou = suc-ord (sucIter-ord n ou)

  +ω-ord : (u : S) → IsOrd u → IsOrd (+ω u)
  +ω-ord u ou = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ)
    (λ m → sucIter (suc (lower m)) u) (λ m → sucIter-ord (suc (lower m)) ou)

-- Closure under +ω: the ω-block above every member stays inside α.
closedω : S → Type (ℓ-suc ℓ)
closedω α = (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ +ω d ∈ˢ α ⟩

-- The code set over the carrier at δ sits at stage δ+ω. Under closure, the
-- stage δ+ω stays below α for every δ below α, so the bound lands in Lset α.
boundCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
            → (b : S) → ⟨ b ∈ˢ Lset (+ω δ) ⟩ → ⟨ b ∈ˢ Lset α ⟩
boundCloses α δ cl δ∈α b b∈ =
  Lset-mono {α = α} {β = +ω δ} (cl δ δ∈α) b∈

-- The environment at δ+3 lifts by the finite-iterate law, then by closure.
envCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
          → (env : S) → ⟨ env ∈ˢ Lset (sucIter 3 δ) ⟩ → ⟨ env ∈ˢ Lset α ⟩
envCloses α δ cl δ∈α env env∈ =
  Lset-mono {α = α} {β = +ω δ} (cl δ δ∈α)
    (Lset-mono {α = +ω δ} {β = sucIter 3 δ} (+ω-iter 3 δ) env∈)
```
