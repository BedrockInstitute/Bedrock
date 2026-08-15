# The generalized continuum hypothesis, stated

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ

-- A7.  The GCH statement, in the shape of `ChoiceStatement`
-- (src/L/Choice/Transversal.lagda.md): a Type over the model, quantifying
-- over the L-carrier with `∈ˢ`, naming the internal cardinal `IsCardinalL`
-- (A4, delivered in src/L/Cardinal.lagda.md) and the ambient injection
-- `_↪_` (delivered in the same master).  The two leading hypotheses are
-- A5's conclusion type and A6's conclusion type, stated on the nose and
-- supplied by NOTHING in this master.

-- S3.  A5's conclusion type: the square law, uniformly over the infinite
-- L-ordinals.
SqShape : Type (ℓ-suc ℓ)
SqShape =
  (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
          → ⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫

-- S4.  A6's conclusion type: the successor absorption, uniformly over the
-- infinite L-ordinals that contain every numeral.
AbsorbsShape : Type (ℓ-suc ℓ)
AbsorbsShape =
  (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ˢ ω ⟩ → Empty.⊥)
          → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫

-- δ is the successor cardinal of κ: a cardinal above κ, and the least
-- cardinal above κ.
SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩ → (⟪ fst δ ⟫ ↪ ⟪ fst c ⟫))

-- S5.  THE STATEMENT.  `sq` and `absorbs` are the two hypotheses A5 and A6
-- discharge; neither is supplied here.  The conclusion is the GCH bound
-- `𝒫(κ) ↪ δ` at the successor cardinal δ of κ.
GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHStatement zf =
  (sq : SqShape)
  → (absorbs : AbsorbsShape)
  → (κ : S)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ]
       ( SuccCardL δ κ
       × (⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )
```
