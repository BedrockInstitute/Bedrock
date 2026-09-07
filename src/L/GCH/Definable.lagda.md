# A definable injection is a coded injection

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Definable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion ) renaming ( module Graph to RecursionGraph )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

## Section 1. The form

A function on the members of a set of L, landing in a set of L, whose graph an
object-language formula defines: the formula holds of the function's own value
(`defines`) and of nothing else (`only`). Value first, index second, as
`Recursion.graph`.

```agda
record DefinableMap : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom cod : S
    fn      : (x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → S
    into    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) → ⟨ fst (fn x m) ∈ˢ fst cod ⟩
    graph   : Formula S 2
    defines : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩)
            → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
```

## Section 2. The pair formula

## Section 3. The graph as a set of L, and three conjuncts

`Recursion.funct` takes the membership proof, so `fn` fills it as it stands: no
total extension off `dom` and no use of `lem`. The table is the replacement
image (src/L/Recursion.lagda.md, `Of`).

```agda
module Graph (M : DefinableMap) where
  open DefinableMap M public
```

The recursion graph supplies the pair table, its readers, and the first two
conjuncts. The codomain contributes only the range proof below.

```agda
  private
    R : Recursion
    R = record
      { dom = dom ; graph = graph
      ; funct = λ x m → (fn x m , defines x m)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ graph)) (sym (only x m y h)) } }

  open RecursionGraph R public
    using ( Mem; isPropMem; F; F-in; F-out; Fib; isPropFib; pair-out; γ; sv; dm )

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst cod ⟩
  ran x y h = subst (λ w → ⟨ w ∈ fst cod ⟩) (sym e) (into x m)
    where
    m = fst (pair-out x y h)
    e = snd (pair-out x y h)
```

## Section 4. Injective, hence coded

```agda
module Inj (M : DefinableMap)
           (inj : (x : S) (m : ⟨ fst x ∈ˢ fst (DefinableMap.dom M) ⟩)
                  (x' : S) (m' : ⟨ fst x' ∈ˢ fst (DefinableMap.dom M) ⟩)
                → fst (DefinableMap.fn M x m) ≡ fst (DefinableMap.fn M x' m')
                → fst x ≡ fst x') where

  open Graph M public

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x' y q
    in inj x m x' m' (sym e ∙ e'))

  code : InjCode F dom cod
  code = sv , dm , ij , ran

  injL : InjL dom cod
  injL = ∣ F , code ∣₁
```
