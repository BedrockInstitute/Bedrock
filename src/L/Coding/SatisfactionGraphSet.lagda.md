<!--en-->
# An internal graph of uniform satisfaction

The uniform satisfaction table assigns one value to every formula code in
`AllCodes W`. This chapter turns that internal value function into a set in `L`
whose members are exactly the pairs of a code and its assigned value, and proves
the two membership readers used by later constructions.
<!--zh-->
# 统一满足关系的内部图

统一的满足关系表为 `AllCodes W` 中的每个公式码指派一个取值。本章把这个内部取值函数化为 `L` 中的集合，其成员恰好是公式码与相应取值组成的有序对，并证明后续构造所用的两个隶属关系读式。
<!--ja-->
# 一様な充足関係の内部グラフ

一様な充足関係表は、`AllCodes W` の各論理式符号に一つの値を割り当てる。本章では、この内部の値関数を `L` の集合にし、その要素が論理式符号と対応する値の順序対にちょうどなることを示し、後続の構成が使う二つの所属関係の読み補題を証明する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.SatisfactionGraphSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )

open import FOL.Syntax using ( Formula )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsSF = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsSF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

```

The graph of the uniform table, as a set. The value function of
src/L/Coding/UniformSatisfaction.lagda.md `Table` supplies a recursion, and
src/L/Recursion/Graph.lagda.md `Graph` makes its graph a set. Sealed where it is
built; its two readers are what the consumer holds.

```agda
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table )
open import L.Recursion {ℓ} lem using ( Recursion )
open import L.Recursion.Graph {ℓ} lem using () renaming ( module Graph to MapGraph )

module SatGraph (W : S) where
```

SEALED: the value at a member is a contractibility centre, and written out it
does not elaborate (src/L/Coding/UniformSatisfaction.lagda.md `val-at`'s measurement). Every
use below names it by this atom.

```agda
  opaque
    valOf : (x : S) → ⟨ fst x ∈ fst (AllCodes W) ⟩ → S
    valOf x mx = Table.val W W x mx

    valOf≡ : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → valOf x mx ≡ Table.val W W x mx
    valOf≡ x mx = refl

  private
    opaque
      unfolding valOf
      gr : Formula S 2
      gr = Table.graph W W

      defines' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ (valOf x mx ∷ x ∷ []) ⊨ gr ⟩
      defines' x mx = Table.funct W W x mx .fst .snd

      only' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ gr ⟩ → y ≡ valOf x mx
      only' x mx y h = sym (Table.val-uniq W W x mx y h)

    M : Recursion
    M = record
      { dom = AllCodes W ; graph = gr
      ; funct = λ x mx → (valOf x mx , defines' x mx)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ gr)) (sym (only' x mx y h)) } }

    module G = MapGraph M using ( F; F-in; pair-out )

  opaque
    pairs : S
    pairs = G.F

    pairs-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (valOf x mx)) ∈ fst pairs ⟩
    pairs-in = G.F-in

    pairs-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst pairs ⟩
              → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (valOf x mx))
    pairs-out = G.pair-out
```

Every member is a pair.

```agda
    pairs-shape : (e : S) → ⟨ fst e ∈ fst pairs ⟩
                → ∥ Σ[ x ∈ S ] Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst e ≡ pr (fst x) (fst (valOf x mx))) ∥₁
    pairs-shape e h = MapGraph.F-out M (fst e) h
```
