<!--en-->
# Cardinals and coded injections inside L

Cardinality inside `L` is expressed through injection graphs that are themselves constructible sets. This chapter defines when a graph codes an injection, states that such a graph exists without choosing one, uses the ordinal well-order to select least cardinal representatives, and characterizes successor cardinals.
<!--zh-->
# L 内部的基数与编码单射

`L` 内部的基数关系通过本身也是可构造集合的单射图来表达。本章定义一个图何时编码单射，在不选定具体图的情况下陈述这种图的存在性，用序数的良序选取最小基数代表，并刻画后继基数。
<!--ja-->
# L の内部における基数と符号化された単射

`L` 内部の基数関係は、それ自身が構成可能集合である単射グラフによって表します。本章では、グラフが単射を符号化する条件を定め、具体的なグラフを選ばずにその存在を述べ、順序数の整列順序を用いて最小の基数代表を選び、後続基数を特徴付けます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Cardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

The ambient injection type, as the square-law chain carries it.

```agda
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)
```

A1. The site at `sucV (fst α)`, for a least-cardinal selection.

`α` is an L-element, the per-site hypothesis is the ordinal certificate `oα`,
and the crossing `up` lifts a member of the tower at `sucV (fst α)` into the
L-carrier. The lift is where the three delivered L-lemmas surface:
`ord∈Lset-suc` and `Lset→isL` give level-hood of the stage, `isL-trans` pushes
it down. The selection itself is the consumer's: `L.GCH.CardinalRepresentative` runs
`leastOf w`, and `L.GCH.Assembly` takes `up`, `self` and `self-eq`.

```agda
module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where
```

`⟨ isL α ⟩` alone does not give level-hood of `sucV (fst α)`; it comes from an
ordinal appearing at the stage after itself, plus membership in a stage being
level-hood.

```agda
  hSucα : ⟨ isL (sucV (fst α)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst α))) (suc-ord (suc-ord oα)) (sucV (fst α))
            (ord∈Lset-suc (sucV (fst α)) (suc-ord oα))
```

`isL-trans` propagates level-hood down to the members, turning a member of the
tower into an L-element.

```agda
  up : ⟪ sucV (fst α) ⟫ → S
  up m = ⟪ sucV (fst α) ⟫↪ m
       , isL-trans (member (sucV (fst α)) m) hSucα
```

The well-order is SEALED. Transparent, its comparison unfolds the union
representation `⟪ sucV (fst α) ⟫` inside every conversion check the consumer's
selection runs. The seal makes `leastOf w` a stuck atom, so the selected member
never re-unfolds, and the master that selects on it falls from about 100 s to
about 9 s.

```agda
  opaque
    w : SWO (⟪ sucV (fst α) ⟫)
    w = ordSWO (sucV (fst α)) (suc-ord oα)
```

The one read the seal needs (R-36): the sealed comparison, in the ambient
membership form, proved inside the seal. No exported type names `w`.

```agda
  opaque
    unfolding w
    w-lt : (m n : ⟪ sucV (fst α) ⟫)
         → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ ⟪ sucV (fst α) ⟫↪ n ⟩
    w-lt m n = refl

  self : ⟪ sucV (fst α) ⟫
  self = fiber (sucV (fst α)) (self∈sucV (fst α)) .fst

  self-eq : ⟪ sucV (fst α) ⟫↪ self ≡ fst α
  self-eq = fiber (sucV (fst α)) (self∈sucV (fst α)) .snd

```

<!--en-->
## Internal injections and successor cardinals

An injection inside `L` is witnessed by a constructible graph satisfying the four `InjCode`{.Agda} conditions. `InjL`{.Agda} says that some such graph exists without selecting one; these injections then define internal cardinals and the least internal cardinal strictly above a given one.
<!--zh-->
## 内部单射与后继基数

`L` 内部的单射由一个满足 `InjCode`{.Agda} 四项条件的可构造图见证。`InjL`{.Agda} 断言某个这样的图存在，却不选定一个；这些单射进而定义内部基数，以及严格大于给定基数的最小内部基数。
<!--ja-->
## 内部の単射と後続基数

`L` の内部の単射は、`InjCode`{.Agda} の四条件を満たす構成可能なグラフによって証されます。`InjL`{.Agda} は具体的なグラフを選ばずに、そのようなグラフが存在すると述べます。これらの単射を用いて内部の基数と、与えられた基数より真に大きい最小の内部基数を定義します。
<!--/-->

A4. The internal cardinal.

`InjCode` is A2's three conjuncts plus the value-in-`b` clause, the four pieces
A2's `Small` readback consumes. `IsCardinalL` is the internal cardinal: no
smaller L-element admits a code. The trophy statement names both.

```agda
InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)

InjL : S → S → Type (ℓ-suc ℓ)
InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsOrd (fst δ)
  × IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩
             → ⟨ δ ⊆ˢ c ⟩)
```
