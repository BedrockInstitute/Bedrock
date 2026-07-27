# A recursion over codes, in the model

<!--en-->
The first instance. It takes the closure of a formula as its domain and sends
each key in it to the closure of the formula that key names, and the point of
building it is not the object it produces, which the meta level already had, but
the shape of the obligation the internalization theorem charges for an object of
that kind.

The graph is written the way a recursion over codes has to be written when it may
not name its answer's construction: not "the value is built from the values at
the subcodes", which the object language cannot say without a table to hold them,
but "the value is the least set containing the key and closed under subcodes".
Least is what makes it single-valued, and antisymmetry is what makes least
single-valued, so the uniqueness half of `funct`{.Agda} costs one extensionality
and no induction at all. Only existence is an induction, and both of its halves
were proved in the chapter before this one.

What the instance therefore measures is the frame, not the content: what it costs
to hand `L.Recursion`{.Agda} a domain, a graph and a `funct`{.Agda}, with the
mathematics under `funct`{.Agda} made as cheap as it can be made. A recursion
whose values are not characterized by a least-fixed-point property will pay for
that separately, and this chapter does not measure that part.
<!--zh-->
第一个实例。它取一条公式的闭包为定义域，把其中每个键送到那个键所命名的公式的闭包；而造它的意义不在于它产出的那个对象 (元语言层面早就有了)，而在于内化定理为那一类对象所收取的义务是什么形状。

那个图，是按「对码的递归在不可点名其答案之构造时必须采用的写法」写的：不是「取值由诸子码处的取值造出」(对象语言没有一张表托着那些取值就说不出这句话)，而是「取值是含有该键且对子码封闭的最小集」。是「最小」使它单值，而是反对称性使「最小」单值，故 `funct`{.Agda} 的唯一性那一半只花一次外延，一次归纳也不用。只有存在性是归纳，而它的两半都在上一章证过了。

故这个实例所测量的是框架、不是内容：把定义域、图与 `funct`{.Agda} 交给 `L.Recursion`{.Agda} 要花多少，而 `funct`{.Agda} 之下的数学已被压到不能再省。取值不由某个最小不动点性质刻画的递归，要为那一部分另外付账，而本章不测量那一部分。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Recursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( closedAt )
open import L.Coding.InL {ℓ}
  using ( key; closure; closure-inv; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed; closureLeast )
open import L.Recursion {ℓ} lem using ( Recursion; mereFunct; module Of )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The graph
<!--zh-->
## 那个图
<!--/-->

<!--en-->
Three conjuncts and one binder: the index is in the value, the value is closed,
and any closed set containing the index contains the value. The variable at
position zero is the value and the one at position one is the index, which is the
convention `Recursion`{.Agda} fixes.
<!--zh-->
三个合取项与一个绑定：索引在取值之中、取值是封闭的、而任何含有该索引的封闭集都含有那个取值。位置零处的变元是取值，位置一处的是索引，而这是 `Recursion`{.Agda} 定下的约定。
<!--/-->

```agda
closureGraph : Formula S 2
closureGraph =
  (var (suc zero) ∈̇ var zero)
  ∧̇ ( closedAt zero
  ∧̇ ∀̇ ( ((var (suc (suc zero)) ∈̇ var zero) ∧̇ closedAt zero)
       ⇒̇ ∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero)) ))
```

<!--en-->
## The instance
<!--zh-->
## 那个实例
<!--/-->

<!--en-->
Existence names the closure of the formula the index is a key of, which
`closure-inv`{.Agda} produces and the previous chapter's two lemmas certify.
Uniqueness plays the two minimality clauses against each other: each value is
contained in the other, so their underlying sets are pointwise equal, and
constructibility is a proposition so the elements are equal.
<!--zh-->
存在性点名「索引所是之键」那条公式的闭包，由 `closure-inv`{.Agda} 产出，由上一章那两条引理背书。唯一性让两个最小性子句互相较劲：每个取值都含于另一个之中，故它们的底集逐点相等；而可构造性是命题，故那两个元素相等。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where
  private
    Cl : ∀ {n} → Formula K n → V ℓ
    Cl = closure f h

  module _ {n : ℕ} (ψ : Formula K n) (x : S) (q : fst x ≡ key f h ψ) where
    private
      k∈ : ⟨ fst x ∈ Cl ψ ⟩
      k∈ = subst (λ w → ⟨ w ∈ Cl ψ ⟩) (sym q) (key∈closure f h ψ)

    holds : ⟨ (clo f h ψ ∷ x ∷ []) ⊨ closureGraph ⟩
    holds = k∈
      , ( closureClosed f h ψ (x ∷ [])
        , (λ z zh w w∈ →
            closureLeast f h ψ z (clo f h ψ ∷ x ∷ [])
              (subst (λ v → ⟨ v ∈ fst z ⟩) q (zh .fst)) (zh .snd)
              (fst w) w∈) )

    uniq : (y' : S) → ⟨ (y' ∷ x ∷ []) ⊨ closureGraph ⟩ → y' ≡ clo f h ψ
    uniq y' hy' = Σ≡Prop (λ v → snd (isL v))
      (extensionalV (λ v → ⇔toPath (fwd v) (bwd v)))
      where
      fwd : (v : V ℓ) → ⟨ v ∈ fst y' ⟩ → ⟨ v ∈ Cl ψ ⟩
      fwd v v∈ = hy' .snd .snd (clo f h ψ)
        (k∈ , closureClosed f h ψ (y' ∷ x ∷ []))
        (v , isL-trans v∈ (snd y')) v∈

      bwd : (v : V ℓ) → ⟨ v ∈ Cl ψ ⟩ → ⟨ v ∈ fst y' ⟩
      bwd = closureLeast f h ψ y' (x ∷ [])
              (subst (λ v → ⟨ v ∈ fst y' ⟩) q (hy' .fst)) (hy' .snd .fst)

  closureRec : ∀ {n} (φ : Formula K n) → Recursion
  Recursion.dom (closureRec φ) = clo f h φ
  Recursion.graph (closureRec φ) = closureGraph
  Recursion.funct (closureRec φ) x x∈ = mereFunct closureGraph x
    (PT.map (λ { (m , ψ , q , _) → clo f h ψ , (holds ψ x q , uniq ψ x q) })
      (closure-inv f h φ (fst x) x∈))
```

<!--en-->
## The table
<!--zh-->
## 那张表
<!--/-->

<!--en-->
And the theorem's half: the graph and the proof above buy the table, an element
of `L` whose members are the pairs of a key with the closure it names. Nothing
further is asked, which is the whole claim the internalization theorem makes.
<!--zh-->
接着是定理的那一半：上面的图与证明买下了那张表，它是 `L` 的一个元素，其成员是「键与它所命名的闭包」之对。此外一无所求，而这就是内化定理所声称的全部。
<!--/-->

```agda
  module Table {n : ℕ} (φ : Formula K n) = Of (closureRec φ)
```
