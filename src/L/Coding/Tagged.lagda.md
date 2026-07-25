# Codes that carry their arity

<!--en-->
A certificate that walks down a formula has a bookkeeping problem. Descending
under a quantifier changes the arity: the body of `∃̇ φ` has one more free
variable than `∃̇ φ` itself. If the certificate quantifies over codes alone it
loses that information, and the clause for a quantifier can no longer say which
arity its subformula has.

The fix is to carry the arity alongside the code. This chapter gathers the pairs
of an arity numeral with a code of that arity, and gives the object-language
readers for such a pair. Nothing here is deep; it is the bookkeeping that lets
the twelve clauses of a satisfaction certificate be stated at all, and it is
shared by every certificate that follows, which is why it gets a chapter rather
than being inlined at each use.

The second reader is the one the binary constructors need: a code is *tagged with
`k` over a pair* when it is the tag `k` applied to the Kuratowski pair of two
sub-codes. That single formula matches conjunction, disjunction, implication and
the two bounded quantifiers, differing only in the numeral `k`.
<!--zh-->
沿公式向下走的证书有一个记账问题。下降到量词之下会改变元数：`∃̇ φ` 的主体比 `∃̇ φ` 本身多一个自由变元。若证书只对码作量化，它就丢失了那个信息，量词的子句便再也说不出它的子公式是几元的。

补救是把元数与码一并携带。本章汇集「元数数码与该元数的一个码」之对，并给出读这种对的对象语言读式。此处没有深刻的东西；这是使满足证书的十二条子句得以陈述的记账工作，且被此后每个证书共享，这正是它成章而非在每个使用处内联的原因。

第二条读式是二元构造子所需的那条：一个码**以 `k` 为标签作用于一个对**，指它是标签 `k` 施于两个子码的 Kuratowski 对。这一条公式就匹配合取、析取、蕴含与两个有界量词，彼此只差数码 `k`。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Tagged {ℓ : Level} where

open import FOL.Syntax using ( Term; con; var; Formula; _∧̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∃∈ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Coding.Base {ℓ}
  using ( ClosedΣ; prAt; Δ₀-prAt; prAt-adequate; tagAt; Δ₀-tagAt; tagAt-adequate
        ; ∈pair-introR )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## The arity-tagged code set
<!--zh-->
## 带元数的码集
<!--/-->

<!--en-->
The same index as the plain code set, but each entry now pairs the arity's
numeral with the code. Membership is definitional again, and the set is
parameter-free, so it too can be named by a constant, which is what a clause
quantifying over codes actually mentions.
<!--zh-->
索引与朴素码集相同，但每个条目如今把元数的数码与码配成对。隶属关系仍按定义成立，而该集合无参，故它同样可由一个常量命名，这正是对码作量化的子句实际提到的东西。
<!--/-->

```agda
taggedCodes : V ℓ
taggedCodes = sett ClosedΣ (λ p → pr (# (p .fst)) VCode.⌜ embed (p .snd) ⌝)

taggedCodes-spec : (c : V ℓ)
  → ⟨ c ∈ taggedCodes ⟩
  ≡ ∥ Σ[ p ∈ ClosedΣ ] (pr (# (p .fst)) VCode.⌜ embed (p .snd) ⌝ ≡ c) ∥₁
taggedCodes-spec c = refl

taggedCode-mem : ∀ {n} (φ : Formula (⊥* {ℓ}) n)
               → ⟨ pr (# n) VCode.⌜ embed φ ⌝ ∈ taggedCodes ⟩
taggedCode-mem {n} φ = ∣ (n , φ) , refl ∣₁

taggedCodesTerm : ∀ {n} → Term (V ℓ) n
taggedCodesTerm = con taggedCodes
```

<!--en-->
## Recognizing an arity-tagged code
<!--zh-->
## 认出一个带元数的码
<!--/-->

<!--en-->
"The pair of these two is an arity-tagged code." One bounded existential over the
set just named, with the Kuratowski reader pinning the shape, so Δ₀ and adequate
by the pattern the reader chapters established.
<!--zh-->
「这两者之对是一个带元数的码。」在刚命名的那个集合上作一个有界存在，由 Kuratowski 读式钉住形状，故按读式诸章立下的套路，Δ₀ 与适足性一并得到。
<!--/-->

```agda
pairInAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
pairInAt x y = ∃̇∈ taggedCodesTerm (prAt zero (suc x) (suc y))

Δ₀-pairInAt : ∀ {n} (x y : Fin n) → Δ₀ (pairInAt x y)
Δ₀-pairInAt x y = δ-∃∈ (Δ₀-prAt zero (suc x) (suc y))

pairInAt-adequate : ∀ {n} (x y : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ pairInAt x y) ≡ (pr (⟦ var x ⟧ γ) (⟦ var y ⟧ γ) ∈ taggedCodes)
pairInAt-adequate x y γ = ⇔toPath fwd bwd
  where
  X = ⟦ var x ⟧ γ
  Y = ⟦ var y ⟧ γ
  fwd : ⟨ γ ⊨ pairInAt x y ⟩ → ⟨ pr X Y ∈ taggedCodes ⟩
  fwd = PT.rec ((pr X Y ∈ taggedCodes) .snd)
    (λ { (q , q∈C , sat) →
      subst (λ z → ⟨ z ∈ taggedCodes ⟩)
        (subst ⟨_⟩ (prAt-adequate zero (suc x) (suc y) (q ∷ γ)) sat)
        q∈C })
  bwd : ⟨ pr X Y ∈ taggedCodes ⟩ → ⟨ γ ⊨ pairInAt x y ⟩
  bwd h = ∣ pr X Y , h
          , subst ⟨_⟩ (sym (prAt-adequate zero (suc x) (suc y) (pr X Y ∷ γ))) refl ∣₁
```

<!--en-->
## The binary constructor shape
<!--zh-->
## 二元构造子的形状
<!--/-->

<!--en-->
The last reader, and the one that does the most work later: a code is the tag `k`
applied to the pair of two sub-codes. Two nested bounded existentials name the
intermediate sets that the Kuratowski encoding introduces, the tag reader pins
the outer layer and the pair reader the inner one, and the de Bruijn positions
shift outward by two accordingly.

The backward direction has to exhibit those intermediates. They are exactly the
brace expressions the encoding is built from, and the membership facts they need
are the pair introductions of the reader chapter, which is why those were made
available rather than kept private.
<!--zh-->
最后一条读式，也是此后出力最多的那条：一个码是标签 `k` 施于两个子码之对。两层嵌套的有界存在为 Kuratowski 编码引入的中间集合命名，标签读式钉住外层、对读式钉住内层，而 de Bruijn 位置相应地向外移两位。

反向需要拿出那些中间集合。它们恰是这套编码所由构造的花括号表达式，而它们所需的隶属事实正是读式那一章的对引入引理，这也是当初把它们公开而非私有的原因。
<!--/-->

```agda
tagPairAt : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula (V ℓ) n
tagPairAt s k a b =
  ∃̇∈ (var s) (∃̇∈ (var zero)
    ( tagAt (suc (suc s)) k zero
    ∧̇ prAt zero (suc (suc a)) (suc (suc b)) ))

Δ₀-tagPairAt : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) → Δ₀ (tagPairAt s k a b)
Δ₀-tagPairAt s k a b =
  δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-tagAt (suc (suc s)) k zero)
                  (Δ₀-prAt zero (suc (suc a)) (suc (suc b)))))

tagPairAt-adequate : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ tagPairAt s k a b)
  ≡ ((⟦ var s ⟧ γ ≡ VCode.mkTag k (pr (⟦ var a ⟧ γ) (⟦ var b ⟧ γ))) , setIsSet _ _)
tagPairAt-adequate s k a b γ = ⇔toPath fwd bwd
  where
  S = ⟦ var s ⟧ γ
  A = ⟦ var a ⟧ γ
  B = ⟦ var b ⟧ γ

  fwd : ⟨ γ ⊨ tagPairAt s k a b ⟩ → S ≡ VCode.mkTag k (pr A B)
  fwd = PT.rec (setIsSet S (VCode.mkTag k (pr A B)))
    (λ { (c , _ , h₁) → PT.rec (setIsSet S (VCode.mkTag k (pr A B)))
      (λ { (w , _ , sat₁ , sat₂) →
        subst ⟨_⟩ (tagAt-adequate (suc (suc s)) k zero (w ∷ c ∷ γ)) sat₁
        ∙ cong (VCode.mkTag k)
            (subst ⟨_⟩
              (prAt-adequate zero (suc (suc a)) (suc (suc b)) (w ∷ c ∷ γ))
              sat₂) })
      h₁ })

  bwd : S ≡ VCode.mkTag k (pr A B) → ⟨ γ ⊨ tagPairAt s k a b ⟩
  bwd h =
    ∣ ⁅ # k , pr A B ⁆
    , subst (λ z → ⟨ ⁅ # k , pr A B ⁆ ∈ z ⟩) (sym h)
        (∈pair-introR {u = ⁅ # k ⁆s} {v = ⁅ # k , pr A B ⁆}
                      {y = ⁅ # k , pr A B ⁆} refl)
    , ∣ pr A B
      , ∈pair-introR {u = # k} {v = pr A B} {y = pr A B} refl
      , subst ⟨_⟩
          (sym (tagAt-adequate (suc (suc s)) k zero
            (pr A B ∷ ⁅ # k , pr A B ⁆ ∷ γ))) h
      , subst ⟨_⟩
          (sym (prAt-adequate zero (suc (suc a)) (suc (suc b))
            (pr A B ∷ ⁅ # k , pr A B ⁆ ∷ γ))) refl
      ∣₁
    ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`taggedCodes`{.Agda} carries an arity beside each code, which is what lets a
clause for a quantifier speak about its subformula's arity;
`pairInAt`{.Agda} recognizes membership in it, and `tagPairAt`{.Agda} matches
the shape every binary constructor's code has. With these the twelve clauses of
a satisfaction certificate can be written, and the next chapter writes them.
<!--zh-->
`taggedCodes`{.Agda} 在每个码旁携带一个元数，正是它使量词的子句能谈论其子公式的元数；`pairInAt`{.Agda} 认出属于它的成员，而 `tagPairAt`{.Agda} 匹配每个二元构造子的码所具有的形状。有了这些，满足证书的十二条子句就写得出来了，而下一章就来写它们。
<!--/-->
