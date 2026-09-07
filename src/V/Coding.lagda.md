<!--en-->
# Coding inside the cumulative hierarchy

The cumulative hierarchy supplies distinct set numerals and an injective Kuratowski pairing. Together they instantiate the generic syntax coding interface, so terms and formulas over sets receive codes that are themselves sets.
<!--zh-->
# 累积层级内的符号化

累积层级提供两两相异的集合数码与单射的 Kuratowski 配对。二者共同实例化通用语法符号化接口，使集合上的词项与公式得到本身仍是集合的码。
<!--ja-->
# 累積階層の内部での符号化

累積階層には、互いに異なる集合としての数項と、単射な Kuratowski 対があります。この二つで一般の構文符号化インターフェースを具体化すると、集合上の項と論理式は、それ自身が集合である符号を持ちます。
<!--/-->

<!--en-->
For the naturals, the hierarchy's own numerals serve. Distinct numerals are
distinct sets because a smaller numeral belongs to a larger one, and no set
belongs to itself. For pairing, Kuratowski's encoding serves: the pair of `a`
and `b` is the set whose members are the singleton of `a` and the unordered pair
of `a` and `b`, so the first component is recoverable as the common element and
the second as the one that may differ.

Both proofs are conducted entirely through the library's classification
specifications, transporting memberships along paths. At no point is a nested
brace expression handed to the typechecker to unfold, which is a discipline
rather than an aesthetic: these encodings nest three deep, and unfolding one is
how a proof about them stops terminating.
<!--zh-->
自然数这边，层级自己的数码即可胜任。相异的数码是相异的集合，因为较小的数码属于较大的，而没有集合属于自身。配对这边，Kuratowski 的编码即可胜任：`a` 与 `b` 的对，是以 `a` 的单点集与 `a`、`b` 的无序对为成员的那个集合，于是第一分量可作为公共元素还原，第二分量则作为那个可能不同的元素还原。

两个证明全程只经库的分类规格进行，沿路径搬运隶属关系。任何时候都不把嵌套的花括号表达式交给类型检查器去展开，这是纪律而非美学：这些编码嵌套三层深，而展开其中之一，正是关于它们的证明停止终止的方式。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Coding {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Coding
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )

open import Cubical.Data.Nat.Order using ( _<_; <-split; ¬-<-zero; _≟_; lt; eq; gt )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Numerals are distinct

Monotonicity first: a smaller numeral belongs to a larger one. The induction is
on the *larger* index, so that each step is the syntactic successor and no
arithmetic on indices appears. That is deliberate. Inducting on the difference
instead would put `suc k + m` against `suc (k + m)`, and reducing that equation
forces the membership type to unfold through successor, union and the small
member type, which does not finish.
<!--zh-->
## 数码两两相异

先看单调性：较小的数码属于较大的。归纳沿**较大的**那个序号进行，使得每一步都是句法上的后继，索引上不出现任何算术。这是有意为之。若改沿差量归纳，就会把 `suc k + m` 与 `suc (k + m)` 对上，而化简那个等式会迫使隶属类型经后继、并与小成员类型展开，那是走不完的。
<!--ja-->
## 数項は互いに異なる

小さい数項は大きい数項に属し、どの集合も自分自身には属しません。この二つの事実を自然数の三分律と組み合わせると、階層の数項写像が単射であると分かります。
<!--/-->

<!--en-->
The case split is written with an explicit eliminator rather than `with`, for
the same reason: `with` abstracts the goal, and abstracting this goal normalizes
it.
<!--zh-->
分情形用显式消去子而非 `with` 写出，理由相同：`with` 会抽象目标，而抽象这个目标就会把它归一化。
<!--/-->

```agda
#⊆suc : (n : ℕ) {x : S} → ⟨ x ∈ˢ (# n) ⟩ → ⟨ x ∈ˢ (# (suc n)) ⟩
#⊆suc n {x} = ∈sucV-inl {A = # n} {x = x}

#mono : (m n : ℕ) → m < n → ⟨ (# m) ∈ˢ (# n) ⟩
#mono m zero    m<0    = Empty.rec (¬-<-zero m<0)
#mono m (suc n) m<sucn = Sum.rec
  (λ m<n → #⊆suc n (#mono m n m<n))
  (λ m≡n → subst (λ M → ⟨ (# M) ∈ˢ (# (suc n)) ⟩) (sym m≡n) (self∈sucV (# n)))
  (<-split m<sucn)
```

<!--en-->
Injectivity follows by trichotomy on the indices. Equal indices are the
conclusion; a strictly smaller one would put a numeral inside itself once the
two codes are identified, which irreflexivity forbids; and the remaining case is
the mirror image.
<!--zh-->
单射性随即由序号上的三歧得出。序号相等即是结论；若严格更小，则把两个码认同之后会把某个数码放进它自身，而无自环性禁止这一点；余下的情形是镜像。
<!--/-->

```agda
#-inj : (m n : ℕ) → # m ≡ # n → m ≡ n
#-inj m n #m≡#n with m ≟ n
... | eq m≡n = m≡n
... | lt m<n = Empty.rec (∈-irrefl (# n)
      (subst (λ z → ⟨ z ∈ˢ (# n) ⟩) #m≡#n (#mono m n m<n)))
... | gt n<m = Empty.rec (∈-irrefl (# m)
      (subst (λ z → ⟨ z ∈ˢ (# m) ⟩) (sym #m≡#n) (#mono n m n<m)))

#-inj′ : ∀ {m n} → # m ≡ # n → m ≡ n
#-inj′ {m} {n} = #-inj m n
```

<!--en-->
## Kuratowski pairing

The classification specifications, named once so the proof reads as membership
reasoning rather than as brace manipulation. Membership in a singleton is
equality to its element; membership in an unordered pair is equality to one of
the two, merely. From these, a singleton determines its element, and a
singleton that happens to equal an unordered pair forces both components down to
that element.
<!--zh-->
## Kuratowski 配对

先把分类规格各命名一次，好让证明读起来像隶属关系的推理，而不是花括号的摆弄。属于单点集就是等于它那个元素；属于无序对就是仅仅等于二者之一。由此，单点集决定它的元素；而恰好等于某个无序对的单点集，会把两个分量都压到那个元素上。
<!--ja-->
## Kuratowski 対

Kuratowski 対は単集合と非順序対で二つの成分を記録します。それぞれの所属の特徴付けを使うと等しい符号から両成分を復元できるため、この対符号化は単射です。
<!--/-->



```agda
private
  ∈singl : {a x : S} → ⟨ x ∈ₛ ⁅ a ⁆s ⟩ → x ≡ a
  ∈singl {a} {x} = SetPackage.classification (SingletonPackage a) x .fst

  singl∈ : {a x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a ⁆s ⟩
  singl∈ {a} {x} = SetPackage.classification (SingletonPackage a) x .snd

  self∈singl : (a : S) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
  self∈singl a = singl∈ refl

  inl∈⁅,⁆ : {a b x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
  inl∈⁅,⁆ {a} {b} {x} e = pairing-ax a b x .snd ∣ inl e ∣₁

  inr∈⁅,⁆ : {a b x : S} → x ≡ b → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
  inr∈⁅,⁆ {a} {b} {x} e = pairing-ax a b x .snd ∣ inr e ∣₁

  mem⁅,⁆ : {a b x : S} → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩ → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁
  mem⁅,⁆ {a} {b} {x} = pairing-ax a b x .fst

  singl-inj : {a c : S} → ⁅ a ⁆s ≡ ⁅ c ⁆s → a ≡ c
  singl-inj {a} {c} q = ∈singl (subst (λ s → ⟨ a ∈ₛ s ⟩) q (self∈singl a))

  singl≡pair : {a c d : S} → ⁅ a ⁆s ≡ ⁅ c , d ⁆ → (c ≡ a) × (d ≡ a)
  singl≡pair {a} {c} {d} q =
      ∈singl (subst (λ s → ⟨ c ∈ₛ s ⟩) (sym q) (inl∈⁅,⁆ {a = c} {b = d} refl))
    , ∈singl (subst (λ s → ⟨ d ∈ₛ s ⟩) (sym q) (inr∈⁅,⁆ {a = c} {b = d} refl))
```

<!--en-->
The pair, and the theorem the chapter exists for. Both components are recovered
by transporting a membership across the assumed equation and classifying the
result. The first component is the easier one; the second needs the degenerate
case, where the pair collapses because its two components coincide, and there
the missing information is recovered by transporting in the other direction.
<!--zh-->
配对本身，以及本章为之存在的那条定理。两个分量都是把一个隶属关系沿假设的等式搬运过去、再对结果作分类而还原的。第一个分量较易；第二个需要处理退化情形，即两个分量重合使对塌陷的情形，那里缺失的信息靠向另一个方向搬运补回。
<!--/-->

```agda
pr : S → S → S
pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆

pr-inj : ∀ {a b c d} → pr a b ≡ pr c d → (a ≡ c) × (b ≡ d)
pr-inj {a} {b} {c} {d} p = a≡c , b≡d
  where
  H₁ : ∥ (⁅ a ⁆s ≡ ⁅ c ⁆s) ⊎ (⁅ a ⁆s ≡ ⁅ c , d ⁆) ∥₁
  H₁ = mem⁅,⁆ (subst (λ s → ⟨ ⁅ a ⁆s ∈ₛ s ⟩) p (inl∈⁅,⁆ {b = ⁅ a , b ⁆} refl))

  a≡c : a ≡ c
  a≡c = PT.rec (setIsSet a c)
    (Sum.rec singl-inj (λ e → sym (singl≡pair e .fst))) H₁

  H₂ : ∥ (⁅ a , b ⁆ ≡ ⁅ c ⁆s) ⊎ (⁅ a , b ⁆ ≡ ⁅ c , d ⁆) ∥₁
  H₂ = mem⁅,⁆ (subst (λ s → ⟨ ⁅ a , b ⁆ ∈ₛ s ⟩) p (inr∈⁅,⁆ {a = ⁅ a ⁆s} refl))

  K : ∥ (⁅ c , d ⁆ ≡ ⁅ a ⁆s) ⊎ (⁅ c , d ⁆ ≡ ⁅ a , b ⁆) ∥₁
  K = mem⁅,⁆ (subst (λ s → ⟨ ⁅ c , d ⁆ ∈ₛ s ⟩) (sym p) (inr∈⁅,⁆ {a = ⁅ c ⁆s} refl))

  d≡b-from-K : a ≡ b → d ≡ b
  d≡b-from-K a≡b = PT.rec (setIsSet d b)
    (Sum.rec
      (λ e → singl≡pair (sym e) .snd ∙ a≡b)
      (λ e → PT.rec (setIsSet d b)
        (Sum.rec (λ d≡a → d≡a ∙ a≡b) (λ d≡b → d≡b))
        (mem⁅,⁆ (subst (λ s → ⟨ d ∈ₛ s ⟩) e (inr∈⁅,⁆ {a = c} refl)))))
    K

  b≡d : b ≡ d
  b≡d = PT.rec (setIsSet b d)
    (Sum.rec
      (λ e → let b≡c = singl≡pair (sym e) .snd
             in sym (d≡b-from-K (a≡c ∙ sym b≡c)))
      (λ e → PT.rec (setIsSet b d)
        (Sum.rec
          (λ b≡c → sym (d≡b-from-K (a≡c ∙ sym b≡c)))
          (λ b≡d → b≡d))
        (mem⁅,⁆ (subst (λ s → ⟨ b ∈ₛ s ⟩) e (inr∈⁅,⁆ {a = a} refl)))))
    H₂
```

<!--en-->
## The instance

Both parameters discharged, the coding chapter applies to the hierarchy, and
formulas over the hierarchy's own sets acquire codes that are again sets of the
hierarchy. This is the object the internal coding certificates read and write.
<!--zh-->
## 实例

两组参数都已兑现，编码那一章便适用于层级，而以层级自家集合为常元的公式，获得的码又是层级的集合。这就是内部编码诸章的证书所读写的对象。
<!--ja-->
## 具体化

単射な数項と単射な対がそろったので、一般の符号化構成を `V`{.Agda} に具体化します。こうして集合を定数とする論理式の符号も階層内の集合になります。
<!--/-->



```agda
module VCode = FOL.Coding {ℓ-suc ℓ} 𝒮ᵥ pr pr-inj #_ #-inj′
```

<!--en-->
## Recap

Numerals are injective (`#-inj`{.Agda}, through monotonicity and
irreflexivity) and Kuratowski pairs are injective (`pr-inj`{.Agda}, through the
classification specifications), so `VCode`{.Agda} is the previous chapter's
coding applied to the hierarchy. Formulas are now sets of `V`, with the
`Codes`{.Agda} relation available to reason about them, and the internal coding development can start
building certificates that quantify over coded syntax.
<!--zh-->
## 小结

数码单射 (`#-inj`{.Agda}，经单调性与无自环性)，Kuratowski 对单射 (`pr-inj`{.Agda}，经分类规格)，于是 `VCode`{.Agda} 就是上一章的编码施于层级。公式如今是 `V` 的集合，`Codes`{.Agda} 关系可用来对它们推理，而可构造宇宙诸章可以开始搭建对编码语法作量化的证书了。
<!--ja-->
## まとめ

`#-inj`{.Agda} と `pr-inj`{.Agda} が一般の符号化に必要な二つの単射を与えます。`VCode`{.Agda} はこれらを使い、項と論理式を累積階層の集合として符号化します。
<!--/-->
