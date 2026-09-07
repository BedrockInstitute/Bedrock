# Bounded formulas

<!--en-->
Relabelling moved a formula from one constant domain to another along a total
function. The constructions of the constructible-universe chapters need the partial case. There, a formula
arrives with constants drawn from a whole universe, and it has to be replanted
inside one *stage* of a hierarchy, which can only receive the constants that
happen to lie in that stage. A total function does not exist; what exists is a
certificate, per occurrence, that this constant is one the target can accept.

This chapter is that certificate. `BoundedFo P φ` records, occurrence by
occurrence, that every constant appearing in `φ` satisfies `P`. It is defined by
the same case analysis as the formula it inspects, so it splits automatically
under pattern matching, and no proof ever has to reason about a list of the
constants of a formula. Being pure syntax, the chapter mentions neither
hierarchies nor stages, and costs nothing.

The companion is monotonicity. A certificate for a narrower predicate is one for
a wider predicate, which is how certificates written against different stages are
brought to a common stage before being used together.
<!--zh-->
重标沿一个全函数把公式从一个常量域搬到另一个。可构造宇宙诸章的构造需要部分函数的情形。在那里，公式带着取自整个宇宙的常元到来，却必须被移植进层级的某**一个阶段**里面，而那个阶段只能接收恰好落在其中的常元。全函数并不存在；存在的是逐次出现的一份证书，说明这个常元是目标接收得了的。

本章就是那份证书。`BoundedFo P φ` 逐次出现地记录：`φ` 中出现的每个常元都满足 `P`。它按被检查公式的同一套分情形定义，故在模式匹配下自动拆开，任何证明都不必对「公式的常元列表」作推理。由于是纯语法，本章既不提层级也不提阶段，且分文不花。

配套的是单调性。窄谓词的证书就是宽谓词的证书，而这正是把针对不同阶段写下的证书带到公共阶段、以便一并使用的办法。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module FOL.Manipulation.Bounding where

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo )

open import Cubical.Data.Unit using ( Unit )
```

<!--en-->
## The certificate
<!--zh-->
## 证书
<!--/-->

<!--en-->
A term carries a certificate when its constant satisfies the predicate; a
variable carries nothing, which is recorded as the trivial datum at the right
universe level. A formula's certificate is the tuple of its parts', following the
constructors one for one. Bounded quantifiers carry a certificate for their
bounding term as well, since that term is where a constant most often enters.
<!--zh-->
项在其常元满足谓词时携带证书；变元什么也不带，这以恰当宇宙层级上的平凡数据记下。公式的证书是其各部分证书的元组，与构造子一一对应。有界量词还为其界项携带一份证书，因为常元最常正是从那里进入。
<!--/-->

```agda
BoundedTm : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Term K n → Type ℓp
BoundedTm P (con c) = P c
BoundedTm P (var i) = Lift Unit

BoundedFo : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Formula K n → Type ℓp
BoundedFo P (t ∈̇ u)  = BoundedTm P t × BoundedTm P u
BoundedFo P (t ≐ u)  = BoundedTm P t × BoundedTm P u
BoundedFo P (φ ∧̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ∨̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ⇒̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P ⊥̇        = Lift Unit
BoundedFo P (∃̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇∈ t φ) = BoundedTm P t × BoundedFo P φ
BoundedFo P (∃̇∈ t φ) = BoundedTm P t × BoundedFo P φ
```

<!--en-->
## Monotonicity
<!--zh-->
## 单调性
<!--/-->

<!--en-->
Weakening the predicate weakens the certificate, by the same recursion. The
predicate that matters later is "lies in this stage", and stages grow, so this
is the lemma that lets several certificates, each written for the stage its own
formula needed, be read together at one stage above them all.
<!--zh-->
放宽谓词即放宽证书，沿同一套递归。日后要紧的那个谓词是「落在这个阶段里」，而阶段会增长，故正是这条引理使得若干份证书 (各自为其公式所需的阶段而写) 能在一个高于它们全体的阶段上被一并读出。
<!--/-->

```agda
module _ {ℓk ℓp ℓq} {K : Type ℓk} {P : K → Type ℓp} {Q : K → Type ℓq}
         (P⊆Q : (c : K) → P c → Q c) where

  BoundedTm-mono : ∀ {n} (t : Term K n) → BoundedTm P t → BoundedTm Q t
  BoundedTm-mono (con c) p = P⊆Q c p
  BoundedTm-mono (var i) _ = _

  BoundedFo-mono : ∀ {n} (φ : Formula K n) → BoundedFo P φ → BoundedFo Q φ
  BoundedFo-mono (t ∈̇ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (t ≐ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (φ ∧̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono (φ ∨̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono (φ ⇒̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono ⊥̇        _         = _
  BoundedFo-mono (∃̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
  BoundedFo-mono (∃̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
```

<!--en-->
## Relabelling, partially
<!--zh-->
## 部分地重标
<!--/-->

<!--en-->
And the payoff the certificate was for. Relabelling wanted a total function
between constant domains; here there is only a partial one, defined where the
predicate holds. The certificate says the predicate holds at every constant a
given formula actually mentions, so the formula can be relabelled after all,
occurrence by occurrence, with the certificate supplying the argument at each.

The interface is stated in the generality its user needs. Two domains, a common
world they both map into, a predicate on the source, a partial map defined under
it, and the equation saying the partial map agrees with the two projections. In
the intended instance the source is the model's carrier, the target is a stage's
member type, the world is the hierarchy, and the equation is the fact that a
member of a stage, viewed as a set, is the set it was.
<!--zh-->
然后是那份证书为之而设的回报。重标要的是常量域之间的全函数；此处只有一个部分函数，在谓词成立处有定义。而证书说该谓词在给定公式实际提到的每个常元处都成立，故这条公式终究还是可以被重标，逐次出现地重标，每一处由证书提供那个参数。

接口以其使用者所需的一般性陈述：两个域、它们共同映入的一个世界、源上的一个谓词、在其之下有定义的一个部分映射，以及说明该部分映射与两个投影相符的等式。在预期的实例中，源是模型的载体，目标是某个阶段的成员类型，世界是层级，而那条等式就是「阶段的成员作为集合看，仍是它原本那个集合」这一事实。
<!--/-->

```agda
module Relabel
  {ℓk ℓk' ℓv ℓp : Level}
  {K  : Type ℓk}
  {K' : Type ℓk'}
  {W  : Type ℓv}
  (proj : K → W)
  (up   : K' → W)
  (P    : K → Type ℓp)
  (down : (c : K) → P c → K')
  (down-correct : (c : K) (p : P c) → up (down c p) ≡ proj c)
  where

  liftTm : ∀ {n} (t : Term K n) → BoundedTm P t → Term K' n
  liftTm (con c) p = con (down c p)
  liftTm (var i) _ = var i

  liftFo : ∀ {n} (φ : Formula K n) → BoundedFo P φ → Formula K' n
  liftFo (t ∈̇ u)  (ht , hu) = liftTm t ht ∈̇ liftTm u hu
  liftFo (t ≐ u)  (ht , hu) = liftTm t ht ≐ liftTm u hu
  liftFo (φ ∧̇ ψ)  (hφ , hψ) = liftFo φ hφ ∧̇ liftFo ψ hψ
  liftFo (φ ∨̇ ψ)  (hφ , hψ) = liftFo φ hφ ∨̇ liftFo ψ hψ
  liftFo (φ ⇒̇ ψ)  (hφ , hψ) = liftFo φ hφ ⇒̇ liftFo ψ hψ
  liftFo ⊥̇        _         = ⊥̇
  liftFo (∃̇ φ)    hφ        = ∃̇ liftFo φ hφ
  liftFo (∀̇ φ)    hφ        = ∀̇ liftFo φ hφ
  liftFo (∀̇∈ t φ) (ht , hφ) = ∀̇∈ (liftTm t ht) (liftFo φ hφ)
  liftFo (∃̇∈ t φ) (ht , hφ) = ∃̇∈ (liftTm t ht) (liftFo φ hφ)
```

<!--en-->
Correctness says the relabelling changed nothing that matters: pushing the result
into the common world along one map gives the same formula as pushing the
original along the other. That is the equation the two legs of an absoluteness
argument meet at, and it holds occurrence by occurrence for the reason the
interface demanded.

The Levy witness survives too, since relabelling touches constants and the
witness never looks at them.
<!--zh-->
正确性说这次重标没有改变任何要紧的东西：沿一个映射把结果推进那个共同世界，与沿另一个映射把原式推进去，得到的是同一条公式。那正是绝对性论证的两条腿会合之处的等式，而它逐次出现地成立，理由正是接口所索取的那一条。

Lévy 见证也存活下来，因为重标动的是常元，而见证从不看它们。
<!--/-->

```agda
  liftTm-correct : ∀ {n} (t : Term K n) (h : BoundedTm P t)
                 → mapTm up (liftTm t h) ≡ mapTm proj t
  liftTm-correct (con c) p = cong con (down-correct c p)
  liftTm-correct (var i) _ = refl

  liftFo-correct : ∀ {n} (φ : Formula K n) (h : BoundedFo P φ)
                 → mapFo up (liftFo φ h) ≡ mapFo proj φ
  liftFo-correct (t ∈̇ u) (ht , hu) =
    cong₂ _∈̇_ (liftTm-correct t ht) (liftTm-correct u hu)
  liftFo-correct (t ≐ u) (ht , hu) =
    cong₂ _≐_ (liftTm-correct t ht) (liftTm-correct u hu)
  liftFo-correct (φ ∧̇ ψ) (hφ , hψ) =
    cong₂ _∧̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ∨̇ ψ) (hφ , hψ) =
    cong₂ _∨̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ⇒̇ ψ) (hφ , hψ) =
    cong₂ _⇒̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct ⊥̇ _ = refl
  liftFo-correct (∃̇ φ) hφ = cong ∃̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇ φ) hφ = cong ∀̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇∈ t φ) (ht , hφ) =
    cong₂ ∀̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)
  liftFo-correct (∃̇∈ t φ) (ht , hφ) =
    cong₂ ∃̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)

  Δ₀-liftFo : ∀ {n} {φ : Formula K n} (h : BoundedFo P φ) → Δ₀ φ → Δ₀ (liftFo φ h)
  Δ₀-liftFo (ht , hu) δ-∈       = δ-∈
  Δ₀-liftFo (ht , hu) δ-≐       = δ-≐
  Δ₀-liftFo (hφ , hψ) (δ-∧ c d) = δ-∧ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-∨ c d) = δ-∨ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-⇒ c d) = δ-⇒ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo _         δ-⊥       = δ-⊥
  Δ₀-liftFo (ht , hφ) (δ-∀∈ c)  = δ-∀∈ (Δ₀-liftFo hφ c)
  Δ₀-liftFo (ht , hφ) (δ-∃∈ c)  = δ-∃∈ (Δ₀-liftFo hφ c)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`BoundedFo`{.Agda} is a per-occurrence certificate that a formula's constants
satisfy a predicate, and `BoundedFo-mono`{.Agda} weakens it. Nothing here is
about sets; the payoff is `Relabel`{.Agda}, where the certificate becomes the
licence to relabel a formula into a smaller constant domain, with
`liftFo-correct`{.Agda} saying the relabelling changed nothing the meaning
depends on and `Δ₀-liftFo`{.Agda} carrying the Levy witness across.
<!--zh-->
`BoundedFo`{.Agda} 是「公式的常元满足某谓词」的逐次出现证书，`BoundedFo-mono`{.Agda} 把它放宽。此处与集合无关；回报是 `Relabel`{.Agda}：那里这份证书成为把公式重标进更小常量域的许可，`liftFo-correct`{.Agda} 说这次重标没有改变含义所依赖的任何东西，而 `Δ₀-liftFo`{.Agda} 把 Lévy 见证带了过去。
<!--/-->
