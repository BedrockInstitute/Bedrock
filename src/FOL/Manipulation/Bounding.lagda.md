# Bounded formulas

<!--en-->
Relabelling moved a formula from one constant domain to another along a total
function. The constructions of Part 4 need the partial case. There, a formula
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
重标沿一个全函数把公式从一个常量域搬到另一个。第四部的构造需要部分函数的情形。在那里，公式带着取自整个宇宙的常元到来，却必须被移植进层级的某**一个阶段**里面，而那个阶段只能接收恰好落在其中的常元。全函数并不存在；存在的是逐次出现的一份证书，说明这个常元是目标接收得了的。

本章就是那份证书。`BoundedFo P φ` 逐次出现地记录：`φ` 中出现的每个常元都满足 `P`。它按被检查公式的同一套分情形定义，故在模式匹配下自动拆开，任何证明都不必对「公式的常元列表」作推理。由于是纯语法，本章既不提层级也不提阶段，且分文不花。

配套的是单调性。窄谓词的证书就是宽谓词的证书，而这正是把针对不同阶段写下的证书带到公共阶段、以便一并使用的办法。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module FOL.Manipulation.Bounding where

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

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
BoundedFo P (¬̇ φ)    = BoundedFo P φ
BoundedFo P ⊤̇        = Lift Unit
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
  BoundedFo-mono (¬̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono ⊤̇        _         = _
  BoundedFo-mono ⊥̇        _         = _
  BoundedFo-mono (∃̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
  BoundedFo-mono (∃̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`BoundedFo`{.Agda} is a per-occurrence certificate that a formula's constants
satisfy a predicate, and `BoundedFo-mono`{.Agda} weakens it. Nothing here is
about sets; the payoff comes when the predicate is "lies in a given stage", at
which point the certificate is exactly the licence to relabel a formula into
that stage's constant domain.
<!--zh-->
`BoundedFo`{.Agda} 是「公式的常元满足某谓词」的逐次出现证书，`BoundedFo-mono`{.Agda} 把它放宽。此处与集合无关；回报发生在谓词取为「落在给定阶段里」之时，那时这份证书恰是把公式重标进该阶段常量域的许可。
<!--/-->
