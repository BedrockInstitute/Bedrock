# The cardinal predicates

<!--en-->
The cardinal chapter's definitional layer is three internal predicates,
equinumerosity, cardinal, and successor cardinal, each a reified formula with a
certificate that its satisfaction says exactly the intended set-theoretic
notion. The layer is built generally, once, and the two rulings that shape it
come from the W7 scope gate: equinumerosity is the existence of a bijection,
never injections both ways, because the latter would make every equality a
per-consumer Cantor-Bernstein obligation; and the predicates are built as the
general relation forms, not as GCH-specific shims, because the fine-structure
era's cardinal notion and the geology era's internal cardinality function are
extensions of exactly these.

The chapter's substrate is the ordered pair. The object language has no
function symbols and no constants here, so "there is a bijection from `x` onto
`y`" has to be spelled out as: there is a set `f` of Kuratowski ordered pairs
that is a relation from `x` to `y`, single-valued and total on `x`, injective,
and surjective onto `y`. Everything below the three predicates is that spelling:
the singleton, the unordered pair, the Kuratowski pair, the five clauses of the
bijection, and the certificates tying each formula to its meta-level reading.
<!--zh-->
基数章的定义层是三个内部谓词：等势、基数与后继基数，各是一条具体化了的公式，配一份证书，说明其满足关系说的恰是所要的集合论概念。这一层一次性泛型地建成，其形状由 W7 的作用域门给出两条裁决：等势取「存在双射」，绝不取「两边各有单射」，因为后者会把每个等式变成每个消费方各自的 Cantor-Bernstein 义务；而谓词建成一般的关系形态、不作 GCH 专用垫片，因为细结构时代的基数概念与地质时代的内基数函数，恰是这些谓词的延展。

本章的基底是有序对。对象语言在这里既无函数符号也无常元，故「从 `x` 到 `y` 有双射」必须逐字拼出：存在一个 Kuratowski 有序对之集 `f`，它是从 `x` 到 `y` 的关系，在 `x` 上单值且全，单射，且满射到 `y`。三个谓词之下的一切都是这番拼写：单点集、无序对、Kuratowski 对、双射的五条子句，以及把每条公式钉到其元层读法上的证书。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.CardinalPredicates {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; ∈singl; singl∈; inl∈⁅,⁆; inr∈⁅,⁆; mem⁅,⁆ )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )

open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Relation.Nullary using ( isProp¬ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## Being an ordinal, at any depth
<!--zh-->
## 任何深度处的「是序数」
<!--/-->

<!--en-->
The house pattern for a certified internal predicate is the ordinal of the
stages chapter: transitive set of transitive sets, said with bounded
quantifiers alone, so the formula is Δ₀. Here the same two clauses are written
once, generic in the de Bruijn position of the candidate, so one formula serves
at every depth of nesting. At position zero in arity one it is the stages
chapter's `φ-ord` on the nose.
<!--zh-->
经证书的内部谓词的范式是阶段一章的序数：成员皆传递的传递集，只用有界量词说出，故公式是 Δ₀。此处两条子句照写一遍，对候选的 de Bruijn 位置泛型，于是同一条公式在任何嵌套深度上都能用。在一元中的零号位置，它就是阶段一章的 `φ-ord` 一字不差。
<!--/-->

```agda
ordFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Formula K n
ordFo v =
  (∀̇∈ (var v) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc v)))))
  ∧̇ (∀̇∈ (var v) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-ordFo : ∀ {ℓk} {K : Type ℓk} {n} (v : Fin n) → Δ₀ (ordFo {K = K} v)
Δ₀-ordFo v = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))
```

<!--en-->
## The ordered pair
<!--zh-->
## 有序对
<!--/-->

<!--en-->
The pair substrate is the object language's way of saying "this is the
Kuratowski pair of those". Three formulas, each taking its de Bruijn positions
as arguments, so the same formula serves at any depth. A singleton is a set
whose members are exactly one set; an unordered pair a set whose members are
exactly two; the ordered pair `⟨a, b⟩` is the set whose members are the
singleton of `a` and the unordered pair of `a` and `b`. Every quantifier is
bounded, so all three carry Δ₀ witnesses read straight off their shape, the
bookkeeping being the usual one: a bounded quantifier binds a fresh variable at
position zero and pushes the earlier ones outward.
<!--zh-->
对基底是对象语言说「这是那两个的 Kuratowski 对」的方式。三条公式，各把 de Bruijn 位置取作参数，故同一条公式在任何深度上可用。单点集是成员恰为一个集合的集合；无序对是成员恰为两个的集合；有序对 `⟨a, b⟩` 是以 `a` 的单点集与 `a`、`b` 的无序对为成员的集合。每个量词都有界，故三条公式都带直接由其形状读出的 Δ₀ 见证，记账是老一套：有界量词在位置零绑定新变元，把先前的向外推。
<!--/-->

```agda
sglFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Formula K n
sglFo p a = (var a ∈̇ var p) ∧̇ (∀̇∈ (var p) (var zero ≐ var (suc a)))

pairFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Fin n → Formula K n
pairFo p a b = (var a ∈̇ var p) ∧̇ ((var b ∈̇ var p)
            ∧̇ (∀̇∈ (var p) ((var zero ≐ var (suc a)) ∨̇ (var zero ≐ var (suc b)))))

oprFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Fin n → Formula K n
oprFo p a b = (∃̇∈ (var p) (sglFo zero (suc a)))
           ∧̇ ((∃̇∈ (var p) (pairFo zero (suc a) (suc b)))
           ∧̇ (∀̇∈ (var p) (sglFo zero (suc a) ∨̇ pairFo zero (suc a) (suc b))))

Δ₀-sglFo : ∀ {ℓk} {K : Type ℓk} {n} (p a : Fin n) → Δ₀ (sglFo {K = K} p a)
Δ₀-sglFo p a = δ-∧ δ-∈ (δ-∀∈ δ-≐)

Δ₀-pairFo : ∀ {ℓk} {K : Type ℓk} {n} (p a b : Fin n) → Δ₀ (pairFo {K = K} p a b)
Δ₀-pairFo p a b = δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∀∈ (δ-∨ δ-≐ δ-≐)))

Δ₀-oprFo : ∀ {ℓk} {K : Type ℓk} {n} (p a b : Fin n) → Δ₀ (oprFo {K = K} p a b)
Δ₀-oprFo p a b = δ-∧ (δ-∃∈ (Δ₀-sglFo zero (suc a)))
  (δ-∧ (δ-∃∈ (Δ₀-pairFo zero (suc a) (suc b)))
       (δ-∀∈ (δ-∨ (Δ₀-sglFo zero (suc a)) (Δ₀-pairFo zero (suc a) (suc b)))))
```

<!--en-->
The certificate for the pair is the meta-level characterization, written in
the shape the formula's satisfaction unfolds to, which is what makes the
adequacy lemma one line instead of a second proof. A set is the Kuratowski pair
of `a` and `b` exactly when it has a member that is the singleton of `a`, a
member that is the unordered pair, and no other members. The two auxiliary
predicates are private: they exist only to carry this characterization.
<!--zh-->
对的证书是元层特征刻画，按公式的满足关系将要展开成的形状写成，这使适足引理只是一行，而非第二个证明。一个集合是 `a` 与 `b` 的 Kuratowski 对，恰当它有一个成员是 `a` 的单点集、有一个成员是无序对、且没有别的成员。两个辅助谓词是私有的：它们只为承载这条刻画而存在。
<!--/-->

```agda
private
  SglOf : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  SglOf U w = ⟨ U ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ U)

  PairOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PairOf U W w = ⟨ U ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ U) ⊎ (z ≡ W) ∥₁))

  sgl-char : (w U : V ℓ) → SglOf U w → w ≡ ⁅ U ⁆s
  sgl-char w U (hU , hall) = extensionality w ⁅ U ⁆s (sub₁ , sub₂)
    where
    sub₁ : ⟨ w ⊆ ⁅ U ⁆s ⟩
    sub₁ z z∈ₛw = singl∈ {a = U} (hall z (∈∈ₛ {a = z} {b = w} .snd z∈ₛw))
    sub₂ : ⟨ ⁅ U ⁆s ⊆ w ⟩
    sub₂ z z∈ₛs = subst (λ y → ⟨ y ∈ₛ w ⟩) (sym (∈singl z∈ₛs))
      (∈∈ₛ {a = U} {b = w} .fst hU)

  pair-char : (w U W : V ℓ) → ⟨ U ∈ w ⟩ → ⟨ W ∈ w ⟩
            → ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ U) ⊎ (z ≡ W) ∥₁)
            → w ≡ ⁅ U , W ⁆
  pair-char w U W hU hW hall = extensionality w ⁅ U , W ⁆ (sub₁ , sub₂)
    where
    sub₁ : ⟨ w ⊆ ⁅ U , W ⁆ ⟩
    sub₁ z z∈ₛw = PT.rec ((z ∈ₛ ⁅ U , W ⁆) .snd)
        (Sum.rec (λ e → inl∈⁅,⁆ {a = U} {b = W} e)
                 (λ e → inr∈⁅,⁆ {a = U} {b = W} e))
        (hall z (∈∈ₛ {a = z} {b = w} .snd z∈ₛw))
    sub₂ : ⟨ ⁅ U , W ⁆ ⊆ w ⟩
    sub₂ z z∈ₛp = PT.rec ((z ∈ₛ w) .snd)
      (Sum.rec (λ e → subst (λ y → ⟨ y ∈ₛ w ⟩) (sym e) (∈∈ₛ {a = U} {b = w} .fst hU))
               (λ e → subst (λ y → ⟨ y ∈ₛ w ⟩) (sym e) (∈∈ₛ {a = W} {b = w} .fst hW)))
      (mem⁅,⁆ z∈ₛp)

  sglOf⁅⁆ : (U : V ℓ) → SglOf U ⁅ U ⁆s
  sglOf⁅⁆ U = (∈∈ₛ {a = U} {b = ⁅ U ⁆s} .snd (singl∈ {a = U} refl)) ,
            (λ z z∈ → ∈singl (∈∈ₛ {a = z} {b = ⁅ U ⁆s} .fst z∈))

  pairOf⁅⁆ : (U W : V ℓ) → PairOf U W ⁅ U , W ⁆
  pairOf⁅⁆ U W =
    (∈∈ₛ {a = U} {b = ⁅ U , W ⁆} .snd (inl∈⁅,⁆ {a = U} {b = W} refl)) ,
    (∈∈ₛ {a = W} {b = ⁅ U , W ⁆} .snd (inr∈⁅,⁆ {a = U} {b = W} refl)) ,
    (λ z z∈ → mem⁅,⁆ (∈∈ₛ {a = z} {b = ⁅ U , W ⁆} .fst z∈))

  sglOf-subst : {U w : V ℓ} → w ≡ ⁅ U ⁆s → SglOf U w
  sglOf-subst {U} {w} e = subst (SglOf U) (sym e) (sglOf⁅⁆ U)

  pairOf-subst : {U W w : V ℓ} → w ≡ ⁅ U , W ⁆ → PairOf U W w
  pairOf-subst {U} {W} {w} e = subst (PairOf U W) (sym e) (pairOf⁅⁆ U W)

  opr-char-fwd : (Q U W : V ℓ)
    → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
    → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
    → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁)
    → Q ≡ pr U W
  opr-char-fwd Q U W h₁ h₂ h₃ = extensionality Q (pr U W) (sub₁ , sub₂)
    where
    sub₁ : ⟨ Q ⊆ pr U W ⟩
    sub₁ y y∈ₛQ = PT.rec ((y ∈ₛ pr U W) .snd)
      (Sum.rec
        (λ s → inl∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆} (sgl-char y U s))
        (λ p → inr∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆}
            (pair-char y U W (p .fst) (p .snd .fst) (p .snd .snd))))
      (h₃ y (∈∈ₛ {a = y} {b = Q} .snd y∈ₛQ))
    sub₂ : ⟨ pr U W ⊆ Q ⟩
    sub₂ y y∈ₛpr = PT.rec ((y ∈ₛ Q) .snd)
      (Sum.rec
        (λ e → PT.rec ((y ∈ₛ Q) .snd)
          (λ { (w , w∈Q , s) → subst (λ z → ⟨ z ∈ₛ Q ⟩)
                 (sym (e ∙ sym (sgl-char w U s))) (∈∈ₛ {a = w} {b = Q} .fst w∈Q) })
          h₁)
        (λ e → PT.rec ((y ∈ₛ Q) .snd)
          (λ { (w , w∈Q , p) → subst (λ z → ⟨ z ∈ₛ Q ⟩)
                 (sym (e ∙ sym (pair-char w U W (p .fst) (p .snd .fst) (p .snd .snd))))
                 (∈∈ₛ {a = w} {b = Q} .fst w∈Q) })
          h₂))
      (mem⁅,⁆ y∈ₛpr)

  opr-char-bwd : (Q U W : V ℓ) → Q ≡ pr U W
    → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
    × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
    × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁))
  opr-char-bwd Q U W e = h₁ , h₂ , h₃
    where
    inQ : {z : V ℓ} → ⟨ z ∈ pr U W ⟩ → ⟨ z ∈ Q ⟩
    inQ {z} h = subst (λ w → ⟨ z ∈ w ⟩) (sym e) h
    h₁ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
    h₁ = ∣ ⁅ U ⁆s , (inQ (∈∈ₛ {a = ⁅ U ⁆s} {b = pr U W} .snd
           (inl∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆} refl)) , sglOf⁅⁆ U) ∣₁
    h₂ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
    h₂ = ∣ ⁅ U , W ⁆ , (inQ (∈∈ₛ {a = ⁅ U , W ⁆} {b = pr U W} .snd
           (inr∈⁅,⁆ {a = ⁅ U ⁆s} {b = ⁅ U , W ⁆} refl)) , pairOf⁅⁆ U W) ∣₁
    h₃ : (y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁
    h₃ y y∈Q = PT.map
      (Sum.rec (λ q → inl (sglOf-subst q)) (λ q → inr (pairOf-subst q)))
      (mem⁅,⁆ (∈∈ₛ {a = y} {b = pr U W} .fst
        (subst (λ w → ⟨ y ∈ w ⟩) e y∈Q)))

oprFo-adequate : ∀ {n} (p a b : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ oprFo p a b)
  ≡ ((⟦ var p ⟧ γ ≡ pr (⟦ var a ⟧ γ) (⟦ var b ⟧ γ)) , setIsSet _ _)
oprFo-adequate p a b γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → opr-char-fwd (⟦ var p ⟧ γ) (⟦ var a ⟧ γ) (⟦ var b ⟧ γ) h₁ h₂ h₃ })
  (λ e → opr-char-bwd (⟦ var p ⟧ γ) (⟦ var a ⟧ γ) (⟦ var b ⟧ γ) e)
```

<!--en-->
## The bijection
<!--zh-->
## 双射
<!--/-->

<!--en-->
The bijection is five clauses, each written at the de Bruijn position of the
candidate function `f`: every member of `f` is an ordered pair; `f` is
single-valued; `f` is total on `x`; `f` is injective; and `f` is surjective onto
`y`. The components of a pair are quantified unbounded, exactly the shape the
scope gate fixed: the predicate says "there is a set of Kuratowski pairs that
relates `x` onto `y`", and the certificate below matches it clause for clause
against the meta-level reading. The five clauses are private; the assembled
`bijFo` is the export.
<!--zh-->
双射是五条子句，各写在候选函数 `f` 的 de Bruijn 位置处：`f` 的每个成员都是有序对；`f` 单值；`f` 在 `x` 上全；`f` 单射；`f` 满射到 `y`。对的分量以无界量词量化，恰是作用域门钉下的形状：谓词说的是「存在一个 Kuratowski 对之集，把 `x` 关系到 `y` 上」，而下面的证书逐条与元层读法对账。五条子句是私有的；组装好的 `bijFo` 才是出口。
<!--/-->

```agda
private
  pairsFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Formula K n
  pairsFo f = ∀̇∈ (var f) (∃̇ (∃̇ (oprFo (suc (suc zero)) (suc zero) zero)))

  singleValuedFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Formula K n
  singleValuedFo f =
    ∀̇∈ (var f)
      (∀̇ (∀̇ (∀̇
        (oprFo (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
          ⇒̇ (oprFo (suc (suc (suc zero))) (suc (suc zero)) zero
          ⇒̇ var (suc zero) ≐ var zero)))))

  totalFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Formula K n
  totalFo f x =
    ∀̇∈ (var x) (∃̇∈ (var (suc f)) (∃̇ (oprFo (suc zero) (suc (suc zero)) zero)))

  injectiveFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Formula K n
  injectiveFo f =
    ∀̇∈ (var f) (∀̇∈ (var (suc f))
      (∀̇ (∀̇ (∀̇
        (oprFo (suc (suc (suc (suc zero)))) (suc (suc zero)) zero
          ⇒̇ (oprFo (suc (suc (suc zero))) (suc zero) zero
          ⇒̇ var (suc (suc zero)) ≐ var (suc zero)))))))

  surjectiveFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Formula K n
  surjectiveFo f y =
    ∀̇∈ (var y) (∃̇∈ (var (suc f)) (∃̇ (oprFo (suc zero) zero (suc (suc zero)))))

bijFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Fin n → Formula K n
bijFo f x y =
  pairsFo f ∧̇ (singleValuedFo f ∧̇ (totalFo f x ∧̇ (injectiveFo f ∧̇ surjectiveFo f y)))
```

<!--en-->
The host notion the certificate states is the same five clauses, unbounded, at
the level of the hierarchy's own sets. Its propositionality is a chain of
proposition closures: Π-types, memberships, truncations, and paths in the
h-set of sets. Equinumerosity is the truncation of "there is such an `f`",
which is the bijection form the scope gate made binding.
<!--zh-->
证书所陈述的元层概念是同样的五条子句，无界，落在层级自家集合的层面上。其命题性是命题闭包的链条：Π 型、成员关系、截断，以及集合这一 h-集里的路径。等势是「存在这样的 `f`」的截断，正是作用域门定死的那种双射形态。
<!--/-->

```agda
HostBij : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
HostBij f a b =
  ( (p : V ℓ) → ⟨ p ∈ f ⟩ → ∥ Σ[ x ∈ V ℓ ] (∥ Σ[ y ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁ )
  × ( (p : V ℓ) → ⟨ p ∈ f ⟩ → (x : V ℓ) → (y : V ℓ) → (y' : V ℓ)
      → p ≡ pr x y → p ≡ pr x y' → y ≡ y' )
  × ( (x : V ℓ) → ⟨ x ∈ a ⟩ → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ f ⟩ × ∥ Σ[ y ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁ )
  × ( (p : V ℓ) → ⟨ p ∈ f ⟩ → (q : V ℓ) → ⟨ q ∈ f ⟩ → (x : V ℓ) → (x' : V ℓ) → (y : V ℓ)
      → p ≡ pr x y → q ≡ pr x' y → x ≡ x' )
  × ( (y : V ℓ) → ⟨ y ∈ b ⟩ → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ f ⟩ × ∥ Σ[ x ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁ )

isPropPairsClause : (f : V ℓ)
  → isProp ((p : V ℓ) → ⟨ p ∈ f ⟩ → ∥ Σ[ x ∈ V ℓ ] (∥ Σ[ y ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁)
isPropPairsClause f = isPropΠ (λ p → isPropΠ (λ _ → squash₁))

isPropSingleValuedClause : (f : V ℓ)
  → isProp ((p : V ℓ) → ⟨ p ∈ f ⟩ → (x : V ℓ) → (y : V ℓ) → (y' : V ℓ)
      → p ≡ pr x y → p ≡ pr x y' → y ≡ y')
isPropSingleValuedClause f = isPropΠ (λ p → isPropΠ (λ _ →
  isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ y' →
    isPropΠ (λ _ → isPropΠ (λ _ → setIsSet y y')))))))

isPropTotalClause : (f a : V ℓ)
  → isProp ((x : V ℓ) → ⟨ x ∈ a ⟩ → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ f ⟩ × ∥ Σ[ y ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁)
isPropTotalClause f a = isPropΠ (λ x → isPropΠ (λ _ → squash₁))

isPropInjectiveClause : (f : V ℓ)
  → isProp ((p : V ℓ) → ⟨ p ∈ f ⟩ → (q : V ℓ) → ⟨ q ∈ f ⟩
      → (x : V ℓ) → (x' : V ℓ) → (y : V ℓ) → p ≡ pr x y → q ≡ pr x' y → x ≡ x')
isPropInjectiveClause f = isPropΠ (λ p → isPropΠ (λ _ → isPropΠ (λ q → isPropΠ (λ _ →
  isPropΠ (λ x → isPropΠ (λ x' → isPropΠ (λ y →
    isPropΠ (λ _ → isPropΠ (λ _ → setIsSet x x')))))))))

isPropSurjectiveClause : (f b : V ℓ)
  → isProp ((y : V ℓ) → ⟨ y ∈ b ⟩ → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ f ⟩ × ∥ Σ[ x ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁)
isPropSurjectiveClause f b = isPropΠ (λ y → isPropΠ (λ _ → squash₁))

isPropHostBij : (f a b : V ℓ) → isProp (HostBij f a b)
isPropHostBij f a b =
  isProp× (isPropPairsClause f)
    (isProp× (isPropSingleValuedClause f)
      (isProp× (isPropTotalClause f a)
        (isProp× (isPropInjectiveClause f) (isPropSurjectiveClause f b))))

HostEq : V ℓ → V ℓ → Type (ℓ-suc ℓ)
HostEq a b = ∥ Σ[ f ∈ V ℓ ] HostBij f a b ∥₁

isPropHostEq : (a b : V ℓ) → isProp (HostEq a b)
isPropHostEq a b = squash₁
```

<!--en-->
The certificate for the bijection is the clause-by-clause meta-match: each
clause's satisfaction is shown equivalent to its unbounded host reading, the
ordered-pair atom inside transported through the pair certificate. The five
clause lemmas are private; their assembly is the one public statement.
<!--zh-->
双射的证书是逐条子句的元层对账：每条子句的满足关系被证为与其无界元层读法等价，其中的有序对原子经对证书搬运。五条子句引理是私有的；其组装是唯一公开的陈述。
<!--/-->

```agda
private
  _↔_ : ∀ {ℓa ℓb} → Type ℓa → Type ℓb → Type (ℓ-max ℓa ℓb)
  A ↔ B = (A → B) × (B → A)

  pairs-at : ∀ {n} (γ : (V ℓ) ^ n) (p x y : V ℓ)
    → ((y ∷ x ∷ p ∷ γ) ⊨ oprFo {n = suc (suc (suc n))} (suc (suc zero)) (suc zero) zero)
    ≡ ((p ≡ pr x y) , setIsSet _ _)
  pairs-at {n} γ p x y =
    oprFo-adequate {n = suc (suc (suc n))} (suc (suc zero)) (suc zero) zero
      (y ∷ x ∷ p ∷ γ)

  singleValued-at : ∀ {n} (γ : (V ℓ) ^ n) (p x y y' : V ℓ)
    → ((y' ∷ y ∷ x ∷ p ∷ γ) ⊨ oprFo {n = suc (suc (suc (suc n)))}
        (suc (suc (suc zero))) (suc (suc zero)) (suc zero))
    ≡ ((p ≡ pr x y) , setIsSet _ _)
  singleValued-at {n} γ p x y y' =
    oprFo-adequate {n = suc (suc (suc (suc n)))} (suc (suc (suc zero)))
      (suc (suc zero)) (suc zero) (y' ∷ y ∷ x ∷ p ∷ γ)

  singleValued-at' : ∀ {n} (γ : (V ℓ) ^ n) (p x y y' : V ℓ)
    → ((y' ∷ y ∷ x ∷ p ∷ γ) ⊨ oprFo {n = suc (suc (suc (suc n)))}
        (suc (suc (suc zero))) (suc (suc zero)) zero)
    ≡ ((p ≡ pr x y') , setIsSet _ _)
  singleValued-at' {n} γ p x y y' =
    oprFo-adequate {n = suc (suc (suc (suc n)))} (suc (suc (suc zero)))
      (suc (suc zero)) zero (y' ∷ y ∷ x ∷ p ∷ γ)

  total-at : ∀ {n} (γ : (V ℓ) ^ n) (p a y : V ℓ)
    → ((y ∷ p ∷ a ∷ γ) ⊨ oprFo {n = suc (suc (suc n))} (suc zero) (suc (suc zero)) zero)
    ≡ ((p ≡ pr a y) , setIsSet _ _)
  total-at {n} γ p a y =
    oprFo-adequate {n = suc (suc (suc n))} (suc zero) (suc (suc zero)) zero
      (y ∷ p ∷ a ∷ γ)

  injective-at : ∀ {n} (γ : (V ℓ) ^ n) (p q x x' y : V ℓ)
    → ((y ∷ x' ∷ x ∷ q ∷ p ∷ γ) ⊨ oprFo {n = suc (suc (suc (suc (suc n))))}
        (suc (suc (suc (suc zero)))) (suc (suc zero)) zero)
    ≡ ((p ≡ pr x y) , setIsSet _ _)
  injective-at {n} γ p q x x' y =
    oprFo-adequate {n = suc (suc (suc (suc (suc n))))}
      (suc (suc (suc (suc zero)))) (suc (suc zero)) zero
      (y ∷ x' ∷ x ∷ q ∷ p ∷ γ)

  injective-at' : ∀ {n} (γ : (V ℓ) ^ n) (p q x x' y : V ℓ)
    → ((y ∷ x' ∷ x ∷ q ∷ p ∷ γ) ⊨ oprFo {n = suc (suc (suc (suc (suc n))))}
        (suc (suc (suc zero))) (suc zero) zero)
    ≡ ((q ≡ pr x' y) , setIsSet _ _)
  injective-at' {n} γ p q x x' y =
    oprFo-adequate {n = suc (suc (suc (suc (suc n))))}
      (suc (suc (suc zero))) (suc zero) zero
      (y ∷ x' ∷ x ∷ q ∷ p ∷ γ)

  surjective-at : ∀ {n} (γ : (V ℓ) ^ n) (p b x : V ℓ)
    → ((x ∷ p ∷ b ∷ γ) ⊨ oprFo {n = suc (suc (suc n))} (suc zero) zero (suc (suc zero)))
    ≡ ((p ≡ pr x b) , setIsSet _ _)
  surjective-at {n} γ p b x =
    oprFo-adequate {n = suc (suc (suc n))} (suc zero) zero (suc (suc zero))
      (x ∷ p ∷ b ∷ γ)

  pairs-sat : ∀ {n} (f : Fin n) (γ : (V ℓ) ^ n)
    → ⟨ γ ⊨ pairsFo f ⟩
    ↔ ((p : V ℓ) → ⟨ p ∈ ⟦ var f ⟧ γ ⟩
        → ∥ Σ[ x ∈ V ℓ ] (∥ Σ[ y ∈ V ℓ ] (p ≡ pr x y) ∥₁) ∥₁)
  pairs-sat f γ =
    (λ h p hp → PT.map (λ { (x , hx) → x ,
      PT.map (λ { (y , hy) → y , subst ⟨_⟩ (pairs-at γ p x y) hy }) hx }) (h p hp)) ,
    (λ h p hp → PT.map (λ { (x , hx) → x ,
      PT.map (λ { (y , hy) → y , subst ⟨_⟩ (sym (pairs-at γ p x y)) hy }) hx }) (h p hp))

  singleValued-sat : ∀ {n} (f : Fin n) (γ : (V ℓ) ^ n)
    → ⟨ γ ⊨ singleValuedFo f ⟩
    ↔ ((p : V ℓ) → ⟨ p ∈ ⟦ var f ⟧ γ ⟩ → (x : V ℓ) → (y : V ℓ) → (y' : V ℓ)
        → p ≡ pr x y → p ≡ pr x y' → y ≡ y')
  singleValued-sat f γ =
    (λ h p hp x y y' pxy pxy' →
      h p hp x y y' (subst ⟨_⟩ (sym (singleValued-at γ p x y y')) pxy)
        (subst ⟨_⟩ (sym (singleValued-at' γ p x y y')) pxy')) ,
    (λ h p hp x y y' hxy hxy' →
      h p hp x y y' (subst ⟨_⟩ (singleValued-at γ p x y y') hxy)
        (subst ⟨_⟩ (singleValued-at' γ p x y y') hxy'))

  total-sat : ∀ {n} (f x : Fin n) (γ : (V ℓ) ^ n)
    → ⟨ γ ⊨ totalFo f x ⟩
    ↔ ((a : V ℓ) → ⟨ a ∈ ⟦ var x ⟧ γ ⟩
        → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ ⟦ var f ⟧ γ ⟩ × ∥ Σ[ y ∈ V ℓ ] (p ≡ pr a y) ∥₁) ∥₁)
  total-sat f x γ =
    (λ h a ha → PT.map (λ { (p , hp , hx) → p , (hp , PT.map
      (λ { (y , hy) → y , subst ⟨_⟩ (total-at γ p a y) hy }) hx) }) (h a ha)) ,
    (λ h a ha → PT.map (λ { (p , hp , hx) → p , (hp , PT.map
      (λ { (y , hy) → y , subst ⟨_⟩ (sym (total-at γ p a y)) hy }) hx) }) (h a ha))

  injective-sat : ∀ {n} (f : Fin n) (γ : (V ℓ) ^ n)
    → ⟨ γ ⊨ injectiveFo f ⟩
    ↔ ((p : V ℓ) → ⟨ p ∈ ⟦ var f ⟧ γ ⟩ → (q : V ℓ) → ⟨ q ∈ ⟦ var f ⟧ γ ⟩
        → (x : V ℓ) → (x' : V ℓ) → (y : V ℓ) → p ≡ pr x y → q ≡ pr x' y → x ≡ x')
  injective-sat f γ =
    (λ h p hp q hq x x' y pxy qxy →
      h p hp q hq x x' y (subst ⟨_⟩ (sym (injective-at γ p q x x' y)) pxy)
        (subst ⟨_⟩ (sym (injective-at' γ p q x x' y)) qxy)) ,
    (λ h p hp q hq x x' y hxy hx'y →
      h p hp q hq x x' y (subst ⟨_⟩ (injective-at γ p q x x' y) hxy)
        (subst ⟨_⟩ (injective-at' γ p q x x' y) hx'y))

  surjective-sat : ∀ {n} (f y : Fin n) (γ : (V ℓ) ^ n)
    → ⟨ γ ⊨ surjectiveFo f y ⟩
    ↔ ((b : V ℓ) → ⟨ b ∈ ⟦ var y ⟧ γ ⟩
        → ∥ Σ[ p ∈ V ℓ ] (⟨ p ∈ ⟦ var f ⟧ γ ⟩ × ∥ Σ[ x ∈ V ℓ ] (p ≡ pr x b) ∥₁) ∥₁)
  surjective-sat f y γ =
    (λ h b hb → PT.map (λ { (p , hp , hx) → p , (hp , PT.map
      (λ { (x , hx') → x , subst ⟨_⟩ (surjective-at γ p b x) hx' }) hx) }) (h b hb)) ,
    (λ h b hb → PT.map (λ { (p , hp , hx) → p , (hp , PT.map
      (λ { (x , hx') → x , subst ⟨_⟩ (sym (surjective-at γ p b x)) hx' }) hx) }) (h b hb))

bijFo-adequate : ∀ {n} (f x y : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ bijFo f x y)
  ≡ (HostBij (⟦ var f ⟧ γ) (⟦ var x ⟧ γ) (⟦ var y ⟧ γ)
    , isPropHostBij (⟦ var f ⟧ γ) (⟦ var x ⟧ γ) (⟦ var y ⟧ γ))
bijFo-adequate f x y γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ bijFo f x y ⟩ → HostBij (⟦ var f ⟧ γ) (⟦ var x ⟧ γ) (⟦ var y ⟧ γ)
  fwd (h₁ , h₂ , h₃ , h₄ , h₅) =
    pairs-sat f γ .fst h₁ ,
    singleValued-sat f γ .fst h₂ ,
    total-sat f x γ .fst h₃ ,
    injective-sat f γ .fst h₄ ,
    surjective-sat f y γ .fst h₅
  bwd : HostBij (⟦ var f ⟧ γ) (⟦ var x ⟧ γ) (⟦ var y ⟧ γ) → ⟨ γ ⊨ bijFo f x y ⟩
  bwd (p₁ , p₂ , p₃ , p₄ , p₅) =
    pairs-sat f γ .snd p₁ ,
    singleValued-sat f γ .snd p₂ ,
    total-sat f x γ .snd p₃ ,
    injective-sat f γ .snd p₄ ,
    surjective-sat f y γ .snd p₅
```

<!--en-->
## Equinumerosity, cardinal, successor cardinal
<!--zh-->
## 等势、基数、后继基数
<!--/-->

<!--en-->
With the bijection in place the three predicates write themselves in the exact
shapes the scope gate fixed. Equinumerosity is a bijection existing: `∃ f`,
`f` a bijection from `x` onto `y`. A cardinal is an ordinal with no smaller
ordinal equinumerous to it, the initial-ordinal notion; the unbounded
existential inside equinumerosity makes the cardinal predicate read as Jech's
Π₁ classification of "α is a cardinal" (Jech 13.13): no function from a smaller
ordinal can reach it. The successor cardinal of `κ` is the least cardinal above
it: a cardinal `s` with `κ ∈ s` and no cardinal `λ` strictly between. Each
certificate is the ambient one: satisfaction at the full hierarchy is the host
notion on the nose.
<!--zh-->
双射就位，三个谓词便按作用域门钉下的形状径直写下。等势即存在双射：`∃ f`，`f` 是从 `x` 到 `y` 的双射。基数是无更小序数与之等势的序数，即初始序数概念；等势内部的无界存在量词使基数谓词读起来正如 Jech 对「α 是基数」的 Π₁ 分类 (Jech 13.13)：没有来自更小序数的函数能够到它。`κ` 的后继基数是它上方的最小基数：一个基数 `s`，满足 `κ ∈ s`，且没有基数 `λ` 严格居间。每条证书都是环境层的：在完整层级中的满足关系恰是元层概念本身。
<!--/-->

```agda
eqFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Formula K n
eqFo a b = ∃̇ (bijFo zero (suc a) (suc b))

eqFo-adequate : ∀ {n} (a b : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ eqFo a b) ≡ (HostEq (⟦ var a ⟧ γ) (⟦ var b ⟧ γ)
    , isPropHostEq (⟦ var a ⟧ γ) (⟦ var b ⟧ γ))
eqFo-adequate a b γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ eqFo a b ⟩ → HostEq (⟦ var a ⟧ γ) (⟦ var b ⟧ γ)
  fwd h = PT.map
    (λ { (f , hf) → f , subst ⟨_⟩ (bijFo-adequate zero (suc a) (suc b) (f ∷ γ)) hf }) h
  bwd : HostEq (⟦ var a ⟧ γ) (⟦ var b ⟧ γ) → ⟨ γ ⊨ eqFo a b ⟩
  bwd h = PT.map
    (λ { (f , hf) → f , subst ⟨_⟩ (sym (bijFo-adequate zero (suc a) (suc b) (f ∷ γ))) hf }) h

ordFo-adequate : ∀ {n} (v : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ ordFo v) ≡ (IsOrd (⟦ var v ⟧ γ) , isPropIsOrd (⟦ var v ⟧ γ))
ordFo-adequate v γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ ordFo v ⟩ → IsOrd (⟦ var v ⟧ γ)
  fwd (h₁ , h₂) = (λ {x} {y} y∈x x∈A → h₁ x x∈A y y∈x) ,
    (λ x x∈A {y} {z} z∈y y∈x → h₂ x x∈A y y∈x z z∈y)
  bwd : IsOrd (⟦ var v ⟧ γ) → ⟨ γ ⊨ ordFo v ⟩
  bwd (tr , memtr) = (λ x x∈A y y∈x → tr y∈x x∈A) ,
    (λ x x∈A y y∈x z z∈y → memtr x x∈A {x = y} {y = z} z∈y y∈x)

cardFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Formula K n
cardFo v = ordFo v ∧̇ (∀̇∈ (var v) (¬̇ eqFo zero (suc v)))

IsCard : V ℓ → Type (ℓ-suc ℓ)
IsCard v = IsOrd v × ((y : V ℓ) → ⟨ y ∈ v ⟩ → HostEq y v → Empty.⊥)

isPropIsCard : (v : V ℓ) → isProp (IsCard v)
isPropIsCard v = isProp× (isPropIsOrd v) (isPropΠ (λ y → isPropΠ (λ _ → isProp¬ (HostEq y v))))

cardFo-adequate : ∀ {n} (v : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ cardFo v) ≡ (IsCard (⟦ var v ⟧ γ) , isPropIsCard (⟦ var v ⟧ γ))
cardFo-adequate v γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ cardFo v ⟩ → IsCard (⟦ var v ⟧ γ)
  fwd (ord , h) = subst ⟨_⟩ (ordFo-adequate v γ) ord ,
    λ y y∈A hy → h y y∈A (subst ⟨_⟩ (sym (eqFo-adequate zero (suc v) (y ∷ γ))) hy)
  bwd : IsCard (⟦ var v ⟧ γ) → ⟨ γ ⊨ cardFo v ⟩
  bwd (ord , hc) = subst ⟨_⟩ (sym (ordFo-adequate v γ)) ord ,
    λ y y∈A heq → hc y y∈A (subst ⟨_⟩ (eqFo-adequate zero (suc v) (y ∷ γ)) heq)

succCardFo : ∀ {ℓk} {K : Type ℓk} {n} → Fin n → Fin n → Formula K n
succCardFo s k =
  cardFo s ∧̇ ((var k ∈̇ var s) ∧̇
    (∀̇ (cardFo zero ⇒̇ (var (suc k) ∈̇ var zero)
       ⇒̇ ((var (suc s) ∈̇ var zero) ∨̇ (var (suc s) ≐ var zero)))))

IsSuccCard : V ℓ → V ℓ → Type (ℓ-suc ℓ)
IsSuccCard s k =
  IsCard s × (⟨ k ∈ s ⟩ × ((α : V ℓ) → IsCard α → ⟨ k ∈ α ⟩ → ∥ ⟨ s ∈ α ⟩ ⊎ (s ≡ α) ∥₁))

isPropIsSuccCard : (s k : V ℓ) → isProp (IsSuccCard s k)
isPropIsSuccCard s k =
  isProp× (isPropIsCard s)
    (isProp× (snd (k ∈ s)) (isPropΠ (λ α → isPropΠ (λ _ → isPropΠ (λ _ → squash₁)))))

succCardFo-adequate : ∀ {n} (s k : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ succCardFo s k) ≡ (IsSuccCard (⟦ var s ⟧ γ) (⟦ var k ⟧ γ)
    , isPropIsSuccCard (⟦ var s ⟧ γ) (⟦ var k ⟧ γ))
succCardFo-adequate s k γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ succCardFo s k ⟩ → IsSuccCard (⟦ var s ⟧ γ) (⟦ var k ⟧ γ)
  fwd (hs , hk , hλ) =
    subst ⟨_⟩ (cardFo-adequate s γ) hs ,
    (hk , λ α icard hκ → hλ α (subst ⟨_⟩ (sym (cardFo-adequate zero (α ∷ γ))) icard) hκ)
  bwd : IsSuccCard (⟦ var s ⟧ γ) (⟦ var k ⟧ γ) → ⟨ γ ⊨ succCardFo s k ⟩
  bwd (cs , k∈s , least) =
    subst ⟨_⟩ (sym (cardFo-adequate s γ)) cs ,
    (k∈s , λ α hcard hκ → least α (subst ⟨_⟩ (cardFo-adequate zero (α ∷ γ)) hcard) hκ)
```

<!--en-->
The fixed-arity forms are the ones the statement of the chapter that consumes
this layer will name: `φ-bij` at three free variables, `φ-eq` at two, `φ-card`
at one, `φ-succ-card` at two. The de Bruijn convention is that variable zero is
the first argument, so `φ-card` reads "the set at index zero is a cardinal"
and `φ-succ-card` reads "the set at index zero is the successor cardinal of
the set at index one".
<!--zh-->
固定元数的形态是消费本章的那一章的陈述将要点名的：`φ-bij` 三个自由变量，`φ-eq` 两个，`φ-card` 一个，`φ-succ-card` 两个。de Bruijn 约定是零号变元即第一个实参，故 `φ-card` 读作「零号索引处的集合是基数」，`φ-succ-card` 读作「零号索引处的集合是一号索引处集合的后继基数」。
<!--/-->

```agda
φ-bij : ∀ {ℓk} {K : Type ℓk} → Formula K 3 ; φ-bij = bijFo zero (suc zero) (suc (suc zero))
φ-eq : ∀ {ℓk} {K : Type ℓk} → Formula K 2 ; φ-eq = eqFo zero (suc zero)
φ-card : ∀ {ℓk} {K : Type ℓk} → Formula K 1 ; φ-card = cardFo zero
φ-succ-card : ∀ {ℓk} {K : Type ℓk} → Formula K 2 ; φ-succ-card = succCardFo zero (suc zero)
```
```
