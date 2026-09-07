# Reading codes from inside

<!--en-->
Codes are sets now, but a certificate living inside the model cannot use that
directly: it can only say things in the object language, and what it needs to say
is "this set is the code of a formula with such and such a shape". So the shapes
have to be spelled out as formulas, and this chapter spells them out.

The chapter provides the *readers*: object formulas saying "this set is the
singleton of that", "this is the unordered pair", and "this is the Kuratowski
pair". Their quantifiers are bounded, and their de Bruijn positions are
arguments, so the same formula serves at any depth of nesting. The adequacy
lemma for the assembled pair reader turns satisfaction into equality with a
Kuratowski pair; its singleton and unordered-pair clauses use the corresponding
set-theoretic characterizations.

The discipline throughout: nothing ever compares two code *values*. Membership
is transported along paths through the library's classification lemmas, and the
shape of a code is carried by the coding relation of Part 1. Comparing code
values directly is what makes these proofs stop terminating, and the previous
chapters were arranged specifically so that it never has to happen.
<!--zh-->
码如今是集合了，但住在模型内部的证书不能直接用这一点：它只能用对象语言说话，而它要说的是「这个集合是某种形状的公式的码」。所以那些形状必须被写成公式，本章就来写它们。

本章提供**读式**：说「这个集合是那个的单点集」「这是无序对」「这是 Kuratowski 对」的对象公式。它们的量词都有界，de Bruijn 位置取作参数，故同一条公式在任何嵌套深度上都能用。组装后的对读式配有适足引理，把满足关系换成与 Kuratowski 对的相等；其中的单点集与无序对子句使用相应的集合论特征刻画。

全程的纪律：任何时候都不比较两个码**值**。隶属关系经库的分类引理沿路径搬运，而码的形状由第一部的编码关系携带。直接比较码值，正是使这些证明停止终止的原因，而前几章的安排就是为了让这件事永远不必发生。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Base {ℓ : Level} where

open import FOL.Syntax
  using ( var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )

open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## Singletons and pairs, characterized
<!--zh-->
## 单点集与对的特征刻画
<!--/-->

<!--en-->
The library's classification specifications, named so the proofs below read as
membership reasoning. Then the two characterizations: a set whose only member is
`u` *is* the singleton of `u`, and a set whose members are exactly `u` and `v`
*is* their unordered pair. Both are one application of extensionality, and both
are the meta-level content the readers will express.
<!--zh-->
先给库的分类规格命名，好让下面的证明读起来像隶属关系的推理。然后是两条特征刻画：唯一成员为 `u` 的集合**就是** `u` 的单点集，而成员恰为 `u` 与 `v` 的集合**就是**它们的无序对。两者都是一次外延性的应用，也都是读式将要表达的元层内容。
<!--/-->

```agda
∈sgl-elim : {u y : V ℓ} → ⟨ y ∈ ⁅ u ⁆s ⟩ → y ≡ u
∈sgl-elim {u} {y} h =
    SetPackage.classification (SingletonPackage u) y .fst (∈∈ₛ {a = y} {b = ⁅ u ⁆s} .fst h)

∈sgl-intro : {u y : V ℓ} → y ≡ u → ⟨ y ∈ ⁅ u ⁆s ⟩
∈sgl-intro {u} {y} e = ∈∈ₛ {a = y} {b = ⁅ u ⁆s} .snd
    (SetPackage.classification (SingletonPackage u) y .snd e)

∈pair-elim : {u v y : V ℓ} → ⟨ y ∈ ⁅ u , v ⁆ ⟩ → ∥ (y ≡ u) ⊎ (y ≡ v) ∥₁
∈pair-elim {u} {v} {y} h = pairing-ax u v y .fst (∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .fst h)

∈pair-introL : {u v y : V ℓ} → y ≡ u → ⟨ y ∈ ⁅ u , v ⁆ ⟩
∈pair-introL {u} {v} {y} e = ∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .snd
    (pairing-ax u v y .snd ∣ inl e ∣₁)

∈pair-introR : {u v y : V ℓ} → y ≡ v → ⟨ y ∈ ⁅ u , v ⁆ ⟩
∈pair-introR {u} {v} {y} e = ∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .snd
    (pairing-ax u v y .snd ∣ inr e ∣₁)

sgl-char : (x u : V ℓ) → ⟨ u ∈ x ⟩ → ((y : V ℓ) → ⟨ y ∈ x ⟩ → y ≡ u) → x ≡ ⁅ u ⁆s
sgl-char x u hu hall = extensionalV (λ y → ⇔toPath (sub₁ y) (sub₂ y))
  where
  sub₁ : (y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ y ∈ ⁅ u ⁆s ⟩
  sub₁ y hy = ∈sgl-intro (hall y hy)
  sub₂ : (y : V ℓ) → ⟨ y ∈ ⁅ u ⁆s ⟩ → ⟨ y ∈ x ⟩
  sub₂ y hy = subst (λ z → ⟨ z ∈ x ⟩) (sym (∈sgl-elim hy)) hu


pair-char : (x u v : V ℓ) → ⟨ u ∈ x ⟩ → ⟨ v ∈ x ⟩
          → ((y : V ℓ) → ⟨ y ∈ x ⟩ → ∥ (y ≡ u) ⊎ (y ≡ v) ∥₁)
          → x ≡ ⁅ u , v ⁆
pair-char x u v hu hv hall = extensionalV (λ y → ⇔toPath (sub₁ y) (sub₂ y))
  where
  sub₁ : (y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ y ∈ ⁅ u , v ⁆ ⟩
  sub₁ y hy = PT.rec ((y ∈ ⁅ u , v ⁆) .snd)
    (Sum.rec (∈pair-introL {u = u} {v = v}) (∈pair-introR {u = u} {v = v})) (hall y hy)
  sub₂ : (y : V ℓ) → ⟨ y ∈ ⁅ u , v ⁆ ⟩ → ⟨ y ∈ x ⟩
  sub₂ y hy = PT.rec ((y ∈ x) .snd)
    (Sum.rec (λ e → subst (λ z → ⟨ z ∈ x ⟩) (sym e) hu)
             (λ e → subst (λ z → ⟨ z ∈ x ⟩) (sym e) hv)) (∈pair-elim hy)
```

<!--en-->
## The Kuratowski pair, at the meta level
<!--zh-->
## 元层的 Kuratowski 对
<!--/-->

<!--en-->
Before writing the reader, the fact it will express: a set is the Kuratowski pair
of `U` and `W` exactly when it has a member that is the singleton of `U`, a
member that is the unordered pair, and no other members. The two auxiliary
predicates are written in the shape the reader's satisfaction will unfold to, so
that the adequacy lemmas afterwards are one line each rather than a second proof.
<!--zh-->
在写读式之前，先给出它将要表达的事实：一个集合是 `U` 与 `W` 的 Kuratowski 对，恰当它有一个成员是 `U` 的单点集、有一个成员是那个无序对，且没有别的成员。两个辅助谓词按读式的满足关系将要展开成的形状写出，好让随后的适足引理各只需一行，而不是第二个证明。
<!--/-->

```agda
private
  SglOf : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  SglOf U w = ⟨ U ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ U)

  PairOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PairOf U W w =
    ⟨ U ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ U) ⊎ (z ≡ W) ∥₁))

  sglOf→≡ : {U w : V ℓ} → SglOf U w → w ≡ ⁅ U ⁆s
  sglOf→≡ {U} {w} (hu , hall) = sgl-char w U hu hall

  pairOf→≡ : {U W w : V ℓ} → PairOf U W w → w ≡ ⁅ U , W ⁆
  pairOf→≡ {U} {W} {w} (hu , hv , hall) = pair-char w U W hu hv hall

  sglOf⁅⁆ : (U : V ℓ) → SglOf U ⁅ U ⁆s
  sglOf⁅⁆ U = ∈sgl-intro refl , (λ z z∈ → ∈sgl-elim z∈)

  pairOf⁅⁆ : (U W : V ℓ) → PairOf U W ⁅ U , W ⁆
  pairOf⁅⁆ U W = ∈pair-introL refl , ∈pair-introR refl , (λ z z∈ → ∈pair-elim z∈)

  sglOf-subst : {U w : V ℓ} → w ≡ ⁅ U ⁆s → SglOf U w
  sglOf-subst {U} e = subst (SglOf U) (sym e) (sglOf⁅⁆ U)

  pairOf-subst : {U W w : V ℓ} → w ≡ ⁅ U , W ⁆ → PairOf U W w
  pairOf-subst {U} {W} e = subst (PairOf U W) (sym e) (pairOf⁅⁆ U W)

prChar-fwd : (Q U W : V ℓ)
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
  → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁)
  → Q ≡ pr U W
prChar-fwd Q U W h₁ h₂ h₃ = pair-char Q ⁅ U ⁆s ⁅ U , W ⁆
  (PT.rec ((⁅ U ⁆s ∈ Q) .snd)
    (λ { (w , hw , h) → subst (λ z → ⟨ z ∈ Q ⟩) (sglOf→≡ h) hw }) h₁)
  (PT.rec ((⁅ U , W ⁆ ∈ Q) .snd)
    (λ { (w , hw , h) → subst (λ z → ⟨ z ∈ Q ⟩) (pairOf→≡ h) hw }) h₂)
  (λ y hy → PT.map (Sum.map sglOf→≡ pairOf→≡) (h₃ y hy))


prChar-bwd : (Q U W : V ℓ) → Q ≡ pr U W
  → (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁)
  × ((∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁)
  × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁))
prChar-bwd Q U W e = h₁ , h₂ , h₃
  where
  inQ : {z : V ℓ} → ⟨ z ∈ pr U W ⟩ → ⟨ z ∈ Q ⟩
  inQ {z} h = subst (λ w → ⟨ z ∈ w ⟩) (sym e) h
  h₁ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
  h₁ = ∣ ⁅ U ⁆s , (inQ (∈pair-introL refl) , sglOf⁅⁆ U) ∣₁
  h₂ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
  h₂ = ∣ ⁅ U , W ⁆ , (inQ (∈pair-introR refl) , pairOf⁅⁆ U W) ∣₁
  h₃ : (y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁
  h₃ y y∈Q = PT.map (Sum.rec (λ q → inl (sglOf-subst q)) (λ q → inr (pairOf-subst q)))
    (∈pair-elim (subst (λ w → ⟨ y ∈ w ⟩) e y∈Q))
```

<!--en-->
## The readers
<!--zh-->
## 读式
<!--/-->

<!--en-->
Now the object formulas. Each takes the de Bruijn positions it speaks about, and
the bookkeeping is the usual one: a bounded quantifier binds a fresh variable at
position zero and pushes the others outward, so a position mentioned under one
binder appears as its successor.

Every clause is a bounded quantifier or an atom, so every reader is Δ₀ and its
witness is read straight off its shape.
<!--zh-->
现在是对象公式。每一条都取它所谈论的 de Bruijn 位置，而记账是老一套：有界量词在位置零绑定一个新变元，把其余的向外推，故在一层约束之下提到的位置以其后继出现。

每条子句都是有界量词或原子，故每条读式都是 Δ₀，其见证直接从形状读出。
<!--/-->

```agda
sglAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
sglAt k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

pairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
pairAt k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
            ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

```

<!--en-->
The assembled pair reader has three clauses: some member is the singleton,
some member is the pair, and every member is one of the two. The boundedness
checker certifies the resulting formula from its syntax.
<!--zh-->
组装好的对读式有三条子句：某个成员是那个单点集，某个成员是那个对，且每个成员二者居其一。有界性检查器从所得公式的语法给出证书。
<!--/-->

```agda
prAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
prAt q u v = (∃̇∈ (var q) (sglAt zero (suc u)))
          ∧̇ ((∃̇∈ (var q) (pairAt zero (suc u) (suc v)))
          ∧̇ (∀̇∈ (var q) (sglAt zero (suc u) ∨̇ pairAt zero (suc u) (suc v))))

Δ₀-prAt : ∀ {n} (q u v : Fin n) → Δ₀ (prAt q u v)
Δ₀-prAt q u v = checkΔ₀ (prAt q u v) tt

```

<!--en-->
## Adequacy
<!--zh-->
## 充分性
<!--/-->

<!--en-->
And the payoff. Unfolding what it means to satisfy `prAt` gives, clause for
clause, the hypotheses of the meta-level characterization: the truth algebra's
conjunction is a product, its bounded existential a truncated sum, its equality a
path. So each direction is the corresponding half of that characterization, and
the lemma is one line. This is why the auxiliary predicates above were written in
that particular shape.
<!--zh-->
然后是回报。展开满足 `prAt` 是什么意思，逐条子句得到的恰是元层特征刻画的诸前提：真值代数的合取是积，其有界存在是截断的和，其等词是路径。于是每个方向都是那条刻画的相应一半，引理只需一行。这正是上面那两个辅助谓词要写成那个特定形状的原因。
<!--/-->

```agda
prAt-adequate : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
              → (γ ⊨ prAt q u v) ≡ ((⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ))
                                   , setIsSet _ _)
prAt-adequate q u v γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → prChar-fwd _ _ _ h₁ h₂ h₃ })
  (λ e → prChar-bwd _ _ _ e)

```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`prAt`{.Agda} reads a Kuratowski pair from inside the object language; it is
Δ₀ and adequate. Everything a certificate needs
in order to destructure a code is now available in bounded form, with no
recursion and no comparison of code values. The chapters that follow build
certificates on top of these.
<!--zh-->
`prAt`{.Agda} 从对象语言内部读出 Kuratowski 对，它是 Δ₀ 且适足。证书解构一个码所需的一切，如今都以有界形式就位，无递归，也无码值的比较。随后诸章在这些之上搭建证书。
<!--/-->
