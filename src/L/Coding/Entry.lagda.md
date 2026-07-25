# Certificate entries

<!--en-->
A satisfaction certificate is a set of entries, and an entry records three
things: an arity, a code, and an environment. So every one of the twelve clauses
a certificate is made of has to say, at some point, "this triple belongs to the
certificate". This chapter gives that single form, once, so the clauses can use
it and say nothing about how a triple is built.

The encoding nests: a triple is a pair whose second component is a pair. Reading
it back therefore means reaching a component of a component, and the object
language reaches downward only through bounded quantifiers. Three of them
suffice, naming the entry, the intermediate brace set the outer pair introduces,
and the inner pair; the Kuratowski reader then pins both layers at once.
<!--zh-->
满足证书是一批条目之集，而每个条目记录三样东西：一个元数、一个码、一个环境。故构成证书的十二条子句，每一条在某处都必须说「这个三元组属于该证书」。本章把那个唯一的形式一次给出，好让诸子句直接取用，而不必谈论三元组是怎么造出来的。

编码是嵌套的：三元组是一个对，其第二分量又是一个对。读回它因而意味着抵达成员之成员，而对象语言只经有界量词向下抵达。三层就够了，分别为条目、外层对所引入的中间花括号集合、以及内层对命名；随后 Kuratowski 读式一举钉住两层。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Entry {ℓ : Level} where

open import FOL.Syntax using ( var; Formula; _∧̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Coding.Base {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate; ∈pair-introR )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆; ⁅_⁆s )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## The triple, as a formula
<!--zh-->
## 作为公式的三元组
<!--/-->

<!--en-->
Three nested bounded existentials, innermost last. The first names an entry of
the certificate, the second the brace set that the outer pair is built from, and
the third the inner pair itself. Positions mentioned from outside shift out by
three accordingly, and the body is two applications of the Kuratowski reader: one
saying the entry is the arity paired with something, one saying that something is
the code paired with the environment.
<!--zh-->
三层嵌套的有界存在，最内的在最后。第一层为证书的一个条目命名，第二层为外层对所由构造的花括号集合命名，第三层为内层对本身命名。从外部提到的位置相应向外移三位，而主体是 Kuratowski 读式的两次应用：一次说该条目是元数与某物之对，一次说那个某物是码与环境之对。
<!--/-->

```agda
tripleInT : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula (V ℓ) n
tripleInT T N s e =
  ∃̇∈ (var T) (∃̇∈ (var zero) (∃̇∈ (var zero)
    ( prAt (suc (suc zero)) (suc (suc (suc N))) zero
    ∧̇ prAt zero (suc (suc (suc s))) (suc (suc (suc e))) )))

Δ₀-tripleInT : ∀ {n} (T N s e : Fin n) → Δ₀ (tripleInT T N s e)
Δ₀-tripleInT T N s e =
  δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧
    (Δ₀-prAt (suc (suc zero)) (suc (suc (suc N))) zero)
    (Δ₀-prAt zero (suc (suc (suc s))) (suc (suc (suc e)))))))
```

<!--en-->
## Adequacy
<!--zh-->
## 适足性
<!--/-->

<!--en-->
Forwards, the three witnesses are stripped and the two readers rewrite the entry
into the triple, which then carries its membership along. The rewriting is
extracted as a named step rather than left inline, because its conclusion is a
membership in a set the environment mentions, and leaving such a conclusion
inside three nested eliminations is how these proofs become uncheckable.

Backwards, the witnesses have to be produced. They are exactly the sets the
Kuratowski encoding builds, and the memberships they need are the pair
introductions, taken from the reader chapter.
<!--zh-->
正向：剥掉三个见证，两条读式把条目改写成那个三元组，随后隶属关系随之而行。改写抽成具名的一步而非内联，因为它的结论是「属于一个环境所提到的集合」，而把这样的结论留在三层嵌套的消去里面，正是这类证明变得不可检查的方式。

反向：见证必须被造出来。它们恰是 Kuratowski 编码所构造的那些集合，而它们所需的隶属事实就是读式那一章的对引入引理。
<!--/-->

```agda
tripleInT-adequate : ∀ {n} (T N s e : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ tripleInT T N s e)
  ≡ (pr (⟦ var N ⟧ γ) (pr (⟦ var s ⟧ γ) (⟦ var e ⟧ γ)) ∈ ⟦ var T ⟧ γ)
tripleInT-adequate T N s e γ = ⇔toPath fwd bwd
  where
  T' = ⟦ var T ⟧ γ
  N' = ⟦ var N ⟧ γ
  s' = ⟦ var s ⟧ γ
  e' = ⟦ var e ⟧ γ

  step : (q c w : V ℓ) → ⟨ q ∈ T' ⟩
       → ⟨ (w ∷ c ∷ q ∷ γ) ⊨ prAt (suc (suc zero)) (suc (suc (suc N))) zero ⟩
       → ⟨ (w ∷ c ∷ q ∷ γ) ⊨ prAt zero (suc (suc (suc s))) (suc (suc (suc e))) ⟩
       → ⟨ pr N' (pr s' e') ∈ T' ⟩
  step q c w q∈T sat₁ sat₂ =
    subst (λ z → ⟨ z ∈ T' ⟩)
      (subst ⟨_⟩
        (prAt-adequate (suc (suc zero)) (suc (suc (suc N))) zero (w ∷ c ∷ q ∷ γ))
        sat₁
       ∙ cong (pr N')
          (subst ⟨_⟩
            (prAt-adequate zero (suc (suc (suc s))) (suc (suc (suc e)))
              (w ∷ c ∷ q ∷ γ))
            sat₂))
      q∈T

  fwd : ⟨ γ ⊨ tripleInT T N s e ⟩ → ⟨ pr N' (pr s' e') ∈ T' ⟩
  fwd = PT.rec ((pr N' (pr s' e') ∈ T') .snd)
    (λ { (q , q∈T , h₁) → PT.rec ((pr N' (pr s' e') ∈ T') .snd)
      (λ { (c , _ , h₂) → PT.rec ((pr N' (pr s' e') ∈ T') .snd)
        (λ { (w , _ , sat₁ , sat₂) → step q c w q∈T sat₁ sat₂ })
        h₂ })
      h₁ })

  bwd : ⟨ pr N' (pr s' e') ∈ T' ⟩ → ⟨ γ ⊨ tripleInT T N s e ⟩
  bwd h =
    ∣ pr N' (pr s' e') , h
    , ∣ ⁅ N' , pr s' e' ⁆
      , ∈pair-introR {u = ⁅ N' ⁆s} {v = ⁅ N' , pr s' e' ⁆}
                     {y = ⁅ N' , pr s' e' ⁆} refl
      , ∣ pr s' e'
        , ∈pair-introR {u = N'} {v = pr s' e'} {y = pr s' e'} refl
        , subst ⟨_⟩
            (sym (prAt-adequate (suc (suc zero)) (suc (suc (suc N))) zero
              (pr s' e' ∷ ⁅ N' , pr s' e' ⁆ ∷ pr N' (pr s' e') ∷ γ))) refl
        , subst ⟨_⟩
            (sym (prAt-adequate zero (suc (suc (suc s))) (suc (suc (suc e)))
              (pr s' e' ∷ ⁅ N' , pr s' e' ⁆ ∷ pr N' (pr s' e') ∷ γ))) refl
        ∣₁
      ∣₁
    ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`tripleInT`{.Agda} is the single object-language form for "this arity, code and
environment are recorded in this certificate", Δ₀ and adequate. Every clause of
a satisfaction certificate reads and writes its entries through it, and none of
them has to mention how a triple is encoded.
<!--zh-->
`tripleInT`{.Agda} 是「这个元数、码与环境记录在这份证书里」的唯一对象语言形式，Δ₀ 且适足。满足证书的每一条子句都经它读写自己的条目，而没有一条需要提到三元组是如何编码的。
<!--/-->
