# Recovering a formula from a code

<!--en-->
The decode. Given a set that is closed and shaped at a carrier, a member handed
over as a key at a stated arity is the key of a formula **over that carrier**,
and the formula can be produced.

Which alphabet the formula is over is the whole point of the chapter, and it is
decided here rather than at the end. A formula over the model would be recovered
by the same six frames and would be useless to the consumer, whose index type is
the formulas over one carrier. So the target is stated over an alphabet, the
alphabet is a parameter, and the one thing the shape predicate cannot supply
about it, that the carrier's members are the alphabet's image, is a hypothesis
beside it.

The target being the alphabet's own coding also makes the frames shorter rather
than longer. Over the model each frame had to bridge two codings, the model's and
the hierarchy's, before it could compare a code with a payload; over the alphabet
the code already is an element of the hierarchy and the bridge is gone.

What is *not* proved here is that every member is such a key, and the set is what
owes it. Shapedness binds the arity component existentially and puts no condition
on it, so a set holding a pair whose first component is not a numeral satisfies
both halves and this theorem says nothing about it. The set the next chapter
builds pins the arity from outside, by separating inside a family indexed at one
fixed arity, which is why the predicate is not asked to.

The recursion runs on the rank of the code, not on the code and not on the key.
Not on the code because membership does not descend into a Kuratowski pair; not
on the key because the key carries the arity beside the code and rank arithmetic
on a pair is a fact nobody has proved. Carrying the arity as a natural number
alongside, and descending on the code alone, needs neither.

One step is `peel`{.Agda}, one descent is the previous chapter, and the ten
cases collapse to six, because the ten tags have six shapes between them and
what changes inside a shape is a tag and a constructor.
<!--zh-->
解码。给定一个在某载体上既封闭又成形的集合，一个以「某个已言明元数处的键」的形式递交过来的成员，就是**该载体之上**某条公式的键，而那条公式可以被造出来。

那条公式落在哪个字母表上，是整章的要害，而它在此处定案、不在末尾。模型之上的公式会由同样六个框架还原出来，而对消费方毫无用处，因为它的索引类型是单个载体之上的诸公式。故目标在一个字母表上陈述，字母表是一个参数，而关于它的、形状谓词供不出的那一件事，即载体的诸成员就是字母表的像，作为一条假设摆在旁边。

目标取字母表自己的编码，也使诸框架变短、而不是变长。在模型之上，每个框架先得把模型的与层级的两套编码搭起桥来，才能把一个码与一个载荷相比；在字母表之上，码本来就是层级的元素，那座桥没有了。

此处**没有**证明的是「每个成员都是这样一个键」，而欠这笔账的是那个集合。形状把元数分量存在量化、且对它不加任何条件，故一个持有「第一分量不是数码的对」的集合同样满足两半，而本定理对它什么也没说。下一章所造的那个集合从外面把元数钉住，即在一个固定元数上被索引的族之内作分离，这正是不去要求那条谓词的原因。

递归跑在**码的秩**上，不跑在码上、也不跑在键上。不跑在码上，是因为成员关系不下降进 Kuratowski 的对；不跑在键上，是因为键在码旁边还带着元数，而「对的秩的算术」是一条没人证过的事实。把元数作为一个自然数在旁边带着、只对码下降，两者都不需要。

一步是 `peel`{.Agda}，一次下降是上一章，而十个情形收拢为六个，因为十个标签之间只有六种形状，而一种形状之内变动的只是一个标签与一个构造子。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Recover {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Rank {ℓ} using ( rank )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.Closure {ℓ} using ( closedAt )
open import L.Coding.Descent {ℓ} using ( payload≺; leftPart; rightPart )
open import L.Coding.Shape {ℓ}
  using ( shapedAt; isTmAt-decode; Onto; BinWit; UnWit; bothTm; zeroPay
        ; module Peel )

import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Keys, and what is to be produced
<!--zh-->
## 键，与要造出的东西
<!--/-->

<!--en-->
A key is an arity-tagged code, and the closed set holds keys. What the decode
produces is a formula whose code is the key's code component, at the arity the
key's other component names, with its constants drawn from the alphabet.

The code is taken of the formula's image in the hierarchy, which is what
`mapFo`{.Agda} is doing there. It is not a step of the construction: relabelling
commutes with every constructor definitionally, so a formula over the alphabet
and its image code together exactly as a formula over the model does.
<!--zh-->
键是带元数标签的码，而那个封闭集持有的是键。解码所造出的，是一条公式，其码即该键的码分量，元数即该键另一个分量所点名的那个，而其诸常元取自那个字母表。

码是对该公式在层级中的像取的，那正是 `mapFo`{.Agda} 在那里做的事。它不是构造的一步：常量改名按定义与每个构造子交换，故字母表之上的一条公式连同它的像，其编码与模型之上的公式完全一样。
<!--/-->

```agda
keyOf : ℕ → S → S
keyOf n x = prʟ (numeralL n) x

keyOf-fst : (n : ℕ) (x : S) → fst (keyOf n x) ≡ pr (# n) (fst x)
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl

Coded : {K : Type ℓ} (f : K → V ℓ) → ℕ → S → Type (ℓ-suc ℓ)
Coded {K} f n x = ∥ Σ[ φ ∈ Formula K n ] (VCode.⌜ mapFo f φ ⌝ ≡ fst x) ∥₁
```

<!--en-->
## The recursion
<!--zh-->
## 那场递归
<!--/-->

<!--en-->
The motive quantifies over the arity as well as the code, because a quantifier
raises it and the induction must be free to come back at a larger one. That is
the whole reason the arity is a natural number here rather than a set: it is
carried, not descended into. The carrier is not quantified over at all: it is a
slot of the environment, fixed before the induction starts, and the induction
never asks what is in it.

The alphabet's two parameters ride outside the induction for the same reason.
Only two of the six frames look at them, the two whose payload holds a term, and
they look at them by handing the hypothesis straight to the term decode.
<!--zh-->
动机除码之外还对元数作量化，因为量词会抬升元数，而归纳必须自由地在一个更大的元数上回来。这正是元数在此处是一个自然数、而不是一个集合的全部理由：它是被带着走的，不是被下降进去的。载体则压根不被量化：它是环境的一位，在归纳开跑之前就已固定，而归纳从不问那里面装着什么。

字母表的两个参数出于同样的理由骑在归纳之外。六个框架里只有两个去看它们，即载荷里放着词项的那两个，而它们看的方式，是把那条假设径直递给词项解码。
<!--/-->

```agda
module Decode {K : Type ℓ} (f : K → V ℓ)
              {m : ℕ} (C A : Fin m) (γ : S ^ m) (onto : Onto f A γ)
              (hcl : ⟨ γ ⊨ closedAt C ⟩) (hsh : ⟨ γ ⊨ shapedAt C A ⟩) where
  open Peel C A γ hcl hsh

  Wf : ℕ → S → Type (ℓ-suc ℓ)
  Wf n x = ⟨ keyOf n x ∈ˢ lookup C γ ⟩

  recover : (n : ℕ) (x : S) → Wf n x → Coded f n x
  recover n x = ∈-induction go (rank (fst x)) n x refl
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P r = (j : ℕ) (z : S) → rank (fst z) ≡ r → Wf j z → Coded f j z

    go : (r : V ℓ) → ((y : V ℓ) → ⟨ y ∈ r ⟩ → P y) → P r
    go r IH j z qr wz = PT.rec squash₁ fill (peel (keyOf j z) wz)
      where
      D = fst (lookup C γ)

      rec : (i : ℕ) (u : S) → ⟨ rank (fst u) ∈ rank (fst z) ⟩
          → Wf i u → Coded f i u
      rec i u lt wu = IH (rank (fst u))
        (subst (λ w → ⟨ rank (fst u) ∈ w ⟩) qr lt) i u refl wu
```

The arity numeral and the payload, read out of the key's shape.

```agda
      split : (N : S) (p : V ℓ) → fst (keyOf j z) ≡ pr (fst N) p
            → (# j ≡ fst N) × (fst z ≡ p)
      split N p e = pr-inj (sym (keyOf-fst j z) ∙ e)

      inD : (i : ℕ) (N u : S) → # i ≡ fst N → ⟨ pr (fst N) (fst u) ∈ D ⟩
          → Wf i u
      inD i N u qN h = subst (λ w → ⟨ w ∈ D ⟩)
        (cong₂ pr (sym qN) refl ∙ sym (keyOf-fst i u)) h

      inD⁺ : (i : ℕ) (N u : S) → # i ≡ fst N
           → ⟨ pr (sucV (fst N)) (fst u) ∈ D ⟩ → Wf (suc i) u
      inD⁺ i N u qN h = subst (λ w → ⟨ w ∈ D ⟩)
        (cong₂ pr (cong sucV (sym qN)) refl ∙ sym (keyOf-fst (suc i) u)) h
```

The six frames. Each takes the constructor's coding equation rather than
leaving the elaborator to find it: with the constructor a variable, nothing
reduces, and the unification is the whole cost. Over the alphabet the equation
is still `refl` at every call site, because relabelling commutes with every
constructor definitionally.

```agda
      atom : (k : ℕ) (op : ∀ {i} → Term K i → Term K i → Formula K i)
           → (∀ {i} (t u : Term K i)
              → VCode.⌜ mapFo f (op t u) ⌝
                ≡ VCode.mkTag k (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ))
           → BinWit k (bothTm A) γ (keyOf j z) → Coded f j z
      atom k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (t , qt) → PT.map
            (λ { (u , qu) → op t u
               , ( qop t u
                 ∙ cong (VCode.mkTag k) (cong₂ pr qt qu)
                 ∙ sym qx ) })
            (isTmAt-decode f zero (suc (suc zero)) (suc (suc (suc (suc A))))
              (b ∷ a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) onto hb) })
          (isTmAt-decode f (suc zero) (suc (suc zero)) (suc (suc (suc (suc A))))
            (b ∷ a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) onto ha)
        where
        sp = split N (pr (# k) (pr (fst a) (fst b))) e
        qN = sp .fst
        qx = sp .snd

      binSame : (k : ℕ) (op : ∀ {i} → Formula K i → Formula K i → Formula K i)
              → (∀ {i} (φ ψ : Formula K i)
                 → VCode.⌜ mapFo f (op φ ψ) ⌝
                   ≡ VCode.mkTag k (pr VCode.⌜ mapFo f φ ⌝ VCode.⌜ mapFo f ψ ⌝))
              → BinSame k (keyOf j z) → Coded f j z
      binSame k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (φ , qφ) → PT.map
            (λ { (ψ , qψ) → op φ ψ
               , ( qop φ ψ
                 ∙ cong (VCode.mkTag k) (cong₂ pr qφ qψ)
                 ∙ sym qx ) })
            (rec j b (subst (λ w → ⟨ rank (fst b) ∈ rank w ⟩) (sym qx)
                       (rightPart (# k) (fst a) (fst b)))
                     (inD j N b qN hb)) })
          (rec j a (subst (λ w → ⟨ rank (fst a) ∈ rank w ⟩) (sym qx)
                     (leftPart (# k) (fst a) (fst b)))
                   (inD j N a qN ha))
        where
        sp = split N (pr (# k) (pr (fst a) (fst b))) e
        qN = sp .fst
        qx = sp .snd

      unSame : (k : ℕ) (op : ∀ {i} → Formula K i → Formula K i)
             → (∀ {i} (φ : Formula K i)
                → VCode.⌜ mapFo f (op φ) ⌝ ≡ VCode.mkTag k VCode.⌜ mapFo f φ ⌝)
             → UnSame k (keyOf j z) → Coded f j z
      unSame k op qop (N , (a , (e , ha))) = PT.map
        (λ { (φ , qφ) → op φ
           , ( qop φ ∙ cong (VCode.mkTag k) qφ ∙ sym qx ) })
        (rec j a (subst (λ w → ⟨ rank (fst a) ∈ rank w ⟩) (sym qx)
                   (payload≺ (# k) (fst a)))
                 (inD j N a qN ha))
        where
        sp = split N (pr (# k) (fst a)) e
        qN = sp .fst
        qx = sp .snd

      konst : (k : ℕ) (op : ∀ {i} → Formula K i)
            → (∀ i → VCode.⌜ mapFo f (op {i}) ⌝ ≡ VCode.mkTag k (# 0))
            → UnWit k zeroPay γ (keyOf j z) → Coded f j z
      konst k op qop (N , (a , (e , ha))) = ∣ op
        , ( qop j ∙ cong (VCode.mkTag k) (sym (ha ∙ numeralL-fst 0))
          ∙ sym qx ) ∣₁
        where
        qx = split N (pr (# k) (fst a)) e .snd

      unSucc : (k : ℕ) (op : ∀ {i} → Formula K (suc i) → Formula K i)
             → (∀ {i} (φ : Formula K (suc i))
                → VCode.⌜ mapFo f (op φ) ⌝ ≡ VCode.mkTag k VCode.⌜ mapFo f φ ⌝)
             → UnSucc k (keyOf j z) → Coded f j z
      unSucc k op qop (N , (a , (e , ha))) = PT.map
        (λ { (φ , qφ) → op φ
           , ( qop φ ∙ cong (VCode.mkTag k) qφ ∙ sym qx ) })
        (rec (suc j) a
          (subst (λ w → ⟨ rank (fst a) ∈ rank w ⟩) (sym qx)
            (payload≺ (# k) (fst a)))
          (inD⁺ j N a qN ha))
        where
        sp = split N (pr (# k) (fst a)) e
        qN = sp .fst
        qx = sp .snd

      bnd : (k : ℕ) (op : ∀ {i} → Term K i → Formula K (suc i) → Formula K i)
          → (∀ {i} (t : Term K i) (φ : Formula K (suc i))
             → VCode.⌜ mapFo f (op t φ) ⌝
               ≡ VCode.mkTag k (pr VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f φ ⌝))
          → BinSucc k (keyOf j z) → Coded f j z
      bnd k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (t , qt) → PT.map
            (λ { (φ , qφ) → op t φ
               , ( qop t φ
                 ∙ cong (VCode.mkTag k) (cong₂ pr qt qφ)
                 ∙ sym qx ) })
            (rec (suc j) b (subst (λ w → ⟨ rank (fst b) ∈ rank w ⟩) (sym qx)
                             (rightPart (# k) (fst a) (fst b)))
                           (inD⁺ j N b qN hb)) })
          (isTmAt-decode f zero (suc zero) (suc (suc (suc A)))
            (a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) onto ha)
        where
        sp = split N (pr (# k) (pr (fst a) (fst b))) e
        qN = sp .fst
        qx = sp .snd

      fill : PeelWit (keyOf j z) → Coded f j z
      fill =
        Sum.rec (atom 0 _∈̇_ (λ _ _ → refl))
        (Sum.rec (atom 1 _≐_ (λ _ _ → refl))
        (Sum.rec (binSame 2 _∧̇_ (λ _ _ → refl))
        (Sum.rec (binSame 3 _∨̇_ (λ _ _ → refl))
        (Sum.rec (binSame 4 _⇒̇_ (λ _ _ → refl))
        (Sum.rec (konst 5 ⊥̇ (λ _ → refl))
        (Sum.rec (unSucc 6 ∃̇_ (λ _ → refl))
        (Sum.rec (unSucc 7 ∀̇_ (λ _ → refl))
        (Sum.rec (bnd 8 ∀̇∈ (λ _ _ → refl))
        (bnd 9 ∃̇∈ (λ _ _ → refl))))))))))

```
