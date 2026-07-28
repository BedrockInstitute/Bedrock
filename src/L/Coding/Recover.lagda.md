# Recovering a formula from a code

<!--en-->
The decode. Given a set that is closed and shaped, a member handed over as a key
at a stated arity is the key of a formula, and the formula can be produced.

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

One step is `peel`{.Agda}, one descent is the previous chapter, and the twelve
cases collapse to six, because the twelve tags have six shapes between them and
what changes inside a shape is a tag and a constructor.
<!--zh-->
解码。给定一个既封闭又成形的集合，一个以「某个已言明元数处的键」的形式递交过来的成员，就是某条公式的键，而那条公式可以被造出来。

此处**没有**证明的是「每个成员都是这样一个键」，而欠这笔账的是那个集合。形状把元数分量存在量化、且对它不加任何条件，故一个持有「第一分量不是数码的对」的集合同样满足两半，而本定理对它什么也没说。下一章所造的那个集合从外面把元数钉住，即在一个固定元数上被索引的族之内作分离，这正是不去要求那条谓词的原因。

递归跑在**码的秩**上，不跑在码上、也不跑在键上。不跑在码上，是因为成员关系不下降进 Kuratowski 的对；不跑在键上，是因为键在码旁边还带着元数，而「对的秩的算术」是一条没人证过的事实。把元数作为一个自然数在旁边带着、只对码下降，两者都不需要。

一步是 `peel`{.Agda}，一次下降是上一章，而十二个情形收拢为六个，因为十二个标签之间只有六种形状，而一种形状之内变动的只是一个标签与一个构造子。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Recover {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Rank {ℓ} using ( rank )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; tagBridge; closedAt; module LCode )
open import L.Coding.Descent {ℓ} using ( payload≺; leftPart; rightPart )
open import L.Coding.Shape {ℓ}
  using ( shapedAt; isTmAt-decode; BinWit; UnWit; bothTm; zeroPay; module Peel )

open import Cubical.Data.Sum using ( inl; inr )
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
key's other component names.
<!--zh-->
键是带元数标签的码，而那个封闭集持有的是键。解码所造出的，是一条公式，其码即该键的码分量，元数即该键另一个分量所点名的那个。
<!--/-->

```agda
keyOf : ℕ → S → S
keyOf n x = prʟ (numeralL n) x

keyOf-fst : (n : ℕ) (x : S) → fst (keyOf n x) ≡ pr (# n) (fst x)
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl

Coded : ℕ → S → Type (ℓ-suc ℓ)
Coded n x = ∥ Σ[ φ ∈ Formula S n ] (fst LCode.⌜ φ ⌝ ≡ fst x) ∥₁
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
carried, not descended into.
<!--zh-->
动机除码之外还对元数作量化，因为量词会抬升元数，而归纳必须自由地在一个更大的元数上回来。这正是元数在此处是一个自然数、而不是一个集合的全部理由：它是被带着走的，不是被下降进去的。
<!--/-->

```agda
module Decode {m : ℕ} (C : Fin m) (γ : S ^ m)
              (hcl : ⟨ γ ⊨ closedAt C ⟩) (hsh : ⟨ γ ⊨ shapedAt C ⟩) where
  open Peel C γ hcl hsh

  Wf : ℕ → S → Type (ℓ-suc ℓ)
  Wf n x = ⟨ keyOf n x ∈ˢ lookup C γ ⟩

  recover : (n : ℕ) (x : S) → Wf n x → Coded n x
  recover n x = ∈-induction go (rank (fst x)) n x refl
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P r = (j : ℕ) (z : S) → rank (fst z) ≡ r → Wf j z → Coded j z

    go : (r : V ℓ) → ((y : V ℓ) → ⟨ y ∈ r ⟩ → P y) → P r
    go r IH j z qr wz = PT.rec squash₁ fill (peel (keyOf j z) wz)
      where
      D = fst (lookup C γ)

      rec : (i : ℕ) (u : S) → ⟨ rank (fst u) ∈ rank (fst z) ⟩
          → Wf i u → Coded i u
      rec i u lt wu = IH (rank (fst u))
        (subst (λ w → ⟨ rank (fst u) ∈ w ⟩) qr lt) i u refl wu

      -- the arity numeral and the payload, read out of the key's shape
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

      -- the six frames. Each takes the constructor's coding equation rather
      -- than leaving the elaborator to find it: with the constructor a
      -- variable, nothing reduces, and the unification is the whole cost.
      atom : (k : ℕ) (op : ∀ {i} → Term S i → Term S i → Formula S i)
           → (∀ {i} (t u : Term S i)
              → LCode.⌜ op t u ⌝ ≡ LCode.mkTag k (prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ u ⌝ᵗ))
           → BinWit k bothTm γ (keyOf j z) → Coded j z
      atom k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (t , qt) → PT.map
            (λ { (u , qu) → op t u
               , ( cong fst (qop t u)
                 ∙ tagBridge k (prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ u ⌝ᵗ)
                 ∙ cong (pr (# k)) (prʟ-fst LCode.⌜ t ⌝ᵗ LCode.⌜ u ⌝ᵗ
                     ∙ cong₂ pr qt qu)
                 ∙ sym qx ) })
            (isTmAt-decode zero (suc (suc zero))
              (b ∷ a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) hb) })
          (isTmAt-decode (suc zero) (suc (suc zero))
            (b ∷ a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) ha)
        where
        sp = split N (pr (# k) (pr (fst a) (fst b))) e
        qN = sp .fst
        qx = sp .snd

      binSame : (k : ℕ) (op : ∀ {i} → Formula S i → Formula S i → Formula S i)
              → (∀ {i} (φ ψ : Formula S i)
                 → LCode.⌜ op φ ψ ⌝ ≡ LCode.mkTag k (prʟ LCode.⌜ φ ⌝ LCode.⌜ ψ ⌝))
              → BinSame k (keyOf j z) → Coded j z
      binSame k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (φ , qφ) → PT.map
            (λ { (ψ , qψ) → op φ ψ
               , ( cong fst (qop φ ψ)
                 ∙ tagBridge k (prʟ LCode.⌜ φ ⌝ LCode.⌜ ψ ⌝)
                 ∙ cong (pr (# k)) (prʟ-fst LCode.⌜ φ ⌝ LCode.⌜ ψ ⌝
                     ∙ cong₂ pr qφ qψ)
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

      unSame : (k : ℕ) (op : ∀ {i} → Formula S i → Formula S i)
             → (∀ {i} (φ : Formula S i) → LCode.⌜ op φ ⌝ ≡ LCode.mkTag k LCode.⌜ φ ⌝)
             → UnSame k (keyOf j z) → Coded j z
      unSame k op qop (N , (a , (e , ha))) = PT.map
        (λ { (φ , qφ) → op φ
           , ( cong fst (qop φ) ∙ tagBridge k LCode.⌜ φ ⌝
             ∙ cong (pr (# k)) qφ ∙ sym qx ) })
        (rec j a (subst (λ w → ⟨ rank (fst a) ∈ rank w ⟩) (sym qx)
                   (payload≺ (# k) (fst a)))
                 (inD j N a qN ha))
        where
        sp = split N (pr (# k) (fst a)) e
        qN = sp .fst
        qx = sp .snd

      konst : (k : ℕ) (op : ∀ {i} → Formula S i)
            → (∀ i → LCode.⌜ op {i} ⌝ ≡ LCode.mkTag k (numeralL 0))
            → UnWit k zeroPay γ (keyOf j z) → Coded j z
      konst k op qop (N , (a , (e , ha))) = ∣ op
        , ( cong fst (qop j) ∙ tagBridge k (numeralL 0)
          ∙ cong (pr (# k)) (sym ha) ∙ sym qx ) ∣₁
        where
        qx = split N (pr (# k) (fst a)) e .snd

      unSucc : (k : ℕ) (op : ∀ {i} → Formula S (suc i) → Formula S i)
             → (∀ {i} (φ : Formula S (suc i))
                → LCode.⌜ op φ ⌝ ≡ LCode.mkTag k LCode.⌜ φ ⌝)
             → UnSucc k (keyOf j z) → Coded j z
      unSucc k op qop (N , (a , (e , ha))) = PT.map
        (λ { (φ , qφ) → op φ
           , ( cong fst (qop φ) ∙ tagBridge k LCode.⌜ φ ⌝
             ∙ cong (pr (# k)) qφ ∙ sym qx ) })
        (rec (suc j) a
          (subst (λ w → ⟨ rank (fst a) ∈ rank w ⟩) (sym qx)
            (payload≺ (# k) (fst a)))
          (inD⁺ j N a qN ha))
        where
        sp = split N (pr (# k) (fst a)) e
        qN = sp .fst
        qx = sp .snd

      bnd : (k : ℕ) (op : ∀ {i} → Term S i → Formula S (suc i) → Formula S i)
          → (∀ {i} (t : Term S i) (φ : Formula S (suc i))
             → LCode.⌜ op t φ ⌝ ≡ LCode.mkTag k (prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ φ ⌝))
          → BinSucc k (keyOf j z) → Coded j z
      bnd k op qop (N , (a , (b , (e , (ha , hb))))) =
        PT.rec squash₁
          (λ { (t , qt) → PT.map
            (λ { (φ , qφ) → op t φ
               , ( cong fst (qop t φ)
                 ∙ tagBridge k (prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ φ ⌝)
                 ∙ cong (pr (# k)) (prʟ-fst LCode.⌜ t ⌝ᵗ LCode.⌜ φ ⌝
                     ∙ cong₂ pr qt qφ)
                 ∙ sym qx ) })
            (rec (suc j) b (subst (λ w → ⟨ rank (fst b) ∈ rank w ⟩) (sym qx)
                             (rightPart (# k) (fst a) (fst b)))
                           (inD⁺ j N b qN hb)) })
          (isTmAt-decode zero (suc zero)
            (a ∷ N ∷ keyOf j z ∷ γ) j (sym qN) ha)
        where
        sp = split N (pr (# k) (pr (fst a) (fst b))) e
        qN = sp .fst
        qx = sp .snd

      fill : PeelWit (keyOf j z) → Coded j z
      fill (inl x) = atom 0 _∈̇_ (λ _ _ → refl) x
      fill (inr (inl x)) = atom 1 _≐_ (λ _ _ → refl) x
      fill (inr (inr (inl x))) = binSame 2 _∧̇_ (λ _ _ → refl) x
      fill (inr (inr (inr (inl x)))) = binSame 3 _∨̇_ (λ _ _ → refl) x
      fill (inr (inr (inr (inr (inl x))))) = binSame 4 _⇒̇_ (λ _ _ → refl) x
      fill (inr (inr (inr (inr (inr (inl x)))))) = unSame 5 ¬̇_ (λ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inl x))))))) = konst 6 ⊤̇ (λ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inr (inl x)))))))) =
        konst 7 ⊥̇ (λ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))) =
        unSucc 8 ∃̇_ (λ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x)))))))))) =
        unSucc 9 ∀̇_ (λ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl x))))))))))) =
        bnd 10 ∀̇∈ (λ _ _ → refl) x
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr x))))))))))) =
        bnd 11 ∃̇∈ (λ _ _ → refl) x
```
