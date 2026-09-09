<!--en-->
# Closing a code slot under its seven constructors

A slot collects the codes available below one bound. To support structural recursion, this chapter proves that whenever a code is in the slot, the keys of all immediate parts required by its seven constructor shapes are in the slot as well.
<!--zh-->
# 使编码槽位对七种构造闭合

槽位收集某个界以下可用的编码。为了支持结构递归，本章证明：若一个编码位于槽位中，则七种构造形状所需的所有直接部件的键也位于其中。
<!--ja-->
# コードスロットを七つの構成子について閉じる

スロットは一つの上界より下で利用できるコードを集める。構造再帰を支えるため、コードがスロットに入れば、七つの構成子の形で必要となるすべての直下成分の鍵もスロットに入ることを示す。
<!--/-->

<!--en-->
The hypothesis the graph will state about its index set, discharged for the slot
a formula's own recursion is indexed by. It is the closure chapter's theorem
again, on the model's own coding rather than the hierarchy's, and it is shorter
here because the pieces it needs were built for the two halves and not for it.

Each of the seven clauses is four moves: invert the index to the formula whose
key it is, compute that formula's constructor from the clause's tag, put the
part's key back into the whole's slot, and carry it up the containment the
inversion returned. The four constructors with no subformula have nothing to say
and are not among the seven.
<!--zh-->
图对索引集所需的假设，在「一条公式自身的递归所索引的槽位」处得到满足。这是闭包一章的定理在模型编码上的对应结果，而非层级编码上的结果；此处的证明更短，因为所需部件已经为前述两个方向构造完毕。

七条子句每一条都分四步：把索引求逆回「它是谁的键」的那条公式、从子句的标签算出那条公式的构造子、把部件的键放回整体的槽里，再沿由求逆返回的那条包含关系提升到整体。没有子公式的那四个构造子不涉及这一论证，故不在这七条之列。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.SlotClosure {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( module LCode; prʟ; prʟ-fst )
open import L.Coding.Closure {ℓ} using ( closedAt; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.SatisfactionTable {ℓ} lem
  using ( keyʟ; keyʟ-shape; slot; satTable; slot-inv; module Parts )

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Putting a part's key back
<!--zh-->
## 把部件的键放回去
<!--ja-->
## 成分の鍵をスロットへ戻す
<!--/-->

<!--en-->
The descent lemmas place a component key below the enclosing code's key. Downward closure of the bound then returns that key to the same slot.
<!--zh-->
下降引理给出：部件的键位于外围编码的键之下。由界的向下闭合性，该键随之落回同一槽位。
<!--ja-->
降下補題により、成分の鍵は外側のコードの鍵より下にある。上界の下方閉性から、その鍵も同じスロットへ戻る。
<!--/-->

<!--en-->
The one computation, shared by all seven: the pair a clause reads is the part's
own key, once the arity and the payload component are identified. The successor
form is the same with the arity raised, which is the only difference the four
binding constructors make.
<!--zh-->
这段计算只需做一次，七条子句共用：一旦把元数与那个载荷分量认同起来，子句所读的那个对就是部件自己的键。后继的情形相同，只是元数抬高一级，而这也是那四个绑定变元的构造子造成的唯一差别。
<!--/-->

```agda
module _ (B : S) where
  private
    Sl : ∀ {n} → Formula S n → S
    Sl = slot B

  key≡ : ∀ {j} (χ : Formula S j) (ar p : V ℓ) → # j ≡ ar
       → p ≡ fst LCode.⌜ χ ⌝ → pr ar p ≡ fst (keyʟ χ)
  key≡ {j} χ ar p qa qp =
      cong₂ pr (sym qa) qp
    ∙ cong (λ w → pr w (fst LCode.⌜ χ ⌝)) (sym (numeralL-fst j))
    ∙ sym (prʟ-fst (numeralL j) LCode.⌜ χ ⌝)

  keyS≡ : ∀ {j} (χ : Formula S (suc j)) (ar p : V ℓ) → # j ≡ ar
        → p ≡ fst LCode.⌜ χ ⌝ → pr (sucV ar) p ≡ fst (keyʟ χ)
  keyS≡ {j} χ ar p qa qp =
      cong₂ pr (cong sucV (sym qa)) qp
    ∙ cong (λ w → pr w (fst LCode.⌜ χ ⌝)) (sym (numeralL-fst (suc j)))
    ∙ sym (prʟ-fst (numeralL (suc j)) LCode.⌜ χ ⌝)
```

<!--en-->
## The seven clauses
<!--zh-->
## 七条子句
<!--ja-->
## 七つの構成子の場合
<!--/-->

<!--en-->
Each constructor exposes a fixed collection of immediate subcodes. The seven clauses apply the generic component argument to those positions, yielding exactly the closure data required by code recursion.
<!--zh-->
每种构造都带有一组固定的直接子码。七条子句把通用部件论证应用到这些位置，恰好得到编码递归所需的闭合数据。
<!--ja-->
各構成子は決まった直下の部分コードをもつ。七つの場合について一般の成分論法をそれらの位置に適用し、コード再帰が必要とする閉性のデータを得る。
<!--/-->

<!--en-->
Two shared bodies, one per frame, and seven instantiations. What changes between
two clauses of the same frame is the tag and which part the constructor hands
back, and both are arguments.
<!--zh-->
共用主体有两段，每个框架一段，另加七次实例化。同一框架下两条子句之间不同的只有标签，以及该构造子给出哪个部件，而两者都是参数。
<!--/-->

```agda
  module _ {n : ℕ} (φ : Formula S n) {k : ℕ} (γ : S ^ k) where
    private
      δ : S ^ (suc (suc (suc k)))
      δ = B ∷ satTable B φ ∷ Sl φ ∷ γ

      Ci : Fin (suc (suc (suc k)))
      Ci = suc (suc zero)

    binSame : (k' : ℕ) (op : ∀ {m} → Formula S m → Formula S m → Formula S m)
            → (∀ {m} (ψ : Formula S m) → LCode.Match k' ψ
               → Σ[ a' ∈ Formula S m ] (Σ[ b' ∈ Formula S m ] (ψ ≡ op a' b')))
            → (∀ {m} (a' b' : Formula S m)
               → LCode.payOf (op a' b') ≡ prʟ LCode.⌜ a' ⌝ LCode.⌜ b' ⌝)
            → (∀ {m} (a' b' : Formula S m) (z : V ℓ)
               → ⟨ z ∈ fst (Sl a') ⟩ → ⟨ z ∈ fst (Sl (op a' b')) ⟩)
            → (∀ {m} (a' b' : Formula S m) (z : V ℓ)
               → ⟨ z ∈ fst (Sl b') ⟩ → ⟨ z ∈ fst (Sl (op a' b')) ⟩)
            → ⟨ δ ⊨ binShapeAt Ci k' (bothSameAt Ci) ⟩
    binSame k' op get payOp inL inR = binSameClosed-in Ci k' δ
      (λ c ar a b c∈ sh → PT.rec
        (isProp× (snd (pr (fst ar) (fst a) ∈ fst (Sl φ)))
                 (snd (pr (fst ar) (fst b) ∈ fst (Sl φ))))
        (λ { (m , ψ , (q , incl)) →
          let r  = keyʟ-shape ψ k' (fst ar) (pr (fst a) (fst b)) (sym q ∙ sh)
              g  = get ψ (r .fst)
              a' = g .fst
              b' = g .snd .fst
              eψ = g .snd .snd
              pay = sym (prʟ-fst LCode.⌜ a' ⌝ LCode.⌜ b' ⌝)
                  ∙ cong fst (sym (payOp a' b'))
                  ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
              inψ : (χ : Formula S m) → ⟨ fst (keyʟ χ) ∈ fst (Sl ψ) ⟩
                  → ⟨ fst (keyʟ χ) ∈ fst (Sl φ) ⟩
              inψ χ h = incl (fst (keyʟ χ)) h
          in subst (λ w → ⟨ w ∈ fst (Sl φ) ⟩)
               (sym (key≡ a' (fst ar) (fst a) (r .snd .fst) (sym (pr-inj pay .fst))))
               (inψ a' (subst (λ w → ⟨ fst (keyʟ a') ∈ fst (Sl w) ⟩) (sym eψ)
                 (inL a' b' _ (Parts.self B keyʟ a'))))
           , subst (λ w → ⟨ w ∈ fst (Sl φ) ⟩)
               (sym (key≡ b' (fst ar) (fst b) (r .snd .fst) (sym (pr-inj pay .snd))))
               (inψ b' (subst (λ w → ⟨ fst (keyʟ b') ∈ fst (Sl w) ⟩) (sym eψ)
                 (inR a' b' _ (Parts.self B keyʟ b')))) })
        (slot-inv B φ (fst c) c∈))

    andC : ⟨ δ ⊨ binShapeAt Ci 2 (bothSameAt Ci) ⟩
    andC = binSame 2 _∧̇_ (λ _ m → m) (λ _ _ → refl)
             (λ a' b' → Parts.left B keyʟ (a' ∧̇ b') a' b')
             (λ a' b' → Parts.right B keyʟ (a' ∧̇ b') a' b')

    orC : ⟨ δ ⊨ binShapeAt Ci 3 (bothSameAt Ci) ⟩
    orC = binSame 3 _∨̇_ (λ _ m → m) (λ _ _ → refl)
            (λ a' b' → Parts.left B keyʟ (a' ∨̇ b') a' b')
            (λ a' b' → Parts.right B keyʟ (a' ∨̇ b') a' b')

    impC : ⟨ δ ⊨ binShapeAt Ci 4 (bothSameAt Ci) ⟩
    impC = binSame 4 _⇒̇_ (λ _ m → m) (λ _ _ → refl)
             (λ a' b' → Parts.left B keyʟ (a' ⇒̇ b') a' b')
             (λ a' b' → Parts.right B keyʟ (a' ⇒̇ b') a' b')

    unSame : (k' : ℕ) (op : ∀ {m} → Formula S m → Formula S m)
           → (∀ {m} (ψ : Formula S m) → LCode.Match k' ψ
              → Σ[ a' ∈ Formula S m ] (ψ ≡ op a'))
           → (∀ {m} (a' : Formula S m) → LCode.payOf (op a') ≡ LCode.⌜ a' ⌝)
           → (∀ {m} (a' : Formula S m) (z : V ℓ)
              → ⟨ z ∈ fst (Sl a') ⟩ → ⟨ z ∈ fst (Sl (op a')) ⟩)
           → ⟨ δ ⊨ unShapeAt Ci k' (oneSameAt Ci) ⟩
    unSame k' op get payOp inA = unSameClosed-in Ci k' δ
      (λ c ar a c∈ sh → PT.rec (snd (pr (fst ar) (fst a) ∈ fst (Sl φ)))
        (λ { (m , ψ , (q , incl)) →
          let r  = keyʟ-shape ψ k' (fst ar) (fst a) (sym q ∙ sh)
              g  = get ψ (r .fst)
              a' = g .fst
              eψ = g .snd
              pay = cong fst (sym (payOp a'))
                  ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
          in subst (λ w → ⟨ w ∈ fst (Sl φ) ⟩)
               (sym (key≡ a' (fst ar) (fst a) (r .snd .fst) (sym pay)))
               (incl (fst (keyʟ a'))
                 (subst (λ w → ⟨ fst (keyʟ a') ∈ fst (Sl w) ⟩) (sym eψ)
                   (inA a' _ (Parts.self B keyʟ a')))) })
        (slot-inv B φ (fst c) c∈))

    unSucc : (k' : ℕ) (op : ∀ {m} → Formula S (suc m) → Formula S m)
           → (∀ {m} (ψ : Formula S m) → LCode.Match k' ψ
              → Σ[ a' ∈ Formula S (suc m) ] (ψ ≡ op a'))
           → (∀ {m} (a' : Formula S (suc m)) → LCode.payOf (op a') ≡ LCode.⌜ a' ⌝)
           → (∀ {m} (a' : Formula S (suc m)) (z : V ℓ)
              → ⟨ z ∈ fst (Sl a') ⟩ → ⟨ z ∈ fst (Sl (op a')) ⟩)
           → ⟨ δ ⊨ unShapeAt Ci k' (oneSuccAt Ci) ⟩
    unSucc k' op get payOp inA = unSuccClosed-in Ci k' δ
      (λ c ar a c∈ sh → PT.rec (snd (pr (sucV (fst ar)) (fst a) ∈ fst (Sl φ)))
        (λ { (m , ψ , (q , incl)) →
          let r  = keyʟ-shape ψ k' (fst ar) (fst a) (sym q ∙ sh)
              g  = get ψ (r .fst)
              a' = g .fst
              eψ = g .snd
              pay = cong fst (sym (payOp a'))
                  ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
          in subst (λ w → ⟨ w ∈ fst (Sl φ) ⟩)
               (sym (keyS≡ a' (fst ar) (fst a) (r .snd .fst) (sym pay)))
               (incl (fst (keyʟ a'))
                 (subst (λ w → ⟨ fst (keyʟ a') ∈ fst (Sl w) ⟩) (sym eψ)
                   (inA a' _ (Parts.self B keyʟ a')))) })
        (slot-inv B φ (fst c) c∈))

    binSucc : (k' : ℕ)
            → (op : ∀ {m} → Term S m → Formula S (suc m) → Formula S m)
            → (∀ {m} (ψ : Formula S m) → LCode.Match k' ψ
               → Σ[ t ∈ Term S m ] (Σ[ a' ∈ Formula S (suc m) ] (ψ ≡ op t a')))
            → (∀ {m} (t : Term S m) (a' : Formula S (suc m))
               → LCode.payOf (op t a') ≡ prʟ LCode.⌜ t ⌝ᵗ LCode.⌜ a' ⌝)
            → (∀ {m} (t : Term S m) (a' : Formula S (suc m)) (z : V ℓ)
               → ⟨ z ∈ fst (Sl a') ⟩ → ⟨ z ∈ fst (Sl (op t a')) ⟩)
            → ⟨ δ ⊨ binShapeAt Ci k' (succSndAt Ci) ⟩
    binSucc k' op get payOp inA = binSuccClosed-in Ci k' δ
      (λ c ar a b c∈ sh → PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ fst (Sl φ)))
        (λ { (m , ψ , (q , incl)) →
          let r  = keyʟ-shape ψ k' (fst ar) (pr (fst a) (fst b)) (sym q ∙ sh)
              g  = get ψ (r .fst)
              t  = g .fst
              a' = g .snd .fst
              eψ = g .snd .snd
              pay = sym (prʟ-fst LCode.⌜ t ⌝ᵗ LCode.⌜ a' ⌝)
                  ∙ cong fst (sym (payOp t a'))
                  ∙ cong (λ w → fst (LCode.payOf w)) (sym eψ) ∙ r .snd .snd
          in subst (λ w → ⟨ w ∈ fst (Sl φ) ⟩)
               (sym (keyS≡ a' (fst ar) (fst b) (r .snd .fst)
                 (sym (pr-inj pay .snd))))
               (incl (fst (keyʟ a'))
                 (subst (λ w → ⟨ fst (keyʟ a') ∈ fst (Sl w) ⟩) (sym eψ)
                   (inA t a' _ (Parts.self B keyʟ a')))) })
        (slot-inv B φ (fst c) c∈))

    exC : ⟨ δ ⊨ unShapeAt Ci 6 (oneSuccAt Ci) ⟩
    exC = unSucc 6 ∃̇_ (λ _ m → m) (λ _ → refl)
            (λ a' → Parts.only B keyʟ (∃̇ a') a')

    allC : ⟨ δ ⊨ unShapeAt Ci 7 (oneSuccAt Ci) ⟩
    allC = unSucc 7 ∀̇_ (λ _ m → m) (λ _ → refl)
             (λ a' → Parts.only B keyʟ (∀̇ a') a')

    allInC : ⟨ δ ⊨ binShapeAt Ci 8 (succSndAt Ci) ⟩
    allInC = binSucc 8 ∀̇∈ (λ _ m → m) (λ _ _ → refl)
               (λ t a' → Parts.only B keyʟ (∀̇∈ t a') a')

    exInC : ⟨ δ ⊨ binShapeAt Ci 9 (succSndAt Ci) ⟩
    exInC = binSucc 9 ∃̇∈ (λ _ m → m) (λ _ _ → refl)
              (λ t a' → Parts.only B keyʟ (∃̇∈ t a') a')

    slotClosed : ⟨ δ ⊨ closedAt Ci ⟩
    slotClosed = andC , (orC , (impC
               , (exC , (allC , (allInC , exInC)))))
```
