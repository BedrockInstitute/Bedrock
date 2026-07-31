# Operations preserve constructibility

<!--en-->
Fed constructible arguments, each Gödel operation returns a constructible set.
This chapter opens the account with the Boolean stock: intersection, union,
difference. The proof is the same move three times. Some stage contains both
arguments at once; the operation's connective, applied to two membership atoms,
defines the operation's value over that stage; and the definable-subset door
closes the value back into the class. The formulas on display are the route's
thesis in miniature: what the operation does to sets, its defining formula does
with one connective on two atoms, and nothing else.
<!--zh-->
喂给可构造的实参，每个 Gödel 运算返回可构造的集合。本章从布尔存货开账：交、并、差。证明是同一步棋走三遍。某个阶段同时装下两个实参；运算的联结词作用于两枚隶属原子，便在该阶段上定义出运算的取值；可定义子集之门再把取值收回类中。摆出来的公式是本路线论题的缩影：运算对集合做的事，其定义公式用一个联结词在两枚原子上做完，别无其他。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.InL {ℓ : Level} where

open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; _∨̇_; ¬̇_ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( isL; Lset; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( isL-directed; defSet→isL )
open import L.Godel.Operations {ℓ}
  using ( _∪_; ∪-left; ∪-right; ∪-out; _∩_; ∩-in; ∩-out; _∖_; ∖-in; ∖-out )

open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; _⊆_; extensionality )
```

<!--en-->
## One stage
<!--zh-->
## 单个阶段
<!--/-->

<!--en-->
Two constructible sets always sit in a common stage: `isL-directed`{.Agda}
hands over one stage containing both arguments. Everything below lives in the
module of one such stage. The shared plumbing is fixed once: each argument's
fiber index in the stage, the path reading the index back, and one membership
atom per argument, saying "variable zero lies in this argument". Every defining
formula below is a connective applied to these two atoms.
<!--zh-->
两个可构造集合总能同处一个阶段：`isL-directed`{.Agda} 交出一个同时装着两个实参的阶段。以下一切都住在这样一个阶段的模块里。公用件一次固定：每个实参在阶段中的纤维索引、把索引读回去的道路，以及每个实参一枚隶属原子，说「零号变元属于这个实参」。下面的每条定义公式都是一个联结词作用于这两枚原子。
<!--/-->

```agda
private
  module Stage (X Y σ : V ℓ) (X∈ : ⟨ X ∈ Lset σ ⟩) (Y∈ : ⟨ Y ∈ Lset σ ⟩) where
    module DefA = DefOf (Lset σ)

    Atrans = layer-trans (Lset-layer σ)

    mX = ∈-asFiber {a = X} {b = Lset σ} X∈ .fst
    qX : ⟪ Lset σ ⟫↪ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset σ} X∈ .snd

    mY = ∈-asFiber {a = Y} {b = Lset σ} Y∈ .fst
    qY : ⟪ Lset σ ⟫↪ mY ≡ Y
    qY = ∈-asFiber {a = Y} {b = Lset σ} Y∈ .snd

    atomX atomY : Formula ⟪ Lset σ ⟫ 1
    atomX = var zero ∈̇ con mX
    atomY = var zero ∈̇ con mY
```

<!--en-->
## Intersection
<!--zh-->
## 交
<!--/-->

<!--en-->
Intersection is conjunction. The satisfaction value of `∧̇`{.Agda} is a pair,
and the intersection's membership laws speak in the same pairs. Reading the
defined set into the intersection moves each half along the fiber paths;
reading a member of the intersection back finds its fiber through transitivity
of the stage, and satisfies each atom by the same two substitutions, reversed.
<!--zh-->
交就是合取。`∧̇`{.Agda} 的满足值是序对，而交的隶属定律说的正是同样的序对。把被定义集读进交，是沿纤维道路搬运两半；把交的成员读回来，是经阶段的传递性找到它的纤维，再用同样两次替换的反向让两枚原子得到满足。
<!--/-->

```agda
    capφ : Formula ⟪ Lset σ ⟫ 1
    capφ = atomX ∧̇ atomY

    cap≡ : DefA.defSet capφ ≡ X ∩ Y
    cap≡ = extensionality (DefA.defSet capφ) (X ∩ Y) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet capφ ⊆ (X ∩ Y) ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ (X ∩ Y)))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ (X ∩ Y) ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = X ∩ Y} .fst
              (mem m (subst ⟨_⟩ (DefA.defSet-mem capφ m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet capφ} .snd y∈ₛ)
        where
        mem : (m : ⟪ Lset σ ⟫) → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ capφ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ (X ∩ Y) ⟩
        mem m sat = ∩-in {X} {Y} {⟪ Lset σ ⟫↪ m}
          (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) qX (sat .fst))
          (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) qY (sat .snd))
      sub₂ : ⟨ (X ∩ Y) ⊆ DefA.defSet capφ ⟩
      sub₂ y y∈ₛ = mem (∩-out {X} {Y} {y} (∈∈ₛ {a = y} {b = X ∩ Y} .snd y∈ₛ))
        where
        mem : ⟨ y ∈ X ⟩ × ⟨ y ∈ Y ⟩ → ⟨ y ∈ₛ DefA.defSet capφ ⟩
        mem (hX , hY) =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet capφ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet capφ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem capφ m')) sat))
          where
          y∈A : ⟨ y ∈ Lset σ ⟩
          y∈A = Atrans {x = X} {y = y} hX X∈
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ capφ ⟩
          sat = subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX) hX
              , subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qY) hY
```

<!--en-->
## Union
<!--zh-->
## 并
<!--/-->

<!--en-->
Union is disjunction. The value of `∨̇`{.Agda} is a truncated sum, the union's
membership law answers in the same sum, and the two cases never meet: each
branch reaches the stage through its own argument and satisfies its own atom.
<!--zh-->
并就是析取。`∨̇`{.Agda} 的取值是截断的和，并的隶属定律以同一个和作答，而两个情形从不相遇：每个分支经自己的实参进入阶段、满足自己的原子。
<!--/-->

```agda
    cupφ : Formula ⟪ Lset σ ⟫ 1
    cupφ = atomX ∨̇ atomY

    cup≡ : DefA.defSet cupφ ≡ X ∪ Y
    cup≡ = extensionality (DefA.defSet cupφ) (X ∪ Y) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet cupφ ⊆ (X ∪ Y) ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ (X ∪ Y)))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ (X ∪ Y) ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = X ∪ Y} .fst
              (mem m (subst ⟨_⟩ (DefA.defSet-mem cupφ m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet cupφ} .snd y∈ₛ)
        where
        mem : (m : ⟪ Lset σ ⟫) → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ cupφ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ (X ∪ Y) ⟩
        mem m = PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ (X ∪ Y)))
          λ { (inl hX) → ∪-left  {X} {Y} {⟪ Lset σ ⟫↪ m}
                (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) qX hX)
            ; (inr hY) → ∪-right {X} {Y} {⟪ Lset σ ⟫↪ m}
                (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) qY hY) }
      sub₂ : ⟨ (X ∪ Y) ⊆ DefA.defSet cupφ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet cupφ)) mem
        (∪-out {X} {Y} {y} (∈∈ₛ {a = y} {b = X ∪ Y} .snd y∈ₛ))
        where
        mem : ⟨ y ∈ X ⟩ ⊎ ⟨ y ∈ Y ⟩ → ⟨ y ∈ₛ DefA.defSet cupφ ⟩
        mem c =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet cupφ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet cupφ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem cupφ m')) sat))
          where
          y∈A : ⟨ y ∈ Lset σ ⟩
          y∈A = Sum.rec (λ hX → Atrans {x = X} {y = y} hX X∈)
                        (λ hY → Atrans {x = Y} {y = y} hY Y∈) c
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ cupφ ⟩
          sat = ∣ Sum.map (subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX))
                          (subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qY)) c ∣₁
```

<!--en-->
## Difference
<!--zh-->
## 差
<!--/-->

<!--en-->
Difference is conjunction with a negated atom. The value of a negation is a
function into the empty type, which is exactly the shape the difference's
membership laws emit and consume, so the two directions are again two
substitutions and their reverses.
<!--zh-->
差就是带一枚被否定原子的合取。否定的取值是打到空类型的函数，恰是差的隶属定律所给出与消费的形状，于是两个方向又是两次替换与其反向。
<!--/-->

```agda
    diffφ : Formula ⟪ Lset σ ⟫ 1
    diffφ = atomX ∧̇ (¬̇ atomY)

    diff≡ : DefA.defSet diffφ ≡ X ∖ Y
    diff≡ = extensionality (DefA.defSet diffφ) (X ∖ Y) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet diffφ ⊆ (X ∖ Y) ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ (X ∖ Y)))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ (X ∖ Y) ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = X ∖ Y} .fst
              (mem m (subst ⟨_⟩ (DefA.defSet-mem diffφ m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet diffφ} .snd y∈ₛ)
        where
        mem : (m : ⟪ Lset σ ⟫) → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ diffφ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ (X ∖ Y) ⟩
        mem m sat = ∖-in {X} {Y} {⟪ Lset σ ⟫↪ m}
          (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) qX (sat .fst))
          (λ hY → sat .snd (subst (λ w → ⟨ ⟪ Lset σ ⟫↪ m ∈ w ⟩) (sym qY) hY))
      sub₂ : ⟨ (X ∖ Y) ⊆ DefA.defSet diffφ ⟩
      sub₂ y y∈ₛ = mem (∖-out {X} {Y} {y} (∈∈ₛ {a = y} {b = X ∖ Y} .snd y∈ₛ))
        where
        mem : ⟨ y ∈ X ⟩ × (⟨ y ∈ Y ⟩ → Empty.⊥) → ⟨ y ∈ₛ DefA.defSet diffφ ⟩
        mem (hX , nY) =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet diffφ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet diffφ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem diffφ m')) sat))
          where
          y∈A : ⟨ y ∈ Lset σ ⟩
          y∈A = Atrans {x = X} {y = y} hX X∈
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ diffφ ⟩
          sat = subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX) hX
              , (λ hY → nY (subst2 (λ u w → ⟨ u ∈ w ⟩) q' qY hY))
```

<!--en-->
## Back into the class
<!--zh-->
## 收回类中
<!--/-->

<!--en-->
Each public lemma now reads the same: split the shared-stage witness, hand the
formula and its extensional identification to `defSet→isL`{.Agda}, and the
operation's value is constructible.
<!--zh-->
每条公开引理现在读起来一个样：拆开公共阶段的见证，把公式连同其外延等同交给 `defSet→isL`{.Agda}，运算的取值便可构造。
<!--/-->

```agda
capL : {X Y : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Y ⟩ → ⟨ isL (X ∩ Y) ⟩
capL {X} {Y} lX lY = PT.rec (snd (isL (X ∩ Y)))
  (λ { (σ , (oσ , (X∈ , Y∈))) →
    defSet→isL σ oσ (X ∩ Y) ∣ Stage.capφ X Y σ X∈ Y∈ , Stage.cap≡ X Y σ X∈ Y∈ ∣₁ })
  (isL-directed X Y lX lY)

cupL : {X Y : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Y ⟩ → ⟨ isL (X ∪ Y) ⟩
cupL {X} {Y} lX lY = PT.rec (snd (isL (X ∪ Y)))
  (λ { (σ , (oσ , (X∈ , Y∈))) →
    defSet→isL σ oσ (X ∪ Y) ∣ Stage.cupφ X Y σ X∈ Y∈ , Stage.cup≡ X Y σ X∈ Y∈ ∣₁ })
  (isL-directed X Y lX lY)

diffL : {X Y : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Y ⟩ → ⟨ isL (X ∖ Y) ⟩
diffL {X} {Y} lX lY = PT.rec (snd (isL (X ∖ Y)))
  (λ { (σ , (oσ , (X∈ , Y∈))) →
    defSet→isL σ oσ (X ∖ Y) ∣ Stage.diffφ X Y σ X∈ Y∈ , Stage.diff≡ X Y σ X∈ Y∈ ∣₁ })
  (isL-directed X Y lX lY)
```
