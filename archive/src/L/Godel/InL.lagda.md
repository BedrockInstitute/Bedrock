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
open import Base.Truth

module L.Godel.InL {ℓ : Level} where

open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono
        ; Lset-in; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord; boundingOrd )
open import L.Axioms.Basic {ℓ} using ( isL-directed; defSet→isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Base {ℓ}
  using ( prAt-adequate; ∈pair-introL; ∈pair-introR; ∈pair-elim )
open import L.Coding.Environment {ℓ} using ( sucAt-adequate )
open import L.Coding.InL {ℓ} using ( sglL )
open import L.Godel.Operations {ℓ}
  using ( _∪_; ∪-left; ∪-right; ∪-out; _∩_; ∩-in; ∩-out; _∖_; ∖-in; ∖-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; values; values-in; values-wit
        ; singleton-self; singleton-in; singleton-out
        ; tailGraph; tailGraph-in; tailGraph-out
        ; shiftDown; shiftDown-in; shiftDown-out
        ; extendGraph; extendGraph-zero; extendGraph-suc; extendGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out )
open import L.Godel.Tuples {ℓ} using ( allTuples; allTuples-zero; allTuples-suc )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK
        ; ⟦_⟧ᴷ )

open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.FinData using ( toℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
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
## A family, one stage
<!--zh-->
## 一族集合，一个阶段
<!--/-->

<!--en-->
The selections carry parameters, so their chapters need more than two sets in
one stage. The two-set argument iterates: the empty stage handles the empty
family, and one bounding ordinal joins the head's stage to the tail's.
<!--zh-->
选择带参数，故其章节需要两个以上的集合共处一个阶段。两集合的论证迭代即可：空阶段处理空族，一个上界序数把头的阶段与尾的阶段并起来。
<!--/-->

```agda
stageFam : (k : ℕ) (h : Fin k → V ℓ) → ((i : Fin k) → ⟨ isL (h i) ⟩)
         → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × ((i : Fin k) → ⟨ h i ∈ Lset σ ⟩)) ∥₁
stageFam zero h hL = ∣ ∅ , ∅-ord , (λ ()) ∣₁
stageFam (suc k) h hL = PT.rec2 PT.squash₁ join
  (hL zero) (stageFam k (λ i → h (suc i)) (λ i → hL (suc i)))
  where
  join : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ h zero ∈ Lset α ⟩)
       → Σ[ τ ∈ V ℓ ] (IsOrd τ × ((i : Fin k) → ⟨ h (suc i) ∈ Lset τ ⟩))
       → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × ((i : Fin (suc k)) → ⟨ h i ∈ Lset σ ⟩)) ∥₁
  join (α , oα , h0∈) (τ , oτ , rest∈) = ∣ σ' , oσ' , total ∣₁
    where
    f : Lift {ℓ-zero} {ℓ} Bool → V ℓ
    f (lift true)  = α
    f (lift false) = τ
    hf : (b : Lift {ℓ-zero} {ℓ} Bool) → IsOrd (f b)
    hf (lift true)  = oα
    hf (lift false) = oτ
    bnd = boundingOrd (Lift {ℓ-zero} {ℓ} Bool) f hf
    σ' = bnd .fst
    oσ' = bnd .snd .fst
    total : (i : Fin (suc k)) → ⟨ h i ∈ Lset σ' ⟩
    total zero    = Lset-mono (bnd .snd .snd (lift true)) h0∈
    total (suc i) = Lset-mono (bnd .snd .snd (lift false)) (rest∈ i)
```

<!--en-->
## The pair formula, carried over
<!--zh-->
## 对公式，搬运过来
<!--/-->

<!--en-->
The graph-reading operations speak about Kuratowski pairs, so their defining
formulas must too. The coding part of the book already wrote the pair reader
once, constant-free, together with its adequacy at the outer satisfaction; the
only mismatch is the constant domain, fixed there and free here. So the reader
is restated verbatim with the domain a parameter, and adequacy is not restated
at all: a constant-free formula is fixed by every relabelling, so once the
membership question has been carried to the outer world (`abs-defSet`{.Agda}
and one relabelling), the original adequacy lemma applies unchanged. A few
fixed variable indices are named once; de Bruijn arithmetic stays in one place.
<!--zh-->
读图的运算谈论 Kuratowski 对，故其定义公式也必须谈论。本书编码部分已把对读式写过一次，无常量，并配了外层满足处的充分性；唯一的错位在常量域，彼处固定而此处自由。于是把读式一字不差地重述一遍，让域成为参数；而充分性完全不必重述：无常量公式被每次重标固定，故一旦隶属问题被搬到外层世界 (`abs-defSet`{.Agda} 加一次重标)，原来的充分性引理原样适用。几个固定的变元序号一次命名，de Bruijn 算术只住在一处。
<!--/-->

```agda
private
  sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
  sglAt′ k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

  pairAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  pairAt′ k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
              ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

  prAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  prAt′ q u v = (∃̇∈ (var q) (sglAt′ zero (suc u)))
             ∧̇ ((∃̇∈ (var q) (pairAt′ zero (suc u) (suc v)))
             ∧̇ (∀̇∈ (var q) (sglAt′ zero (suc u) ∨̇ pairAt′ zero (suc u) (suc v))))

  Δ₀-sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (k i : Fin n)
            → Δ₀ (sglAt′ {K = K} k i)
  Δ₀-sglAt′ k i = δ-∧ δ-∈ (δ-∀∈ δ-≐)

  Δ₀-pairAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (k i j : Fin n)
             → Δ₀ (pairAt′ {K = K} k i j)
  Δ₀-pairAt′ k i j = δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∀∈ (δ-∨ δ-≐ δ-≐)))

  Δ₀-prAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (q u v : Fin n)
           → Δ₀ (prAt′ {K = K} q u v)
  Δ₀-prAt′ q u v = δ-∧ (δ-∃∈ (Δ₀-sglAt′ zero (suc u)))
    (δ-∧ (δ-∃∈ (Δ₀-pairAt′ zero (suc u) (suc v)))
         (δ-∀∈ (δ-∨ (Δ₀-sglAt′ zero (suc u)) (Δ₀-pairAt′ zero (suc u) (suc v)))))

  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc zero
  f2 : {n : ℕ} → Fin (suc (suc (suc n)))
  f2 = suc f1
  f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  f3 = suc f2
  f4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
  f4 = suc f3
  f5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
  f5 = suc f4
  f6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  f6 = suc f5
  f7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  f7 = suc f6
```

<!--en-->
## The selection by membership
<!--zh-->
## 以隶属作的选择
<!--/-->

<!--en-->
The first graph operation. A member of `selectMember X Ka Kb`{.Agda} is a
member of `X` recording, at some key from each key set, two values standing in
membership. The defining formula says it with eight bounded quantifiers: a key
from each key set, then each recorded pair reached through its member chain
inside the member itself, with the two waypoints of each chain bound where the
pair provides them. The two directions of the extensional identification read
the same chain: outward, the satisfaction is peeled truncation by truncation
and the pair reader's adequacy turns each pair clause into an equation the
membership law consumes; inward, the operation's witness reader supplies the
values, and the waypoints are the pair's own two members.
<!--zh-->
第一个图运算。`selectMember X Ka Kb`{.Agda} 的成员是 `X` 的这样一个成员：在各键集的某个键处，记录着两个成隶属关系的取值。定义公式用八个有界量词说出它：各键集取一个键，然后每个被记录的对经成员自身内部的成员链到达，链上两个中转站恰在对提供它们的地方约束。外延等同的两个方向读同一条链：向外，满足逐层剥开截断，对读式的充分性把每条对子句变成隶属定律要消费的等式；向内，运算的见证读式提供取值，中转站就是对自身的两个成员。
<!--/-->

```agda
private
  module SelMem (X Ka Kb σ : V ℓ)
    (X∈ : ⟨ X ∈ Lset σ ⟩) (Ka∈ : ⟨ Ka ∈ Lset σ ⟩) (Kb∈ : ⟨ Kb ∈ Lset σ ⟩) where

    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    module RefA = DefA.Refine Atrans

    mX = ∈-asFiber {a = X} {b = Lset σ} X∈ .fst
    qX : ⟪ Lset σ ⟫↪ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset σ} X∈ .snd
    mKa = ∈-asFiber {a = Ka} {b = Lset σ} Ka∈ .fst
    qKa : ⟪ Lset σ ⟫↪ mKa ≡ Ka
    qKa = ∈-asFiber {a = Ka} {b = Lset σ} Ka∈ .snd
    mKb = ∈-asFiber {a = Kb} {b = Lset σ} Kb∈ .fst
    qKb : ⟪ Lset σ ⟫↪ mKb ≡ Kb
    qKb = ∈-asFiber {a = Kb} {b = Lset σ} Kb∈ .snd

    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = (var zero ∈̇ con mX)
     ∧̇ (∃̇∈ (con mKa) (∃̇∈ (con mKb)
          (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var zero)
            (∃̇∈ (var f5) (∃̇∈ (var zero) (∃̇∈ (var zero)
              (prAt′ f5 f7 f3 ∧̇ (prAt′ f2 f6 zero ∧̇ (var f3 ∈̇ var zero)))))))))))

    dΦ : Δ₀ Φ
    dΦ = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
           (δ-∧ (Δ₀-prAt′ f5 f7 f3) (δ-∧ (Δ₀-prAt′ f2 f6 zero) δ-∈))))))))))

    chain : ∀ m → (⟪ Lset σ ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ dΦ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset σ ⟫↪ m ∷ []))

    defSet≡ : DefA.defSet Φ ≡ selectMember X Ka Kb
    defSet≡ = extensionality (DefA.defSet Φ) (selectMember X Ka Kb) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ selectMember X Ka Kb ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ selectMember X Ka Kb))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ selectMember X Ka Kb ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = selectMember X Ka Kb} .fst
              (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
        where
        fromSat : (m : ⟪ Lset σ ⟫)
                → ⟨ (⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
                → ⟨ ⟪ Lset σ ⟫↪ m ∈ selectMember X Ka Kb ⟩
        fromSat m (hXm , big) =
          PT.rec tgt (λ { (a , ha , w₁) →
          PT.rec tgt (λ { (b , hb , w₂) →
          PT.rec tgt (λ { (p , hp , w₃) →
          PT.rec tgt (λ { (d , hd , w₄) →
          PT.rec tgt (λ { (u , hu , w₅) →
          PT.rec tgt (λ { (p' , hp' , w₆) →
          PT.rec tgt (λ { (d' , hd' , w₇) →
          PT.rec tgt (λ { (v , hv , (sa , sb , huv)) →
            selectMember-in {X} {Ka} {Kb} {⟪ Lset σ ⟫↪ m} {a} {b} {u} {v}
              (subst (λ z → ⟨ ⟪ Lset σ ⟫↪ m ∈ z ⟩) qX hXm)
              (subst (λ z → ⟨ a ∈ z ⟩) qKa ha)
              (subst (λ z → ⟨ b ∈ z ⟩) qKb hb)
              (subst (λ z → ⟨ z ∈ ⟪ Lset σ ⟫↪ m ⟩)
                (subst ⟨_⟩ (prAt-adequate f5 f7 f3
                  (v ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset σ ⟫↪ m ∷ [])) sa)
                hp)
              (subst (λ z → ⟨ z ∈ ⟪ Lset σ ⟫↪ m ⟩)
                (subst ⟨_⟩ (prAt-adequate f2 f6 zero
                  (v ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset σ ⟫↪ m ∷ [])) sb)
                hp')
              huv })
            w₇ }) w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) big
          where
          tgt = snd (⟪ Lset σ ⟫↪ m ∈ selectMember X Ka Kb)
      sub₂ : ⟨ selectMember X Ka Kb ⊆ DefA.defSet Φ ⟩
      sub₂ y y∈ₛ = mem (∈∈ₛ {a = y} {b = selectMember X Ka Kb} .snd y∈ₛ)
        where
        mem : ⟨ y ∈ selectMember X Ka Kb ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
        mem hy = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
          (selectMember-wit {X} {Ka} {Kb} {y} hy)
          where
          y∈X : ⟨ y ∈ X ⟩
          y∈X = selectMember-sub {X} {Ka} {Kb} {y} hy
          y∈A : ⟨ y ∈ Lset σ ⟩
          y∈A = Atrans {x = X} {y = y} y∈X X∈
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
          build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                  ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                  × ⟨ pr a u ∈ y ⟩ × ⟨ pr b v ∈ y ⟩ × ⟨ u ∈ v ⟩ )
                → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          build (a , b , u , v , ha , hb , hau , hbv , huv) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
              (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            E : V ℓ
            E = ⟪ Lset σ ⟫↪ m'
            env : (V ℓ) ^ 9
            env = v ∷ ⁅ b , v ⁆ ∷ pr b v ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ E ∷ []
            sat : ⟨ (E ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
            sat = subst (λ z → ⟨ E ∈ z ⟩) (sym qX)
                    (subst (λ z → ⟨ z ∈ X ⟩) (sym q') y∈X)
                , ∣ a , subst (λ z → ⟨ a ∈ z ⟩) (sym qKa) ha
                , ∣ b , subst (λ z → ⟨ b ∈ z ⟩) (sym qKb) hb
                , ∣ pr a u , subst (λ z → ⟨ pr a u ∈ z ⟩) (sym q') hau
                , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
                , ∣ u , ∈pair-introR refl
                , ∣ pr b v , subst (λ z → ⟨ pr b v ∈ z ⟩) (sym q') hbv
                , ∣ ⁅ b , v ⁆ , ∈pair-introR refl
                , ∣ v , ∈pair-introR refl
                , ( subst ⟨_⟩ (sym (prAt-adequate f5 f7 f3 env)) refl
                  , subst ⟨_⟩ (sym (prAt-adequate f2 f6 zero env)) refl
                  , huv )
                ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
```

<!--en-->
## The selection by equality
<!--zh-->
## 以相等作的选择
<!--/-->

<!--en-->
The second selection differs by one recorded value instead of two: both keys
record the same `u`, which is equality said without the equality sign. The
formula drops one pair chain, since `u` is already bound when the second pair
is reached, and everything else is the previous section verbatim.
<!--zh-->
第二个选择的差别在于记录一个而非两个取值：两个键记录同一个 `u`，这是不写等号说出的相等。公式少掉一条对链，因为到达第二个对时 `u` 已被约束，其余与上一节逐字相同。
<!--/-->

```agda
private
  module SelEq (X Ka Kb σ : V ℓ)
    (X∈ : ⟨ X ∈ Lset σ ⟩) (Ka∈ : ⟨ Ka ∈ Lset σ ⟩) (Kb∈ : ⟨ Kb ∈ Lset σ ⟩) where

    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    module RefA = DefA.Refine Atrans

    mX = ∈-asFiber {a = X} {b = Lset σ} X∈ .fst
    qX : ⟪ Lset σ ⟫↪ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset σ} X∈ .snd
    mKa = ∈-asFiber {a = Ka} {b = Lset σ} Ka∈ .fst
    qKa : ⟪ Lset σ ⟫↪ mKa ≡ Ka
    qKa = ∈-asFiber {a = Ka} {b = Lset σ} Ka∈ .snd
    mKb = ∈-asFiber {a = Kb} {b = Lset σ} Kb∈ .fst
    qKb : ⟪ Lset σ ⟫↪ mKb ≡ Kb
    qKb = ∈-asFiber {a = Kb} {b = Lset σ} Kb∈ .snd

    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = (var zero ∈̇ con mX)
     ∧̇ (∃̇∈ (con mKa) (∃̇∈ (con mKb)
          (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var zero)
            (∃̇∈ (var f5) (prAt′ f3 f5 f1 ∧̇ prAt′ zero f4 f1)))))))

    dΦ : Δ₀ Φ
    dΦ = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
           (δ-∧ (Δ₀-prAt′ f3 f5 f1) (Δ₀-prAt′ zero f4 f1))))))))

    chain : ∀ m → (⟪ Lset σ ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ dΦ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset σ ⟫↪ m ∷ []))

    defSet≡ : DefA.defSet Φ ≡ selectEqual X Ka Kb
    defSet≡ = extensionality (DefA.defSet Φ) (selectEqual X Ka Kb) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ selectEqual X Ka Kb ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ selectEqual X Ka Kb))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ selectEqual X Ka Kb ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = selectEqual X Ka Kb} .fst
              (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
        where
        fromSat : (m : ⟪ Lset σ ⟫)
                → ⟨ (⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
                → ⟨ ⟪ Lset σ ⟫↪ m ∈ selectEqual X Ka Kb ⟩
        fromSat m (hXm , big) =
          PT.rec tgt (λ { (a , ha , w₁) →
          PT.rec tgt (λ { (b , hb , w₂) →
          PT.rec tgt (λ { (p , hp , w₃) →
          PT.rec tgt (λ { (d , hd , w₄) →
          PT.rec tgt (λ { (u , hu , w₅) →
          PT.rec tgt (λ { (p' , hp' , (sa , sb)) →
            selectEqual-in {X} {Ka} {Kb} {⟪ Lset σ ⟫↪ m} {a} {b} {u}
              (subst (λ z → ⟨ ⟪ Lset σ ⟫↪ m ∈ z ⟩) qX hXm)
              (subst (λ z → ⟨ a ∈ z ⟩) qKa ha)
              (subst (λ z → ⟨ b ∈ z ⟩) qKb hb)
              (subst (λ z → ⟨ z ∈ ⟪ Lset σ ⟫↪ m ⟩)
                (subst ⟨_⟩ (prAt-adequate f3 f5 f1
                  (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset σ ⟫↪ m ∷ [])) sa)
                hp)
              (subst (λ z → ⟨ z ∈ ⟪ Lset σ ⟫↪ m ⟩)
                (subst ⟨_⟩ (prAt-adequate zero f4 f1
                  (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset σ ⟫↪ m ∷ [])) sb)
                hp') })
            w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) big
          where
          tgt = snd (⟪ Lset σ ⟫↪ m ∈ selectEqual X Ka Kb)
      sub₂ : ⟨ selectEqual X Ka Kb ⊆ DefA.defSet Φ ⟩
      sub₂ y y∈ₛ = mem (∈∈ₛ {a = y} {b = selectEqual X Ka Kb} .snd y∈ₛ)
        where
        mem : ⟨ y ∈ selectEqual X Ka Kb ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
        mem hy = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
          (selectEqual-wit {X} {Ka} {Kb} {y} hy)
          where
          y∈X : ⟨ y ∈ X ⟩
          y∈X = selectEqual-sub {X} {Ka} {Kb} {y} hy
          y∈A : ⟨ y ∈ Lset σ ⟩
          y∈A = Atrans {x = X} {y = y} y∈X X∈
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
          build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ]
                  ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                  × ⟨ pr a u ∈ y ⟩ × ⟨ pr b u ∈ y ⟩ )
                → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          build (a , b , u , ha , hb , hau , hbu) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
              (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            E : V ℓ
            E = ⟪ Lset σ ⟫↪ m'
            env : (V ℓ) ^ 7
            env = pr b u ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ E ∷ []
            sat : ⟨ (E ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
            sat = subst (λ z → ⟨ E ∈ z ⟩) (sym qX)
                    (subst (λ z → ⟨ z ∈ X ⟩) (sym q') y∈X)
                , ∣ a , subst (λ z → ⟨ a ∈ z ⟩) (sym qKa) ha
                , ∣ b , subst (λ z → ⟨ b ∈ z ⟩) (sym qKb) hb
                , ∣ pr a u , subst (λ z → ⟨ pr a u ∈ z ⟩) (sym q') hau
                , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
                , ∣ u , ∈pair-introR refl
                , ∣ pr b u , subst (λ z → ⟨ pr b u ∈ z ⟩) (sym q') hbu
                , ( subst ⟨_⟩ (sym (prAt-adequate f3 f5 f1 env)) refl
                  , subst ⟨_⟩ (sym (prAt-adequate zero f4 f1 env)) refl )
                ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
```

<!--en-->
## The values
<!--zh-->
## 取值集
<!--/-->

<!--en-->
The last operation of this batch reads the first key's recorded values off a
family: a member of `values X`{.Agda} is anything some member of `X` records at
the numeral key zero. The defined variable is the value itself, so the formula
needs no waypoints at all: a key pinned by the singleton parameter, a family
member, a recorded pair, and one pair clause. The member-side stage argument is
the one place this batch climbs a member chain: the value sits two pairs deep
inside a family member, and transitivity walks all four steps down.
<!--zh-->
本批最后一个运算从族上读出首键的被记录取值：`values X`{.Agda} 的成员就是 `X` 的某个成员在零号数码键处记录的东西。被定义的变元就是取值本身，故公式完全不需要中转站：一个被单点集参数钉住的键、一个族成员、一个被记录的对，加一条对子句。成员侧的阶段论证是本批唯一爬成员链的地方：取值住在族成员内两层对深处，传递性把四步全走下来。
<!--/-->

```agda
private
  module Vals (X σ : V ℓ)
    (X∈ : ⟨ X ∈ Lset σ ⟩) (K0∈ : ⟨ ⁅ # 0 ⁆s ∈ Lset σ ⟩) where

    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    module RefA = DefA.Refine Atrans

    mX = ∈-asFiber {a = X} {b = Lset σ} X∈ .fst
    qX : ⟪ Lset σ ⟫↪ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset σ} X∈ .snd
    mK0 = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset σ} K0∈ .fst
    qK0 : ⟪ Lset σ ⟫↪ mK0 ≡ ⁅ # 0 ⁆s
    qK0 = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset σ} K0∈ .snd

    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = ∃̇∈ (con mK0) (∃̇∈ (con mX) (∃̇∈ (var zero) (prAt′ zero f2 f3)))

    dΦ : Δ₀ Φ
    dΦ = δ-∃∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAt′ zero f2 f3)))

    chain : ∀ m → (⟪ Lset σ ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ dΦ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset σ ⟫↪ m ∷ []))

    defSet≡ : DefA.defSet Φ ≡ values X
    defSet≡ = extensionality (DefA.defSet Φ) (values X) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ values X ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ values X))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ values X ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = values X} .fst
              (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
        where
        fromSat : (m : ⟪ Lset σ ⟫)
                → ⟨ (⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
                → ⟨ ⟪ Lset σ ⟫↪ m ∈ values X ⟩
        fromSat m big =
          PT.rec tgt (λ { (k , hk , w₁) →
          PT.rec tgt (λ { (γ , hγ , w₂) →
          PT.rec tgt (λ { (p , hp , s) →
            values-in {X} {γ} {⟪ Lset σ ⟫↪ m}
              (subst (λ z → ⟨ γ ∈ z ⟩) qX hγ)
              (subst (λ z → ⟨ pr z (⟪ Lset σ ⟫↪ m) ∈ γ ⟩)
                (singleton-out (subst (λ z → ⟨ k ∈ z ⟩) qK0 hk))
                (subst (λ z → ⟨ z ∈ γ ⟩)
                  (subst ⟨_⟩ (prAt-adequate zero f2 f3
                    (p ∷ γ ∷ k ∷ ⟪ Lset σ ⟫↪ m ∷ [])) s)
                  hp)) })
            w₂ }) w₁ }) big
          where
          tgt = snd (⟪ Lset σ ⟫↪ m ∈ values X)
      sub₂ : ⟨ values X ⊆ DefA.defSet Φ ⟩
      sub₂ y y∈ₛ = mem (∈∈ₛ {a = y} {b = values X} .snd y∈ₛ)
        where
        mem : ⟨ y ∈ values X ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
        mem hy = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build (values-wit {X} {y} hy)
          where
          build : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ X ⟩ × ⟨ pr (# 0) y ∈ γ ⟩)
                → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          build (γ , hγ , hv) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
              (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            y∈A : ⟨ y ∈ Lset σ ⟩
            y∈A = Atrans {x = ⁅ # 0 , y ⁆} {y = y} (∈pair-introR refl)
                    (Atrans {x = pr (# 0) y} {y = ⁅ # 0 , y ⁆} (∈pair-introR refl)
                      (Atrans {x = γ} {y = pr (# 0) y} hv
                        (Atrans {x = X} {y = γ} hγ X∈)))
            m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
            q' : ⟪ Lset σ ⟫↪ m' ≡ y
            q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
            E : V ℓ
            E = ⟪ Lset σ ⟫↪ m'
            sat : ⟨ (E ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
            sat = ∣ # 0 , subst (λ z → ⟨ # 0 ∈ z ⟩) (sym qK0) (singleton-self (# 0))
                , ∣ γ , subst (λ z → ⟨ γ ∈ z ⟩) (sym qX) hγ
                , ∣ pr (# 0) E , subst (λ z → ⟨ pr (# 0) z ∈ γ ⟩) (sym q') hv
                , subst ⟨_⟩ (sym (prAt-adequate zero f2 f3
                    (pr (# 0) E ∷ γ ∷ # 0 ∷ E ∷ []))) refl
                ∣₁ ∣₁ ∣₁
```

<!--en-->
## The climbs
<!--zh-->
## 爬升
<!--/-->

<!--en-->
The two movers build new pairs instead of selecting old members, so their
values leave the stage that held the arguments. They do not leave by far: each
constructor climbs a fixed, argument-independent number of stages, because a
set whose members sit in a stage and whose description is one formula over
that stage is a member of the next one. That closing move is `mkUp`{.Agda},
needing no ordinal witness at all, and the singleton, the unordered pair, the
Kuratowski pair and the von Neumann successor each climb by it in one or two
steps.
<!--zh-->
两个移位运算制造新的对而非挑选旧的成员，故其取值会离开装着实参的阶段。离开得并不远：每个构造子爬固定的、与实参无关的级数，因为成员落在某阶段中、且有一条该阶段上公式作描述的集合，是下一个阶段的成员。这记收尾就是 `mkUp`{.Agda}，完全不需要序数见证；单点集、无序对、Kuratowski 对与冯·诺伊曼后继各经它爬一到两步。
<!--/-->

```agda
private
  up : {σ x : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ x ∈ Lset (sucV σ) ⟩
  up {σ} = Lset-mono {sucV σ} {σ} (self∈sucV σ)

  mkUp : (σ x : V ℓ) (Φ : Formula ⟪ Lset σ ⟫ 1) → DefOf.defSet (Lset σ) Φ ≡ x
       → ⟨ x ∈ Lset (sucV σ) ⟩
  mkUp σ x Φ e = Lset-in (sucV σ) σ x (self∈sucV σ) (𝒟ₒ-intro (Lset σ) x ∣ Φ , e ∣₁)

  sglUp : (σ : V ℓ) {x : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ ⁅ x ⁆s ∈ Lset (sucV σ) ⟩
  sglUp σ {x} x∈ = mkUp σ ⁅ x ⁆s Φ defSet≡
    where
    module DefA = DefOf (Lset σ)
    module RefA = DefA.Refine (layer-trans (Lset-layer σ))
    mx = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
    qx : ⟪ Lset σ ⟫↪ mx ≡ x
    qx = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = var zero ≐ con mx
    chain : ∀ m → (⟪ Lset σ ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ δ-≐ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset σ ⟫↪ m ∷ []))
    defSet≡ : DefA.defSet Φ ≡ ⁅ x ⁆s
    defSet≡ = extensionality (DefA.defSet Φ) ⁅ x ⁆s (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ ⁅ x ⁆s ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⁅ x ⁆s))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⁅ x ⁆s ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = ⁅ x ⁆s} .fst
              (singleton-in
                (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁ ∙ qx))) })
        (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
      sub₂ : ⟨ ⁅ x ⁆s ⊆ DefA.defSet Φ ⟩
      sub₂ y y∈ₛ =
        subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qx ∙ sym ex)
          (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mx} {b = DefA.defSet Φ} .fst
            (subst ⟨_⟩ (sym (chain mx)) refl))
        where
        ex : y ≡ x
        ex = singleton-out (∈∈ₛ {a = y} {b = ⁅ x ⁆s} .snd y∈ₛ)

  pairUp : (σ : V ℓ) {x y : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
         → ⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩
  pairUp σ {x} {y} x∈ y∈ = mkUp σ ⁅ x , y ⁆ Φ defSet≡
    where
    module DefA = DefOf (Lset σ)
    module RefA = DefA.Refine (layer-trans (Lset-layer σ))
    mx = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
    qx : ⟪ Lset σ ⟫↪ mx ≡ x
    qx = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
    my = ∈-asFiber {a = y} {b = Lset σ} y∈ .fst
    qy : ⟪ Lset σ ⟫↪ my ≡ y
    qy = ∈-asFiber {a = y} {b = Lset σ} y∈ .snd
    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = (var zero ≐ con mx) ∨̇ (var zero ≐ con my)
    chain : ∀ m → (⟪ Lset σ ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ (δ-∨ δ-≐ δ-≐) m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset σ ⟫↪ m ∷ []))
    defSet≡ : DefA.defSet Φ ≡ ⁅ x , y ⁆
    defSet≡ = extensionality (DefA.defSet Φ) ⁅ x , y ⁆ (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ ⁅ x , y ⁆ ⟩
      sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ x , y ⁆))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⁅ x , y ⁆ ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = ⁅ x , y ⁆} .fst
              (mem m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = z} {b = DefA.defSet Φ} .snd z∈ₛ)
        where
        mem : (m : ⟪ Lset σ ⟫) → ⟨ (⟪ Lset σ ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ ⁅ x , y ⁆ ⟩
        mem m = PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ ⁅ x , y ⁆))
          λ { (inl e) → ∈pair-introL (e ∙ qx)
            ; (inr e) → ∈pair-introR (e ∙ qy) }
      sub₂ : ⟨ ⁅ x , y ⁆ ⊆ DefA.defSet Φ ⟩
      sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet Φ))
        (λ { (inl e) →
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qx ∙ sym e)
                (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mx} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (chain mx)) ∣ inl refl ∣₁))
           ; (inr e) →
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qy ∙ sym e)
                (∈∈ₛ {a = ⟪ Lset σ ⟫↪ my} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (chain my)) ∣ inr refl ∣₁)) })
        (∈pair-elim (∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd z∈ₛ))

  prUp : (σ : V ℓ) {x y : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
       → ⟨ pr x y ∈ Lset (sucV (sucV σ)) ⟩
  prUp σ {x} {y} x∈ y∈ = pairUp (sucV σ) (sglUp σ x∈) (pairUp σ x∈ y∈)

  sucUp : (σ : V ℓ) {x : V ℓ} → ⟨ x ∈ Lset σ ⟩
        → ⟨ sucV x ∈ Lset (sucV (sucV σ)) ⟩
  sucUp σ {x} x∈ = mkUp (sucV σ) (sucV x) Φ defSet≡
    where
    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV σ))
    module RefA = DefA.Refine (layer-trans (Lset-layer (sucV σ)))
    x∈¹ : ⟨ x ∈ Lset (sucV σ) ⟩
    x∈¹ = up x∈
    mx = ∈-asFiber {a = x} {b = Lset (sucV σ)} x∈¹ .fst
    qx : ⟪ Lset (sucV σ) ⟫↪ mx ≡ x
    qx = ∈-asFiber {a = x} {b = Lset (sucV σ)} x∈¹ .snd
    Φ : Formula ⟪ Lset (sucV σ) ⟫ 1
    Φ = (var zero ∈̇ con mx) ∨̇ (var zero ≐ con mx)
    chain : ∀ m → (⟪ Lset (sucV σ) ⟫↪ m ∈ DefA.defSet Φ)
                ≡ ((⟪ Lset (sucV σ) ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ (δ-∨ δ-∈ δ-≐) m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (⟪ Lset (sucV σ) ⟫↪ m ∷ []))
    defSet≡ : DefA.defSet Φ ≡ sucV x
    defSet≡ = extensionality (DefA.defSet Φ) (sucV x) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ sucV x ⟩
      sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ sucV x))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ sucV x ⟩) q
            (∈∈ₛ {a = ⟪ Lset (sucV σ) ⟫↪ m} {b = sucV x} .fst
              (mem m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = z} {b = DefA.defSet Φ} .snd z∈ₛ)
        where
        mem : (m : ⟪ Lset (sucV σ) ⟫)
            → ⟨ (⟪ Lset (sucV σ) ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
            → ⟨ ⟪ Lset (sucV σ) ⟫↪ m ∈ sucV x ⟩
        mem m = PT.rec (snd (⟪ Lset (sucV σ) ⟫↪ m ∈ sucV x))
          λ { (inl h) → ∈sucV-inl {A = x}
                (subst (λ w → ⟨ ⟪ Lset (sucV σ) ⟫↪ m ∈ w ⟩) qx h)
            ; (inr e) → subst (λ w → ⟨ w ∈ sucV x ⟩) (sym (e ∙ qx))
                (self∈sucV x) }
      sub₂ : ⟨ sucV x ⊆ DefA.defSet Φ ⟩
      sub₂ z z∈ₛ = ∈∈ₛ {a = z} {b = DefA.defSet Φ} .fst
        (∈sucV-elim {A = x} {x = z} (snd (z ∈ DefA.defSet Φ))
          (∈∈ₛ {a = z} {b = sucV x} .snd z∈ₛ) kMem kEq)
        where
        kMem : ⟨ z ∈ x ⟩ → ⟨ z ∈ DefA.defSet Φ ⟩
        kMem h =
          subst (λ w → ⟨ w ∈ DefA.defSet Φ ⟩) q'
            (subst ⟨_⟩ (sym (chain m'))
              ∣ inl (subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qx) h) ∣₁)
          where
          z∈¹ : ⟨ z ∈ Lset (sucV σ) ⟩
          z∈¹ = up (Atr {x = x} {y = z} h x∈)
          m' = ∈-asFiber {a = z} {b = Lset (sucV σ)} z∈¹ .fst
          q' : ⟪ Lset (sucV σ) ⟫↪ m' ≡ z
          q' = ∈-asFiber {a = z} {b = Lset (sucV σ)} z∈¹ .snd
        kEq : z ≡ x → ⟨ z ∈ DefA.defSet Φ ⟩
        kEq e =
          subst (λ w → ⟨ w ∈ DefA.defSet Φ ⟩) (qx ∙ sym e)
            (subst ⟨_⟩ (sym (chain mx)) ∣ inr refl ∣₁)
```

<!--en-->
## The tail chain
<!--zh-->
## 尾链
<!--/-->

<!--en-->
Both directions of the shift say the same sentence: "the surveyed member is
`pr a v` for some pair `pr (suc a) v` recorded here". The sentence is written
once, generically: a body of three clauses (the recorded pair, the successor,
the surveyed pair) under six bounded quantifiers walking the recorded pair's
own members, with the bound of the walk a term parameter. The successor reader
joins the pair reader by the same carrying-over, and the two lemmas `seekOut`{.Agda}
and `seekIn`{.Agda} read and write the whole sentence at the outer world, each
used everywhere below.
<!--zh-->
移位的两个方向说同一句话：「被检视的成员是某个在此被记录的对 `pr (suc a) v` 的 `pr a v`」。这句话只写一次，并且泛型：三条子句的体 (被记录的对、后继、被检视的对) 置于六个有界量词之下，量词沿被记录的对自身的成员行走，行走的界是一个项参数。后继读式以同样的搬运与对读式会合，而 `seekOut`{.Agda} 与 `seekIn`{.Agda} 两条引理在外层世界读出与写入整句话，下文处处使用。
<!--/-->

```agda
private
  sucAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
  sucAt′ i j = (var i ∈̇ var j)
            ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
            ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

  Δ₀-sucAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (i j : Fin n)
            → Δ₀ (sucAt′ {K = K} i j)
  Δ₀-sucAt′ i j = δ-∧ δ-∈ (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ (δ-∨ δ-∈ δ-≐)))

  tailBody : {ℓ' : Level} {K : Type ℓ'} {m : ℕ}
           → Formula K (suc (suc (suc (suc (suc (suc (suc m)))))))
  tailBody = prAt′ f5 f3 f1 ∧̇ (sucAt′ zero f3 ∧̇ prAt′ f6 zero f1)

  tailSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} → Term K (suc m) → Formula K (suc m)
  tailSeek B = ∃̇∈ B (∃̇∈ (var zero) (∃̇∈ (var zero)
                 (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody)))))

  Δ₀-tailSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} (B : Term K (suc m))
              → Δ₀ (tailSeek B)
  Δ₀-tailSeek B = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
    (δ-∧ (Δ₀-prAt′ f5 f3 f1)
         (δ-∧ (Δ₀-sucAt′ zero f3) (Δ₀-prAt′ f6 zero f1))))))))

  seekOut : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) ^ (suc n))
          → ⟨ δ ⊨ tailSeek B ⟩
          → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
              ((⟦ var zero ⟧ δ ≡ pr a v) × ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩) ∥₁
  seekOut B δ =
    PT.rec PT.squash₁ (λ { (p , hp , w₁) →
    PT.rec PT.squash₁ (λ { (d₁ , hd₁ , w₂) →
    PT.rec PT.squash₁ (λ { (s , hs , w₃) →
    PT.rec PT.squash₁ (λ { (d₂ , hd₂ , w₄) →
    PT.rec PT.squash₁ (λ { (v , hv , w₅) →
    PT.rec PT.squash₁ (λ { (a , ha , (e₁ , e₂ , e₃)) →
      ∣ a , v
      , subst ⟨_⟩ (prAt-adequate f6 zero f1
          (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₃
      , subst (λ w → ⟨ w ∈ ⟦ B ⟧ δ ⟩)
          (subst ⟨_⟩ (prAt-adequate f5 f3 f1
            (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₁
           ∙ cong (λ w → pr w v)
               (subst ⟨_⟩ (sucAt-adequate zero f3
                 (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₂))
          hp ∣₁ })
    w₅ }) w₄ }) w₃ }) w₂ }) w₁ })

  seekIn : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) ^ (suc n)) (a v : V ℓ)
         → ⟦ var zero ⟧ δ ≡ pr a v → ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩
         → ⟨ δ ⊨ tailSeek B ⟩
  seekIn B δ a v e h =
    ∣ pr (sucV a) v , h
    , ∣ ⁅ sucV a ⁆s , ∈pair-introL refl
    , ∣ sucV a , singleton-self (sucV a)
    , ∣ ⁅ sucV a , v ⁆ , ∈pair-introR refl
    , ∣ v , ∈pair-introR refl
    , ∣ a , self∈sucV a
    , ( subst ⟨_⟩ (sym (prAt-adequate f5 f3 f1 env′)) refl
      , subst ⟨_⟩ (sym (sucAt-adequate zero f3 env′)) refl
      , subst ⟨_⟩ (sym (prAt-adequate f6 zero f1 env′)) e )
    ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    env′ : (V ℓ) ^ (suc (suc (suc (suc (suc (suc (suc _)))))))
    env′ = a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s ∷ pr (sucV a) v ∷ δ
```

<!--en-->
## The tail graph, staged
<!--zh-->
## 尾图，入阶段
<!--/-->

<!--en-->
Before the family, the single graph: the tail of a stage member climbs three
stages. Its members are pairs of things walked out of the argument by
transitivity, so they sit two climbs up, and the description over that stage
is precisely the seek sentence with the argument a constant.
<!--zh-->
族之前先看单个图：阶段成员的尾图爬三级。其成员是从实参沿传递性走出来的东西组成的对，故住在两次爬升之上，而那个阶段上的描述恰是「寻找句」以实参为常量的实例。
<!--/-->

```agda
private
  tailStage : (σ : V ℓ) {z : V ℓ} → ⟨ z ∈ Lset σ ⟩
            → ⟨ tailGraph z ∈ Lset (sucV (sucV (sucV σ))) ⟩
  tailStage σ {z} z∈ = mkUp (sucV (sucV σ)) (tailGraph z) Ψ defSet≡
    where
    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV (sucV σ)))
    module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV σ))))
    z∈² : ⟨ z ∈ Lset (sucV (sucV σ)) ⟩
    z∈² = up (up z∈)
    mz = ∈-asFiber {a = z} {b = Lset (sucV (sucV σ))} z∈² .fst
    qz : ⟪ Lset (sucV (sucV σ)) ⟫↪ mz ≡ z
    qz = ∈-asFiber {a = z} {b = Lset (sucV (sucV σ))} z∈² .snd

    Ψ : Formula ⟪ Lset (sucV (sucV σ)) ⟫ 1
    Ψ = tailSeek (con mz)

    chain : ∀ m → (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ DefA.defSet Ψ)
                ≡ ((⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ))
    chain m = RefA.abs-defSet Ψ (Δ₀-tailSeek (con mz)) m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Ψ) (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []))

    defSet≡ : DefA.defSet Ψ ≡ tailGraph z
    defSet≡ = extensionality (DefA.defSet Ψ) (tailGraph z) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Ψ ⊆ tailGraph z ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ tailGraph z))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ tailGraph z ⟩) q
            (mem m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet Ψ} .snd y∈ₛ)
        where
        mem : (m : ⟪ Lset (sucV (sucV σ)) ⟫)
            → ⟨ (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ) ⟩
            → ⟨ ⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ₛ tailGraph z ⟩
        mem m sat = PT.rec (snd (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ₛ tailGraph z))
          (λ { (a , v , e , h) →
            ∈∈ₛ {a = ⟪ Lset (sucV (sucV σ)) ⟫↪ m} {b = tailGraph z} .fst
              (subst (λ w → ⟨ w ∈ tailGraph z ⟩) (sym e)
                (tailGraph-in
                  (subst (λ w → ⟨ pr (sucV a) v ∈ w ⟩) qz h))) })
          (seekOut (con (⟪ Lset (sucV (sucV σ)) ⟫↪ mz))
            (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) sat)
      sub₂ : ⟨ tailGraph z ⊆ DefA.defSet Ψ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Ψ)) build
        (tailGraph-out {w = z} {z = y} (∈∈ₛ {a = y} {b = tailGraph z} .snd y∈ₛ))
        where
        build : Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr (sucV a) v ∈ z ⟩ × (y ≡ pr a v))
              → ⟨ y ∈ₛ DefA.defSet Ψ ⟩
        build (a , v , h , e) =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet Ψ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset (sucV (sucV σ)) ⟫↪ m'} {b = DefA.defSet Ψ} .fst
              (subst ⟨_⟩ (sym (chain m'))
                (seekIn (con (⟪ Lset (sucV (sucV σ)) ⟫↪ mz))
                  (⟪ Lset (sucV (sucV σ)) ⟫↪ m' ∷ []) a v (q' ∙ e)
                  (subst (λ w → ⟨ pr (sucV a) v ∈ w ⟩) (sym qz) h))))
          where
          prz∈ : ⟨ pr (sucV a) v ∈ Lset σ ⟩
          prz∈ = Atr {x = z} {y = pr (sucV a) v} h z∈
          a∈ : ⟨ a ∈ Lset σ ⟩
          a∈ = Atr {x = sucV a} {y = a} (self∈sucV a)
            (Atr {x = ⁅ sucV a ⁆s} {y = sucV a} (singleton-self (sucV a))
              (Atr {x = pr (sucV a) v} {y = ⁅ sucV a ⁆s} (∈pair-introL refl) prz∈))
          v∈ : ⟨ v ∈ Lset σ ⟩
          v∈ = Atr {x = ⁅ sucV a , v ⁆} {y = v} (∈pair-introR refl)
            (Atr {x = pr (sucV a) v} {y = ⁅ sucV a , v ⁆} (∈pair-introR refl) prz∈)
          y∈² : ⟨ y ∈ Lset (sucV (sucV σ)) ⟩
          y∈² = subst (λ w → ⟨ w ∈ Lset (sucV (sucV σ)) ⟩) (sym e)
            (prUp σ a∈ v∈)
          m' = ∈-asFiber {a = y} {b = Lset (sucV (sucV σ))} y∈² .fst
          q' : ⟪ Lset (sucV (sucV σ)) ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset (sucV (sucV σ))} y∈² .snd
```

<!--en-->
## The shift
<!--zh-->
## 移位
<!--/-->

<!--en-->
The family now. A member of the defined set is, by the formula, some `X`
member's tail: one clause says every member of the surveyed set satisfies the
seek sentence against that `X` member, the converse clause says every suitably
shaped recorded pair reaches the surveyed set, and together they pin the
surveyed set to the tail graph itself, by one extensionality inside the
reading. The member-side direction places the tail through the staging lemma
and writes both clauses back through `seekIn`{.Agda} and the pair reader.
<!--zh-->
现在是族。按公式，被定义集的成员是某个 `X` 成员的尾图：一条子句说被检视集合的每个成员对着那个 `X` 成员满足寻找句，逆向子句说每个形状合适的被记录对都到达被检视集合，二者合起来经读出内部的一次外延性把被检视集合钉在尾图自身上。成员侧方向经入阶段引理安置尾图，并经 `seekIn`{.Agda} 与对读式把两条子句写回。
<!--/-->

```agda
private
  module SftD (X σ : V ℓ) (X∈ : ⟨ X ∈ Lset σ ⟩) where

    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV (sucV (sucV σ))))
    module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV (sucV σ)))))

    E³ : ⟪ Lset (sucV (sucV (sucV σ))) ⟫ → V ℓ
    E³ m = ⟪ Lset (sucV (sucV (sucV σ))) ⟫↪ m

    X∈³ : ⟨ X ∈ Lset (sucV (sucV (sucV σ))) ⟩
    X∈³ = up (up (up X∈))
    mX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV σ)))} X∈³ .fst
    qX : E³ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV σ)))} X∈³ .snd

    Φ : Formula ⟪ Lset (sucV (sucV (sucV σ))) ⟫ 1
    Φ = ∃̇∈ (con mX)
          ( (∀̇∈ (var f1) (tailSeek (var f1)))
          ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero)
               (∀̇∈ (var f2) (∀̇∈ (var zero) (∀̇∈ (var f2)
                 ((prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3)
                   ⇒̇ ∃̇∈ (var f7) (prAt′ zero f1 f2)))))))) )

    dΦ : Δ₀ Φ
    dΦ = δ-∃∈ (δ-∧ (δ-∀∈ (Δ₀-tailSeek (var f1)))
           (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈
             (δ-⇒ (δ-∧ (Δ₀-prAt′ f5 f3 f1) (Δ₀-sucAt′ zero f3))
                  (δ-∃∈ (Δ₀-prAt′ zero f1 f2))))))))))

    chain : ∀ m → (E³ m ∈ DefA.defSet Φ)
                ≡ ((E³ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ dΦ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (E³ m ∷ []))

    defSet≡ : DefA.defSet Φ ≡ shiftDown X
    defSet≡ = extensionality (DefA.defSet Φ) (shiftDown X) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ shiftDown X ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ shiftDown X))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ shiftDown X ⟩) q
            (∈∈ₛ {a = E³ m} {b = shiftDown X} .fst
              (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
        where
        fromSat : (m : ⟪ Lset (sucV (sucV (sucV σ))) ⟫)
                → ⟨ (E³ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
                → ⟨ E³ m ∈ shiftDown X ⟩
        fromSat m = PT.rec (snd (E³ m ∈ shiftDown X))
          (λ { (γ , hγ , membV , imgV) →
            subst (λ w → ⟨ w ∈ shiftDown X ⟩) (sym (T≡ γ membV imgV))
              (shiftDown-in {X = X} {z = γ}
                (subst (λ w → ⟨ γ ∈ w ⟩) qX hγ)) })
          where
          T = E³ m
          T≡ : (γ : V ℓ)
             → ((z : V ℓ) → ⟨ z ∈ T ⟩ → ⟨ (z ∷ γ ∷ T ∷ []) ⊨ tailSeek (var f1) ⟩)
             → ((p : V ℓ) → ⟨ p ∈ γ ⟩ → (d₁ : V ℓ) → ⟨ d₁ ∈ p ⟩
                → (s : V ℓ) → ⟨ s ∈ d₁ ⟩ → (d₂ : V ℓ) → ⟨ d₂ ∈ p ⟩
                → (v : V ℓ) → ⟨ v ∈ d₂ ⟩ → (a : V ℓ) → ⟨ a ∈ s ⟩
                → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ γ ∷ T ∷ [])
                      ⊨ (prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3) ⟩
                → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ γ ∷ T ∷ [])
                      ⊨ ∃̇∈ (var f7) (prAt′ zero f1 f2) ⟩)
             → T ≡ tailGraph γ
          T≡ γ membV imgV = extensionality T (tailGraph γ) (t₁ , t₂)
            where
            t₁ : ⟨ T ⊆ tailGraph γ ⟩
            t₁ z z∈ₛ = PT.rec (snd (z ∈ₛ tailGraph γ))
              (λ { (a , v , e , h) →
                ∈∈ₛ {a = z} {b = tailGraph γ} .fst
                  (subst (λ w → ⟨ w ∈ tailGraph γ ⟩) (sym e)
                    (tailGraph-in h)) })
              (seekOut (var f1) (z ∷ γ ∷ T ∷ [])
                (membV z (∈∈ₛ {a = z} {b = T} .snd z∈ₛ)))
            t₂ : ⟨ tailGraph γ ⊆ T ⟩
            t₂ z z∈ₛ = PT.rec (snd (z ∈ₛ T))
              (λ { (a , v , h , e) → reach a v h e })
              (tailGraph-out {w = γ} {z = z}
                (∈∈ₛ {a = z} {b = tailGraph γ} .snd z∈ₛ))
              where
              reach : (a v : V ℓ) → ⟨ pr (sucV a) v ∈ γ ⟩ → z ≡ pr a v
                    → ⟨ z ∈ₛ T ⟩
              reach a v h e = PT.rec (snd (z ∈ₛ T))
                (λ { (z' , hz' , s') →
                  ∈∈ₛ {a = z} {b = T} .fst
                    (subst (λ w → ⟨ w ∈ T ⟩)
                      (subst ⟨_⟩ (prAt-adequate zero f1 f2
                        (z' ∷ a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                          ∷ pr (sucV a) v ∷ γ ∷ T ∷ [])) s'
                       ∙ sym e)
                      hz') })
                (imgV (pr (sucV a) v) h
                  ⁅ sucV a ⁆s (∈pair-introL refl)
                  (sucV a) (singleton-self (sucV a))
                  ⁅ sucV a , v ⁆ (∈pair-introR refl)
                  v (∈pair-introR refl)
                  a (self∈sucV a)
                  ( subst ⟨_⟩ (sym (prAt-adequate f5 f3 f1
                      (a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                        ∷ pr (sucV a) v ∷ γ ∷ T ∷ []))) refl
                  , subst ⟨_⟩ (sym (sucAt-adequate zero f3
                      (a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                        ∷ pr (sucV a) v ∷ γ ∷ T ∷ []))) refl ))
      sub₂ : ⟨ shiftDown X ⊆ DefA.defSet Φ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
        (shiftDown-out {X = X} {w = y} (∈∈ₛ {a = y} {b = shiftDown X} .snd y∈ₛ))
        where
        build : Σ[ z ∈ V ℓ ] (⟨ z ∈ X ⟩ × (tailGraph z ≡ y))
              → ⟨ y ∈ₛ DefA.defSet Φ ⟩
        build (z , hz , e) =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
            (∈∈ₛ {a = E³ m'} {b = DefA.defSet Φ} .fst
              (subst ⟨_⟩ (sym (chain m')) sat))
          where
          z∈σ : ⟨ z ∈ Lset σ ⟩
          z∈σ = Atr {x = X} {y = z} hz X∈
          y∈³ : ⟨ y ∈ Lset (sucV (sucV (sucV σ))) ⟩
          y∈³ = subst (λ w → ⟨ w ∈ Lset (sucV (sucV (sucV σ))) ⟩) e
            (tailStage σ z∈σ)
          m' = ∈-asFiber {a = y} {b = Lset (sucV (sucV (sucV σ)))} y∈³ .fst
          q' : E³ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset (sucV (sucV (sucV σ)))} y∈³ .snd
          tail≡ : tailGraph z ≡ E³ m'
          tail≡ = e ∙ sym q'
          membV : (zz : V ℓ) → ⟨ zz ∈ E³ m' ⟩
                → ⟨ (zz ∷ z ∷ E³ m' ∷ []) ⊨ tailSeek (var f1) ⟩
          membV zz hzz = PT.rec
            (snd ((zz ∷ z ∷ E³ m' ∷ []) ⊨ tailSeek (var f1)))
            (λ { (a , v , h , e'') →
              seekIn (var f1) (zz ∷ z ∷ E³ m' ∷ []) a v e'' h })
            (tailGraph-out {w = z} {z = zz}
              (subst (λ w → ⟨ zz ∈ w ⟩) (sym tail≡) hzz))
          imgV : (p : V ℓ) → ⟨ p ∈ z ⟩ → (d₁ : V ℓ) → ⟨ d₁ ∈ p ⟩
               → (s : V ℓ) → ⟨ s ∈ d₁ ⟩ → (d₂ : V ℓ) → ⟨ d₂ ∈ p ⟩
               → (v : V ℓ) → ⟨ v ∈ d₂ ⟩ → (a : V ℓ) → ⟨ a ∈ s ⟩
               → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])
                     ⊨ (prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3) ⟩
               → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])
                     ⊨ ∃̇∈ (var f7) (prAt′ zero f1 f2) ⟩
          imgV p hp d₁ hd₁ s hs d₂ hd₂ v hv a ha (s₁ , s₂) =
            ∣ pr a v
            , subst (λ w → ⟨ pr a v ∈ w ⟩) tail≡
                (tailGraph-in
                  (subst (λ w → ⟨ w ∈ z ⟩)
                    (subst ⟨_⟩ (prAt-adequate f5 f3 f1
                      (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])) s₁
                     ∙ cong (λ w → pr w v)
                         (subst ⟨_⟩ (sucAt-adequate zero f3
                           (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])) s₂))
                    hp))
            , subst ⟨_⟩ (sym (prAt-adequate zero f1 f2
                (pr a v ∷ a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ []))) refl
            ∣₁
          sat : ⟨ (E³ m' ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
          sat = ∣ z , subst (λ w → ⟨ z ∈ w ⟩) (sym qX) hz
              , membV , imgV ∣₁
```

<!--en-->
## The extend chain
<!--zh-->
## 扩张链
<!--/-->

<!--en-->
The extension is the shift run backwards, plus one new pair at the empty key.
Its seek sentence mirrors the tail's: the recorded pair now carries the plain
key and the surveyed pair the successor, so the successor witness is bound
through the surveyed member instead. The empty key rides as a constant, and
the empty set enters any next stage by the false formula, whose definable
subset is empty on both readings.
<!--zh-->
扩张就是倒着跑的移位，外加空键处的一个新对。它的寻找句与尾链镜像对应：被记录的对如今携带朴素键，被检视的对携带后继，故后继见证改为经被检视成员约束。空键作为常量随行，而空集经假公式进入任何下一个阶段，其可定义子集在两个读向上都空。
<!--/-->

```agda
private
  emptyDef : (σ : V ℓ) → DefOf.defSet (Lset σ) ⊥̇ ≡ ∅
  emptyDef σ = extensionality (DefA.defSet ⊥̇) ∅ (sub₁ , sub₂)
    where
    module DefA = DefOf (Lset σ)
    sub₁ : ⟨ DefA.defSet ⊥̇ ⊆ ∅ ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
      (λ { ((m , h) , q) →
        Empty.rec (lower
          (subst ⟨_⟩ (DefA.defSet-mem ⊥̇ m) ∣ (m , h) , refl ∣₁)) })
      (∈∈ₛ {a = y} {b = DefA.defSet ⊥̇} .snd y∈ₛ)
    sub₂ : ⟨ ∅ ⊆ DefA.defSet ⊥̇ ⟩
    sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

  ∅Up : (σ : V ℓ) → ⟨ ∅ ∈ Lset (sucV σ) ⟩
  ∅Up σ = mkUp σ ∅ ⊥̇ (emptyDef σ)

  extBody : {ℓ' : Level} {K : Type ℓ'} {m : ℕ}
          → Formula K (suc (suc (suc (suc (suc (suc (suc (suc m))))))))
  extBody = prAt′ f6 f4 f2 ∧̇ (sucAt′ f4 zero ∧̇ prAt′ f7 zero f2)

  extSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} → Term K (suc m) → Formula K (suc m)
  extSeek B = ∃̇∈ B (∃̇∈ (var zero) (∃̇∈ (var zero) (∃̇∈ (var f2)
                (∃̇∈ (var zero) (∃̇∈ (var f5) (∃̇∈ (var zero) extBody))))))

  Δ₀-extSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} (B : Term K (suc m))
             → Δ₀ (extSeek B)
  Δ₀-extSeek B = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
    (δ-∧ (Δ₀-prAt′ f6 f4 f2)
         (δ-∧ (Δ₀-sucAt′ f4 zero) (Δ₀-prAt′ f7 zero f2)))))))))

  extSeekOut : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) ^ (suc n))
             → ⟨ δ ⊨ extSeek B ⟩
             → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                 ((⟦ var zero ⟧ δ ≡ pr (sucV a) v) × ⟨ pr a v ∈ ⟦ B ⟧ δ ⟩) ∥₁
  extSeekOut {n} B δ =
    PT.rec PT.squash₁ (λ { (p , hp , w₁) →
    PT.rec PT.squash₁ (λ { (d , _ , w₂) →
    PT.rec PT.squash₁ (λ { (a , _ , w₃) →
    PT.rec PT.squash₁ (λ { (d′ , _ , w₄) →
    PT.rec PT.squash₁ (λ { (v , _ , w₅) →
    PT.rec PT.squash₁ (λ { (dz , _ , w₆) →
    PT.rec PT.squash₁ (λ { (s , _ , body) →
      finish p d a d′ v dz s hp body })
    w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
    where
    finish : (p d a d′ v dz s : V ℓ) → ⟨ p ∈ ⟦ B ⟧ δ ⟩
           → ⟨ (s ∷ dz ∷ v ∷ d′ ∷ a ∷ d ∷ p ∷ δ) ⊨ extBody ⟩
           → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
               ((⟦ var zero ⟧ δ ≡ pr (sucV a) v) × ⟨ pr a v ∈ ⟦ B ⟧ δ ⟩) ∥₁
    finish p d a d′ v dz s hp (e₁ , e₂ , e₃) =
      ∣ a , v
      , ( subst ⟨_⟩ (prAt-adequate f7 zero f2
            (s ∷ dz ∷ v ∷ d′ ∷ a ∷ d ∷ p ∷ δ)) e₃
        ∙ cong (λ w → pr w v)
            (subst ⟨_⟩ (sucAt-adequate f4 zero
              (s ∷ dz ∷ v ∷ d′ ∷ a ∷ d ∷ p ∷ δ)) e₂) )
      , subst (λ w → ⟨ w ∈ ⟦ B ⟧ δ ⟩)
          (subst ⟨_⟩ (prAt-adequate f6 f4 f2
            (s ∷ dz ∷ v ∷ d′ ∷ a ∷ d ∷ p ∷ δ)) e₁)
          hp ∣₁

  extSeekIn : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) ^ (suc n)) (a v : V ℓ)
            → ⟦ var zero ⟧ δ ≡ pr (sucV a) v → ⟨ pr a v ∈ ⟦ B ⟧ δ ⟩
            → ⟨ δ ⊨ extSeek B ⟩
  extSeekIn B δ a v e h =
    ∣ pr a v , h
    , ∣ ⁅ a ⁆s , ∈pair-introL refl
    , ∣ a , singleton-self a
    , ∣ ⁅ a , v ⁆ , ∈pair-introR refl
    , ∣ v , ∈pair-introR refl
    , ∣ ⁅ sucV a ⁆s , subst (λ w → ⟨ ⁅ sucV a ⁆s ∈ w ⟩) (sym e) (∈pair-introL refl)
    , ∣ sucV a , singleton-self (sucV a)
    , ( subst ⟨_⟩ (sym (prAt-adequate f6 f4 f2 env′)) refl
      , subst ⟨_⟩ (sym (sucAt-adequate f4 zero env′)) refl
      , subst ⟨_⟩ (sym (prAt-adequate f7 zero f2 env′)) e )
    ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    env′ : (V ℓ) ^ (suc (suc (suc (suc (suc (suc (suc (suc _))))))))
    env′ = sucV a ∷ ⁅ sucV a ⁆s ∷ v ∷ ⁅ a , v ⁆ ∷ a ∷ ⁅ a ⁆s ∷ pr a v ∷ δ
```

<!--en-->
## The extended graph, staged
<!--zh-->
## 扩张图，入阶段
<!--/-->

<!--en-->
A single extension climbs five stages: keys pick up a successor, so its pairs
sit two climbs above the successor's two, and the description adds one more.
With the argument, the singleton of the new value and the empty key's
singleton as constants, the description is the empty-key clause or the extend
sentence, and both readings are the two halves of the graph's own reader.
<!--zh-->
单次扩张爬五级：键各添一个后继，故其对住在后继两级之上再两级处，描述再加一级。以实参、新取值的单点集与空键的单点集为常量，描述就是「空键子句或扩张句」，而两个读向恰是图自身读式的两半。
<!--/-->

```agda
private
  extStage : (σ : V ℓ) {y γ : V ℓ} → ⟨ y ∈ Lset σ ⟩ → ⟨ γ ∈ Lset σ ⟩
           → ⟨ extendGraph y γ ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩
  extStage σ {y} {γ} y∈ γ∈ =
    mkUp (sucV (sucV (sucV (sucV σ)))) (extendGraph y γ) Ψ defSet≡
    where
    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV (sucV (sucV (sucV σ)))))
    module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV (sucV (sucV σ))))))

    E⁴ : ⟪ Lset (sucV (sucV (sucV (sucV σ)))) ⟫ → V ℓ
    E⁴ m = ⟪ Lset (sucV (sucV (sucV (sucV σ)))) ⟫↪ m

    γ∈⁴ : ⟨ γ ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩
    γ∈⁴ = up (up (up (up γ∈)))
    mγ = ∈-asFiber {a = γ} {b = Lset (sucV (sucV (sucV (sucV σ))))} γ∈⁴ .fst
    qγ : E⁴ mγ ≡ γ
    qγ = ∈-asFiber {a = γ} {b = Lset (sucV (sucV (sucV (sucV σ))))} γ∈⁴ .snd
    Sy∈⁴ : ⟨ ⁅ y ⁆s ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩
    Sy∈⁴ = up (up (up (sglUp σ y∈)))
    mSy = ∈-asFiber {a = ⁅ y ⁆s} {b = Lset (sucV (sucV (sucV (sucV σ))))} Sy∈⁴ .fst
    qSy : E⁴ mSy ≡ ⁅ y ⁆s
    qSy = ∈-asFiber {a = ⁅ y ⁆s} {b = Lset (sucV (sucV (sucV (sucV σ))))} Sy∈⁴ .snd
    K0∈⁴ : ⟨ ⁅ ∅ ⁆s ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩
    K0∈⁴ = up (up (sglUp (sucV σ) (∅Up σ)))
    mK0 = ∈-asFiber {a = ⁅ ∅ ⁆s} {b = Lset (sucV (sucV (sucV (sucV σ))))} K0∈⁴ .fst
    qK0 : E⁴ mK0 ≡ ⁅ ∅ ⁆s
    qK0 = ∈-asFiber {a = ⁅ ∅ ⁆s} {b = Lset (sucV (sucV (sucV (sucV σ))))} K0∈⁴ .snd

    Ψ : Formula ⟪ Lset (sucV (sucV (sucV (sucV σ)))) ⟫ 1
    Ψ = (∃̇∈ (con mK0) (∃̇∈ (con mSy) (prAt′ f2 f1 zero))) ∨̇ extSeek (con mγ)

    dΨ : Δ₀ Ψ
    dΨ = δ-∨ (δ-∃∈ (δ-∃∈ (Δ₀-prAt′ f2 f1 zero))) (Δ₀-extSeek (con mγ))

    chain : ∀ m → (E⁴ m ∈ DefA.defSet Ψ)
                ≡ ((E⁴ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ))
    chain m = RefA.abs-defSet Ψ dΨ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Ψ) (E⁴ m ∷ []))

    defSet≡ : DefA.defSet Ψ ≡ extendGraph y γ
    defSet≡ = extensionality (DefA.defSet Ψ) (extendGraph y γ) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Ψ ⊆ extendGraph y γ ⟩
      sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ extendGraph y γ))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ extendGraph y γ ⟩) q
            (mem m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = z} {b = DefA.defSet Ψ} .snd z∈ₛ)
        where
        mem : (m : ⟪ Lset (sucV (sucV (sucV (sucV σ)))) ⟫)
            → ⟨ (E⁴ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ) ⟩
            → ⟨ E⁴ m ∈ₛ extendGraph y γ ⟩
        mem m = PT.rec (snd (E⁴ m ∈ₛ extendGraph y γ))
          (λ { (inl zc) → zCase zc ; (inr sk) → sCase sk })
          where
          zCase : ⟨ (E⁴ m ∷ []) ⊨ ∃̇∈ (con (E⁴ mK0)) (∃̇∈ (con (E⁴ mSy)) (prAt′ f2 f1 zero)) ⟩
                → ⟨ E⁴ m ∈ₛ extendGraph y γ ⟩
          zCase = PT.rec (snd (E⁴ m ∈ₛ extendGraph y γ))
            (λ { (e′ , he′ , w₁) →
              PT.rec (snd (E⁴ m ∈ₛ extendGraph y γ))
                (λ { (y′ , hy′ , sZ) →
                  ∈∈ₛ {a = E⁴ m} {b = extendGraph y γ} .fst
                    (subst (λ w → ⟨ w ∈ extendGraph y γ ⟩)
                      (sym ( subst ⟨_⟩ (prAt-adequate f2 f1 zero
                               (y′ ∷ e′ ∷ E⁴ m ∷ [])) sZ
                           ∙ cong₂ pr
                               (singleton-out (subst (λ w → ⟨ e′ ∈ w ⟩) qK0 he′))
                               (singleton-out (subst (λ w → ⟨ y′ ∈ w ⟩) qSy hy′)) ))
                      (extendGraph-zero {y} {γ})) })
                w₁ })
          sCase : ⟨ (E⁴ m ∷ []) ⊨ extSeek (con (E⁴ mγ)) ⟩
                → ⟨ E⁴ m ∈ₛ extendGraph y γ ⟩
          sCase sk = PT.rec (snd (E⁴ m ∈ₛ extendGraph y γ))
            (λ { (a , v , e , h) →
              ∈∈ₛ {a = E⁴ m} {b = extendGraph y γ} .fst
                (subst (λ w → ⟨ w ∈ extendGraph y γ ⟩) (sym e)
                  (extendGraph-suc {y} {γ}
                    (subst (λ w → ⟨ pr a v ∈ w ⟩) qγ h))) })
            (extSeekOut (con (E⁴ mγ)) (E⁴ m ∷ []) sk)
      sub₂ : ⟨ extendGraph y γ ⊆ DefA.defSet Ψ ⟩
      sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet Ψ))
        (λ { (inl e) → zBuild e ; (inr (a , v , h , e)) → sBuild a v h e })
        (extendGraph-out {y} {γ} {z}
          (∈∈ₛ {a = z} {b = extendGraph y γ} .snd z∈ₛ))
        where
        zBuild : z ≡ pr ∅ y → ⟨ z ∈ₛ DefA.defSet Ψ ⟩
        zBuild e =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet Ψ ⟩) q′
            (∈∈ₛ {a = E⁴ m′} {b = DefA.defSet Ψ} .fst
              (subst ⟨_⟩ (sym (chain m′)) sat))
          where
          z∈⁴ : ⟨ z ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩
          z∈⁴ = subst (λ w → ⟨ w ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩) (sym e)
            (up (prUp (sucV σ) (∅Up σ) (up y∈)))
          m′ = ∈-asFiber {a = z} {b = Lset (sucV (sucV (sucV (sucV σ))))} z∈⁴ .fst
          q′ : E⁴ m′ ≡ z
          q′ = ∈-asFiber {a = z} {b = Lset (sucV (sucV (sucV (sucV σ))))} z∈⁴ .snd
          sat : ⟨ (E⁴ m′ ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ) ⟩
          sat = ∣ inl
            ∣ ∅ , subst (λ w → ⟨ ∅ ∈ w ⟩) (sym qK0) (singleton-self ∅)
            , ∣ y , subst (λ w → ⟨ y ∈ w ⟩) (sym qSy) (singleton-self y)
            , subst ⟨_⟩ (sym (prAt-adequate f2 f1 zero
                (y ∷ ∅ ∷ E⁴ m′ ∷ []))) (q′ ∙ e)
            ∣₁ ∣₁ ∣₁
        sBuild : (a v : V ℓ) → ⟨ pr a v ∈ γ ⟩ → z ≡ pr (sucV a) v
               → ⟨ z ∈ₛ DefA.defSet Ψ ⟩
        sBuild a v h e =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet Ψ ⟩) q′
            (∈∈ₛ {a = E⁴ m′} {b = DefA.defSet Ψ} .fst
              (subst ⟨_⟩ (sym (chain m′)) sat))
          where
          p∈σ : ⟨ pr a v ∈ Lset σ ⟩
          p∈σ = Atr {x = γ} {y = pr a v} h γ∈
          a∈σ : ⟨ a ∈ Lset σ ⟩
          a∈σ = Atr {x = ⁅ a ⁆s} {y = a} (singleton-self a)
            (Atr {x = pr a v} {y = ⁅ a ⁆s} (∈pair-introL refl) p∈σ)
          v∈σ : ⟨ v ∈ Lset σ ⟩
          v∈σ = Atr {x = ⁅ a , v ⁆} {y = v} (∈pair-introR refl)
            (Atr {x = pr a v} {y = ⁅ a , v ⁆} (∈pair-introR refl) p∈σ)
          z∈⁴ : ⟨ z ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩
          z∈⁴ = subst (λ w → ⟨ w ∈ Lset (sucV (sucV (sucV (sucV σ)))) ⟩) (sym e)
            (prUp (sucV (sucV σ)) (sucUp σ a∈σ) (up (up v∈σ)))
          m′ = ∈-asFiber {a = z} {b = Lset (sucV (sucV (sucV (sucV σ))))} z∈⁴ .fst
          q′ : E⁴ m′ ≡ z
          q′ = ∈-asFiber {a = z} {b = Lset (sucV (sucV (sucV (sucV σ))))} z∈⁴ .snd
          sat : ⟨ (E⁴ m′ ∷ []) ⊨ mapFo fst (mapFo DefA.ι Ψ) ⟩
          sat = ∣ inr (extSeekIn (con (E⁴ mγ)) (E⁴ m′ ∷ []) a v (q′ ∙ e)
            (subst (λ w → ⟨ pr a v ∈ w ⟩) (sym qγ) h)) ∣₁
```

<!--en-->
## The extension
<!--zh-->
## 扩张
<!--/-->

<!--en-->
The family formula binds the graph and the new value, then pins the surveyed
set with three clauses: every member is the empty-key pair or an extend-shaped
pair, the empty-key pair is a member, and every recorded pair's extension is a
member. The readings are the staged graph's readings run against a bound
variable, with the graph's reader supplying every witness.
<!--zh-->
族公式先约束图与新取值，再用三条子句钉住被检视集合：每个成员是空键对或扩张形对、空键对是成员、每个被记录对的扩张是成员。读法就是入阶段那节的读法对着约束变元再跑一遍，图自身的读式提供全部见证。
<!--/-->

```agda
private
  module ExtF (X Y σ : V ℓ) (X∈ : ⟨ X ∈ Lset σ ⟩) (Y∈ : ⟨ Y ∈ Lset σ ⟩) where

    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV (sucV (sucV (sucV (sucV σ))))))
    module RefA = DefA.Refine
      (layer-trans (Lset-layer (sucV (sucV (sucV (sucV (sucV σ)))))))

    E⁵ : ⟪ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟫ → V ℓ
    E⁵ m = ⟪ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟫↪ m

    X∈⁵ : ⟨ X ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩
    X∈⁵ = up (up (up (up (up X∈))))
    mX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} X∈⁵ .fst
    qX : E⁵ mX ≡ X
    qX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} X∈⁵ .snd
    Y∈⁵ : ⟨ Y ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩
    Y∈⁵ = up (up (up (up (up Y∈))))
    mY = ∈-asFiber {a = Y} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} Y∈⁵ .fst
    qY : E⁵ mY ≡ Y
    qY = ∈-asFiber {a = Y} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} Y∈⁵ .snd
    K0∈⁵ : ⟨ ⁅ ∅ ⁆s ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩
    K0∈⁵ = up (up (up (sglUp (sucV σ) (∅Up σ))))
    mK0 = ∈-asFiber {a = ⁅ ∅ ⁆s} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} K0∈⁵ .fst
    qK0 : E⁵ mK0 ≡ ⁅ ∅ ⁆s
    qK0 = ∈-asFiber {a = ⁅ ∅ ⁆s} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} K0∈⁵ .snd

    Φ : Formula ⟪ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟫ 1
    Φ = ∃̇∈ (con mX) (∃̇∈ (con mY)
          ( (∀̇∈ (var f2)
              ((∃̇∈ (con mK0) (prAt′ f1 zero f2)) ∨̇ extSeek (var f2)))
          ∧̇ ( (∃̇∈ (con mK0) (∃̇∈ (var f3) (prAt′ zero f1 f2)))
          ∧̇ (∀̇∈ (var f1) (∀̇∈ (var zero) (∀̇∈ (var zero)
               (∀̇∈ (var f2) (∀̇∈ (var zero)
                 ((prAt′ f4 f2 zero)
                   ⇒̇ (∃̇∈ (var f7) (∃̇∈ (var zero) (∃̇∈ (var zero)
                        (sucAt′ f5 zero ∧̇ prAt′ f2 zero f3)))))))))) ) ))

    dΦ : Δ₀ Φ
    dΦ = δ-∃∈ (δ-∃∈ (δ-∧
      (δ-∀∈ (δ-∨ (δ-∃∈ (Δ₀-prAt′ f1 zero f2)) (Δ₀-extSeek (var f2))))
      (δ-∧ (δ-∃∈ (δ-∃∈ (Δ₀-prAt′ zero f1 f2)))
           (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈
             (δ-⇒ (Δ₀-prAt′ f4 f2 zero)
                  (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-sucAt′ f5 zero)
                                         (Δ₀-prAt′ f2 zero f3))))))))))))))

    chain : ∀ m → (E⁵ m ∈ DefA.defSet Φ)
                ≡ ((E⁵ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ))
    chain m = RefA.abs-defSet Φ dΦ m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Φ) (E⁵ m ∷ []))

    defSet≡ : DefA.defSet Φ ≡ extendFamily X Y
    defSet≡ = extensionality (DefA.defSet Φ) (extendFamily X Y) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ extendFamily X Y ⟩
      sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ extendFamily X Y))
        (λ { ((m , h) , q) →
          subst (λ u → ⟨ u ∈ₛ extendFamily X Y ⟩) q
            (∈∈ₛ {a = E⁵ m} {b = extendFamily X Y} .fst
              (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = w} {b = DefA.defSet Φ} .snd w∈ₛ)
        where
        fromSat : (m : ⟪ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟫)
                → ⟨ (E⁵ m ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
                → ⟨ E⁵ m ∈ extendFamily X Y ⟩
        fromSat m = PT.rec (snd (E⁵ m ∈ extendFamily X Y))
          (λ { (γ , hγ , big) →
            PT.rec (snd (E⁵ m ∈ extendFamily X Y))
              (λ { (y , hy , membV , imgZV , imgSV) →
                subst (λ u → ⟨ u ∈ extendFamily X Y ⟩)
                  (sym (G≡ γ y membV imgZV imgSV))
                  (extendFamily-in {X = X} {Y = Y}
                    (subst (λ u → ⟨ γ ∈ u ⟩) qX hγ)
                    (subst (λ u → ⟨ y ∈ u ⟩) qY hy)) })
              big })
          where
          T = E⁵ m
          G≡ : (γ y : V ℓ)
             → ((z : V ℓ) → ⟨ z ∈ T ⟩
                → ⟨ (z ∷ y ∷ γ ∷ T ∷ [])
                      ⊨ ((∃̇∈ (con (E⁵ mK0)) (prAt′ f1 zero f2)) ∨̇ extSeek (var f2)) ⟩)
             → ⟨ (y ∷ γ ∷ T ∷ [])
                   ⊨ ∃̇∈ (con (E⁵ mK0)) (∃̇∈ (var f3) (prAt′ zero f1 f2)) ⟩
             → ((p : V ℓ) → ⟨ p ∈ γ ⟩ → (d : V ℓ) → ⟨ d ∈ p ⟩
                → (a : V ℓ) → ⟨ a ∈ d ⟩ → (d′ : V ℓ) → ⟨ d′ ∈ p ⟩
                → (v : V ℓ) → ⟨ v ∈ d′ ⟩
                → ⟨ (v ∷ d′ ∷ a ∷ d ∷ p ∷ y ∷ γ ∷ T ∷ []) ⊨ prAt′ f4 f2 zero ⟩
                → ⟨ (v ∷ d′ ∷ a ∷ d ∷ p ∷ y ∷ γ ∷ T ∷ [])
                      ⊨ ∃̇∈ (var f7) (∃̇∈ (var zero) (∃̇∈ (var zero)
                           (sucAt′ f5 zero ∧̇ prAt′ f2 zero f3))) ⟩)
             → T ≡ extendGraph y γ
          G≡ γ y membV imgZV imgSV =
            extensionality T (extendGraph y γ) (g₁ , g₂)
            where
            g₁ : ⟨ T ⊆ extendGraph y γ ⟩
            g₁ z z∈ₛ = PT.rec (snd (z ∈ₛ extendGraph y γ))
              (λ { (inl zc) → zCase zc ; (inr sk) → sCase sk })
              (membV z (∈∈ₛ {a = z} {b = T} .snd z∈ₛ))
              where
              zCase : ⟨ (z ∷ y ∷ γ ∷ T ∷ []) ⊨ ∃̇∈ (con (E⁵ mK0)) (prAt′ f1 zero f2) ⟩
                    → ⟨ z ∈ₛ extendGraph y γ ⟩
              zCase = PT.rec (snd (z ∈ₛ extendGraph y γ))
                (λ { (e′ , he′ , sZ) →
                  ∈∈ₛ {a = z} {b = extendGraph y γ} .fst
                    (subst (λ u → ⟨ u ∈ extendGraph y γ ⟩)
                      (sym ( subst ⟨_⟩ (prAt-adequate f1 zero f2
                               (e′ ∷ z ∷ y ∷ γ ∷ T ∷ [])) sZ
                           ∙ cong (λ u → pr u y)
                               (singleton-out
                                 (subst (λ u → ⟨ e′ ∈ u ⟩) qK0 he′)) ))
                      (extendGraph-zero {y} {γ})) })
              sCase : ⟨ (z ∷ y ∷ γ ∷ T ∷ []) ⊨ extSeek (var f2) ⟩
                    → ⟨ z ∈ₛ extendGraph y γ ⟩
              sCase sk = PT.rec (snd (z ∈ₛ extendGraph y γ))
                (λ { (a , v , e , h) →
                  ∈∈ₛ {a = z} {b = extendGraph y γ} .fst
                    (subst (λ u → ⟨ u ∈ extendGraph y γ ⟩) (sym e)
                      (extendGraph-suc {y} {γ} h)) })
                (extSeekOut (var f2) (z ∷ y ∷ γ ∷ T ∷ []) sk)
            g₂ : ⟨ extendGraph y γ ⊆ T ⟩
            g₂ z z∈ₛ = PT.rec (snd (z ∈ₛ T))
              (λ { (inl e) → zRead e ; (inr (a , v , h , e)) → sRead a v h e })
              (extendGraph-out {y} {γ} {z}
                (∈∈ₛ {a = z} {b = extendGraph y γ} .snd z∈ₛ))
              where
              zRead : z ≡ pr ∅ y → ⟨ z ∈ₛ T ⟩
              zRead e = PT.rec (snd (z ∈ₛ T))
                (λ { (e″ , he″ , w₁) →
                  PT.rec (snd (z ∈ₛ T))
                    (λ { (z′ , hz′ , sZ′) →
                      ∈∈ₛ {a = z} {b = T} .fst
                        (subst (λ u → ⟨ u ∈ T ⟩)
                          ( ( subst ⟨_⟩ (prAt-adequate zero f1 f2
                                (z′ ∷ e″ ∷ y ∷ γ ∷ T ∷ [])) sZ′
                            ∙ cong (λ u → pr u y)
                                (singleton-out
                                  (subst (λ u → ⟨ e″ ∈ u ⟩) qK0 he″)) )
                          ∙ sym e )
                          hz′) })
                    w₁ })
                imgZV
              sRead : (a v : V ℓ) → ⟨ pr a v ∈ γ ⟩ → z ≡ pr (sucV a) v
                    → ⟨ z ∈ₛ T ⟩
              sRead a v h e = PT.rec (snd (z ∈ₛ T))
                (λ { (z′ , hz′ , w₁) →
                  PT.rec (snd (z ∈ₛ T))
                    (λ { (dz , hdz , w₂) →
                      PT.rec (snd (z ∈ₛ T))
                        (λ { (s , hs , (sS , sP)) →
                          ∈∈ₛ {a = z} {b = T} .fst
                            (subst (λ u → ⟨ u ∈ T ⟩)
                              ( ( subst ⟨_⟩ (prAt-adequate f2 zero f3
                                    (s ∷ dz ∷ z′ ∷ v ∷ ⁅ a , v ⁆ ∷ a ∷ ⁅ a ⁆s
                                      ∷ pr a v ∷ y ∷ γ ∷ T ∷ [])) sP
                                ∙ cong (λ u → pr u v)
                                    (subst ⟨_⟩ (sucAt-adequate f5 zero
                                      (s ∷ dz ∷ z′ ∷ v ∷ ⁅ a , v ⁆ ∷ a ∷ ⁅ a ⁆s
                                        ∷ pr a v ∷ y ∷ γ ∷ T ∷ [])) sS) )
                              ∙ sym e )
                              hz′) })
                        w₂ })
                    w₁ })
                (imgSV (pr a v) h
                  ⁅ a ⁆s (∈pair-introL refl)
                  a (singleton-self a)
                  ⁅ a , v ⁆ (∈pair-introR refl)
                  v (∈pair-introR refl)
                  (subst ⟨_⟩ (sym (prAt-adequate f4 f2 zero
                    (v ∷ ⁅ a , v ⁆ ∷ a ∷ ⁅ a ⁆s ∷ pr a v ∷ y ∷ γ ∷ T ∷ []))) refl))
      sub₂ : ⟨ extendFamily X Y ⊆ DefA.defSet Φ ⟩
      sub₂ w w∈ₛ = PT.rec (snd (w ∈ₛ DefA.defSet Φ)) build
        (extendFamily-out {X = X} {Y = Y} {w = w}
          (∈∈ₛ {a = w} {b = extendFamily X Y} .snd w∈ₛ))
        where
        build : Σ[ γ ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                (⟨ γ ∈ X ⟩ × ⟨ y ∈ Y ⟩ × (w ≡ extendGraph y γ))
              → ⟨ w ∈ₛ DefA.defSet Φ ⟩
        build (γ , y , hγ , hy , e) =
          subst (λ u → ⟨ u ∈ₛ DefA.defSet Φ ⟩) q′
            (∈∈ₛ {a = E⁵ m′} {b = DefA.defSet Φ} .fst
              (subst ⟨_⟩ (sym (chain m′)) sat))
          where
          γ∈σ : ⟨ γ ∈ Lset σ ⟩
          γ∈σ = Atr {x = X} {y = γ} hγ X∈
          y∈σ : ⟨ y ∈ Lset σ ⟩
          y∈σ = Atr {x = Y} {y = y} hy Y∈
          w∈⁵ : ⟨ w ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩
          w∈⁵ = subst (λ u → ⟨ u ∈ Lset (sucV (sucV (sucV (sucV (sucV σ))))) ⟩)
            (sym e) (extStage σ y∈σ γ∈σ)
          m′ = ∈-asFiber {a = w} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} w∈⁵ .fst
          q′ : E⁵ m′ ≡ w
          q′ = ∈-asFiber {a = w} {b = Lset (sucV (sucV (sucV (sucV (sucV σ)))))} w∈⁵ .snd
          ext≡ : extendGraph y γ ≡ E⁵ m′
          ext≡ = sym e ∙ sym q′
          membV : (z : V ℓ) → ⟨ z ∈ E⁵ m′ ⟩
                → ⟨ (z ∷ y ∷ γ ∷ E⁵ m′ ∷ [])
                      ⊨ ((∃̇∈ (con (E⁵ mK0)) (prAt′ f1 zero f2)) ∨̇ extSeek (var f2)) ⟩
          membV z hz = PT.rec
            (snd ((z ∷ y ∷ γ ∷ E⁵ m′ ∷ [])
              ⊨ ((∃̇∈ (con (E⁵ mK0)) (prAt′ f1 zero f2)) ∨̇ extSeek (var f2))))
            (λ { (inl e″) →
                  ∣ inl ∣ ∅ , subst (λ u → ⟨ ∅ ∈ u ⟩) (sym qK0) (singleton-self ∅)
                    , subst ⟨_⟩ (sym (prAt-adequate f1 zero f2
                        (∅ ∷ z ∷ y ∷ γ ∷ E⁵ m′ ∷ []))) e″
                    ∣₁ ∣₁
               ; (inr (a , v , h , e″)) →
                  ∣ inr (extSeekIn (var f2) (z ∷ y ∷ γ ∷ E⁵ m′ ∷ []) a v e″ h) ∣₁ })
            (extendGraph-out {y} {γ} {z}
              (subst (λ u → ⟨ z ∈ u ⟩) (sym ext≡) hz))
          imgZV : ⟨ (y ∷ γ ∷ E⁵ m′ ∷ [])
                      ⊨ ∃̇∈ (con (E⁵ mK0)) (∃̇∈ (var f3) (prAt′ zero f1 f2)) ⟩
          imgZV = ∣ ∅ , subst (λ u → ⟨ ∅ ∈ u ⟩) (sym qK0) (singleton-self ∅)
            , ∣ pr ∅ y
              , subst (λ u → ⟨ pr ∅ y ∈ u ⟩) ext≡ (extendGraph-zero {y} {γ})
              , subst ⟨_⟩ (sym (prAt-adequate zero f1 f2
                  (pr ∅ y ∷ ∅ ∷ y ∷ γ ∷ E⁵ m′ ∷ []))) refl
            ∣₁ ∣₁
          imgSV : (p : V ℓ) → ⟨ p ∈ γ ⟩ → (d : V ℓ) → ⟨ d ∈ p ⟩
                → (a : V ℓ) → ⟨ a ∈ d ⟩ → (d′ : V ℓ) → ⟨ d′ ∈ p ⟩
                → (v : V ℓ) → ⟨ v ∈ d′ ⟩
                → ⟨ (v ∷ d′ ∷ a ∷ d ∷ p ∷ y ∷ γ ∷ E⁵ m′ ∷ []) ⊨ prAt′ f4 f2 zero ⟩
                → ⟨ (v ∷ d′ ∷ a ∷ d ∷ p ∷ y ∷ γ ∷ E⁵ m′ ∷ [])
                      ⊨ ∃̇∈ (var f7) (∃̇∈ (var zero) (∃̇∈ (var zero)
                           (sucAt′ f5 zero ∧̇ prAt′ f2 zero f3))) ⟩
          imgSV p hp d hd a ha d′ hd′ v hv s₁ =
            ∣ pr (sucV a) v
            , subst (λ u → ⟨ pr (sucV a) v ∈ u ⟩) ext≡
                (extendGraph-suc {y} {γ}
                  (subst (λ u → ⟨ u ∈ γ ⟩)
                    (subst ⟨_⟩ (prAt-adequate f4 f2 zero
                      (v ∷ d′ ∷ a ∷ d ∷ p ∷ y ∷ γ ∷ E⁵ m′ ∷ [])) s₁)
                    hp))
            , ∣ ⁅ sucV a ⁆s , ∈pair-introL refl
            , ∣ sucV a , singleton-self (sucV a)
              , ( subst ⟨_⟩ (sym (sucAt-adequate f5 zero
                    (sucV a ∷ ⁅ sucV a ⁆s ∷ pr (sucV a) v ∷ v ∷ d′ ∷ a ∷ d
                      ∷ p ∷ y ∷ γ ∷ E⁵ m′ ∷ []))) refl
                , subst ⟨_⟩ (sym (prAt-adequate f2 zero f3
                    (sucV a ∷ ⁅ sucV a ⁆s ∷ pr (sucV a) v ∷ v ∷ d′ ∷ a ∷ d
                      ∷ p ∷ y ∷ γ ∷ E⁵ m′ ∷ []))) refl )
            ∣₁ ∣₁ ∣₁
          sat : ⟨ (E⁵ m′ ∷ []) ⊨ mapFo fst (mapFo DefA.ι Φ) ⟩
          sat = ∣ γ , subst (λ u → ⟨ γ ∈ u ⟩) (sym qX) hγ
              , ∣ y , subst (λ u → ⟨ y ∈ u ⟩) (sym qY) hy
              , membV , imgZV , imgSV ∣₁ ∣₁
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

selectMemberL : {X Ka Kb : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Ka ⟩ → ⟨ isL Kb ⟩
              → ⟨ isL (selectMember X Ka Kb) ⟩
selectMemberL {X} {Ka} {Kb} lX lKa lKb =
  PT.rec (snd (isL (selectMember X Ka Kb)))
    (λ { (σ , oσ , mem3) →
      defSet→isL σ oσ (selectMember X Ka Kb)
        ∣ SelMem.Φ X Ka Kb σ (mem3 zero) (mem3 f1) (mem3 f2)
        , SelMem.defSet≡ X Ka Kb σ (mem3 zero) (mem3 f1) (mem3 f2) ∣₁ })
    (stageFam 3 fam famL)
  where
  fam : Fin 3 → V ℓ
  fam zero = X
  fam (suc zero) = Ka
  fam (suc (suc zero)) = Kb
  famL : (i : Fin 3) → ⟨ isL (fam i) ⟩
  famL zero = lX
  famL (suc zero) = lKa
  famL (suc (suc zero)) = lKb

selectEqualL : {X Ka Kb : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Ka ⟩ → ⟨ isL Kb ⟩
             → ⟨ isL (selectEqual X Ka Kb) ⟩
selectEqualL {X} {Ka} {Kb} lX lKa lKb =
  PT.rec (snd (isL (selectEqual X Ka Kb)))
    (λ { (σ , oσ , mem3) →
      defSet→isL σ oσ (selectEqual X Ka Kb)
        ∣ SelEq.Φ X Ka Kb σ (mem3 zero) (mem3 f1) (mem3 f2)
        , SelEq.defSet≡ X Ka Kb σ (mem3 zero) (mem3 f1) (mem3 f2) ∣₁ })
    (stageFam 3 fam famL)
  where
  fam : Fin 3 → V ℓ
  fam zero = X
  fam (suc zero) = Ka
  fam (suc (suc zero)) = Kb
  famL : (i : Fin 3) → ⟨ isL (fam i) ⟩
  famL zero = lX
  famL (suc zero) = lKa
  famL (suc (suc zero)) = lKb

shiftDownL : {X : V ℓ} → ⟨ isL X ⟩ → ⟨ isL (shiftDown X) ⟩
shiftDownL {X} = PT.rec (snd (isL (shiftDown X)))
  λ { (σ , oσ , X∈) →
    defSet→isL (sucV (sucV (sucV σ))) (suc-ord (suc-ord (suc-ord oσ)))
      (shiftDown X)
      ∣ SftD.Φ X σ X∈ , SftD.defSet≡ X σ X∈ ∣₁ }

extendFamilyL : {X Y : V ℓ} → ⟨ isL X ⟩ → ⟨ isL Y ⟩
              → ⟨ isL (extendFamily X Y) ⟩
extendFamilyL {X} {Y} lX lY = PT.rec (snd (isL (extendFamily X Y)))
  (λ { (σ , (oσ , (X∈ , Y∈))) →
    defSet→isL (sucV (sucV (sucV (sucV (sucV σ)))))
      (suc-ord (suc-ord (suc-ord (suc-ord (suc-ord oσ)))))
      (extendFamily X Y)
      ∣ ExtF.Φ X Y σ X∈ Y∈ , ExtF.defSet≡ X Y σ X∈ Y∈ ∣₁ })
  (isL-directed X Y lX lY)

valuesL : {X : V ℓ} → ⟨ isL X ⟩ → ⟨ isL (values X) ⟩
valuesL {X} lX = PT.rec (snd (isL (values X)))
  (λ { (σ , oσ , mem2) →
    defSet→isL σ oσ (values X)
      ∣ Vals.Φ X σ (mem2 zero) (mem2 f1)
      , Vals.defSet≡ X σ (mem2 zero) (mem2 f1) ∣₁ })
  (stageFam 2 fam famL)
  where
  zeroL : ⟨ isL (# 0) ⟩
  zeroL = subst (λ z → ⟨ isL z ⟩) (numeralL-fst 0) (numeralL 0 .snd)
  fam : Fin 2 → V ℓ
  fam zero = X
  fam (suc zero) = ⁅ # 0 ⁆s
  famL : (i : Fin 2) → ⟨ isL (fam i) ⟩
  famL zero = lX
  famL (suc zero) = sglL zeroL
```

<!--en-->
## The whole table
<!--zh-->
## 整张表
<!--/-->

<!--en-->
The capstone. All tuples over a constructible carrier are constructible by
induction on the arity: the empty case is the singleton of the empty graph,
and the successor case is exactly the tuple chapter's extension equation read
through the family lemma. Every numeral is constructible through the numeral
chain, every member of a constructible set through transitivity, and with
that, one term induction closes the account: **every denotation of every
combinator term over a constructible carrier is constructible**. This is the
statement the internal tower will quantify.
<!--zh-->
封顶。可构造载体上的全体元组对元数归纳可构造：空情形是空图的单点集，后继情形恰是元组章的扩张等式经族引理读出。每个数码经数码链可构造，可构造集合的每个成员经传递性可构造，于是一次项归纳合上账本：**可构造载体上每个组合子项的每个指称都可构造**。这就是内部塔将要量化的陈述。
<!--/-->

```agda
private
  numL : (k : ℕ) → ⟨ isL (# k) ⟩
  numL k = subst (λ z → ⟨ isL z ⟩) (numeralL-fst k) (numeralL k .snd)

  ∅L : ⟨ isL ∅ ⟩
  ∅L = defSet→isL ∅ ∅-ord ∅ ∣ ⊥̇ , emptyDef ∅ ∣₁

allTuplesL : (A : V ℓ) → ⟨ isL A ⟩ → (n : ℕ) → ⟨ isL (allTuples A n) ⟩
allTuplesL A lA zero =
  subst (λ z → ⟨ isL z ⟩) (sym (allTuples-zero A))
    (subst (λ z → ⟨ isL z ⟩) (sym (pair-singleton ∅)) (sglL ∅L))
allTuplesL A lA (suc n) =
  subst (λ z → ⟨ isL z ⟩) (sym (allTuples-suc A n))
    (extendFamilyL {X = allTuples A n} {Y = A} (allTuplesL A lA n) lA)

denoteL : (A : V ℓ) → ⟨ isL A ⟩ → {n : ℕ} (t : KT ⟪ A ⟫ n)
        → ⟨ isL (⟦_⟧ᴷ A t) ⟩
denoteL A lA {n} allK = allTuplesL A lA n
denoteL A lA {n} (selMemK i j) =
  selectMemberL {X = allTuples A n} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
    (allTuplesL A lA n) (sglL (numL (toℕ i))) (sglL (numL (toℕ j)))
denoteL A lA {n} (selEqK i j) =
  selectEqualL {X = allTuples A n} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
    (allTuplesL A lA n) (sglL (numL (toℕ i))) (sglL (numL (toℕ j)))
denoteL A lA {n} (selEqConK i a) =
  shiftDownL
    {X = selectEqual (extendFamily (allTuples A n) ⁅ ⟪ A ⟫↪ a ⁆s)
           ⁅ # (suc (toℕ i)) ⁆s ⁅ # 0 ⁆s}
    (selectEqualL
      {X = extendFamily (allTuples A n) ⁅ ⟪ A ⟫↪ a ⁆s}
      {Ka = ⁅ # (suc (toℕ i)) ⁆s} {Kb = ⁅ # 0 ⁆s}
      (extendFamilyL {X = allTuples A n} {Y = ⁅ ⟪ A ⟫↪ a ⁆s}
        (allTuplesL A lA n)
        (sglL (isL-trans {x = A} {y = ⟪ A ⟫↪ a}
          (∈∈ₛ {a = ⟪ A ⟫↪ a} {b = A} .snd (∈ₛ⟪ A ⟫↪ a)) lA)))
      (sglL (numL (suc (toℕ i)))) (sglL (numL 0)))
denoteL A lA (interK s t) =
  capL {X = ⟦_⟧ᴷ A s} {Y = ⟦_⟧ᴷ A t} (denoteL A lA s) (denoteL A lA t)
denoteL A lA (unionK s t) =
  cupL {X = ⟦_⟧ᴷ A s} {Y = ⟦_⟧ᴷ A t} (denoteL A lA s) (denoteL A lA t)
denoteL A lA {n} (complK t) =
  diffL {X = allTuples A n} {Y = ⟦_⟧ᴷ A t} (allTuplesL A lA n) (denoteL A lA t)
denoteL A lA (shiftK t) =
  shiftDownL {X = ⟦_⟧ᴷ A t} (denoteL A lA t)
```
