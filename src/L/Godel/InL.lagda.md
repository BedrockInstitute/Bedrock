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
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( isL; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd )
open import L.Axioms.Basic {ℓ} using ( isL-directed; defSet→isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Base {ℓ} using ( prAt-adequate; ∈pair-introR )
open import L.Coding.InL {ℓ} using ( sglL )
open import L.Godel.Operations {ℓ}
  using ( _∪_; ∪-left; ∪-right; ∪-out; _∩_; ∩-in; ∩-out; _∖_; ∖-in; ∖-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; values; values-in; values-wit; singleton-self; singleton-out )

open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Bool using ( Bool; true; false )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id using ( _⊨_ )
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
选择带参数，故其章节需要两个以上的集合共处一个阶段。两集合的论证迭代即可：空阶段处理空族，一个界层序数把头的阶段与尾的阶段并起来。
<!--/-->

```agda
private
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
读图的运算谈论 Kuratowski 对，故其定义公式也必须谈论。本书编码部分已把对读式写过一次，无常量，并配了外层满足处的适足性；唯一的错位在常量域，彼处固定而此处自由。于是把读式一字不差地重述一遍，让域成为参数；而适足性完全不必重述：无常量公式被每次重标固定，故一旦隶属问题被搬到外层世界 (`abs-defSet`{.Agda} 加一次重标)，原来的适足性引理原样适用。几个固定的变元序号一次命名，de Bruijn 算术只住在一处。
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
第一个图运算。`selectMember X Ka Kb`{.Agda} 的成员是 `X` 的这样一个成员：在各键集的某个键处，记录着两个成隶属关系的取值。定义公式用八个有界量词说出它：各键集取一个键，然后每个被记录的对经成员自身内部的成员链到达，链上两个中转站恰在对提供它们的地方约束。外延等同的两个方向读同一条链：向外，满足逐层剥开截断，对读式的适足性把每条对子句变成隶属定律要消费的等式；向内，运算的见证读式提供取值，中转站就是对自身的两个成员。
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
