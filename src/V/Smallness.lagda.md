# Smallness

<!--en-->
The previous chapter ended on a warning about universes: `V ℓ` is a large type
built from small indexing data, and its truth values live in `hProp (ℓ-suc ℓ)`,
one level up. The warning matters because every set-forming device the library
offers, `sett`{.Agda} first among them, accepts only **small** input: a small
index type, a small predicate. To build a set out of a property, the property's
truth value must first be brought down a universe. This chapter builds the
toolkit for exactly that, and its payoff is the part's first theorem worth
framing: separation for Δ₀ formulas costs no axiom at all.
<!--zh-->
上一章以一句宇宙警告收尾：`V ℓ` 是由小索引数据造出的大类型，其真值住在高一层的 `hProp (ℓ-suc ℓ)`。这句警告的分量在于：库提供的每一件造集装置，头一件就是 `sett`{.Agda}，都只收**小**输入：小索引类型、小谓词。要想用一条性质造出集合，先得把这条性质的真值降下一个宇宙。本章打造的正是这套工具，而它的回报是本部第一条值得裱起来的定理：Δ₀ 公式的分离不花任何公理。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Smallness {ℓ : Level} where

open import FOL.Structure using ( ZFStructure; _^_; _↾_ )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEq; invEquiv; secEq; propBiimpl→Equiv )
import Cubical.Functions.Logic as Logic
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∼_; identityPrinciple; _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module SeparationSet )

open TruthAlgebra (hPropAlgebra {ℓ-suc ℓ})
open ZFStructure 𝒮ᵥ
```

<!--en-->
## Being small
<!--zh-->
## 何谓小
<!--/-->

<!--en-->
A proposition one universe up **is small** when it is equivalent to some
proposition one universe down. The definition carries the witness, and the whole
chapter is an exercise in passing such witnesses around.
<!--zh-->
高一层的命题**是小的**，指它与某个低一层的命题等价。定义随身携带见证，而整章无非是把这种见证传来传去的一套体操。
<!--/-->

```agda
isSmall : hProp (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
isSmall P = Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
The atoms are small straight from the library. This is the local-smallness
apparatus the previous chapter glimpsed: membership has a small twin `∈ₛ`
(`∈∈ₛ`{.Agda} converts back and forth), and equality of sets compresses to the
bisimilarity `∼` through `identityPrinciple`{.Agda}.
<!--zh-->
原子的小性直接来自库。这就是上一章瞥见过的局部小性装置：成员关系有小孪生 `∈ₛ` (`∈∈ₛ`{.Agda} 双向换形)，集合相等经 `identityPrinciple`{.Agda} 压缩为双相似 `∼`。
<!--/-->

```agda
small-∈ : (a b : S) → isSmall (a ∈ˢ b)
small-∈ a b = (a ∈ₛ b) ,
  propBiimpl→Equiv (snd (a ∈ˢ b)) (snd (a ∈ₛ b))
    (∈∈ₛ {a = a} {b = b} .fst) (∈∈ₛ {a = a} {b = b} .snd)

small-≡ : (a b : S) → isSmall (a ≈ˢ b)
small-≡ a b = (a ∼ b) , invEquiv identityPrinciple
```

<!--en-->
## The connectives preserve smallness
<!--zh-->
## 联结词保小
<!--/-->

<!--en-->
Each of the six propositional operations passes smallness witnesses through; each
proof is the mechanical transport of a bi-implication. (The qualified
`Logic`{.Agda} names are the library's connectives at the *lower* level, the
codomain of the compression.)
<!--zh-->
六个命题运算逐个传递小性见证，每条证明都是双蕴含的机械搬运。(限定名 `Logic`{.Agda} 是库在**低**一层的联结词，即压缩的落点。)
<!--/-->

```agda
small⊓ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊓ Q)
small⊓ {P} {Q} (P' , eP) (Q' , eQ) = (P' Logic.⊓ Q') ,
  propBiimpl→Equiv (snd (P ⊓ Q)) (snd (P' Logic.⊓ Q'))
    (λ pq → equivFun eP (pq .fst) , equivFun eQ (pq .snd))
    (λ pq → invEq eP (pq .fst) , invEq eQ (pq .snd))

small⊔ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊔ Q)
small⊔ {P} {Q} (P' , eP) (Q' , eQ) = (P' Logic.⊔ Q') ,
  propBiimpl→Equiv (snd (P ⊔ Q)) (snd (P' Logic.⊔ Q'))
    (PT.map (Sum.map (equivFun eP) (equivFun eQ)))
    (PT.map (Sum.map (invEq eP) (invEq eQ)))

small⇒ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⇒ Q)
small⇒ {P} {Q} (P' , eP) (Q' , eQ) = (P' Logic.⇒ Q') ,
  propBiimpl→Equiv (snd (P ⇒ Q)) (snd (P' Logic.⇒ Q'))
    (λ f p' → equivFun eQ (f (invEq eP p')))
    (λ g p → invEq eQ (g (equivFun eP p)))

small¬ : {P : hProp (ℓ-suc ℓ)} → isSmall P → isSmall (¬ P)
small¬ {P} (P' , eP) = (Logic.¬ P') ,
  propBiimpl→Equiv (snd (¬ P)) (snd (Logic.¬ P'))
    (λ np p' → np (invEq eP p'))
    (λ np' p → np' (equivFun eP p))

small⊤ : isSmall ⊤
small⊤ = Logic.⊤ ,
  propBiimpl→Equiv (⊤ .snd) (snd (Logic.⊤ {ℓ}))
    (λ _ → tt*) (λ _ → tt*)

small⊥ : isSmall ⊥
small⊥ = (⊥* , isProp⊥*) ,
  propBiimpl→Equiv isProp⊥* isProp⊥* (λ ()) (λ ())
```

<!--en-->
## Bounded quantifiers preserve smallness
<!--zh-->
## 有界量词保小
<!--/-->

<!--en-->
Here is the load-bearing step, and the point where the syntax chapter's oldest
promise pays off in the currency of universes. A quantifier over all of `V ℓ`
ranges over a large type and has no reason to be small. A quantifier **bounded by
a set `a`** can instead range over the library's small member type `⟪ a ⟫`, the
index type of `a`'s family, and smallness survives. The two directions travel
along `∈-asFiber`{.Agda}, whose fibers are **untruncated** because `⟪ a ⟫↪` is an
embedding: passing from "a member of `a`" back to "an index of `⟪ a ⟫`" is a
function, not a choice.
<!--zh-->
承重的一步到了，语法章最古老的那句许诺，在此以宇宙为通货兑付。范围取全 `V ℓ` 的量词量化在大类型上，没有任何理由是小的。而**以集合 `a` 为界**的量词可以改在库的小成员类型 `⟪ a ⟫` 上量化，即 `a` 的族的索引类型，小性就此存活。往返两趟走 `∈-asFiber`{.Agda}，其纤维**不加截断**，因为 `⟪ a ⟫↪` 是嵌入：从「`a` 的成员」回到「`⟪ a ⟫` 的索引」是函数，不是选择。
<!--/-->

```agda
small-∀∈ : (a : S) {B : S → hProp (ℓ-suc ℓ)}
         → (∀ x → isSmall (B x))
         → isSmall (⋀ S (λ x → (x ∈ˢ a) ⇒ B x))
small-∀∈ a {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
  big = ⋀ S (λ x → (x ∈ˢ a) ⇒ B x)
  Qsm = Logic.∀[]-syntax (λ (m : ⟪ a ⟫) → sm (⟪ a ⟫↪ m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd f m = equivFun (sm (⟪ a ⟫↪ m) .snd)
                     (f (⟪ a ⟫↪ m) (∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)))
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
  bwd g x x∈a =
    subst (λ v → ⟨ B v ⟩) (mf .snd)
          (invEq (sm (⟪ a ⟫↪ (mf .fst)) .snd) (g (mf .fst)))
    where mf = ∈-asFiber {a = x} {b = a} x∈a

small-∃∈ : (a : S) {B : S → hProp (ℓ-suc ℓ)}
         → (∀ x → isSmall (B x))
         → isSmall (⋁ S (λ x → (x ∈ˢ a) ⊓ B x))
small-∃∈ a {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
  big = ⋁ S (λ x → (x ∈ˢ a) ⊓ B x)
  Qsm = Logic.∃[]-syntax (λ (m : ⟪ a ⟫) → sm (⟪ a ⟫↪ m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd = PT.map λ where
    (x , x∈a , bx) →
      let mf = ∈-asFiber {a = x} {b = a} x∈a
      in mf .fst ,
         equivFun (sm (⟪ a ⟫↪ (mf .fst)) .snd)
                  (subst (λ v → ⟨ B v ⟩) (sym (mf .snd)) bx)
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
  bwd = PT.map λ where
    (m , q) → ⟪ a ⟫↪ m , ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)
            , invEq (sm (⟪ a ⟫↪ m) .snd) q
```

<!--en-->
## The separation pipe
<!--zh-->
## 分离的水管
<!--/-->

<!--en-->
What smallness buys: a pointwise-small predicate can be separated. The library's
`SeparationSet`{.Agda} accepts only small predicates, and a smallness witness is
exactly the ticket in; the specification comes back in the model record's field
shape. Every separation this part performs, whatever pays for the smallness,
flows through this one pipe.
<!--zh-->
小性买到的东西：逐点小的谓词可以分离。库的 `SeparationSet`{.Agda} 只收小谓词，小性见证恰好是入场券；规格以模型 record 的字段形状交还。本部往后的每一次分离，无论小性由谁买单，都流经这一根水管。
<!--/-->

```agda
separateFromSmall : (a : S) (P : S → hProp (ℓ-suc ℓ))
                  → (∀ y → isSmall (P y))
                  → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ P y))
separateFromSmall a P sm = Sep.SEPAREE , λ y → ⇔toPath (fwd y) (bwd y)
  where
  ϕₛ : S → hProp ℓ
  ϕₛ y = sm y .fst
  module Sep = SeparationSet a ϕₛ
  fwd : ∀ y → ⟨ y ∈ˢ Sep.SEPAREE ⟩ → ⟨ (y ∈ˢ a) ⊓ P y ⟩
  fwd y y∈s = ∈∈ₛ {a = y} {b = a} .snd (Sep.separation-ax y .fst y∈ₛs .fst)
            , invEq (sm y .snd) (Sep.separation-ax y .fst y∈ₛs .snd)
    where y∈ₛs = ∈∈ₛ {a = y} {b = Sep.SEPAREE} .fst y∈s
  bwd : ∀ y → ⟨ (y ∈ˢ a) ⊓ P y ⟩ → ⟨ y ∈ˢ Sep.SEPAREE ⟩
  bwd y yp = ∈∈ₛ {a = y} {b = Sep.SEPAREE} .snd (Sep.separation-ax y .snd
               (∈∈ₛ {a = y} {b = a} .fst (yp .fst) , equivFun (sm y .snd) (yp .snd)))
```

<!--en-->
## Δ₀ formulas evaluate small
<!--zh-->
## Δ₀ 公式求值小
<!--/-->

<!--en-->
Now the graded witnesses earn a second salary. One induction over the `Δ₀`
witness shows that the witnessed formula's truth value at any environment is
small: the two atoms are the library compressions, the eight connective cases are
the closure lemmas, and the two bounded-quantifier cases consume
`small-∀∈`{.Agda} and `small-∃∈`{.Agda}. There is **no case for the unbounded
quantifiers, because the witness has no such constructors**: absence is the
classification. This is the second load-bearing induction over Δ₀ witnesses
(absoluteness was the first), and it is why the Levy hierarchy doubles as a cost
accounting: Δ₀ means *free*, in the precise sense of universe levels.
<!--zh-->
分级见证开始挣第二份薪水。对 `Δ₀` 见证做一次归纳，即知带见证的公式在任何环境下的真值都小：两个原子情形是库压缩，八个联结词情形是封闭性引理，两个有界量词情形消费 `small-∀∈`{.Agda} 与 `small-∃∈`{.Agda}。**没有无界量词的情形，因为见证压根没有那两个构造子**：缺席即分类。这是压在 Δ₀ 见证上的第二条承重归纳 (第一条是绝对性)，也是 Lévy 层级兼任成本账簿的原因：Δ₀ 意谓**免费**，在宇宙层级的精确意义上。
<!--/-->

```agda
module SemanticsV = FOL.Semantics (hPropAlgebra {ℓ-suc ℓ}) 𝒮ᵥ

module Δ₀Small {ℓc} {K : Type ℓc} (ι : K → S) where

  open SemanticsV.At ι

  Δ₀-small : ∀ {n} {φ : Formula K n} → Δ₀ φ → (γ : S ^ n) → isSmall (γ ⊨ φ)
  Δ₀-small (δ-∈ {t = t} {u}) γ = small-∈ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-≐ {t = t} {u}) γ = small-≡ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-∧ {φ = φ} {ψ} c d) γ =
    small⊓ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-∨ {φ = φ} {ψ} c d) γ =
    small⊔ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-⇒ {φ = φ} {ψ} c d) γ =
    small⇒ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-¬ {φ = φ} c) γ = small¬ {P = γ ⊨ φ} (Δ₀-small c γ)
  Δ₀-small δ-⊤ γ = small⊤
  Δ₀-small δ-⊥ γ = small⊥
  Δ₀-small (δ-∀∈ {t = t} {φ = φ} c) γ =
    small-∀∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
  Δ₀-small (δ-∃∈ {t = t} {φ = φ} c) γ =
    small-∃∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
```

<!--en-->
## The theorem: Δ₀ separation is free
<!--zh-->
## 定理：Δ₀ 分离免费
<!--/-->

<!--en-->
Compose the induction with the pipe, at the canonical constant interpretation,
and the flagship falls out: a formula carrying a Δ₀ witness can be separated
with no resizing and no axiom, `--safe` all the way down. The model chapter will
still owe *full* separation, but this theorem is the first hard evidence for a
running theme: the witnesses are portable assets, and carrying them pays.
<!--zh-->
把这条归纳与那根水管在典范常量解释处一复合，招牌定理应声落地：携带 Δ₀ 见证的公式，其分离不需任何降层、不花任何公理，一路 `--safe`。模型章仍欠**全**分离，但这条定理是一个贯穿主题的第一份硬证据：见证是可携资产，随身携带自有回报。
<!--/-->

```agda
open Δ₀Small (λ (x : S) → x)
open SemanticsV.At (λ (x : S) → x) using ( _⊨_ )

separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
separateΔ₀ a φ c = separateFromSmall a (λ y → (y ∷ []) ⊨ φ) (λ y → Δ₀-small c (y ∷ []))
```

<!--en-->
## Essentially small worlds
<!--zh-->
## 本质小的世界
<!--/-->

<!--en-->
One more register of smallness, bought not by witnesses but by **location**.
When the quantification range is itself equivalent to a small type, even the
*unbounded* quantifiers preserve smallness: quantify along the equivalence. This
does not contradict the cost accounting above, which priced quantifiers ranging
over all of `V ℓ`; here the range is the carrier of a **restricted structure**
`𝒮ᵥ ↾ M`, and smallness is exactly what the restriction buys.
<!--zh-->
小性还有一个音区，买单的不是见证而是**地段**。当量化范围自身等价于某个小类型时，连**无界**量词也保小：沿等价搬运量化即可。这与上文的成本账簿并不冲突，那里标价的是范围为全 `V ℓ` 的量词；此处的范围是**限制结构** `𝒮ᵥ ↾ M` 的载体，小性恰是「限制」二字买来的。
<!--/-->

```agda
small-⋀ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋀ A B)
small-⋀ {A} {X} e {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
  big = ⋀ A B
  Qsm = Logic.∀[]-syntax (λ (m : X) → sm (equivFun e m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd f m = equivFun (sm (equivFun e m) .snd) (f (equivFun e m))
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
  bwd g a = subst (λ v → ⟨ B v ⟩) (secEq e a)
                  (invEq (sm (equivFun e (invEq e a)) .snd) (g (invEq e a)))

small-⋁ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋁ A B)
small-⋁ {A} {X} e {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
  big = ⋁ A B
  Qsm = Logic.∃[]-syntax (λ (m : X) → sm (equivFun e m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd = PT.map λ where
    (a , ba) → invEq e a ,
               equivFun (sm (equivFun e (invEq e a)) .snd)
                        (subst (λ v → ⟨ B v ⟩) (sym (secEq e a)) ba)
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
  bwd = PT.map λ where
    (m , q) → equivFun e m , invEq (sm (equivFun e m) .snd) q
```

<!--en-->
The consequence: over an essentially small restricted structure, **every** formula
evaluates small, no witness required. The quantifier clauses walk along the
equivalence, the atoms drop back to `V`'s atomic smallness through the first
projection. This is "spoken inside a small world, everything said is small", and
it is the engine of Part 4's single construction step.
<!--zh-->
后果是：在本质小的限制结构上，**任何**公式求值皆小，无需见证。量词子句沿等价行走，原子经第一投影落回 `V` 的原子小性。这就是「在小世界里说话，说什么都小」，也是第四部那一步构造的发动机。
<!--/-->

```agda
module InnerSmall (M : S → hProp (ℓ-suc ℓ))
                  (X : Type ℓ) (e : X ≃ (Σ[ x ∈ S ] ⟨ M x ⟩))
                  {ℓc} {K : Type ℓc}
                  (ι : K → Σ[ x ∈ S ] ⟨ M x ⟩) where

  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] ⟨ M x ⟩

  𝒮M : ZFStructure (hPropAlgebra {ℓ-suc ℓ})
  𝒮M = 𝒮ᵥ ↾ M

  module SemanticsM = FOL.Semantics (hPropAlgebra {ℓ-suc ℓ}) 𝒮M
  open SemanticsM.At ι renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ ) public

  ⊨ᵐ-small : ∀ {n} (φ : Formula K n) (δ : SM ^ n) → isSmall (δ ⊨ᵐ φ)
  ⊨ᵐ-small (t ∈̇ u)  δ = small-∈ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (t ≐ u)  δ = small-≡ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (φ ∧̇ ψ)  δ =
    small⊓ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (φ ∨̇ ψ)  δ =
    small⊔ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (φ ⇒̇ ψ)  δ =
    small⇒ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (¬̇ φ)    δ = small¬ {P = δ ⊨ᵐ φ} (⊨ᵐ-small φ δ)
  ⊨ᵐ-small ⊤̇        δ = small⊤
  ⊨ᵐ-small ⊥̇        δ = small⊥
  ⊨ᵐ-small (∃̇ φ)    δ =
    small-⋁ e {B = λ xm → (xm ∷ δ) ⊨ᵐ φ} (λ xm → ⊨ᵐ-small φ (xm ∷ δ))
  ⊨ᵐ-small (∀̇ φ)    δ =
    small-⋀ e {B = λ xm → (xm ∷ δ) ⊨ᵐ φ} (λ xm → ⊨ᵐ-small φ (xm ∷ δ))
  ⊨ᵐ-small (∀̇∈ t φ) δ =
    small-⋀ e {B = λ xm → (fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)) ⇒ ((xm ∷ δ) ⊨ᵐ φ)} (λ xm →
      small⇒ {P = fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)} {Q = (xm ∷ δ) ⊨ᵐ φ}
        (small-∈ (fst xm) (fst (⟦ t ⟧ᵐ δ))) (⊨ᵐ-small φ (xm ∷ δ)))
  ⊨ᵐ-small (∃̇∈ t φ) δ =
    small-⋁ e {B = λ xm → (fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)) ⊓ ((xm ∷ δ) ⊨ᵐ φ)} (λ xm →
      small⊓ {P = fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)} {Q = (xm ∷ δ) ⊨ᵐ φ}
        (small-∈ (fst xm) (fst (⟦ t ⟧ᵐ δ))) (⊨ᵐ-small φ (xm ∷ δ)))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Smallness is equivalence to a proposition one universe down (`isSmall`{.Agda});
the atoms compress through the library, the connectives and the bounded
quantifiers pass witnesses along, and `separateFromSmall`{.Agda} is the one pipe
from small predicates to sets. The induction `Δ₀-small`{.Agda} then makes the
Levy hierarchy a cost accounting, with `separateΔ₀`{.Agda} as the free tier. What
Δ₀ cannot reach is priced in the model chapter, and the price has a name:
resizing.
<!--zh-->
小性即与低一层命题的等价 (`isSmall`{.Agda})；原子经库压缩，联结词与有界量词传递见证，`separateFromSmall`{.Agda} 是从小谓词到集合的唯一水管。归纳 `Δ₀-small`{.Agda} 让 Lévy 层级兼任成本账簿，`separateΔ₀`{.Agda} 是其中的免费档。Δ₀ 够不到的部分在模型章标价，而那个价格有名字：降层。
<!--/-->
