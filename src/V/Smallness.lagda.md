<!--en-->
# Small truth values in the cumulative hierarchy

A proposition over `V`{.Agda} is small when it is equivalent to one in the lower universe. Atomic formulas, connectives, and bounded quantifiers preserve this property, yielding Δ₀ separation without resizing and full smallness over essentially small substructures.
<!--zh-->
# 累积层级中的小真值

`V`{.Agda} 上的命题若等价于低一层宇宙中的命题，就是小的。原子公式、联结词与有界量词保持此性质，由此无需降层即可得到 Δ₀ 分离，并在本质小的子结构上得到全体公式的小性。
<!--ja-->
# 累積階層における小さな真理値

`V`{.Agda} 上の命題が一段低い宇宙の命題と同値であるとき、それを小さいと呼びます。原子論理式、結合子、有界量化子はこの性質を保存するので、リサイズなしの Δ₀ 分出と、本質的に小さな部分構造上でのすべての論理式の小ささが得られます。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Smallness {ℓ : Level} where

open import Base.Impredicativity using ( isSmall )
open import FOL.ZFStructure using ( ZFStructure; _↾_ )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEq; invEquiv; equivΠ; propBiimpl→Equiv )
import Cubical.Functions.Logic as Logic
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( Σ-cong-equiv )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∼_; identityPrinciple; _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module SeparationSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ
```

<!--en-->
## Being small

A proposition one universe up **is small** when it is equivalent to some
proposition one universe down: the definition (`isSmall`{.Agda}) was minted in
`Base.Impredicativity`, where the resizing interface asserts it of every proposition wholesale.
This chapter assumes no such thing. It **earns** instances, one atom at a time,
and the whole chapter is an exercise in passing the earned witnesses around.
<!--zh-->
## 何谓小

高一层的命题**是小的**，指它与某个低一层的命题等价：这个定义 (`isSmall`{.Agda}) 铸于基础章节，在那里，降层接口把它一揽子断言于每个命题。本章不作这种假设。它逐原子地**挣得**实例，而整章无非是把挣来的见证传来传去的一套体操。
<!--ja-->
## 小さい命題

高い宇宙の命題が低い宇宙の命題と同値であるとき、その命題は小さいといいます。階層の所属と等号はライブラリの小さな関係によって、この性質を満たします。
<!--/-->



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

Each of the six propositional operations passes smallness witnesses through; each
proof is the mechanical transport of a bi-implication. (The qualified
`Logic`{.Agda} names are the library's connectives at the *lower* level, the
codomain of the compression.)
<!--zh-->
## 联结词保小

六个命题运算逐个传递小性见证，每条证明都是双蕴含的机械搬运。(限定名 `Logic`{.Agda} 是库在**低**一层的联结词，即压缩的落点。)
<!--ja-->
## 結合子による保存

小さな命題の証人は、真、偽、連言、選言、含意、否定を通して組み合わせられます。それぞれの証明は低い宇宙で対応する結合子を作り、同値を移します。
<!--/-->



```agda
small⊓ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊓ Q)
small⊓ {P} {Q} (P' , eP) (Q' , eQ) =
  (P' Logic.⊓ Q') , Σ-cong-equiv eP (λ _ → eQ)

small⊔ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊔ Q)
small⊔ {P} {Q} (P' , eP) (Q' , eQ) =
  (P' Logic.⊔ Q') , PT.propTrunc≃ (Sum.⊎-equiv eP eQ)

small⇒ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⇒ Q)
small⇒ {P} {Q} (P' , eP) (Q' , eQ) =
  (P' Logic.⇒ Q') , equivΠ eP (λ _ → eQ)

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

Here is the load-bearing step, and the point where the syntax chapter's oldest
promise pays off in the currency of universes. A quantifier over all of `V ℓ`
ranges over a large type and has no reason to be small. A quantifier **bounded by
a set `a`** can instead range over the library's small member type `⟪ a ⟫`, the
index type of `a`'s family, and smallness survives. The two directions travel
along `∈-asFiber`{.Agda}, whose fibers are **untruncated** because `⟪ a ⟫↪` is an
embedding: passing from "a member of `a`" back to "an index of `⟪ a ⟫`" is a
function, not a choice.
<!--zh-->
## 有界量词保小

承重的一步到了，语法章最古老的那句许诺，在此以宇宙为通货兑付。范围取全 `V ℓ` 的量词量化在大类型上，没有任何理由是小的。而**以集合 `a` 为界**的量词可以改在库的小成员类型 `⟪ a ⟫` 上量化，即 `a` 的族的索引类型，小性就此存活。往返两趟走 `∈-asFiber`{.Agda}，其纤维**不加截断**，因为 `⟪ a ⟫↪` 是嵌入：从「`a` 的成员」回到「`⟪ a ⟫` 的索引」是函数，不是选择。
<!--ja-->
## 有界量化子による保存

集合で有界な量化は、その集合の小さな提示上の量化へ移せます。所属のファイバーから要素と添字を相互に移すことで、全称量化と存在量化の小ささが保存されます。
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

What smallness buys: a pointwise-small predicate can be separated. The library's
`SeparationSet`{.Agda} accepts only small predicates, and a smallness witness is
exactly the ticket in; the specification comes back in the model record's field
shape. Every separation this part performs, whatever pays for the smallness,
flows through this one pipe.
<!--zh-->
## 分离的水管

小性买到的东西：逐点小的谓词可以分离。库的 `SeparationSet`{.Agda} 只收小谓词，小性见证恰好是入场券；规格以模型 record 的字段形状交还。本部往后的每一次分离，无论小性由谁买单，都流经这一根水管。
<!--ja-->
## 小ささから分出へ

各点で小さい述語は、ライブラリの分出構成へ渡して集合にできます。`separateFromSmall`{.Agda} は小ささの証人を受け取り、モデルの分出公理と同じ形の所属仕様を返します。
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

Now the Δ₀ witnesses earn a second salary. One induction over the `Δ₀`
witness shows that the witnessed formula's truth value at any environment is
small: the two atoms are the library compressions, the eight connective cases are
the closure lemmas, and the two bounded-quantifier cases consume
`small-∀∈`{.Agda} and `small-∃∈`{.Agda}. There is **no case for the unbounded
quantifiers, because the witness has no such constructors**: absence is the
classification. This is the second load-bearing induction over Δ₀ witnesses
(absoluteness was the first), and it is why the Lévy hierarchy doubles as a cost
accounting: Δ₀ means *free*, in the precise sense of universe levels.
<!--zh-->
## Δ₀ 公式求值小

Δ₀ 见证开始挣第二份薪水。对 `Δ₀` 见证做一次归纳，即知带见证的公式在任何环境下的真值都小：两个原子情形是库压缩，八个联结词情形是封闭性引理，两个有界量词情形消费 `small-∀∈`{.Agda} 与 `small-∃∈`{.Agda}。**没有无界量词的情形，因为见证压根没有那两个构造子**：缺席即分类。这是压在 Δ₀ 见证上的第二条承重归纳 (第一条是绝对性)，也是 Lévy 层级兼任成本账簿的原因：Δ₀ 意谓**免费**，在宇宙层级的精确意义上。
<!--ja-->
## Δ₀ 論理式の評価は小さい

Δ₀ の証人に関する帰納法により、原子での小ささを結合子と有界量化子へ伝えます。非有界量化子の構成子がないため、どの環境でも評価結果は小さい命題になります。
<!--/-->



```agda
module SemanticsV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemanticsV using ( _^_ )

module Δ₀Small {ℓc} {K : Type ℓc} (ι : K → S) where

  open SemanticsV.At K ι

  Δ₀-small : ∀ {n} {φ : Formula K n} → Δ₀ φ → (γ : S ^ n) → isSmall (γ ⊨ φ)
  Δ₀-small (δ-∈ {t = t} {u}) γ = small-∈ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-≐ {t = t} {u}) γ = small-≡ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-∧ {φ = φ} {ψ} c d) γ =
    small⊓ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-∨ {φ = φ} {ψ} c d) γ =
    small⊔ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-⇒ {φ = φ} {ψ} c d) γ =
    small⇒ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small δ-⊥ γ = small⊥
  Δ₀-small (δ-∀∈ {t = t} {φ = φ} c) γ =
    small-∀∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
  Δ₀-small (δ-∃∈ {t = t} {φ = φ} c) γ =
    small-∃∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
```

<!--en-->
## The theorem: Δ₀ separation is free

Compose the induction with the pipe, at the canonical constant interpretation,
and the flagship falls out: a formula carrying a Δ₀ witness can be separated
with no resizing and no axiom, `--safe` all the way down. The model chapter will
still owe *full* separation, but this theorem is the first hard evidence for a
running theme: the Δ₀ witnesses are portable assets, and carrying them pays.
<!--zh-->
## 定理：Δ₀ 分离免费

把这条归纳与那根水管在典范常元解释处一复合，招牌定理应声落地：携带 Δ₀ 见证的公式，其分离不需任何降层、不花任何公理，一路 `--safe`。模型章仍欠**全**分离，但这条定理是一个贯穿主题的第一份硬证据：Δ₀ 见证是可携资产，随身携带自有回报。
<!--ja-->
## 定理：Δ₀ 分出に仮定は不要

`Δ₀-small`{.Agda} で得た点ごとの小ささを分出構成へ渡すと、Δ₀ 論理式による部分集合が得られます。この定理には命題リサイズも追加の公理も必要ありません。
<!--/-->



```agda
open Δ₀Small id
open SemanticsV.At S id using ( _⊨_ )

separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
separateΔ₀ a φ c = separateFromSmall a (λ y → (y ∷ []) ⊨ φ) (λ y → Δ₀-small c (y ∷ []))
```

<!--en-->
## Essentially small worlds

One more register of smallness, bought not by Δ₀ witnesses but by **location**.
When the quantification range is itself equivalent to a small type, even the
*unbounded* quantifiers preserve smallness: quantify along the equivalence. This
does not contradict the cost accounting above, which priced quantifiers ranging
over all of `V ℓ`; here the range is the carrier of a **restricted structure**
`𝒮ᵥ ↾ M`, and smallness is exactly what the restriction buys.
<!--zh-->
## 本质小的世界

小性还有一种买法，买单的不是 Δ₀ 见证而是**地段**。当量化范围自身等价于某个小类型时，连**无界**量词也保小：沿等价搬运量化即可。这与上文的成本账簿并不冲突，那里标价的是范围为全 `V ℓ` 的量词；此处的范围是**限制结构** `𝒮ᵥ ↾ M` 的载体，小性恰是「限制」二字买来的。
<!--ja-->
## 本質的に小さな世界

制限構造の台が小さな型と同値なら、非有界量化もその小さな型上へ移せます。そのため、この世界の中では Δ₀ に限らず、すべての論理式の評価が小さくなります。
<!--/-->



```agda
small-⋀ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋀ A B)
small-⋀ e sm = Logic.∀[]-syntax (λ m → sm (equivFun e m) .fst)
  , invEquiv (equivΠ e (λ m → invEquiv (sm (equivFun e m) .snd)))

small-⋁ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋁ A B)
small-⋁ e sm = Logic.∃[]-syntax (λ m → sm (equivFun e m) .fst)
  , invEquiv (PT.propTrunc≃ (Σ-cong-equiv e (λ m → invEquiv (sm (equivFun e m) .snd))))
```

<!--en-->
The consequence: over an essentially small restricted structure, **every** formula
evaluates small, no Δ₀ witness required. The quantifier clauses walk along the
equivalence, the atoms drop back to `V`'s atomic smallness through the first
projection. This is "spoken inside a small world, everything said is small", and
it is the engine of the constructible hierarchy's definability step.
<!--zh-->
后果是：在本质小的限制结构上，**任何**公式求值皆小，无需 Δ₀ 见证。量词子句沿等价行走，原子经第一投影落回 `V` 的原子小性。这就是「在小世界里说话，说什么都小」，也是可构造层级的可定义性步骤的发动机。
<!--/-->

```agda
module InnerSmall (M : S → hProp (ℓ-suc ℓ))
                  (X : Type ℓ) (e : X ≃ (Σ[ x ∈ S ] (x ∈ᶜ M)))
                  {ℓc} {K : Type ℓc}
                  (ι : K → Σ[ x ∈ S ] (x ∈ᶜ M)) where

  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] (x ∈ᶜ M)

  𝒮M : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
  𝒮M = 𝒮ᵥ ↾ M

  module SemanticsM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮M
  open SemanticsM.At K ι renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ ) public

  ⊨ᵐ-small : ∀ {n} (φ : Formula K n) (δ : SM ^ n) → isSmall (δ ⊨ᵐ φ)
  ⊨ᵐ-small (t ∈̇ u)  δ = small-∈ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (t ≐ u)  δ = small-≡ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (φ ∧̇ ψ)  δ =
    small⊓ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (φ ∨̇ ψ)  δ =
    small⊔ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (φ ⇒̇ ψ)  δ =
    small⇒ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
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

Smallness is equivalence to a proposition one universe down (`isSmall`{.Agda});
the atoms compress through the library, the connectives and the bounded
quantifiers pass smallness witnesses along, and `separateFromSmall`{.Agda} is the one pipe
from small predicates to sets. The induction `Δ₀-small`{.Agda} then makes the
Lévy hierarchy a cost accounting, with `separateΔ₀`{.Agda} as the free tier. What
Δ₀ cannot reach is priced in the model chapter, and the price has a name:
resizing.
<!--zh-->
## 小结

小性即与低一层命题的等价 (`isSmall`{.Agda})；原子经库压缩，联结词与有界量词传递小性见证，`separateFromSmall`{.Agda} 是从小谓词到集合的唯一水管。归纳 `Δ₀-small`{.Agda} 让 Lévy 层级兼任成本账簿，`separateΔ₀`{.Agda} 是其中的免费档。Δ₀ 够不到的部分在模型章标价，而那个价格有名字：降层。
<!--ja-->
## まとめ

原子、結合子、有界量化子について小ささが閉じるため、Δ₀ の評価と分出は追加の仮定なしに構成できます。本質的に小さな制限構造では同じ結論がすべての論理式へ広がります。
<!--/-->
