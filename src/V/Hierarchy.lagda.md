# The cumulative hierarchy

<!--en-->
Part 3 opens, and the tone changes. So far every model has been hypothetical:
`isZFModel`{.Agda} is a specification, and nothing yet inhabits it. This part
exhibits the inhabitant, and the universe it lives on is not built by this book at
all: the cubical library ships the **cumulative hierarchy** `V`{.Agda} as a higher
inductive type, following the HoTT book. This chapter introduces that type, plugs
it into the framework as a structure, and banks the first two fields of the record
for free.
<!--zh-->
第三部开幕，语气随之一变。至此的模型都是假设性的：`isZFModel`{.Agda} 是一份规格书，尚无居民。本部就来交出居民，而它栖身的宇宙甚至不是本书亲手所造：cubical 库自带**累积层级** `V`{.Agda}，一个沿 HoTT book 构造的高阶归纳类型。本章介绍这个类型，把它作为结构插进框架，并免费入账 record 的头两个字段。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module V.Hierarchy where

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; pathStructure; _∈ᵗ_ )

import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Induction.WellFounded as WellFoundedInduction
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; isPropAcc )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; setIsSet; _∈_; elimProp )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( sett )  -- lint-agda: keep (prose references link through this import)
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality )
```

<!--en-->
## The higher inductive type
<!--zh-->
## 高阶归纳类型
<!--/-->

<!--en-->
The generating idea is the oldest one in set theory: a set is no more than the
collection of its members. The constructor `sett`{.Agda} takes a small index type
`X : Type ℓ` and a family `ix : X → V ℓ`, and forms the set whose members are the
image of `ix`. Membership accordingly asks for a preimage, merely:
`y ∈ sett X ix` is the truncation of "some `i : X` with `ix i ≡ y`". Two families
with the same image should give the *same* set, and in a higher inductive type
that "should" is a constructor: a path constructor (the library calls it
`seteq`) makes extensional equality hold **by construction**, and `setIsSet`{.Agda}
truncates the whole type to an h-set. The library's own header describes what this
buys: a model of "ZF − power set". The missing power set, and the two schemas,
are exactly what the rest of this part must supply.
<!--zh-->
生成性想法是集合论里最古老的那句话：集合无非其成员之汇集。构造子 `sett`{.Agda} 取一个小索引类型 `X : Type ℓ` 与一个族 `ix : X → V ℓ`，形成以 `ix` 的像为成员的集合。成员关系于是就是问原像，且仅仅是问：`y ∈ sett X ix` 是「存在 `i : X` 使 `ix i ≡ y`」的截断。像相同的两个族理应给出**同一个**集合，而在高阶归纳类型里，这句「理应」本身就是构造子：一个路径构造子 (库中名为 `seteq`) 让外延相等**按构造**成立，`setIsSet`{.Agda} 再把整个类型截断为 h-集。库文件头自陈了这笔买卖的成色：一个「ZF 减幂集」的模型。缺席的幂集与两条模式公理，正是本部余下各章必须补上的。
<!--/-->

<!--en-->
## The structure, in one line
<!--zh-->
## 结构，一行
<!--/-->

<!--en-->
The interface fit is exact: the carrier is an h-set, membership lands in
`hProp`{.Agda}, and equality can be taken to be the path type, which is what
`pathStructure`{.Agda} was made for. One line, no adapter code, and every tool of
Parts 1 and 2, syntax, satisfaction, representations, certificates, absoluteness,
the model record itself, is available on `𝒮ᵥ` at once. The subscript is a plain
`v`, for the hierarchy.
<!--zh-->
接口严丝合缝：载体是 h-集，成员关系落在 `hProp`{.Agda}，等词可取路径类型，而这正是 `pathStructure`{.Agda} 的用武之地。一行，零适配代码，第一、二部的全部工具，语法、满足、表示、证书、绝对性，连同模型 record 本身，即刻在 `𝒮ᵥ` 上可用。下标就是普通的 `v`，指层级。
<!--/-->

```agda
𝒮ᵥ : ∀ {ℓ} → ZFStructure (hPropAlgebra {ℓ-suc ℓ})
𝒮ᵥ {ℓ} = pathStructure (V ℓ) setIsSet _∈_
```

<!--en-->
One reading of the levels, worth fixing early because the next chapter revolves
around it: the carrier `V ℓ` lives in `Type (ℓ-suc ℓ)`, one universe above its
index types, and truth values live in `hProp (ℓ-suc ℓ)` alongside it. The
hierarchy is a *large* type built from *small* indexing data.
<!--zh-->
先把层级的读法钉下，因为下一章整章围着它转：载体 `V ℓ` 住在 `Type (ℓ-suc ℓ)`，比它的索引类型高一个宇宙，真值也随之住在 `hProp (ℓ-suc ℓ)`。层级是由**小**索引数据造出的**大**类型。
<!--/-->

<!--en-->
## Two fields banked for free
<!--zh-->
## 免费入账的两个字段
<!--/-->

<!--en-->
The model record opens with extensionality and regularity, and the hierarchy
supplies both without spending anything. Extensionality is the path constructor
cashing out: the record's field wants "pointwise equal membership implies equal",
the library's `extensionality`{.Agda} wants mutual inclusion, and `subst`{.Agda}
carries membership along the pointwise paths to convert one into the other.
<!--zh-->
模型 record 以外延与正则开篇，而层级把两者都白送。外延公理是路径构造子的兑现：字段要「逐点成员相等则相等」，库的 `extensionality`{.Agda} 要双向包含，`subst`{.Agda} 沿逐点路径搬运成员资格，一转即合。
<!--/-->

```agda
extensionalV : ∀ {ℓ} {a b : V ℓ} → ((x : V ℓ) → (x ∈ a) ≡ (x ∈ b)) → a ≡ b
extensionalV {ℓ} {a} {b} h = extensionality a b
  ( (λ x x∈ₛa → ∈∈ₛ {a = x} {b = b} .fst
      (subst ⟨_⟩ (h x) (∈∈ₛ {a = x} {b = a} .snd x∈ₛa)))
  , (λ x x∈ₛb → ∈∈ₛ {a = x} {b = a} .fst
      (subst ⟨_⟩ (sym (h x)) (∈∈ₛ {a = x} {b = b} .snd x∈ₛb))) )
```

<!--en-->
(The `∈ₛ` appearing through `∈∈ₛ`{.Agda} is the library's *small* membership; the
next chapter dwells on it. Here it is only glue.)

Regularity asks that membership be well-founded, and the proof is four lines with
no axiom in sight. Accessibility is a proposition (`isPropAcc`{.Agda}), so
`elimProp`{.Agda} eliminates the HIT straight into it: the members of
`sett X ix` are merely hit by `ix`, and accessibility, being propositional,
transports along the connecting path from the inductive hypothesis. The path
constructors impose no obligations at all.
<!--zh-->
(经 `∈∈ₛ`{.Agda} 现身的 `∈ₛ` 是库的**小**成员关系，下一章将细说；此处它只是胶水。)

正则公理要求成员关系良基，证明四行，全程不见公理。可及性是命题 (`isPropAcc`{.Agda})，于是 `elimProp`{.Agda} 把 HIT 直接消去到它上面：`sett X ix` 的成员仅仅被 `ix` 截断地命中，而可及性既是命题，便沿连接路径从归纳假设搬运过来。路径构造子不产生任何义务。
<!--/-->

```agda
regularityV : ∀ {ℓ} → WellFounded (_∈ᵗ_ (𝒮ᵥ {ℓ}))
regularityV {ℓ} = elimProp (λ s → isPropAcc s)
  (λ X ix rec → acc (λ y y∈ →
    PT.rec (isPropAcc y)
           (λ { (i , p) → subst (Acc (_∈ᵗ_ (𝒮ᵥ {ℓ}))) p (rec i) })
           y∈))
```

<!--en-->
## Recursion on membership
<!--zh-->
## 沿成员关系的递归
<!--/-->

<!--en-->
Regularity pays its first dividend at once. A well-founded relation supports
recursion, so the library's well-founded induction instantiates on membership:
to define something for every set, it suffices to define it for `x` given its
values on the members of `x`, into an **arbitrary** type family, with the
recursion equation holding propositionally. This is transfinite recursion with
no ordinals in sight, and Part 4 builds its universe with it.
<!--zh-->
正则性立刻付出第一笔红利。良基关系支持递归，于是库的良基归纳在成员关系上实例化：要对每个集合定义某物，只需在给定 `x` 各成员处取值的前提下给出 `x` 处的值，落点是**任意**类型族，递归方程命题级成立。这是不见序数的超穷递归，第四部就用它构造自己的宇宙。
<!--/-->

```agda
∈-induction : ∀ {ℓ ℓ'} {P : V ℓ → Type ℓ'}
            → (∀ x → (∀ y → _∈ᵗ_ (𝒮ᵥ {ℓ}) y x → P y) → P x)
            → ∀ x → P x
∈-induction {ℓ} = WellFoundedInduction.WFI.induction (regularityV {ℓ})

∈-induction-compute : ∀ {ℓ ℓ'} {P : V ℓ → Type ℓ'}
  (e : ∀ x → (∀ y → _∈ᵗ_ (𝒮ᵥ {ℓ}) y x → P y) → P x) (x : V ℓ)
  → ∈-induction e x ≡ e x (λ y _ → ∈-induction e y)
∈-induction-compute {ℓ} = WellFoundedInduction.WFI.induction-compute (regularityV {ℓ})
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The cumulative hierarchy arrives from the library as a higher inductive type:
sets are images of small families, extensional equality is a constructor, and the
whole type is an h-set. `𝒮ᵥ`{.Agda} plugs it into the framework in one line, and
extensionality (`extensionalV`{.Agda}) and regularity (`regularityV`{.Agda}) are
already banked. Everything still owed lives one universe down: the next chapter
builds the smallness toolkit that pays for it.
<!--zh-->
累积层级以高阶归纳类型的身份从库中到来：集合是小族的像，外延相等是构造子，整个类型是 h-集。`𝒮ᵥ`{.Agda} 一行把它插进框架，外延 (`extensionalV`{.Agda}) 与正则 (`regularityV`{.Agda}) 已然入账。尚欠的一切都住在低一层宇宙里：下一章打造为它付账的小性工具链。
<!--/-->
