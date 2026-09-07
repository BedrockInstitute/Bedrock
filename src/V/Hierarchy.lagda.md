<!--en-->
# The cumulative hierarchy

The higher inductive type `V`{.Agda} presents sets as images of small families and builds extensional equality into their paths. This chapter equips it with the set-theoretic structure `𝒮ᵥ`{.Agda}, proves regularity, and derives recursion along membership.
<!--zh-->
# 累积层级

高阶归纳类型 `V`{.Agda} 把集合呈现为小族的像，并把外延相等构造进路径。本章赋予它集合论结构 `𝒮ᵥ`{.Agda}，证明正则性，并导出沿隶属关系的递归。
<!--ja-->
# 累積階層

高階帰納型 `V`{.Agda} は集合を小さな族の像として提示し、外延的等しさをパスへ組み込みます。本章では集合論的構造 `𝒮ᵥ`{.Agda} を与え、正則性を示し、所属関係に沿う再帰を導きます。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Hierarchy {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import Cubical.Induction.WellFounded as WellFoundedInduction
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; isPropAcc; wf→x≮x )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; setIsSet; _∈_; elimProp )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( sett )  -- lint-agda: keep (prose references link through this import)
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality )
```

<!--en-->
## The higher inductive type

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
## 高阶归纳类型

生成性想法是集合论里最古老的那句话：集合无非其成员之汇集。构造子 `sett`{.Agda} 取一个小索引类型 `X : Type ℓ` 与一个族 `ix : X → V ℓ`，形成以 `ix` 的像为成员的集合。成员关系于是就是问原像，且仅仅是问：`y ∈ sett X ix` 是「存在 `i : X` 使 `ix i ≡ y`」的截断。像相同的两个族理应给出**同一个**集合，而在高阶归纳类型里，这句「理应」本身就是构造子：一个路径构造子 (库中名为 `seteq`) 让外延相等**按构造**成立，`setIsSet`{.Agda} 再把整个类型截断为 h-集。库文件头自陈了这笔买卖的成色：一个「ZF 减幂集」的模型。缺席的幂集与两条模式公理，正是本部余下各章必须补上的。
<!--ja-->
## 高階帰納型

`sett`{.Agda} は小さな型で添字付けられた族の像を集合にします。所属はその原像の命題的切り詰めであり、パス構成子が外延性を、集合切り詰めが h-集合性を与えます。
<!--/-->



<!--en-->
## The structure

The interface fit is exact: the carrier is an h-set, membership lands in
`hProp`{.Agda}, and equality is simply the path type, packaged as a proposition
by set-hood, the promise the structure chapter made for the propositional side,
kept. Four fields, no adapter code, and every tool of
Parts 1 and 2, syntax, satisfaction, representations, Levy witnesses, absoluteness,
the model record itself, is available on `𝒮ᵥ` at once. The subscript is a plain
`v`, for the hierarchy.
<!--zh-->
## 结构

接口严丝合缝：载体是 h-集，成员关系落在 `hProp`{.Agda}，等词径直取路径类型，由集合性打包成命题，结构章对命题侧许下的诺言在此兑现。四个字段，零适配代码，第一、二部的全部工具，语法、满足、表示、Lévy 见证、绝对性，连同模型 record 本身，即刻在 `𝒮ᵥ` 上可用。下标就是普通的 `v`，指层级。
<!--ja-->
## 構造

台を `V ℓ`、等号をパス、所属を階層の所属関係とすると、真理値代数上の構造 `𝒮ᵥ`{.Agda} が得られます。これにより論理式の意味論とモデルの定義を階層へ適用できます。
<!--/-->



```agda
𝒮ᵥ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
𝒮ᵥ = record
  { S      = V ℓ
  ; isSetS = setIsSet
  ; _≈ˢ_   = λ x y → (x ≡ y) , setIsSet x y
  ; _∈ˢ_   = _∈_ }

open hPropStructure 𝒮ᵥ
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

The model record opens with extensionality and regularity, and the hierarchy
supplies both without spending anything. Extensionality is the path constructor
cashing out: the record's field wants "pointwise equal membership implies equal",
the library's `extensionality`{.Agda} wants mutual inclusion, and `subst`{.Agda}
carries membership along the pointwise paths to convert one into the other.
<!--zh-->
## 免费入账的两个字段

模型 record 以外延与正则开篇，而层级把两者都白送。外延公理是路径构造子的兑现：字段要「逐点成员相等则相等」，库的 `extensionality`{.Agda} 要双向包含，`subst`{.Agda} 沿逐点路径搬运成员资格，一转即合。
<!--ja-->
## 構成から得られる二つの公理

外延性は階層のパス構成から得られ、正則性は所属関係の整礎性から得られます。したがってモデル構造体の最初の二つの欄は追加の仮定なしで満たされます。
<!--/-->



```agda
extensionalV : {a b : V ℓ} → ((x : V ℓ) → (x ∈ a) ≡ (x ∈ b)) → a ≡ b
extensionalV {a} {b} h = extensionality a b
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
regularityV : WellFounded _∈ᵗ_
regularityV = elimProp (λ s → isPropAcc s)
  (λ X ix rec → acc (λ y y∈ →
    PT.rec (isPropAcc y)
           (λ { (i , p) → subst (Acc _∈ᵗ_) p (rec i) })
           y∈))
```

<!--en-->
Its first dividend, one line: no set belongs to itself, since a self-member
would be an infinite descent. The later chapters reach for this constantly.
<!--zh-->
它的第一笔红利，一行：没有集合属于自身，因为自属会构成一条无穷下降。后文诸章会不断取用。
<!--/-->

```agda
∈-irrefl : (A : S) → ⟨ A ∈ˢ A ⟩ → Empty.⊥
∈-irrefl A = wf→x≮x regularityV {x = A}
```

<!--en-->
## Recursion on membership

Regularity pays its first dividend at once. A well-founded relation supports
recursion, so the library's well-founded induction instantiates on membership:
to define something for every set, it suffices to define it for `x` given its
values on the members of `x`, into an **arbitrary** type family, with the
recursion equation holding propositionally. This is transfinite recursion with
no ordinals in sight, and the constructible-universe development builds its universe with it.
<!--zh-->
## 沿成员关系的递归

正则性立刻付出第一笔红利。良基关系支持递归，于是库的良基归纳在成员关系上实例化：要对每个集合定义某物，只需在给定 `x` 各成员处取值的前提下给出 `x` 处的值，落点是**任意**类型族，递归方程命题级成立。这是不见序数的超穷递归，可构造宇宙的开发就用它构造自己的宇宙。
<!--ja-->
## 所属関係上の再帰

所属関係の整礎性により、各集合での値をその要素での値から定められます。`∈-induction`{.Agda} とその計算法則は、序数を介さずにこの再帰原理を提供します。
<!--/-->



```agda
∈-induction : ∀ {ℓ'} {P : V ℓ → Type ℓ'}
            → (∀ x → (∀ y → y ∈ᵗ x → P y) → P x)
            → ∀ x → P x
∈-induction = WellFoundedInduction.WFI.induction regularityV

∈-induction-compute : ∀ {ℓ'} {P : V ℓ → Type ℓ'}
  (e : ∀ x → (∀ y → y ∈ᵗ x → P y) → P x) (x : V ℓ)
  → ∈-induction e x ≡ e x (λ y _ → ∈-induction e y)
∈-induction-compute = WellFoundedInduction.WFI.induction-compute regularityV
```

<!--en-->
## Recap

The cumulative hierarchy arrives from the library as a higher inductive type:
sets are images of small families, extensional equality is a constructor, and the
whole type is an h-set. `𝒮ᵥ`{.Agda} plugs it into the framework, and
extensionality (`extensionalV`{.Agda}) and regularity (`regularityV`{.Agda}) are
already banked. Everything still owed lives one universe down: the next chapter
builds the smallness toolkit that pays for it.
<!--zh-->
## 小结

累积层级以高阶归纳类型的身份从库中到来：集合是小族的像，外延相等是构造子，整个类型是 h-集。`𝒮ᵥ`{.Agda} 把它插进框架，外延 (`extensionalV`{.Agda}) 与正则 (`regularityV`{.Agda}) 已然入账。尚欠的一切都住在低一层宇宙里：下一章打造为它付账的小性工具链。
<!--ja-->
## まとめ

累積階層は小さな族の像からなる高階帰納型です。`𝒮ᵥ`{.Agda} はそれを集合論的構造として扱い、外延性、正則性、所属関係上の再帰を後続の章へ提供します。
<!--/-->
