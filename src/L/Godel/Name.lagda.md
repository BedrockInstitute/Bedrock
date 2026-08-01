# Names, as terms

<!--en-->
The step of the choice construction consumes names: for each stage, a type that
denotes the members of the next stage, carries a strict well-order, and yields
a least name for every denoted member. The route through internalized
satisfaction built that type from formulas, and the building was the bulk of
two chapters: parameters had to leave the syntax, and the order had to open a
limit construction every time two codes were compared.

This chapter delivers the same interface from the terms. A name is an arity-one
term over the members of the stage, exactly what the tower already quantifies;
it denotes the set of values of its evaluation, and completeness is the banked
equivalence of the terms chapter, spent as one transport. The order is bought
generically: a term is pictured as a finite labelled tree, the alphabet of
labels is assembled by the well-order combinators, the trees are ordered
shortlex, and the name order is the tree order pulled back along the picture.
The only fact the pull-back demands is that the picture is injective, and that
is not a case matrix: the picture has a left inverse, and a map with a left
inverse is injective for free.
<!--zh-->
选择构造的步进消费名字：对每个阶段，要有一个类型，指称下一个阶段的成员，携带一个严格良序，并为每个被指称的成员交出一个最小的名字。经由内化满足的路线用公式造出了那个类型，而造它是两章的主体：参数必须离开语法，而序在每次比较两个码时都要撬开一个极限构造。

本章从诸项交付同一接口。名字就是阶段成员上的元数一的项，恰是塔已经在量化的那种东西；它指称其求值的取值之集，而完备性是项那一章已入账的等价，一次搬运即花掉。序则是泛型地买来的：把项画成一棵有穷带标签树，标签字母表由良序组合子组装，树按 shortlex 排序，名字的序就是树的序沿这幅画拉回。拉回唯一索要的事实是这幅画是单射，而那不是一张情形矩阵：这幅画有左逆，而有左逆的映射免费单射。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Godel.Name {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒟ₒ-inv )
open import L.Godel.Operations {ℓ} using ( values )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK
        ; shiftK; ⟦_⟧ᴷ; module WithLEM )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf
        ; natSWO; unitSWO; sumSWO; prodSWO; pullSWO )
open import L.WellOrder.Tree {ℓ} using ( Tree; node; module TreeOrder )

open import Cubical.Data.FinData using ( toℕ; ¬Fin0 )
open import Cubical.Data.List using ( []; _∷_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## The names, and completeness

The interface takes membership of the definable powerset as the completeness
hypothesis, and the terms chapter has already identified the definable powerset
with the values of the arity-one terms. So a name is such a term, denotation is
evaluation followed by `values`{.Agda}, and completeness is the identification
transported backwards: membership on either side is definitionally the
truncated fiber the statement asks for, so nothing remains to prove. The one
seal on the way is that the tower keeps `𝒟ₒ`{.Agda} opaque, and
`𝒟ₒ-inv`{.Agda} is its sanctioned opening.
<!--zh-->
## 诸名字，与完备性

接口以可定义幂集的成员性为完备性的前提，而项那一章已把可定义幂集与元数一诸项的取值等同。于是名字就是这样一个项，指称就是求值后接 `values`{.Agda}，完备性就是那次等同向后搬运：两侧的成员性按定义都是陈述所要的截断纤维，无事可证。路上唯一的封印是塔把 `𝒟ₒ`{.Agda} 保持 opaque，而 `𝒟ₒ-inv`{.Agda} 是它获准的开封。
<!--/-->

```agda
module Naming (A : S) (w : SWO ⟪ A ⟫) where
  Name : Type ℓ
  Name = KT ⟪ A ⟫ 1

  denote : Name → S
  denote t = values (⟦_⟧ᴷ A t)

  private
    module TW = WithLEM A lem

  names-complete : (x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
                 → ∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁
  names-complete x h =
    subst (λ z → ⟨ x ∈ˢ z ⟩) (sym TW.termDef≡Def) (𝒟ₒ-inv A x h)
```

<!--en-->
## The picture

Each constructor contributes one node. The label carries the constructor's tag,
the selector indices when there are any, read off as numbers, and the parameter
when there is one; the children are the pictures of the subterms. The labels
carry no arities: the comparison only ever holds two terms of the same arity
side by side, and the subterm arities then agree position by position.
<!--zh-->
## 那幅画

每个构造子贡献一个节点。标签携带构造子的标记、有选择子指标时读成数字的指标、有参数时的那个参数；孩子是子项的画。标签不携带元数：比较从来只把两个同元数的项并排，而此时子项的元数逐位置一致。
<!--/-->

```agda
  private
    Lab : Type ℓ
    Lab = ℕ × ℕ × ℕ × (Unit* {ℓ} ⊎ ⟪ A ⟫)

    toTree : {n : ℕ} → KT ⟪ A ⟫ n → Tree Lab
    toTree allK            = node (0 , 0 , 0 , inl tt*) []
    toTree (selMemK i j)   = node (1 , toℕ i , toℕ j , inl tt*) []
    toTree (selEqK i j)    = node (2 , toℕ i , toℕ j , inl tt*) []
    toTree (selEqConK i a) = node (3 , toℕ i , 0 , inr a) []
    toTree (interK s t)    = node (4 , 0 , 0 , inl tt*) (toTree s ∷ toTree t ∷ [])
    toTree (unionK s t)    = node (5 , 0 , 0 , inl tt*) (toTree s ∷ toTree t ∷ [])
    toTree (complK t)      = node (6 , 0 , 0 , inl tt*) (toTree t ∷ [])
    toTree (shiftK t)      = node (7 , 0 , 0 , inl tt*) (toTree t ∷ [])
```

<!--en-->
## The left inverse

Injectivity is proved by exhibiting a left inverse, term by term. Reading a
label's numbers back as selector indices needs a conversion from numbers to
`Fin`{.Agda} that never fails, so the conversion clamps: on the image of
`toℕ`{.Agda} it is exact, and that is the only place the left inverse is
evaluated. Off the image the reading returns a harmless default, and coverage
is bought by one catch-all clause. The clauses that do inspect the arity are
quarantined in their own helpers, so that the reading itself never splits on
it: a round trip at a neutral arity then still computes, constructor by
constructor.
<!--zh-->
## 左逆

单射性靠逐项给出左逆来证。把标签上的数字读回选择子指标，需要一个从数字到 `Fin`{.Agda} 的永不失败的转换，于是转换取钳制：在 `toℕ`{.Agda} 的像上它精确，而左逆只在那里被求值。像之外，读取返回无害的缺省值，覆盖由一条兜底从句买单。确需检视元数的从句被隔离进各自的辅助函数，使读取本身从不按元数分裂：中立元数下的一次往返仍逐构造子计算。
<!--/-->

```agda
    mkFin : {n : ℕ} → ℕ → Fin (suc n)
    mkFin zero            = zero
    mkFin {zero}  (suc k) = zero
    mkFin {suc n} (suc k) = suc (mkFin k)

    mkFin-toℕ : {n : ℕ} (i : Fin (suc n)) → mkFin (toℕ i) ≡ i
    mkFin-toℕ zero            = refl
    mkFin-toℕ {zero}  (suc i) = Empty.rec (¬Fin0 i)
    mkFin-toℕ {suc n} (suc i) = cong suc (mkFin-toℕ i)

    selM : (n : ℕ) → ℕ → ℕ → KT ⟪ A ⟫ n
    selM zero    i j = allK
    selM (suc m) i j = selMemK (mkFin i) (mkFin j)

    selE : (n : ℕ) → ℕ → ℕ → KT ⟪ A ⟫ n
    selE zero    i j = allK
    selE (suc m) i j = selEqK (mkFin i) (mkFin j)

    selC : (n : ℕ) → ℕ → Unit* {ℓ} ⊎ ⟪ A ⟫ → KT ⟪ A ⟫ n
    selC zero    i p       = allK
    selC (suc m) i (inl u) = allK
    selC (suc m) i (inr a) = selEqConK (mkFin i) a

    fromTree : (n : ℕ) → Tree Lab → KT ⟪ A ⟫ n
    fromTree n (node (0 , _ , _ , _) _) = allK
    fromTree n (node (1 , i , j , _) _) = selM n i j
    fromTree n (node (2 , i , j , _) _) = selE n i j
    fromTree n (node (3 , i , _ , p) _) = selC n i p
    fromTree n (node (4 , _ , _ , _) (c₁ ∷ c₂ ∷ [])) =
      interK (fromTree n c₁) (fromTree n c₂)
    fromTree n (node (5 , _ , _ , _) (c₁ ∷ c₂ ∷ [])) =
      unionK (fromTree n c₁) (fromTree n c₂)
    fromTree n (node (6 , _ , _ , _) (c ∷ [])) = complK (fromTree n c)
    fromTree n (node (7 , _ , _ , _) (c ∷ [])) = shiftK (fromTree (suc n) c)
    fromTree n t = allK

    retractK : {n : ℕ} (t : KT ⟪ A ⟫ n) → fromTree n (toTree t) ≡ t
    retractK allK = refl
    retractK {zero}  (selMemK i j)   = Empty.rec (¬Fin0 i)
    retractK {suc m} (selMemK i j)   = cong₂ selMemK (mkFin-toℕ i) (mkFin-toℕ j)
    retractK {zero}  (selEqK i j)    = Empty.rec (¬Fin0 i)
    retractK {suc m} (selEqK i j)    = cong₂ selEqK (mkFin-toℕ i) (mkFin-toℕ j)
    retractK {zero}  (selEqConK i a) = Empty.rec (¬Fin0 i)
    retractK {suc m} (selEqConK i a) = cong (λ z → selEqConK z a) (mkFin-toℕ i)
    retractK (interK s t) = cong₂ interK (retractK s) (retractK t)
    retractK (unionK s t) = cong₂ unionK (retractK s) (retractK t)
    retractK (complK t)   = cong complK (retractK t)
    retractK (shiftK t)   = cong shiftK (retractK t)

    toTree-inj : (s t : KT ⟪ A ⟫ 1) → toTree s ≡ toTree t → s ≡ t
    toTree-inj s t q = sym (retractK s) ∙ cong (fromTree 1) q ∙ retractK t
```

<!--en-->
## The order

The alphabet is three numbers and an optional member of the stage, ordered by
lexicographic products of the ground order on numbers with the given stage
order placed after a point; the trees over it are ordered shortlex by the
previous chapter; and the names are ordered by pulling the tree order back
along the picture. Each layer is one appeal to the kit, and the pull-back is
where the left inverse is spent.
<!--zh-->
## 序

字母表是三个数字加一个可选的阶段成员，以数字地面序与「单点之后放置的给定阶段序」的字典积排序；其上的树由上一章按 shortlex 排序；名字则沿那幅画把树的序拉回。每一层都是对配件的一次调用，而拉回正是左逆被花掉的地方。
<!--/-->

```agda
  private
    labSWO : SWO Lab
    labSWO = prodSWO natSWO (prodSWO natSWO (prodSWO natSWO (sumSWO unitSWO w)))

    module TO = TreeOrder labSWO

  nameOrder : SWO Name
  nameOrder = pullSWO TO.treeSWO toTree toTree-inj

  _≺ₙ_ : Name → Name → Type (ℓ-suc ℓ)
  _≺ₙ_ = SWO._<∙_ nameOrder
```

<!--en-->
## The bundle, and the least name

The bundle is the interface the choosing device takes, and the least-name
search is the well-order chapter's search applied to it. The exported names
match the internalized route's chapter, member for member, which is what lets
the step chapter change routes by re-pointing one import.
<!--zh-->
## 束，与最小的名字

这个束就是选取装置取用的接口，而最小名字的搜索就是良序那一章的搜索施于其上。导出的名字与内化路线那一章逐一对应，这正是使步进章只改一个导入即可换路的原因。
<!--/-->

```agda
  leastName : (P : Name → hProp (ℓ-suc ℓ))
            → ∥ Σ[ a ∈ Name ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ Name ] IsLeast nameOrder P a
  leastName = leastOf nameOrder lem
```

<!--en-->
## Recap

A `Name`{.Agda} is an arity-one term; `denote`{.Agda} evaluates it and takes
values; `names-complete`{.Agda} spends the terms chapter's identification as
one transport. The order is assembled, not invented: combinators for the
alphabet, shortlex for the trees, and a pull-back along an injective picture
whose injectivity is a left inverse rather than a discrimination matrix.
`leastName`{.Agda} closes the interface, and the step chapter can consume it in
place of the internalized one.
<!--zh-->
## 小结

`Name`{.Agda} 是元数一的项；`denote`{.Agda} 对它求值并取值；`names-complete`{.Agda} 把项那一章的等同当作一次搬运花掉。序是组装而非发明的：字母表用组合子，树用 shortlex，再沿一幅单射的画拉回，其单射性是一个左逆、而非一张判别矩阵。`leastName`{.Agda} 合上接口，步进章可以用它顶替内化的那一个。
<!--/-->
