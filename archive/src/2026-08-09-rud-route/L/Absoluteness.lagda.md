# Reading a hierarchy formula inside L

<!--en-->
The coding chapters wrote their readers about the hierarchy: a formula whose
constants are sets of `V`, evaluated where the quantifiers range over all of `V`.
The chapters that consume them from here on speak about `L` instead: formulas
whose constants are elements of the model, evaluated where the quantifiers range
over `L` only. The two are different languages, and something has to carry a
reader from one to the other.

Two facts do it, and both are already proved. Relabelling replaces each constant
of a formula by an element of the model, provided each constant *is* one; that is
the bounded-formula machinery, used here with the bound "constructible" rather
than "inside a stage". And Δ₀ absoluteness says that a bounded formula means the
same thing inside a transitive class as outside it, which is what makes the
replacement harmless.

So a Δ₀ reader whose constants are constructible transfers, and the transfer is
one chain of four steps with no induction of its own. Every later chapter that
wants to say, in the object language of `L`, that one set is the pair of two
others, or that a code has such-and-such a shape, gets to say it by quoting a
reader and applying this.
<!--zh-->
编码诸章把读式写成关于层级的：常元是 `V` 的集合，求值时量词遍历整个 `V`。而此后消费它们的诸章谈论的是 `L`：常元是模型的元素，求值时量词只遍历 `L`。这是两门不同的语言，总得有东西把一条读式从其中一门运到另一门。

两件事就够，且两件都已证毕。常量改名把公式的每个常元换成模型的元素，只要那个常元**确实是**一个；那是有界公式那套机器，此处所用的界是「可构造」而非「落在某阶段内」。而 Δ₀ 绝对性说：有界公式在传递类之内与之外含义相同，正是这一点使那次替换无害。

于是常元可构造的 Δ₀ 读式可以运过去，而这次搬运是一条四步的链，自身不含任何归纳。此后每一章想在 `L` 的对象语言里说「这个集合是那两个的对」，或「这个码具有某种形状」，都只需引用一条读式，再施以本章。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Absoluteness {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )

open import Cubical.Data.Vec using ( map )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The bound is constructibility
<!--zh-->
## 界就是可构造性
<!--/-->

<!--en-->
The relabelling is instantiated once. A constant of the hierarchy is admissible
when it is constructible; the element of the model it becomes is that constant
paired with its certificate; and the round trip is `refl`{.Agda}, since taking
the underlying set of that pair gives the constant back. Nothing else about `L`
is used.

A reader with no constants at all is admissible for free, which is worth naming,
because most of the structural readers are of that kind: they speak entirely
through variables and bounded quantifiers, so there is nothing to be
constructible.
<!--zh-->
常量改名只实例化一次。层级的一个常元合格，指它可构造；它所变成的模型元素，就是该常元与它的证书之对；而往返是 `refl`{.Agda}，因为取那个对的底集就把常元原样取回。关于 `L` 再没有用到别的。

完全不含常元的读式白白合格，这值得点名，因为大多数结构性读式正是这一类：它们全靠变元与有界量词说话，压根没有东西需要可构造。
<!--/-->

```agda
InL : V ℓ → Type (ℓ-suc ℓ)
InL c = ⟨ isL c ⟩

module ToL = Relabel {K = V ℓ} {K' = S} {W = V ℓ}
  id fst InL (λ c p → c , p) (λ c p → refl)

open ToL public using ( liftFo; Δ₀-liftFo )
```

<!--en-->
## The transfer
<!--zh-->
## 搬运
<!--/-->

<!--en-->
Four steps, read from the model outward. Absoluteness moves the lifted formula
from satisfaction in `L` to satisfaction in the hierarchy at the projected
environment. Then relabelling along the projection is undone, twice: once to
recognize the lifted formula as the original with its constants replaced, and
once, in the opposite direction, to see the original as itself. The middle step
is where the relabelling's own correctness enters, and it is the only place the
constants are looked at.

The identity relabelling in the last step is not idle. A formula is not
definitionally its own image under the identity map on constants, since the map
is applied by recursion; but its *meaning* is, and that is exactly what the
relabelling theorem says at `f = id`.
<!--zh-->
四步，自模型向外读。绝对性把抬升后的公式从「在 `L` 中满足」搬到「在层级中、于投影后的环境处满足」。随后沿投影的常量改名被撤销两次：一次是认出抬升后的公式就是原公式换掉常元的样子，一次是反方向地看出原公式就是它自己。中间那一步是常量改名自身的正确性登场之处，也是唯一看常元的地方。

最后一步的恒等变换不是白费。一条公式并不按定义等于它在常元恒等映射下的像，因为那个映射是递归施加的；但它的**含义**等于，而那正是常量改名定理在 `f = id` 处所说的话。
<!--/-->

```agda
transferFo : ∀ {n} (φ : Formula (V ℓ) n) (h : BoundedFo InL φ) → Δ₀ φ
           → (γ : S ^ n) → (γ ⊨ liftFo φ h) ≡ ((map fst γ) ⊨v φ)
transferFo φ h dφ γ =
    abs₀ (Δ₀-liftFo h dφ) γ
  ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id (liftFo φ h) (map fst γ))
  ∙ cong (λ ψ → (map fst γ) ⊨v ψ) (ToL.liftFo-correct φ h)
  ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ id id φ (map fst γ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`liftFo`{.Agda} carries a Δ₀ formula about the hierarchy into the object language
of `L`, provided its constants are constructible, and `transferFo`{.Agda} says
the two say the same thing. The coding chapters were written on the hierarchy
side and stay there; this is how their readers are quoted from the `L` side, and
it costs a chain of four steps rather than a re-statement.

One thing this does *not* do, and should not be asked to. It is Δ₀ only, because
absoluteness is. That is no longer a restriction on what can be *said* in `L`,
since the comprehension fields there take formulas of any complexity; it is a
restriction on what can be *imported* from the hierarchy for free. A predicate
that is easier to write unbounded should be written unbounded, directly over the
model, and never routed through here.
<!--zh-->
`liftFo`{.Agda} 把关于层级的 Δ₀ 公式运进 `L` 的对象语言，只要它的常元可构造，而 `transferFo`{.Agda} 说两者说的是同一件事。编码诸章写在层级一侧，就留在那里；这便是从 `L` 一侧引用它们的读式的办法，代价是一条四步的链，而非重新陈述一遍。

有一件事它**不**做，也不该被要求去做。它只管 Δ₀，因为绝对性只管 Δ₀。这已不再是对「在 `L` 中能说什么」的限制，因为那边的概括字段接受任意复杂度的公式；它限制的是「能从层级白白进口什么」。一个写成无界更省事的谓词，就该无界地、直接在模型上写，绝不该绕经此处。
<!--/-->
