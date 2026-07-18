# The root: L ⊨ ZFC

<!--en-->
This is the root of the book, the chapter every other chapter exists to serve.
Read its statement with care, because the care is the content.

**What is proven.** Within cubical Agda, the constructible structure `𝒮ʟ` is a
model of ZFC: `L⊨ZFC`{.Agda} below. Together with Part 3, where the ambient
hierarchy models ZF, this is the **relative consistency of choice** in semantic
form: a universe satisfying ZF contains a sub-universe satisfying ZFC, so any
inconsistency of ZFC would already be an inconsistency of ZF.

**Relative to what.** To the host. The construction lives inside cubical Agda
with its universe tower, a metatheory informally about as strong as ZFC plus an
inaccessible cardinal. The book never claims an unconditional "Con(ZFC)";
consistency here is always consistency *relative to the declared host*, and the
host's strength is a price printed on the label, not hidden in the machinery.
This is no defect of mechanization: every consistency proof anywhere is relative
to the metatheory that carries it, and the only choice is whether to say so.

**What is assumed, today.** The module takes two parameters: the excluded-middle
interface of Part 0, the standing assumption of the book's classical cone, and
the previous chapter's **frontier**, the registry of statements not yet proven.
Given these, the theorem below is an ordinary, machine-checked theorem, and it
compiles today. Every remaining part of the book shrinks the frontier; when the
registry is empty its parameter disappears, and this page's statement stands
with the excluded middle alone. The chapter is therefore two things at once: the
book's main theorem, and its progress meter.
<!--zh-->
这里是本书的根，其余每一章都为它服务的那一章。请仔细读它的陈述，因为这份仔细本身就是内容。

**证了什么。**在 cubical Agda 之内，可构造结构 `𝒮ʟ` 是 ZFC 的模型：下文的 `L⊨ZFC`{.Agda}。与第三部 (环境层级满足 ZF) 合观，这就是语义形式的**选择公理相对一致性**：满足 ZF 的宇宙内部含有满足 ZFC 的子宇宙，故 ZFC 的任何矛盾都早已是 ZF 的矛盾。

**相对于什么。**相对于宿主。整个构造住在带宇宙塔的 cubical Agda 里，这个元理论的强度非形式地约当于 ZFC 加一个不可达基数。本书从不宣称无条件的「Con (ZFC)」；此处的一致性永远是**相对于申明的宿主**的一致性，宿主的强度是印在标签上的价格，不是藏在机器里的暗账。这并非机械化的缺陷：任何地方的任何一致性证明都相对于承载它的元理论，可选的只是说不说出来。

**今天假设了什么。**本模块收两个参数：第零部的排中律接口，即本书经典锥的常设假设；以及上一章的**前沿**，尚未证明的陈述之登记簿。给定二者，下面的定理是一条普通的、机器检验的定理，今天就能编译。本书余下各部不断缩减前沿；登记簿清空之日，其参数消失，本页的陈述便只倚排中律独立成立。所以本章同时是两样东西：本书的主定理，与它的进度表。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import L.Frontier using ( Frontier )

module L.Model {ℓ : Level} (lem : ∀ {ℓ'} → LEM ℓ') (F : Frontier {ℓ}) where

open import FOL.Structure using ( ZFStructure; ↾-reflects; _∈ᵗ_ )
import ZF.Model
open import V.Hierarchy using ( 𝒮ᵥ; extensionalV; regularityV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open ZFStructure 𝒮ʟ
open Frontier F

module ModelL = ZF.Model 𝒮ʟ
open ModelL using ( ZFModel; ZFCModel )
```

<!--en-->
## Two fields the restriction supplies
<!--zh-->
## 限制自己供应的两个字段
<!--/-->

<!--en-->
Extensionality and regularity are not frontier debts: they descend from the
ambient hierarchy to any transitive sub-universe, and `L` is transitive. For
extensionality, two constructible sets with the same constructible members have
the same members outright, because each member is itself constructible by
transitivity; the hierarchy's extensionality then equates the underlying sets,
and `↾-reflects`{.Agda} lifts the path back through the restriction.
<!--zh-->
外延与正则不在前沿的债目里：它们从环境层级下降到任何传递的子宇宙，而 `L` 传递。看外延：两个可构造集若可构造成员相同，则成员干脆全同，因为每个成员经传递性自身可构造；层级的外延性随即等同底层集合，`↾-reflects`{.Agda} 再把路径抬回限制结构。
<!--/-->

```agda
extensionalL : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
extensionalL {a} {b} h = ↾-reflects {𝒮 = 𝒮ᵥ {ℓ}} {M = isL} (extensionalV {a = fst a} {b = fst b} vwise)
  where
  vwise : (v : V ℓ) → (v ∈ fst a) ≡ (v ∈ fst b)
  vwise v = ⇔toPath fwd bwd
    where
    fwd : ⟨ v ∈ fst a ⟩ → ⟨ v ∈ fst b ⟩
    fwd v∈a = subst ⟨_⟩ (h (v , isL-trans v∈a (a .snd))) v∈a
    bwd : ⟨ v ∈ fst b ⟩ → ⟨ v ∈ fst a ⟩
    bwd v∈b = subst ⟨_⟩ (sym (h (v , isL-trans v∈b (b .snd)))) v∈b
```

<!--en-->
Regularity restricts even more easily: membership in the sub-universe is
membership in the hierarchy, so accessibility transfers along the underlying
set, member by member.
<!--zh-->
正则的下降更省事：子宇宙里的成员关系就是层级里的成员关系，可及性沿底层集合逐成员转移。
<!--/-->

```agda
regularityL : WellFounded (_∈ᵗ_ 𝒮ʟ)
regularityL (v , p) = accL v (regularityV v) p
  where
  accL : (u : V ℓ) → Acc (_∈ᵗ_ (𝒮ᵥ {ℓ})) u → (q : ⟨ isL u ⟩)
       → Acc (_∈ᵗ_ 𝒮ʟ) (u , q)
  accL u (acc rec) q = acc (λ { (y , r) y∈ → accL y (rec y y∈) r })
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

<!--en-->
Assembly. Two fields proven above, ten drawn from the frontier, and the choice
field applied to the very model being assembled, in the structural form the
frontier states it.
<!--zh-->
合龙。两个字段来自上文的证明，十个取自前沿，选择字段则以前沿所陈述的结构形式，作用于正被装配的这个模型自身。
<!--/-->

```agda
L⊨ZF : ZFModel
L⊨ZF = record
  { extensional    = extensionalL
  ; regularity     = regularityL
  ; hasEmpty       = hasEmptyL
  ; hasPair        = hasPairL
  ; hasUnion       = hasUnionL
  ; hasSeparation  = hasSeparationL
  ; hasReplacement = hasReplacementL
  ; hasPower       = hasPowerL
  ; numeral        = numeralL
  ; numeral-zero   = numeralL-zero
  ; numeral-suc    = numeralL-suc
  ; hasInfinity    = hasInfinityL }

L⊨ZFC : ZFCModel
L⊨ZFC = record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The root stands: `L⊨ZFC`{.Agda}, the constructible structure models ZFC, proven
from the excluded-middle interface and the frontier, with extensionality and
regularity supplied by transitivity rather than assumed. What the reader should
carry away is the shape of the claim: a semantic, relative consistency theorem,
priced in the open. The rest of the book is the paying down of the frontier.
<!--zh-->
根已立起：`L⊨ZFC`{.Agda}，可构造结构满足 ZFC，由排中律接口与前沿证得，其中外延与正则由传递性供应而非假设。读者该带走的是这个论断的形状：一条语义的、相对的一致性定理，价格摆在明处。本书余下的一切，就是逐笔偿清前沿。
<!--/-->
