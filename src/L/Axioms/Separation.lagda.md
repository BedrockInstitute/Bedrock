<!--en-->
# Separation and replacement, bounded
<!--zh-->
# 有界分离与替换
<!--ja-->
# 有界な分出公理と置換公理
<!--/-->

<!--en-->
This chapter proves Δ₀ separation and replacement in `L`. The proof has two
steps: first bound all formula constants and functional images within ordinal
stages, then construct the required sets using absoluteness and relabelling.
<!--zh-->
本章证明 `L` 中的 Δ₀ 分离与替换。证明分两步：先把公式的全部常元与函数像界在序数阶段之内，再借助绝对性与常元改名构造出所需的集合。
<!--ja-->
本章では、論理式の全定数と関数的な像を順序数段階で抑え、絶対性と定数の改名を用いて必要な集合を切り出すことにより、`L` における Δ₀ 分出公理と置換公理を証明する。
<!--/-->

<!--en-->
Separation asks: given a constructible set and a formula, is the subset it carves
out again constructible? The tools needed to answer this were built up over the
last several chapters, and this one assembles them, for formulas without
unbounded quantifiers.

The argument follows the same pattern as the basic axioms, with one extra
step. To place a set in `L` we exhibit it as a definable subset of a single
stage. The target here is `{x ∈ a : φ}`, and the stage must hold both `a` and
every constant `φ` mentions. Given such a stage, the definability operator requires a
formula over *that stage's* members, while `φ` is a formula over the whole model,
so the formula has to be relabelled down. This is what the bounding certificate
is for, and the extra step is checking that relabelling did not change what
the formula says.

The check is a five-step path through three chapters, and each step is an
equation already proven: definable-subset membership is outer satisfaction of the
relabelled formula; relabelling commutes with the two projections into the
hierarchy; and outer satisfaction of a Δ₀ formula is inner satisfaction. The last
is the only place where Δ₀ is used. Formulas with unbounded quantifiers get
the same treatment, but only after the following chapters provide a stage
that reflects them.
<!--zh-->
分离公理问的是：给定一个可构造集与一条公式，它刻出的子集是否仍可构造？回答这个问题所需的工具已在前几章逐步建立，本章将它们合在一起，用于不含无界量词的公式。

论证的框架与基本公理相同，只多出一步。要把一个集合放进 `L`，我们把它呈现为单一阶段的可定义子集。此处的目标是 `{x ∈ a : φ}`，而那个阶段必须同时容纳 `a` 与 `φ` 提到的每个常元。给定这样一个阶段，可定义性算子需要的是一条在**该阶段**成员之上的公式，而 `φ` 是在整个模型之上的公式，因此公式必须重标下去。这正是界层证书的用途；多出的那一步，就是核对重标没有改变公式所说的内容。

整个核对是一条跨三章的五步路径，每一步都是已证的等式：可定义子集的隶属就是重标后公式的外层满足；重标与两个到层级的投影交换；而 Δ₀ 公式的外层满足就是内层满足。最后一条是唯一用上 Δ₀ 的地方。含无界量词的公式也会得到同样的处理，但要等到随后各章，才能为它们找到一个反射它们的阶段。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Separation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∃∈ )
open import FOL.Manipulation.ConstantBounding
  using ( BoundedTm; BoundedFo; BoundedTm-mono; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Semantics
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono
        ; 𝒟ₒ; 𝒟ₒ-intro; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd; bound2 )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; 𝒟ₒ→isL; uniqueL )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The replacement image
<!--zh-->
## 替换的像
<!--ja-->
## 置換による像
<!--/-->

<!--en-->
`ReplImage a φ`{.Agda} names the class of values related by `φ` to some member of
`a`, fixing the source-first variable convention used by the bounded engine.
<!--zh-->
`ReplImage a φ`{.Agda} 命名 `φ` 与 `a` 的某个成员相关联的诸取值之类，并固定有界引擎所用的源在前变元约定。
<!--ja-->
`ReplImage a φ`{.Agda} は `a` のある要素と `φ` で関係づけられる値のクラスを名づけ、有界な構成が使う始域変数を先に置く規約を固定する。
<!--/-->

<!--en-->
Named once, because the engine below produces it and the model record uses
it: the image of `a` under `φ` is the class of things `φ` relates to some member
of `a`. Here the source variable is at index zero and the image at index one; the
model record states it the other way round, and the chapter that assembles the
field applies a renaming to match.
<!--zh-->
之所以先命名一次，是因为下面的引擎要产出它，而模型 record 要使用它：`a` 在 `φ` 下的像，就是由 `φ` 与 `a` 的某个成员相关联的那些东西构成的类。此处源变元在索引零、像在索引一；模型 record 的陈述次序相反，装配那个字段的章节则以改名调整次序，使之相符。
<!--/-->

```agda
ReplImage : (a : S) (φ : Formula S 2) → S → Ω
ReplImage a φ z = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∷ z ∷ []) ⊨ φ))
```

<!--en-->
## Bounding a functional image
<!--zh-->
## 界住函数像
<!--ja-->
## 関数的な像を抑える
<!--/-->

<!--en-->
`FunctionalImage`{.Agda} chooses the unique value at each source member and uses
smallness plus an ordinal bound to place every related image in one stage.
<!--zh-->
`FunctionalImage`{.Agda} 为源集合的每个成员选取唯一值，并用小性与序数上界把每个相关像放进单一阶段。
<!--ja-->
`FunctionalImage`{.Agda} は始集合の各要素で一意な値を選び、小ささと順序数の上界を用いて、関係するすべての像を一つの段階へ入れる。
<!--/-->

<!--en-->
A functional relation on the members of a set has all its values in one stage.
Choose the unique value at each member, use the small member type to bound the
stages of those choices, and use uniqueness to put every related value under the
same bound. The relation is a parameter, so the result is independent of the
variable order used by a particular formula.
<!--zh-->
一个集合的诸成员之上的函数关系，其值全落在同一个阶段。先在每个成员处取唯一值，再用小成员类型界住这些取值的诸阶段，最后以唯一性把每个相关值置于同一界下。关系作为参数传入，故结果不依赖某条特定公式所用的变量次序。
<!--/-->

```agda
module FunctionalImage (a : S) (R : S → S → Ω)
                       (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                           → isContr (Σ[ y ∈ S ] ⟨ R x y ⟩)) where

  Mem : Type (ℓ-suc ℓ)
  Mem = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

  img : Mem → S
  img p = fc (p .fst) (p .snd) .fst .fst

  img-sat : (p : Mem) → ⟨ R (p .fst) (img p) ⟩
  img-sat p = fc (p .fst) (p .snd) .fst .snd

  img-uniq : (p : Mem) (y : S) → ⟨ R (p .fst) y ⟩ → img p ≡ y
  img-uniq p y h = cong fst (fc (p .fst) (p .snd) .snd (y , h))

  private
    memS : ⟪ fst a ⟫ → Mem
    memS m = (⟪ fst a ⟫↪ m
             , isL-trans fm∈fa (a .snd)) , fm∈fa
      where
      fm∈fa : ⟨ ⟪ fst a ⟫↪ m ∈ fst a ⟩
      fm∈fa = ∈∈ₛ {a = ⟪ fst a ⟫↪ m} {b = fst a} .snd (∈ₛ⟪ fst a ⟫↪ m)

    bImg = boundingOrd ⟪ fst a ⟫
      (λ m → stage (fst (img (memS m))) (img (memS m) .snd))
      (λ m → stage-ord (fst (img (memS m))) (img (memS m) .snd))

  βimg : V ℓ
  βimg = bImg .fst

  βimg-ord : IsOrd βimg
  βimg-ord = bImg .snd .fst

  range∈βimg : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S) → ⟨ R x y ⟩
              → ⟨ fst y ∈ Lset βimg ⟩
  range∈βimg x x∈a y h = subst (λ w → ⟨ fst w ∈ Lset βimg ⟩) image≡y
    (Lset-mono {α = βimg} {β = stage (fst (img (memS m))) (img (memS m) .snd)}
      (bImg .snd .snd m) (stage-mem (fst (img (memS m))) (img (memS m) .snd)))
    where
    m = ∈-asFiber {a = fst x} {b = fst a} x∈a .fst
    q : memS m .fst ≡ x
    q = Σ≡Prop (λ z → snd (isL z))
      (∈-asFiber {a = fst x} {b = fst a} x∈a .snd)
    image≡y : img (memS m) ≡ y
    image≡y = img-uniq (memS m) y (subst (λ z → ⟨ R z y ⟩) (sym q) h)
```

<!--en-->
## At a fixed stage
<!--zh-->
## 在固定的阶段上
<!--ja-->
## 固定した段階での構成
<!--/-->

<!--en-->
Inside one ordinal stage, `Below`{.Agda} supplies indices for its constructible
members, and the satisfaction bridge relates formulas over the model carrier to
their relabelled formulas over that stage.
<!--zh-->
在一个固定的序数阶段内，`Below`{.Agda} 为其中的可构造成员提供索引；满足关系之桥则把模型载体上的公式与该阶段上经常元改名的公式联系起来。
<!--ja-->
一つの順序数段階の内部で、`Below`{.Agda} がその構成可能な要素の添字を与え、充足関係の橋がモデルの台上の論理式を、その段階上で定数の改名を施した論理式と結ぶ。
<!--/-->

<!--en-->
Everything below is relative to one stage. The predicate `Below` says a member of
the model lies in that stage; the relabelling instance sends such a member to its
index there, and the equation it needs is that the index names the member back,
which is what a fiber of the membership gives.
<!--zh-->
下文一切都相对于一个阶段。谓词 `Below` 表示模型的一个成员落在该阶段之中；重标实例把这样的成员送到它在其中的索引，而所需的那条等式是「索引把该成员命名回来」，这正由隶属关系的纤维给出。
<!--/-->

```agda
module AtStage (σ : V ℓ) (oσ : IsOrd σ) where
  module DefC = DefOf (Lset σ)

  Atrans : Transitive 𝒮ᵥ DefC.M
  Atrans = layer-trans (Lset-layer σ)

  module RefC = DefC.Refine Atrans
  open RefC.Abs using () renaming ( _⊨ᵛ_ to _⊨σ_ )

  Below : S → Type (ℓ-suc ℓ)
  Below c = ⟨ fst c ∈ Lset σ ⟩

  module RL = Relabel {K = S} {K' = ⟪ Lset σ ⟫} {W = V ℓ}
                fst ⟪ Lset σ ⟫↪ Below
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .fst)
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .snd)
```

<!--en-->
The five-step path. Read it from the top: membership in the definable subset is
outer satisfaction of the relabelled formula read through the stage's inclusion;
two applications of the relabelling law move that to the hierarchy's own reading;
the correctness of the partial relabelling identifies the two readings; and
absoluteness brings it back inside the model. Each link is an equation from an
earlier chapter, and the composite is the only place this chapter does anything
delicate.
<!--zh-->
那条五步路径自上而下读来如下：属于可定义子集，就是经该阶段的含入读出的、重标后公式的外层满足；两次重标律把它转换为层级自身的读法；部分重标的正确性把两种读法等同起来；而绝对性把它带回模型内部。每一环都是前面某章已证的等式，这个复合则是本章唯一需要细致工作的地方。
<!--/-->

```agda
  satBridge : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ((⟪ Lset σ ⟫↪ m ∷ []) ⊨σ (mapFo DefC.ι (RL.liftFo φ h)))
              ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  satBridge φ h dφ m xL =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ DefC.ι fst (RL.liftFo φ h)
        (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ⟪ Lset σ ⟫↪ id (RL.liftFo φ h)
             (⟪ Lset σ ⟫↪ m ∷ []))
    ∙ cong (λ ψ → (⟪ Lset σ ⟫↪ m ∷ []) ⊨v ψ) (RL.liftFo-correct φ h)
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id φ (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (abs₀ dφ ((⟪ Lset σ ⟫↪ m , xL) ∷ []))

  carveSat : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
           → (⟪ Lset σ ⟫↪ m ∈ DefC.defSet (RL.liftFo φ h))
             ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  carveSat φ h dφ m xL =
    RefC.abs-defSet (RL.liftFo φ h) (RL.Δ₀-liftFo h dφ) m ∙ satBridge φ h dφ m xL

```

<!--en-->
The carved set is sealed, and the facts about it are proved through the
seal. Unsealed, `defSet` unfolds to a set over formulas, and every later type
mentioning the carved set would carry that unfolding into conversion; sealing it
and exporting exactly what is needed keeps the rest of the chapter working with a
black box.
<!--zh-->
刻出的集合被封装起来，而关于它的事实经这一封装证明。若不封装，`defSet` 会展开为公式之上的一个集合，此后每个提到该集合的类型都会把这次展开带进转换检查；封装起来并只导出所需内容，本章其余部分便可把它当作黑箱使用。
<!--/-->

```agda
  opaque
    carve : Formula ⟪ Lset σ ⟫ 1 → V ℓ
    carve ψ = DefC.defSet ψ

  opaque
    unfolding carve
    carve∈𝒟ₒ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
    carve∈𝒟ₒ ψ = 𝒟ₒ-intro (Lset σ) (DefC.defSet ψ) ∣ ψ , refl ∣₁

    carve⊆ : (ψ : Formula ⟪ Lset σ ⟫ 1) (y : V ℓ) → ⟨ y ∈ carve ψ ⟩
           → ⟨ y ∈ Lset σ ⟩
    carve⊆ ψ y mem = DefC.defSet⊆A ψ y mem

    imageOut : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
               (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
             → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
             → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
    imageOut φ h dφ m xL mem = subst ⟨_⟩ (carveSat φ h dφ m xL) mem

    imageIn : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
    imageIn φ h dφ m xL sat = subst ⟨_⟩ (sym (carveSat φ h dφ m xL)) sat
```

<!--en-->
One more small tool. Satisfaction depends only on the underlying set, not on the
proof of constructibility carried alongside it, so a satisfaction fact transports
along an equation between underlying sets. Constructibility is propositional, so the
underlying equation gives an equation of model elements directly. The Δ₀
parameters remain in the interfaces used by the callers.
<!--zh-->
还有一个辅助结果。满足关系只依赖底层集合，而不依赖随之携带的可构造性证明，因此满足的事实可沿底层集合之间的等式转移。可构造性是命题，故底层集合的等式直接给出模型元素的等式。Δ₀ 参数保留在供调用方使用的接口中。
<!--/-->

```agda
  opaque
    ⊨-transport : (φ : Formula S 1) (dφ : Δ₀ φ) (u v : S) → fst u ≡ fst v
                → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩
    ⊨-transport φ dφ u v p =
      subst (λ z → ⟨ (z ∷ []) ⊨ φ ⟩) (Σ≡Prop (λ x → snd (isL x)) p)

```

<!--en-->
## Separation at a stage
<!--zh-->
## 在一个阶段上分离
<!--ja-->
## 一つの段階で分出する
<!--/-->

<!--en-->
`carveAt`{.Agda} turns a bounded unary Δ₀ formula whose witnesses stay in the
stage into a constructible set, and `separateAt`{.Agda} specializes it to a
subset of a given set.
<!--zh-->
`carveAt`{.Agda} 把见证落在阶段内的有界一元 Δ₀ 公式化为可构造集合；`separateAt`{.Agda} 则把它专门用于给定集合的子集。
<!--ja-->
`carveAt`{.Agda} は証人が段階内に留まる有界な一変数 Δ₀ 論理式を構成可能集合へ変え、`separateAt`{.Agda} はそれを与えられた集合の部分集合へ特殊化する。
<!--/-->

<!--en-->
The shared construction carves a bounded unary formula whose satisfying sets
lie in the stage. The carved set is definable, hence constructible; the bridge
and transport identify its members with the formula's satisfaction predicate.
Separation instantiates this construction with the conjunction of membership
in `a` and `φ`. Transitivity supplies the stage cover from the membership conjunct.
<!--zh-->
共享的构造处理一条有界一元公式，其满足者均落在该阶段中。刻出的集合可定义，故可构造；语义桥与转移把它的成员关系等同于公式的满足谓词。分离则把该构造实例化为「属于 `a`」与 `φ` 的合取；传递性由成员关系这一合取项提供阶段覆盖。
<!--/-->

```agda
  private
    memberIsL : (m : ⟪ Lset σ ⟫) → ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
    memberIsL m = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

  carveAt : (χ : Formula S 1) (hχ : BoundedFo Below χ) (dχ : Δ₀ χ)
            (cover : (z : S) → ⟨ (z ∷ []) ⊨ χ ⟩ → ⟨ fst z ∈ Lset σ ⟩)
          → isContr (SetOf (λ z → (z ∷ []) ⊨ χ))
  carveAt χ hχ dχ cover = uniqueL (λ z → (z ∷ []) ⊨ χ) (replElt , spec)
    where
    replElt : S
    replElt = carve (RL.liftFo χ hχ)
            , 𝒟ₒ→isL σ oσ (carve (RL.liftFo χ hχ)) (carve∈𝒟ₒ (RL.liftFo χ hχ))

    spec : (z : S) → (z ∈ˢ replElt) ≡ ((z ∷ []) ⊨ χ)
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z ∈ˢ replElt ⟩ → ⟨ ((z ∷ []) ⊨ χ) ⟩
      fwd z∈ = ⊨-transport χ dχ (⟪ Lset σ ⟫↪ m , xL) z q (imageOut χ hχ dχ m xL m∈)
        where
        fz∈Lσ = carve⊆ (RL.liftFo χ hχ) (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) (sym q) z∈

      bwd : ⟨ ((z ∷ []) ⊨ χ) ⟩ → ⟨ z ∈ˢ replElt ⟩
      bwd qz = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) q m∈
        where
        fz∈Lσ = cover z qz
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        satz : ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ χ ⟩
        satz = ⊨-transport χ dχ z (⟪ Lset σ ⟫↪ m , xL) (sym q) qz
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = imageIn χ hχ dχ m xL satz

  separateAt : (a : S) (fa∈σ : ⟨ fst a ∈ Lset σ ⟩)
               (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  separateAt a fa∈σ φ h dφ =
    carveAt ((var zero ∈̇ con a) ∧̇ φ) ((tt* , fa∈σ) , h) (δ-∧ δ-∈ dφ)
      (λ z q → layer-trans (Lset-layer σ) {x = fst a} {y = fst z} (q .fst) fa∈σ)
```

<!--en-->
## Finding the stage
<!--zh-->
## 找到那个阶段
<!--ja-->
## 論理式を収める段階を求める
<!--/-->

<!--en-->
Structural recursion over terms and formulas computes an ordinal stage containing
every constant, merging branch bounds and transporting their boundedness proofs.
<!--zh-->
对词项与公式作结构递归，可计算出包含全部常元的序数阶段，并在分支处合并上界、传输其有界性证明。
<!--ja-->
項と論理式の構造的再帰により全定数を含む順序数段階を計算し、分岐では上界を併合して有界性の証明を輸送する。
<!--/-->

<!--en-->
The construction requires a stage holding every constant of the formula. It obtains one by
recursion on the formula, producing the stage and certificate together. A
constant contributes its own earliest stage, a variable contributes nothing, and
at each branching node the two stages are combined by taking a bound, with
monotonicity raising both certificates to that bound.

The bound of two ordinals is supplied by `bound2`{.Agda} from the ordinal chapter. This is
the only result the recursion needs from ordinal theory.
<!--zh-->
引擎要的是一个装下公式全部常元的阶段。造一个出来，就是沿公式的一次递归，同时产出阶段与证书。常元贡献它自己的最早阶段，变元什么也不贡献，而在每个分叉节点上，两个阶段经界住而合并，单调性把两份证书都抬到合并处。

合并两个序数正是序数那一章的 `bound2`{.Agda}；这次递归对序数理论的全部需求，也到此为止。
<!--/-->

```agda
Below′ : V ℓ → S → Type (ℓ-suc ℓ)
Below′ σ c = ⟨ fst c ∈ Lset σ ⟩


liftTmTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (t : Term S n)
         → BoundedTm (Below′ σ) t → BoundedTm (Below′ β) t
liftTmTo {σ} {β} σ∈β t h =
  BoundedTm-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') t h

liftFoTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (φ : Formula S n)
         → BoundedFo (Below′ σ) φ → BoundedFo (Below′ β) φ
liftFoTo {σ} {β} σ∈β φ h =
  BoundedFo-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') φ h

mkBoundedTm : ∀ {n} (t : Term S n) → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedTm (Below′ σ) t)
mkBoundedTm (con c) = stage (fst c) (c .snd)
                    , (stage-ord (fst c) (c .snd) , stage-mem (fst c) (c .snd))
mkBoundedTm (var i) = ∅ , (∅-ord , _)

private
  mkBounded : ∀ {ℓc ℓd} {C : V ℓ → Type ℓc} {D : V ℓ → Type ℓd}
            → (liftC : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → C σ → C β)
            → (liftD : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → D σ → D β)
            → (r₁ : Σ[ σ ∈ V ℓ ] (IsOrd σ × C σ))
            → (r₂ : Σ[ σ ∈ V ℓ ] (IsOrd σ × D σ))
            → Σ[ σ ∈ V ℓ ] (IsOrd σ × (C σ × D σ))
  mkBounded liftC liftD r₁ r₂ = b .fst , (b .snd .fst ,
      ( liftC (b .snd .snd .fst) (r₁ .snd .snd)
      , liftD (b .snd .snd .snd) (r₂ .snd .snd) ))
    where
    b  = bound2 (r₁ .fst) (r₂ .fst) (r₁ .snd .fst) (r₂ .snd .fst)

mkBoundedFo : ∀ {n} (φ : Formula S n) → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)
mkBoundedFo (t ∈̇ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (t ≐ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (φ ∧̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo (φ ∨̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo (φ ⇒̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo ⊥̇        = ∅ , (∅-ord , _)
mkBoundedFo (∃̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
mkBoundedFo (∃̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
```

<!--en-->
## Δ₀ separation
<!--zh-->
## Δ₀ 分离
<!--ja-->
## Δ₀ 分出公理
<!--/-->

<!--en-->
`separateΔ₀`{.Agda} merges the bounds for the formula's constants and the source
set, then invokes `separateAt`{.Agda} to realize the bounded separation instance.
<!--zh-->
`separateΔ₀`{.Agda} 先把公式常元与源集合的上界合并，再调用 `separateAt`{.Agda} 得到有界分离的实例。
<!--ja-->
`separateΔ₀`{.Agda} は論理式の定数と始集合の上界を併合し、`separateAt`{.Agda} を呼び出して有界な分出公理の事例を実現する。
<!--/-->

<!--en-->
Merge the formula's stage with the argument's own earliest stage,
raise the certificate to the resulting bound, and use these data in the bounded
separation construction. This proves separation for the bounded fragment
unconditionally: it requires neither reflection nor a frontier field, and
uses the results established in the preceding chapters in order.
<!--zh-->
步骤如下：把公式的阶段与实参自身的最早阶段合并，把证书抬升到合并后的阶段，再把结果交给引擎。这正是有界片段的分离公理，无条件成立：既不需要反射，也不需要前沿字段，只是依序使用前几章已经建立的工具。
<!--/-->

```agda
separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
separateΔ₀ a φ dφ = AtStage.separateAt σ oσ a fa∈σ φ h dφ
  where
  rφ = mkBoundedFo φ
  sa = stage (fst a) (a .snd)
  bb = bound2 (rφ .fst) sa (rφ .snd .fst) (stage-ord (fst a) (a .snd))
  σ  = bb .fst
  oσ = bb .snd .fst
  h  = liftFoTo {σ = rφ .fst} {β = σ} (bb .snd .snd .fst) φ (rφ .snd .snd)
  fa∈σ : ⟨ fst a ∈ Lset σ ⟩
  fa∈σ = Lset-mono {α = σ} {β = sa} (bb .snd .snd .snd) (stage-mem (fst a) (a .snd))
```

<!--en-->
## Δ₀ replacement
<!--zh-->
## Δ₀ 替换
<!--ja-->
## Δ₀ 置換公理
<!--/-->

<!--en-->
`replaceΔ₀`{.Agda} first bounds the functional image and then separates that
stage by the bounded existential defining `ReplImage`{.Agda}.
<!--zh-->
`replaceΔ₀`{.Agda} 先界住函数像，再用定义 `ReplImage`{.Agda} 的有界存在式在该阶段上分离。
<!--ja-->
`replaceΔ₀`{.Agda} はまず関数的な像を抑え、次に `ReplImage`{.Agda} を定義する有界存在量化でその段階を分出する。
<!--/-->

<!--en-->
Replacement needs one thing more: a stage containing the image. Functionality
gives the common image bound above. Separate that stage by the bounded
existential saying that some member of the argument is related to the candidate;
the resulting predicate is exactly the replacement image.

Worth noting what this does *not* need. The defining formula's only quantifier is
bounded by the argument, so it stays Δ₀ and absoluteness applies to the whole of
it. The work is done by functionality, not by any reflection across structures,
which is the clean line between this lemma and the unbounded case.
<!--zh-->
替换还多需要一个条件：一个装得下像的阶段。函数性恰好给出上述公共像界。用一条有界存在公式「实参的某个成员与候选者相关」在该阶段上作分离，所得谓词正是替换的像。

值得注意的是它**不**需要什么：定义公式唯一的量词被实参所界，故它保持 Δ₀，绝对性适用于整条公式。真正起作用的是函数性，而非任何跨结构的反射；这正是本引理与无界情形之间的清晰分界。
<!--/-->

```agda
replaceΔ₀ : (a : S) (φ : Formula S 2) → Δ₀ φ
          → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (x ∷ y ∷ []) ⊨ φ ⟩))
          → isContr (SetOf (ReplImage a φ))
replaceΔ₀ a φ dφ fc =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡)
    (separateΔ₀ (LsetS βimg βimg-ord) imageFo (δ-∃∈ dφ))
  where
  module I = FunctionalImage a (λ x y → (x ∷ y ∷ []) ⊨ φ) fc
  open I using ( βimg; βimg-ord; range∈βimg )

  imageFo : Formula S 1
  imageFo = ∃̇∈ (con a) φ

  BoundedImage : S → Ω
  BoundedImage y = (y ∈ˢ LsetS βimg βimg-ord) ⊓ ((y ∷ []) ⊨ imageFo)

  Q≡ : ReplImage a φ ≡ BoundedImage
  Q≡ = funExt (λ y → ⇔toPath (into y) (λ p → p .snd))
    where
    into : (y : S) → ⟨ ReplImage a φ y ⟩ → ⟨ BoundedImage y ⟩
    into y = PT.rec (snd (BoundedImage y)) λ { (x , (x∈a , h)) →
      range∈βimg x x∈a y h , ∣ x , (x∈a , h) ∣₁ }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The bounded engine now yields `separateΔ₀`{.Agda} and `replaceΔ₀`{.Agda}, with
formula constants and functional images each confined to an explicit stage.
<!--zh-->
有界引擎现在给出 `separateΔ₀`{.Agda} 与 `replaceΔ₀`{.Agda}，并把公式常元与函数像分别限制在一个明确阶段内。
<!--ja-->
有界な構成から `separateΔ₀`{.Agda} と `replaceΔ₀`{.Agda} が得られ、論理式の定数と関数的な像はそれぞれ明示的な段階に収められる。
<!--/-->

<!--en-->
Given a stage holding a set and all the constants of a Δ₀ formula,
`separateAt`{.Agda} carves the subset in `L`. Its semantic content is
`carveSat`{.Agda}: membership in the carved set is satisfaction in the model,
along a path supplied by definability, relabelling and absoluteness.
`FunctionalImage`{.Agda} supplies the other ingredient for replacement by bounding
the values of any functional relation. Thus `replaceΔ₀`{.Agda} first bounds its
image and then applies `separateΔ₀`{.Agda} to a bounded existential. For arbitrary
formulas, the full axiom chapter adds reflection only where separation needs it.
<!--zh-->
给定一个装下某集合与某 Δ₀ 公式全部常元的阶段，`separateAt`{.Agda} 在 `L` 中刻出子集。其语义内容是 `carveSat`{.Agda}：属于刻出的集合就是在模型中满足，所沿道路由可定义性、重标与绝对性给出。`FunctionalImage`{.Agda} 提供替换所需的另一件东西：界住任意函数关系的诸值。因此 `replaceΔ₀`{.Agda} 先界住其像，再把 `separateΔ₀`{.Agda} 施于一条有界存在式。对任意公式，完整公理一章只在分离需要之处加入反射。
<!--/-->
