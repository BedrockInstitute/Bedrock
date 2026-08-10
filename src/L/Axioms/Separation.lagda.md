# Separation and replacement, bounded

<!--en-->
Separation asks: given a constructible set and a formula, is the subset it carves
out again constructible? The machinery for answering that has been assembled over
the last several chapters, and this one puts it together, for formulas without
unbounded quantifiers.

The shape of the argument is the same one the basic axioms used, with one extra
step. To place a set in `L` we exhibit it as a definable subset of a single
stage. The target here is `{x ∈ a : φ}`, and the stage must hold both `a` and
every constant `φ` mentions. Given such a stage, the definability operator wants a
formula over *that stage's* members, while `φ` is a formula over the whole model,
so the formula has to be relabelled down. That is what the bounding certificate
was built for, and the extra step is checking that relabelling did not change what
the formula says.

Checking it is a five-step path through three chapters, and each step is an
equation already proven: definable-subset membership is outer satisfaction of the
relabelled formula; relabelling commutes with the two projections into the
hierarchy; and outer satisfaction of a Δ₀ formula is inner satisfaction. The last
is where Δ₀ is spent, and it is the only place. Formulas with unbounded
quantifiers get this treatment too, but only after the next chapters buy them a
stage that reflects them.
<!--zh-->
分离公理问的是：给定一个可构造集与一条公式，它刻出的子集是否仍可构造？回答这个问题的机器已在前几章陆续备齐，本章把它们装到一起，针对不含无界量词的公式。

论证的形状与基本公理用的是同一个，只多一步。要把一个集合放进 `L`，我们把它呈现为单一阶段的可定义子集。此处的目标是 `{x ∈ a : φ}`，而那个阶段必须同时装下 `a` 与 `φ` 提到的每个常元。给定这样一个阶段，可定义性算子要的是一条**该阶段**成员之上的公式，而 `φ` 是整个模型之上的公式，故公式必须被重标下去。那正是界层证书的用途，而多出的那一步就是核对重标没有改变公式所说的内容。

核对它是一条穿过三章的五步路径，每一步都是已证的等式：可定义子集的隶属就是重标后公式的外层满足；重标与两个到层级的投影交换；而 Δ₀ 公式的外层满足就是内层满足。最后一条是花掉 Δ₀ 的地方，也是唯一的地方。含无界量词的公式也会受到同样的对待，但要等随后诸章为它们买到一个反射它们的阶段。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Separation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∃∈ )
open import FOL.Manipulation.Bounding
  using ( BoundedTm; BoundedFo; BoundedTm-mono; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
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
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL; uniqueL )

open import Cubical.Functions.Logic using ( ⇔toPath )
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
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ ; _⊨ᵛ_ to _⊨ᵥ_ )
```

<!--en-->
## The replacement image
<!--zh-->
## 替换的像
<!--/-->

<!--en-->
Named once, because the engine below produces it and the model record consumes
it: the image of `a` under `φ` is the class of things `φ` relates to some member
of `a`. Here the source variable is at index zero and the image at index one; the
model record states it the other way round, and the chapter that assembles the
field applies a renaming to match.
<!--zh-->
先命名一次，因为下面的引擎产出它而模型 record 消费它：`a` 在 `φ` 下的像，是 `φ` 与 `a` 的某个成员相关联的那些东西构成的类。此处源变元在索引零、像在索引一；模型 record 的陈述次序相反，而装配那个字段的章节以改名调整次序以相符。
<!--/-->

```agda
ReplImage : (a : S) (φ : Formula S 2) → S → Ω
ReplImage a φ z = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∷ z ∷ []) ⊨ φ))
```

<!--en-->
## At a fixed stage
<!--zh-->
## 在固定的阶段上
<!--/-->

<!--en-->
Everything below is relative to one stage. The predicate `Below` says a member of
the model lies in that stage; the relabelling instance sends such a member to its
index there, and the equation it needs is that the index names the member back,
which is what a fiber of the membership gives.
<!--zh-->
下文一切都相对于一个阶段。谓词 `Below` 说模型的一个成员落在该阶段中；重标实例把这样的成员送到它在其中的索引，而它所需的那条等式是「索引把该成员命名回来」，那正是隶属关系的纤维所给出的。
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
那条五步路径。自上而下读：属于可定义子集，就是经该阶段的含入读出的、重标后公式的外层满足；两次重标律把它搬到层级自己的读法；部分重标的正确性把两种读法认同；而绝对性把它带回模型内部。每一环都是前面某章的等式，而这个复合是本章唯一做细致事情的地方。
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

  carveSatAnd : (mₐ : ⟪ Lset σ ⟫) (φ : Formula S 1) (h : BoundedFo Below φ)
                (dφ : Δ₀ φ) (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
              → (⟪ Lset σ ⟫↪ m ∈ DefC.defSet ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h))
                ≡ ((⟪ Lset σ ⟫↪ m ∈ ⟪ Lset σ ⟫↪ mₐ)
                   ⊓ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ))
  carveSatAnd mₐ φ h dφ m xL =
      RefC.abs-defSet ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h)
        (δ-∧ δ-∈ (RL.Δ₀-liftFo h dφ)) m
    ∙ cong₂ _⊓_ refl (satBridge φ h dφ m xL)
```

<!--en-->
The carved set is sealed, and the four facts about it are proved through the
seal. Unsealed, `defSet` unfolds to a set over formulas, and every later type
mentioning the carved set would carry that unfolding into conversion; sealing it
and exporting exactly what is needed keeps the rest of the chapter working with a
black box.
<!--zh-->
刻出的集合被封印，而关于它的四个事实经封印证出。不封印的话，`defSet` 会展开成公式之上的一个集合，而此后每个提到该集合的类型都会把那次展开带进转换检查；封印它并只导出所需之物，使本章其余部分对着一个黑箱工作。
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

    carveOut : (mₐ : ⟪ Lset σ ⟫) (φ : Formula S 1) (h : BoundedFo Below φ)
               (dφ : Δ₀ φ) (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
             → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h) ⟩
             → ⟨ (⟪ Lset σ ⟫↪ m ∈ ⟪ Lset σ ⟫↪ mₐ)
                 ⊓ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ) ⟩
    carveOut mₐ φ h dφ m xL mem = subst ⟨_⟩ (carveSatAnd mₐ φ h dφ m xL) mem

    carveIn : (mₐ : ⟪ Lset σ ⟫) (φ : Formula S 1) (h : BoundedFo Below φ)
              (dφ : Δ₀ φ) (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ⟨ (⟪ Lset σ ⟫↪ m ∈ ⟪ Lset σ ⟫↪ mₐ)
                ⊓ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ) ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve ((var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h) ⟩
    carveIn mₐ φ h dφ m xL br = subst ⟨_⟩ (sym (carveSatAnd mₐ φ h dφ m xL)) br

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
along an equation between underlying sets. For a Δ₀ formula this is immediate:
step outside, transport, step back.
<!--zh-->
还有一件小工具。满足关系只依赖底层集合，而不依赖随之携带的可构造性证明，故满足的事实可沿底层集合之间的等式搬运。对 Δ₀ 公式这是直接的：走到外面、搬运、再走回来。
<!--/-->

```agda
  opaque
    ⊨-transport : (φ : Formula S 1) (dφ : Δ₀ φ) (u v : S) → fst u ≡ fst v
                → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩
    ⊨-transport φ dφ u v p hyp =
      subst ⟨_⟩ (sym (abs₀ dφ (v ∷ [])))
        (subst (λ w → ⟨ (w ∷ []) ⊨ᵥ φ ⟩) p
          (subst ⟨_⟩ (abs₀ dφ (u ∷ [])) hyp))

    ⊨-transport₂ : (φ : Formula S 2) (dφ : Δ₀ φ) (u v w : S) → fst u ≡ fst v
                 → ⟨ (u ∷ w ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ w ∷ []) ⊨ φ ⟩
    ⊨-transport₂ φ dφ u v w p hyp =
      subst ⟨_⟩ (sym (abs₀ dφ (v ∷ w ∷ [])))
        (subst (λ s → ⟨ (s ∷ fst w ∷ []) ⊨ᵥ φ ⟩) p
          (subst ⟨_⟩ (abs₀ dφ (u ∷ w ∷ [])) hyp))
```

<!--en-->
## Separation at a stage
<!--zh-->
## 在一个阶段上分离
<!--/-->

<!--en-->
Now the construction. The formula carving the subset out of the stage is the
conjunction of "belongs to `a`", written with `a`'s index as a constant, and the
relabelled `φ`. The carved set is a definable subset of the stage, hence
constructible; and its members are exactly what the specification asks, by the
bridge in each direction, with the transport handling the passage between a
member of the stage and the same set carrying its own constructibility proof.
<!--zh-->
现在是构造本身。从该阶段中刻出子集的那条公式，是「属于 `a`」(以 `a` 的索引为常量写出) 与重标后的 `φ` 的合取。刻出的集合是该阶段的可定义子集，故可构造；而它的成员恰是规格所要求的，经两个方向的那道桥，其中搬运工具负责在「阶段的一个成员」与「携带自身可构造性证明的同一集合」之间过渡。
<!--/-->

```agda
  private
    memberIsL : (m : ⟪ Lset σ ⟫) → ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
    memberIsL m = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

  separateAt : (a : S) (fa∈σ : ⟨ fst a ∈ Lset σ ⟩)
               (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  separateAt a fa∈σ φ h dφ = uniqueL Q (sepElt , spec)
    where
    Q : S → Ω
    Q x = (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)
    mₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈σ .fst
    qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a
    qₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈σ .snd
    ψ : Formula ⟪ Lset σ ⟫ 1
    ψ = (var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h
    sepElt : S
    sepElt = carve ψ , 𝒟ₒ→isL σ oσ (carve ψ) (carve∈𝒟ₒ ψ)

    spec : (z : S) → (z ∈ˢ sepElt) ≡ Q z
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z ∈ˢ sepElt ⟩ → ⟨ Q z ⟩
      fwd z∈ = fz∈fa , zφ
        where
        fz∈Lσ = carve⊆ ψ (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve ψ ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve ψ ⟩) (sym q) z∈
        dk = carveOut mₐ φ h dφ m xL m∈
        fz∈fa = subst (λ w → ⟨ fst z ∈ w ⟩) qₐ
          (subst (λ w → ⟨ w ∈ ⟪ Lset σ ⟫↪ mₐ ⟩) q (dk .fst))
        zφ = ⊨-transport φ dφ (⟪ Lset σ ⟫↪ m , xL) z q (dk .snd)

      bwd : ⟨ Q z ⟩ → ⟨ z ∈ˢ sepElt ⟩
      bwd (fz∈fa , zφ) = subst (λ w → ⟨ w ∈ carve ψ ⟩) q m∈
        where
        fz∈Lσ = layer-trans (Lset-layer σ) {x = fst a} {y = fst z} fz∈fa fa∈σ
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        p₁ : ⟨ ⟪ Lset σ ⟫↪ m ∈ ⟪ Lset σ ⟫↪ mₐ ⟩
        p₁ = subst (λ w → ⟨ w ∈ ⟪ Lset σ ⟫↪ mₐ ⟩) (sym q)
          (subst (λ w → ⟨ fst z ∈ w ⟩) (sym qₐ) fz∈fa)
        p₂ : ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
        p₂ = ⊨-transport φ dφ z (⟪ Lset σ ⟫↪ m , xL) (sym q) zφ
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve ψ ⟩
        m∈ = carveIn mₐ φ h dφ m xL (p₁ , p₂)
```

<!--en-->
## Replacement at a stage
<!--zh-->
## 在一个阶段上替换
<!--/-->

<!--en-->
Replacement reuses the same engine. The image of `a` under a two-variable formula
is what a *one*-variable bounded existential says, so the construction hands that
existential to the machinery above and reads the answer back. The extra
hypothesis is that the image already lies in the stage; producing it is the work
of whoever calls this, and the next chapters do it by bounding the stages of the
images.
<!--zh-->
替换复用同一套引擎。`a` 在一条二元公式下的像，正是一条**一元**有界存在所说的东西，故这个构造把那条存在式交给上面的机器，再把答案读回来。多出的那个假设是像已经落在该阶段中；产出它是调用方的工作，而随后诸章正是经界住诸像的阶段来完成它。
<!--/-->

```agda
  replaceAt : (a : S) (fa∈σ : ⟨ fst a ∈ Lset σ ⟩)
              (φ : Formula S 2) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (cover : (z : S) → ⟨ ReplImage a φ z ⟩ → ⟨ fst z ∈ Lset σ ⟩)
            → isContr (SetOf (ReplImage a φ))
  replaceAt a fa∈σ φ h dφ cover = uniqueL (ReplImage a φ) (replElt , spec)
    where
    χ : Formula S 1
    χ = ∃̇∈ (con a) φ
    hχ : BoundedFo Below χ
    hχ = fa∈σ , h
    dχ : Δ₀ χ
    dχ = δ-∃∈ dφ
    replElt : S
    replElt = carve (RL.liftFo χ hχ)
            , 𝒟ₒ→isL σ oσ (carve (RL.liftFo χ hχ)) (carve∈𝒟ₒ (RL.liftFo χ hχ))

    spec : (z : S) → (z ∈ˢ replElt) ≡ ReplImage a φ z
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z ∈ˢ replElt ⟩ → ⟨ ReplImage a φ z ⟩
      fwd z∈ = ⊨-transport χ dχ (⟪ Lset σ ⟫↪ m , xL) z q (imageOut χ hχ dχ m xL m∈)
        where
        fz∈Lσ = carve⊆ (RL.liftFo χ hχ) (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) (sym q) z∈

      bwd : ⟨ ReplImage a φ z ⟩ → ⟨ z ∈ˢ replElt ⟩
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
```

<!--en-->
## Finding the stage
<!--zh-->
## 找到那个阶段
<!--/-->

<!--en-->
The engine wants a stage holding every constant of the formula. Building one is a
recursion on the formula that produces the stage and the certificate together. A
constant contributes its own earliest stage, a variable contributes nothing, and
at every branching node the two stages are merged by bounding them, with
monotonicity raising both certificates to the merge.

Merging two ordinals is `bound2`{.Agda} from the ordinal chapter, and it is the
only thing this recursion needs from ordinal theory.
<!--zh-->
引擎要的是一个装下公式全部常元的阶段。造一个出来，是沿公式的一次递归，同时产出阶段与证书。常元贡献它自己的最早阶段，变元什么也不贡献，而在每个分叉节点上，两个阶段经界住而合并，单调性把两份证书都抬到合并处。

合并两个序数就是序数那一章的 `bound2`{.Agda}，而这也是这次递归从序数理论索取的全部。
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
mkBoundedFo (¬̇ φ)    = mkBoundedFo φ
mkBoundedFo ⊤̇        = ∅ , (∅-ord , _)
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
<!--/-->

<!--en-->
Everything is now in place. Merge the formula's stage with the argument's own
earliest stage, raise the certificate to the merge, and hand the result to the
engine. This is separation for the bounded fragment, unconditionally: no
reflection, no frontier field, just the machinery of the last several chapters
applied in order.
<!--zh-->
一切就位。把公式的阶段与实参自身的最早阶段合并，把证书抬到合并处，再把结果交给引擎。这就是有界片段的分离公理，无条件成立：不需要反射，不需要前沿字段，只是把前几章的机器按顺序用一遍。
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
<!--/-->

<!--en-->
Replacement needs one thing more: the engine asked that the image already lie in
the stage, and here is where that is paid. Functionality gives, for each member of
the argument, a unique image; each image has its own earliest stage; and the
bounding lemma over the argument's member type merges all of them at once. The
merged ordinal joins the argument's stage and the formula's, and the covering
condition follows because anything in the image is, by uniqueness, the image of
some member.

Worth noting what this does *not* need. The defining formula's only quantifier is
bounded by the argument, so it stays Δ₀ and absoluteness applies to the whole of
it. The work is done by functionality, not by any reflection across structures,
which is the clean line between this lemma and the unbounded case.
<!--zh-->
替换还多要一样：引擎要求像已经落在该阶段中，而正是在此处偿付。函数性为实参的每个成员给出唯一的像；每个像有自己的最早阶段；而界层引理在实参的成员类型上一举把它们全部合并。合并后的序数再与实参的阶段、公式的阶段相并，而覆盖条件随之成立，因为像中的任何东西经唯一性都是某个成员的像。

值得注意它**不**需要什么。定义公式唯一的量词被实参所界，故它保持 Δ₀，绝对性适用于整条公式。出力的是函数性，而非任何跨结构的反射，这正是本引理与无界情形之间那条干净的分界。
<!--/-->

```agda
replaceΔ₀ : (a : S) (φ : Formula S 2) → Δ₀ φ
          → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (x ∷ y ∷ []) ⊨ φ ⟩))
          → isContr (SetOf (ReplImage a φ))
replaceΔ₀ a φ dφ fc = AtStage.replaceAt σ oσ a fa∈σ φ h dφ cover
  where
  memS : (m : ⟪ fst a ⟫) → Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩
  memS m = xₘ , fm∈fa
    where
    fm∈fa : ⟨ ⟪ fst a ⟫↪ m ∈ fst a ⟩
    fm∈fa = ∈∈ₛ {a = ⟪ fst a ⟫↪ m} {b = fst a} .snd (∈ₛ⟪ fst a ⟫↪ m)
    xₘ : S
    xₘ = ⟪ fst a ⟫↪ m , isL-trans {x = fst a} {y = ⟪ fst a ⟫↪ m} fm∈fa (a .snd)
  imgElt : (m : ⟪ fst a ⟫) → S
  imgElt m = fc (memS m .fst) (memS m .snd) .fst .fst
  imgStage : ⟪ fst a ⟫ → V ℓ
  imgStage m = stage (fst (imgElt m)) (imgElt m .snd)
  bImg = boundingOrd ⟪ fst a ⟫ imgStage
           (λ m → stage-ord (fst (imgElt m)) (imgElt m .snd))
  βimg = bImg .fst
  oβimg = bImg .snd .fst
  img∈Lβimg : (m : ⟪ fst a ⟫) → ⟨ fst (imgElt m) ∈ Lset βimg ⟩
  img∈Lβimg m = Lset-mono {α = βimg} {β = imgStage m} (bImg .snd .snd m)
    (stage-mem (fst (imgElt m)) (imgElt m .snd))
  rφ = mkBoundedFo φ
  sa = stage (fst a) (a .snd)
  b1 = bound2 βimg sa oβimg (stage-ord (fst a) (a .snd))
  bb = bound2 (b1 .fst) (rφ .fst) (b1 .snd .fst) (rφ .snd .fst)
  σ  = bb .fst
  oσ = bb .snd .fst
  b1∈σ : ⟨ b1 .fst ∈ σ ⟩
  b1∈σ = bb .snd .snd .fst
  βimg∈σ : ⟨ βimg ∈ σ ⟩
  βimg∈σ = oσ .fst {x = b1 .fst} {y = βimg} (b1 .snd .snd .fst) b1∈σ
  sa∈σ : ⟨ sa ∈ σ ⟩
  sa∈σ = oσ .fst {x = b1 .fst} {y = sa} (b1 .snd .snd .snd) b1∈σ
  fa∈σ : ⟨ fst a ∈ Lset σ ⟩
  fa∈σ = Lset-mono {α = σ} {β = sa} sa∈σ (stage-mem (fst a) (a .snd))
  h  = liftFoTo {σ = rφ .fst} {β = σ} (bb .snd .snd .snd) φ (rφ .snd .snd)
  cover : (z : S) → ⟨ ReplImage a φ z ⟩ → ⟨ fst z ∈ Lset σ ⟩
  cover z = PT.rec (snd (fst z ∈ Lset σ)) step
    where
    step : Σ[ x ∈ S ] (⟨ x ∈ˢ a ⟩ × ⟨ (x ∷ z ∷ []) ⊨ φ ⟩) → ⟨ fst z ∈ Lset σ ⟩
    step (x , x∈a , φxz) = Lset-mono {α = σ} {β = βimg} βimg∈σ fz∈Lβimg
      where
      m = ∈-asFiber {a = fst x} {b = fst a} x∈a .fst
      qx : ⟪ fst a ⟫↪ m ≡ fst x
      qx = ∈-asFiber {a = fst x} {b = fst a} x∈a .snd
      φxₘz : ⟨ (memS m .fst ∷ z ∷ []) ⊨ φ ⟩
      φxₘz = AtStage.⊨-transport₂ σ oσ φ dφ x (memS m .fst) z (sym qx) φxz
      img≡z : imgElt m ≡ z
      img≡z = cong fst (fc (memS m .fst) (memS m .snd) .snd (z , φxₘz))
      fz∈Lβimg : ⟨ fst z ∈ Lset βimg ⟩
      fz∈Lβimg = subst (λ w → ⟨ fst w ∈ Lset βimg ⟩) img≡z (img∈Lβimg m)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Given a stage holding a set and all the constants of a Δ₀ formula,
`separateAt`{.Agda} carves the subset and `replaceAt`{.Agda} takes the image,
both landing in `L`. The whole content is `carveSat`{.Agda}: membership in the
carved set is satisfaction in the model, along a path whose links were proved in
the definability, relabelling and absoluteness chapters, with Δ₀ spent exactly
once at the last of them. What remains for the axioms proper is to produce such a
stage for an arbitrary formula, which is what reflection does.
<!--zh-->
给定一个装下某集合与某 Δ₀ 公式全部常元的阶段，`separateAt`{.Agda} 刻出子集，`replaceAt`{.Agda} 取出像，二者都落在 `L` 中。全部内容就是 `carveSat`{.Agda}：属于刻出的集合就是在模型中满足，沿着一条其各环分别由可定义性、重标与绝对性三章证出的路径，而 Δ₀ 恰在最后一环花掉一次。`mkBoundedFo`{.Agda} 随后沿递归为任何公式产出这样一个阶段，故 `separateΔ₀`{.Agda} 与 `replaceΔ₀`{.Agda} 对有界片段无条件成立：不需要反射，也不需要前沿字段。诸公理本身余下的是无界情形，那里公式的含义不绝对，必须找到一个**反射**它的阶段。
<!--/-->
