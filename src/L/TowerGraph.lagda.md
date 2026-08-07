# The L-tower graph: the two-slot description and its first arm

<!--en-->
This is the fresh surviving home for the L-tower graph's object-level
description, the first block of Build A (ruling D31). The cone this content
was delivered in, `L.Coding` minus `Base`, is in the D18 retirement set, so
this chapter writes the description's text against the surviving interface
(`L.Definability`'s `defSet` and `smallSat`, `L.Constructible`'s `𝒮ʟ`, `𝒟ₒ`
and its two directions, and the `FOL` layer) and takes the satisfaction
internalization itself as named module parameters: the frame the later arms
instantiate. Nothing here imports a retiring master.

The description is the two-slot form the condensation consumes: a
`Formula Sʟ 2` whose slot 0 is the value and slot 1 is the index, readable at
both the ambient and the inner satisfaction. The arm landed by the D22 gate,
`[T132]`'s, is ported here against the frame: the two-directional adequacy of
`DefAt` through the surviving `defSet` and `𝒟ₒ` interface, at the inner
reading the `Lset-only` determination runs at. Later blocks supply the code
machinery, the twelve-clause table and the remaining arms by instantiating
the frame.
<!--zh-->
这是 L-塔图对象级描述的新存活家园，是 Build A (裁定 D31) 的第一块。这份内容当初交付所处的锥体 `L.Coding` 减去 `Base` 属于 D18 退役集，故本章把描述文本写在存活接口之上 (`L.Definability` 的 `defSet` 与 `smallSat`、`L.Constructible` 的 `𝒮ʟ`、`𝒟ₒ` 及其两个方向、以及 `FOL` 层)，并把满足内化本身取作具名模块参数：即后续诸臂所实例化的框架。此处不导入任何退役主章。

这条描述就是凝结章所消费的双槽形态：一条 `Formula Sʟ 2`，槽 0 是取值、槽 1 是指标，在环境读式与内层读式两处皆可读。D22 门所落下的那条臂，即 `[T132]` 的那条，在此对着框架移植：`DefAt` 经由存活 `defSet` 与 `𝒟ₒ` 接口的双向充分性，落在 `Lset-only` 判定所运行的那个内层读式上。后续诸块以实例化框架的方式供给码机制、十二子句表与其余诸臂。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.TowerGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )

open import Cubical.Data.FinData using ( Fin; zero; suc; toℕ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
open import V.Coding {ℓ} using ( pr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Foundations.HLevels using ( isProp× )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The atoms the description is written from
<!--zh-->
## 描述所由写的原子
<!--/-->

<!--en-->
Three pieces belong to this chapter itself, before the frame: the
environment encoding, the extension formula, and the side condition. An
environment of length `n` becomes the set of pairs of an index's numeral
with the value there, so a one-entry environment is the two-line special
case; the description's third conjunct reads exactly such environments. The
extension formula says a slot holds the set of exactly those things
satisfying a condition, as two implications under two quantifiers, and its
readings are the two projections, so nothing is proved here at all. The
side condition `DefOK` closes the gap `[T130]` named: an object-language
quantifier ranges over `L`, so the description can only pick out
constructible sets, and `DefOK A` records that every definable subset of the
carrier is constructible, which is exactly what the elimination needs when
the carrier arrives at a slot rather than in a caller's hand.
<!--zh-->
框架之前有三件属于本章自己的东西：环境编码、外延公式与旁条件。长度为 `n` 的环境成为「序号的数码与该处取值」之对的集合，于是单条目环境就是两行的特例；描述第三个合取项读的恰是这种环境。外延公式说一位持有「恰好满足某条件的那些东西」之集，写成两个量词下的两条蕴含，其两种读法就是两个投影，故此处什么也没有证。旁条件 `DefOK` 堵上 `[T130]` 点名的缝：对象语言量词在 `L` 上取值，故描述只能挑出可构造集，而 `DefOK A` 记录「载体的每个可定义子集都可构造」，这正是载体以槽位而非以调用方之手到来时消去所必需的东西。
<!--/-->

```agda
-- The environment of a finite index family, as a set of pairs, and the
-- one-entry environment the description's third conjunct reads.
env : ∀ {n} → (Fin n → V ℓ) → V ℓ
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))

envOne : V ℓ → V ℓ
envOne y = env {1} (λ _ → y)

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

-- The extension formula: slot `y` holds the set of exactly those members
-- satisfying `φ`. Its two readings are the two projections.
extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd

  extAt-in-both : ((z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
                → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
                → ⟨ γ ⊨ extAt y φ ⟩
  extAt-in-both f g = f , g

-- The side condition the elimination travels with.
DefOK : S → Type (ℓ-suc ℓ)
DefOK A = (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst A) ⟩ → ⟨ isL x ⟩
```

<!--en-->
## The carrier and the frame
<!--zh-->
## 载体与框架
<!--/-->

<!--en-->
The chapter is generic over the carrier `A`, an abstract constructible set,
exactly as the gate's probe was: the walk never mentions a concrete `sett`
body, and the instantiation at a real set happens only when a consumer
supplies it (P-h). Around the carrier sit the four derived names the
description needs: the embedding of a member of `A` into the universe, the
membership certificate that makes it a constant of the class structure, and
the relabelling `toS` that carries a formula over `A`'s members into one
over `L`.

The internalization frame is the chapter's second telescope, in two levels,
for the same reason `StepStory`'s clause telescope exists: the content it
names lives only in the frozen retirement set and nothing may import across
that boundary. The formula texts the description's conjuncts read, the code
atoms `tagAtL`/`keyArityAtL`/`hasWitnessAt` and the satisfaction graph
`satGraphAt`, come first, because the description's own text is written from
them. The semantic readings the arm walks on, `Sat`/`keyS`/`keyʟ`/`keyBridge`/
`defSet-Sat` and the per-conjunct directions, come second, because their
types mention the fresh description. Every parameter is a named module
hypothesis, not a postulate: the later blocks discharge them, the code block
and the table block for the texts, the bridge and the per-conjunct blocks
for the readings.
<!--zh-->
本章对载体 `A` 泛型化，`A` 是一个抽象可构造集，与门探针完全一致：走读从不点名具体的 `sett` 体，只有在消费方供给它时才在真实集合处实例化 (P-h)。载体周围是描述所需的四个派生名：把 `A` 的成员嵌入宇宙、把嵌入证书做成类结构的常元、以及把 `A` 诸成员上的公式重标进 `L` 之上的 `toS`。

内化框架是本章的第二重望远镜，分两层，理由与 `StepStory` 的子句望远镜相同：它所点名的内容只活在冻结的退役集里，而任何东西都不得跨过那条边界进口。描述诸合取项所读的公式文本，即码原子 `tagAtL`/`keyArityAtL`/`hasWitnessAt` 与满足图 `satGraphAt`，排在最前，因为描述自己的文本由它们写就。臂所走读的语义读式，`Sat`/`keyS`/`keyʟ`/`keyBridge`/`defSet-Sat` 与各合取项的方向，排在其次，因为它们的类型点名新鲜描述。每个参数都是具名模块假设，不是公设：后续诸块把它们解除，码块与表块解除文本，桥与各合取项块解除读式。
<!--/-->

```agda
module _ (A : S) where
  module DA = DefOf (fst A)

  ιA : ⟪ fst A ⟫ → V ℓ
  ιA = ⟪ fst A ⟫↪

  ιA∈ : (m : ⟪ fst A ⟫) → ⟨ ιA m ∈ fst A ⟩
  ιA∈ m = ∈∈ₛ {a = ιA m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  asConst : ⟪ fst A ⟫ → S
  asConst m = ιA m , isL-trans (ιA∈ m) (snd A)

  toS : Formula ⟪ fst A ⟫ 1 → Formula S 1
  toS ψ = mapFo asConst ψ

  module Frame
    (tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n)
    (keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n)
    (hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n)
    (satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    where

    -- The two-slot description, written from the frame's atoms.  Slot 0 of
    -- `DefAt₂` is the value, slot 1 the index; as a formula over `S = Sʟ`
    -- both the ambient and the inner satisfaction apply to it.
    envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
    envOneAt e y = extAt e (tagAtL zero 0 (suc y))

    isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
    isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

    DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                              ∧̇ ∃̇ ( envOneAt zero (suc zero)
                                   ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

    DefBody : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
    DefBody w = isCodeAt (suc zero) (sh3 w)
                ∧̇ ( satGraphAt (sh3 w) (suc zero) zero
                  ∧̇ DefinesAt (suc (suc zero)) (sh3 w) zero )

    DefAt : ∀ {n} → Fin n → Fin n → Formula S n
    DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))

    DefAt₂ : Formula S 2
    DefAt₂ = DefAt zero (suc zero)

    HoldsDef : ∀ {n} (w v : Fin n) (γ : S ^ n) (z : S) → Type (ℓ-suc ℓ)
    HoldsDef w v γ z = ⟨ fst z ∈ fst (lookup w γ) ⟩
                       × ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩

    module Readings
      (Sat : Formula S 1 → S)
      (keyS : Formula ⟪ fst A ⟫ 1 → S)
      (keyʟ : Formula S 1 → S)
      (keyBridge : (ψ : Formula ⟪ fst A ⟫ 1)
                 → fst (keyS ψ) ≡ fst (keyʟ (toS ψ)))
      (defSet-Sat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
                  → (ιA m ∈ DA.defSet ψ)
                  ≡ (envOne (ιA m) ∈ fst (Sat (toS ψ))))
      (codeAt-in : ∀ {n} (c w : Fin n) (γ : S ^ n)
                 → fst (lookup w γ) ≡ fst A
                 → (ψ : Formula ⟪ fst A ⟫ 1) → fst (lookup c γ) ≡ fst (keyS ψ)
                 → ⟨ γ ⊨ isCodeAt c w ⟩)
      (codeAt-out : ∀ {n} (c w : Fin n) (γ : S ^ n)
                  → fst (lookup w γ) ≡ fst A
                  → ⟨ γ ⊨ isCodeAt c w ⟩
                  → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                        (fst (lookup c γ) ≡ fst (keyS ψ))) ∥₁)
      (graphAt-holds : (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
                     → fst (lookup w γ) ≡ fst A
                     → fst (lookup c γ) ≡ fst (keyʟ φ)
                     → fst (lookup v γ) ≡ fst (Sat φ)
                     → ⟨ γ ⊨ satGraphAt w c v ⟩)
      (graphAt-unique : (φ : Formula S 1) → ∀ {n} (w c v : Fin n) (γ : S ^ n)
                      → fst (lookup w γ) ≡ fst A
                      → fst (lookup c γ) ≡ fst (keyʟ φ)
                      → ⟨ γ ⊨ satGraphAt w c v ⟩
                      → fst (lookup v γ) ≡ fst (Sat φ))
      (DefinesAt-in : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                    → ⟨ γ ⊨ DefinesAt x w v ⟩
                    → (z : S) → HoldsDef w v γ z
                    → ⟨ fst z ∈ fst (lookup x γ) ⟩)
      (DefinesAt-out : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                     → ⟨ γ ⊨ DefinesAt x w v ⟩
                     → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩
                     → HoldsDef w v γ z)
      (DefinesAt-both : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                      → ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩
                                 → HoldsDef w v γ z)
                      → ((z : S) → HoldsDef w v γ z
                                 → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                      → ⟨ γ ⊨ DefinesAt x w v ⟩)
      where
```

<!--en-->
## The arm: `DefAt`'s adequacy, both directions
<!--zh-->
## 那条臂：`DefAt` 的充分性，两个方向
<!--/-->

<!--en-->
The ported arm closes the description against the surviving interface in
both directions. In, a named member `z ≡ defSet ψ` of the definable
powerset is assembled into satisfaction of the object description, with the
value taken to be the internalized satisfaction and the code the relabelled
key. Out, satisfaction of the description names a formula and the
extensional identity `defSet ψ ≡ z`, through the code and graph uniqueness.
The two `where` branches under each truncation carry written types (I-5),
and the formula index of the uniqueness application is explicit (`toS ψ`
named, I-4), which is exactly the shape the gate measured as the cheap one.
The carrier-level closure then reads the description's own extension
against `𝒟ₒ` in both directions, with `DefOK` discharged by the caller.
<!--zh-->
这条移植过来的臂在两个方向上都把描述对着存活接口合拢。进入方向：可定义幂集的一个具名成员 `z ≡ defSet ψ` 被装配成对象描述的满足，取值取作内化满足、码取作重标后的键。出去方向：描述的满足点名一条公式与外延等式 `defSet ψ ≡ z`，经码与图唯一性。每条截断之下的两个 `where` 分支都带书面类型 (I-5)，唯一性应用的公式指标显式 (`toS ψ` 具名，I-4)，这正是门所量出的廉价形状。载体验证级闭包随后把描述自己的外延对着 `𝒟ₒ` 双向读出，`DefOK` 由调用方解除。
<!--/-->

```agda
      Fibre : Formula ⟪ fst A ⟫ 1 → V ℓ → Type (ℓ-suc ℓ)
      Fibre ψ y = Σ[ p ∈ Σ[ m ∈ ⟪ fst A ⟫ ] ⟨ DA.smallSat ψ m ⟩ ]
                    (ιA (p .fst) ≡ y)

      inSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
            → ⟨ ιA m ∈ DA.defSet ψ ⟩
            → ⟨ envOne (ιA m) ∈ fst (Sat (toS ψ)) ⟩
      inSat ψ m h = subst ⟨_⟩ (defSet-Sat ψ m) h

      outSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
             → ⟨ envOne (ιA m) ∈ fst (Sat (toS ψ)) ⟩
             → ⟨ ιA m ∈ DA.defSet ψ ⟩
      outSat ψ m h = subst ⟨_⟩ (sym (defSet-Sat ψ m)) h

      fill : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
           → (z : S) (ψ : Formula ⟪ fst A ⟫ 1) → DA.defSet ψ ≡ fst z
           → ⟨ (Sat (toS ψ) ∷ keyS ψ ∷ z ∷ γ) ⊨ DefBody w ⟩
      fill {n} w γ qw z ψ qz = hcode , (hgraph , hdef)
        where
        δ : S ^ (suc (suc (suc n)))
        δ = Sat (toS ψ) ∷ keyS ψ ∷ z ∷ γ

        hcode : ⟨ δ ⊨ isCodeAt (suc zero) (sh3 w) ⟩
        hcode = codeAt-in (suc zero) (sh3 w) δ qw ψ refl

        hgraph : ⟨ δ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
        hgraph = graphAt-holds (toS ψ) (sh3 w) (suc zero) zero δ qw
                   (keyBridge ψ) refl

        Holds : S → Type (ℓ-suc ℓ)
        Holds y = ⟨ fst y ∈ fst (lookup w γ) ⟩
                  × ⟨ envOne (fst y) ∈ fst (Sat (toS ψ)) ⟩

        into : (y : S) → ⟨ fst y ∈ fst z ⟩ → Holds y
        into y y∈ = PT.rec
          (isProp× (snd (fst y ∈ fst (lookup w γ)))
                   (snd (envOne (fst y) ∈ fst (Sat (toS ψ)))))
          step (subst (λ X → ⟨ fst y ∈ X ⟩) (sym qz) y∈)
          where
          step : Fibre ψ (fst y) → Holds y
          step ((m , hm) , qm) =
              subst (λ u → ⟨ u ∈ fst (lookup w γ) ⟩) qm
                (subst (λ X → ⟨ ιA m ∈ X ⟩) (sym qw) (ιA∈ m))
            , subst (λ u → ⟨ envOne u ∈ fst (Sat (toS ψ)) ⟩) qm
                (inSat ψ m ∣ (m , hm) , refl ∣₁)

        back : (y : S) → Holds y → ⟨ fst y ∈ fst z ⟩
        back y (yw , ys) = subst (λ X → ⟨ fst y ∈ X ⟩) qz
          (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
            (outSat ψ (fib .fst)
              (subst (λ u → ⟨ envOne u ∈ fst (Sat (toS ψ)) ⟩)
                (sym (fib .snd)) ys)))
          where
          fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ fst y)
          fib = ∈-asFiber {a = fst y} {b = fst A}
            (subst (λ X → ⟨ fst y ∈ X ⟩) qw yw)

        hdef : ⟨ δ ⊨ DefinesAt (suc (suc zero)) (sh3 w) zero ⟩
        hdef = DefinesAt-both (suc (suc zero)) (sh3 w) zero δ into back

      read : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
           → (z c v : S) → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
           → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
      read {n} w γ qw z c v (hcode , (hgraph , hdef)) =
        PT.rec squash₁ step (codeAt-out (suc zero) (sh3 w) δ qw hcode)
        where
        δ : S ^ (suc (suc (suc n)))
        δ = v ∷ c ∷ z ∷ γ

        step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst c ≡ fst (keyS ψ))
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
        step (ψ , qc) = ∣ ψ , extensionality (DA.defSet ψ) (fst z) (sub₁ , sub₂) ∣₁
          where
          qv : fst v ≡ fst (Sat (toS ψ))
          qv = graphAt-unique (toS ψ) (sh3 w) (suc zero) zero δ qw
                 (qc ∙ keyBridge ψ) hgraph

          sub₁ : ⟨ DA.defSet ψ ⊆ fst z ⟩
          sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst z} .fst
            (PT.rec (snd (y ∈ fst z)) place
              (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈ₛ))
            where
            place : Fibre ψ y → ⟨ y ∈ fst z ⟩
            place ((m , hm) , qm) =
              DefinesAt-in (suc (suc zero)) (sh3 w) zero δ hdef
                (y , isL-trans {x = fst A} {y = y}
                       (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m)) (snd A))
                ( subst (λ X → ⟨ y ∈ X ⟩) (sym qw)
                    (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m))
                , subst (λ X → ⟨ envOne y ∈ X ⟩) (sym qv)
                    (subst (λ u → ⟨ envOne u ∈ fst (Sat (toS ψ)) ⟩) qm
                      (inSat ψ m ∣ (m , hm) , refl ∣₁)) )

          sub₂ : ⟨ fst z ⊆ DA.defSet ψ ⟩
          sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
            (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
              (outSat ψ (fib .fst)
                (subst (λ u → ⟨ envOne u ∈ fst (Sat (toS ψ)) ⟩) (sym (fib .snd))
                  (subst (λ X → ⟨ envOne y ∈ X ⟩) qv (cond .snd)))))
            where
            y∈ : ⟨ y ∈ fst z ⟩
            y∈ = ∈∈ₛ {a = y} {b = fst z} .snd y∈ₛ

            yS : S
            yS = y , isL-trans {x = fst z} {y = y} y∈ (snd z)

            cond : ⟨ y ∈ fst (lookup w γ) ⟩ × ⟨ envOne y ∈ fst v ⟩
            cond = DefinesAt-out (suc (suc zero)) (sh3 w) zero δ hdef yS y∈

            fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ y)
            fib = ∈-asFiber {a = y} {b = fst A}
              (subst (λ X → ⟨ y ∈ X ⟩) qw (cond .fst))

      describe : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
               → (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
               → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
      describe w γ qw z = PT.rec squash₁ viaCode
        where
        Target : Type (ℓ-suc ℓ)
        Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁

        viaValue : (c : S)
                 → Σ[ v ∈ S ] ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩ → Target
        viaValue c (v , hv) = read w γ qw z c v hv

        viaCode : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (DefBody w) ⟩ → Target
        viaCode (c , hc) = PT.rec squash₁ (viaValue c) hc

      assemble : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
               → (z : S)
               → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
               → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
      assemble w γ qw z = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)))) step
        where
        step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)
             → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
        step (ψ , qψ) = ∣ keyS ψ , ∣ Sat (toS ψ) , fill w γ qw z ψ qψ ∣₁ ∣₁

      DefAt-in : ∀ {n} (u w : Fin n) (γ : S ^ n)
               → fst (lookup w γ) ≡ fst A
               → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
               → ⟨ γ ⊨ DefAt u w ⟩
      DefAt-in {n} u w γ qw qu = extAt-in-both u Φ γ f g
        where
        Φ : Formula S (suc n)
        Φ = ∃̇ (∃̇ (DefBody w))

        f : (z : S) → ⟨ fst z ∈ fst (lookup u γ) ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
        f z z∈ = assemble w γ qw z
          (𝒟ₒ-inv (fst A) (fst z) (subst (λ X → ⟨ fst z ∈ X ⟩) qu z∈))

        g : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ fst (lookup u γ) ⟩
        g z hz = subst (λ X → ⟨ fst z ∈ X ⟩) (sym qu)
          (𝒟ₒ-intro (fst A) (fst z) (describe w γ qw z hz))

      DefAt-out : ∀ {n} (u w : Fin n) (γ : S ^ n) → DefOK A
                → fst (lookup w γ) ≡ fst A
                → ⟨ γ ⊨ DefAt u w ⟩
                → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
      DefAt-out {n} u w γ ok qw h =
        extensionality (fst (lookup u γ)) (𝒟ₒ (fst A)) (sub₁ , sub₂)
        where
        Φ : Formula S (suc n)
        Φ = ∃̇ (∃̇ (DefBody w))

        sub₁ : ⟨ fst (lookup u γ) ⊆ 𝒟ₒ (fst A) ⟩
        sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .fst
          (𝒟ₒ-intro (fst A) y (describe w γ qw yS (extAt-out u Φ γ h yS y∈)))
          where
          y∈ : ⟨ y ∈ fst (lookup u γ) ⟩
          y∈ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .snd y∈ₛ

          yS : S
          yS = y , isL-trans {x = fst (lookup u γ)} {y = y} y∈ (snd (lookup u γ))

        sub₂ : ⟨ 𝒟ₒ (fst A) ⊆ fst (lookup u γ) ⟩
        sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .fst
          (extAt-in u Φ γ h yS
            (assemble w γ qw yS (𝒟ₒ-inv (fst A) y y∈)))
          where
          y∈ : ⟨ y ∈ 𝒟ₒ (fst A) ⟩
          y∈ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .snd y∈ₛ

          yS : S
          yS = y , ok y y∈
```

<!--en-->
## The two-slot form, closed
<!--zh-->
## 双槽形态，合拢
<!--/-->

<!--en-->
At arity two the generic adequacy is exactly the two-slot contract the
condensation consumes: the value at slot 0 and the index at slot 1, read at
the inner satisfaction, with `DefOK A` on the elimination. The ambient
reading of the same object formula is defined (it is the same `Formula Sʟ 2`),
and its agreement with the inner reading is the later transfer obligation,
not this block: `[T130]` placed `TransferL`/`ValueIsL` in the `W1p` row.
<!--zh-->
在元数二处，泛型充分性恰是凝结章所消费的双槽契约：取值在槽 0、指标在槽 1，于内层读式处读出，消去那一半带着 `DefOK A`。同一对象公式的环境读式当然有定义 (它是同一条 `Formula Sʟ 2`)，而它与内层读式的一致是更晚的转移义务，不属此块：`[T130]` 把 `TransferL`/`ValueIsL` 放进 `W1p` 行。
<!--/-->

```agda
      DefAt₂-in : (γ : S ^ 2) → fst (lookup (suc zero) γ) ≡ fst A
                → fst (lookup zero γ) ≡ 𝒟ₒ (fst A)
                → ⟨ γ ⊨ DefAt₂ ⟩
      DefAt₂-in = DefAt-in zero (suc zero)

      DefAt₂-out : (γ : S ^ 2) → DefOK A → fst (lookup (suc zero) γ) ≡ fst A
                 → ⟨ γ ⊨ DefAt₂ ⟩ → fst (lookup zero γ) ≡ 𝒟ₒ (fst A)
      DefAt₂-out = DefAt-out zero (suc zero)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter lands the fresh home: the two-slot description `DefAt₂` and its
generic `DefAt` text, written against the surviving interface, the
internalization frame as two named module telescopes (the code atoms and the
satisfaction graph; then the semantic readings), and the one measured arm,
`DefAt`'s adequacy in both directions. Nothing imports a retiring master;
the frame is the interface the remaining blocks instantiate, and the arm is
the pattern they follow.
<!--zh-->
本章落下新鲜家园：双槽描述 `DefAt₂` 及其泛型 `DefAt` 文本，写在存活接口之上；内化框架作为两个具名模块望远镜 (先是码原子与满足图，再是语义读式)；以及那一条被量过的一条臂，即 `DefAt` 双向的充分性。此处不导入任何退役主章；框架就是其余诸块所实例化的接口，而这条臂是它们所循的模式。
<!--/-->
