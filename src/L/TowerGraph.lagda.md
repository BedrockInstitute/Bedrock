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
open import FOL.Manipulation.Bounding using ( BoundedTm; BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo )
open import L.Coding.Base {ℓ}
  using ( tagAt; Δ₀-tagAt; tagAt-adequate; sglConAt; pairConAt
        ; ∈pair-elim; ∈pair-introL; sgl-char )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

open import Cubical.Data.FinData using ( Fin; zero; suc; toℕ )
open import Cubical.Data.Vec using ( lookup; map )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
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
## The two atoms this chapter writes fresh
<!--zh-->
## 本章新写的两个原子
<!--/-->

<!--en-->
Two of the four atoms belong to this chapter itself. The tag atom says one
slot holds a pair of a numeral and the value at another slot. The key atom
says the same without naming the second component. The hierarchy's tag
reader already says the first sentence. The lift into the model's language
carries the reader over, and it asks for one certificate only: the numeral
is constructible. The key reader is one existential above the tag reader.
The one-entry environment reading needs the key reader's constructor, so
the model's own pair stands beside the atoms.
<!--zh-->
四个原子中有两个属于本章自己。标签原子说：一个槽位持有「一个数码与另一槽位取值之对」。键原子说同一件事，但不点名第二分量。层级的标签读式已说出第一句。进入模型语言的抬升把读式运过去，且它只索取一份证书：那个数码可构造。键读式就是标签读式之上的一层存在量词。单条目环境读式需要键读式的构造子，故模型自己的对就站在原子旁边。
<!--/-->

```agda
private
  lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
             → lookup i (map fst γ) ≡ fst (lookup i γ)
  lookup-fst zero    (m ∷ γ) = refl
  lookup-fst (suc i) (m ∷ γ) = lookup-fst i γ

  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

  pair-singleton : (a : V ℓ) → ⁅ a , a ⁆ ≡ ⁅ a ⁆s
  pair-singleton a = sgl-char ⁅ a , a ⁆ a (∈pair-introL {u = a} {v = a} refl) hall
    where
    hall : (y : V ℓ) → ⟨ y ∈ ⁅ a , a ⁆ ⟩ → y ≡ a
    hall y y∈ = PT.rec (setIsSet y a) collapse
      (∈pair-elim {u = a} {v = a} {y = y} y∈)
      where
      collapse : (y ≡ a) ⊎ (y ≡ a) → y ≡ a
      collapse (inl e) = e
      collapse (inr e) = e

-- The model's own pair, and the key it builds.
prʟ : S → S → S
prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)

prʟ-fst : (a b : S) → fst (prʟ a b) ≡ pr (fst a) (fst b)
prʟ-fst a b = pairʟ-fst (pairʟ a a) (pairʟ a b)
  ∙ cong₂ ⁅_,_⁆ (pairʟ-fst a a ∙ pair-singleton (fst a)) (pairʟ-fst a b)

keyOf : ℕ → S → S
keyOf n x = prʟ (numeralL n) x

keyOf-fst : (n : ℕ) (x : S) → fst (keyOf n x) ≡ pr (# n) (fst x)
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl

private
  numeral-inL : (k : ℕ) → InL (# k)
  numeral-inL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

  certVar : ∀ {n} (i : Fin n) → BoundedTm InL (var i)
  certVar i = tt*

  certSgl : ∀ {n} (k : ℕ) → BoundedFo InL (sglConAt {n = suc n} zero (# k))
  certSgl {n} k = (numeral-inL k , certVar {suc n} zero)
                , (certVar {suc n} zero , (certVar {suc n} zero , numeral-inL k))

  certPair : ∀ {n} (k : ℕ) (x : Fin n)
           → BoundedFo InL (pairConAt {n = suc n} zero (# k) (suc x))
  certPair {n} k x = (numeral-inL k , certVar {suc n} zero)
                   , ( (certVar {suc n} (suc x) , certVar {suc n} zero)
                     , (certVar {suc n} zero
                       , ((certVar {suc n} zero , numeral-inL k)
                        , (certVar {suc n} zero
                          , certVar {suc (suc n)} (suc (suc x))))) )

  tagBounded : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n)
             → BoundedFo InL (tagAt s k x)
  tagBounded {n} s k x = (certVar {n} s , certSgl {n} k)
                       , ( (certVar {n} s , certPair {n} k x)
                         , (certVar {n} s , (certSgl {n} k , certPair {n} k x)) )

-- The tag atom, and its reading: slot `s` is a pair of the numeral `k` and
-- the value at slot `x`.
tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = liftFo (tagAt s k x) (tagBounded s k x)

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ =
    transferFo (tagAt s k x) (tagBounded s k x) (Δ₀-tagAt s k x) γ
  ∙ tagAt-adequate s k x (map fst γ)
  ∙ cong₂ PairIs (lookup-fst s γ)
      (cong₂ pr (refl {x = # k}) (lookup-fst x γ))

-- The key atom, one existential above the tag atom.
keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

keyArityAtL-out : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n)
                → ⟨ γ ⊨ keyArityAtL c k ⟩
                → ∥ (Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))) ∥₁
keyArityAtL-out c k γ = PT.map step
  where
  step : Σ[ z ∈ S ] ⟨ (z ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
       → Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))
  step (z , hz) = z , subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (z ∷ γ)) hz

keyArityAtL-in : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) (z : S)
               → fst (lookup c γ) ≡ pr (# k) (fst z)
               → ⟨ γ ⊨ keyArityAtL c k ⟩
keyArityAtL-in c k γ z e =
  ∣ z , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (z ∷ γ))) e ∣₁
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
that boundary. The tag and key atoms above stand in the chapter, and the
frame carries the other two texts: the witness atom `hasWitnessAt` and the
satisfaction graph `satGraphAt`. The description is written from all four.
The semantic readings the arm walks on, `Sat`/`keyS`/`keyʟ`/`keyBridge`/
`defSet-Sat` and the per-conjunct directions, come second, because their
types mention the fresh description. Every parameter is a named module
hypothesis, not a postulate: the later blocks discharge them, the code block
and the table block for the texts, the bridge and the per-conjunct blocks
for the readings.
<!--zh-->
本章对载体 `A` 泛型化，`A` 是一个抽象可构造集，与门探针完全一致：走读从不点名具体的 `sett` 体，只有在消费方供给它时才在真实集合处实例化 (P-h)。载体周围是描述所需的四个派生名：把 `A` 的成员嵌入宇宙、把嵌入证书做成类结构的常元、以及把 `A` 诸成员上的公式重标进 `L` 之上的 `toS`。

上面的标签原子与键原子站在本章里，框架则携带另外两条文本：见证原子 `hasWitnessAt` 与满足图 `satGraphAt`。描述由这四个原子写就。臂所走读的语义读式，`Sat`/`keyS`/`keyʟ`/`keyBridge`/`defSet-Sat` 与各合取项的方向，排在其次，因为它们的类型点名新鲜描述。每个参数都是具名模块假设，不是公设：后续诸块把它们解除，码块与表块解除文本，桥与各合取项块解除读式。
<!--/-->

<!--en-->
The chapter states four arms. Each arm is a reading of one conjunct. All four
arms were parameters of `Readings`. Two arms are proved in this chapter: the
reading of the one-entry environment conjunct, `envOneAt-in`/`envOneAt-out`,
and the reading of `DefinesAt`, `DefinesAt-in`/`DefinesAt-out`/
`DefinesAt-both`. The reading of `DefinesAt` uses the environment arm. The
code reading `codeAt-in`/`codeAt-out` and the graph reading
`graphAt-holds`/`graphAt-unique` stay parameters. The code reading needs the
witness and shape machinery. The graph reading needs the table.
<!--zh-->
本章陈述四条臂。每条臂是一个合取项的读式。四条臂原本都是 `Readings` 的参数。本章证明其中两条：单条目环境合取项的读式 `envOneAt-in`/`envOneAt-out`，以及 `DefinesAt` 的读式 `DefinesAt-in`/`DefinesAt-out`/`DefinesAt-both`。`DefinesAt` 的读式用到环境那条臂。码读式 `codeAt-in`/`codeAt-out` 与图读式 `graphAt-holds`/`graphAt-unique` 仍是参数。码读式需要见证与形状机器。图读式需要那张表。
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
      where
```

<!--en-->
## The three readings this chapter proves
<!--zh-->
## 本章证明的三条读式
<!--/-->

<!--en-->
The environment reading is the one-entry special case of the extension
reader, and its two directions are the tag atom's adequacy and the model's
own pair. The defines reading is the extension reader around the
environment conjunct, and its three directions reuse the environment
reading. Both follow the delivered proofs, written against the fresh atoms.
<!--zh-->
环境读式是外延读式的单条目特例，其两个方向就是标签原子的适足等式与模型自己的对。defines 读式是绕在环境合取项之外的外延读式，其三个方向复用环境读式。两者都循着交付时的证明，对着新鲜原子写就。
<!--/-->

```agda
      private
        module EnvOneReadings {n : ℕ} (e y : Fin n) (γ : S ^ n) where
          E : S
          E = lookup e γ

          v : V ℓ
          v = fst (lookup y γ)

          readEntry : (z : S) → ⟨ fst z ∈ envOne v ⟩ → fst z ≡ pr (# 0) v
          readEntry z = PT.rec (setIsSet (fst z) (pr (# 0) v)) step
            where
            step : Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin 1) ]
                     (pr (# (toℕ (lower li))) v ≡ fst z)
                 → fst z ≡ pr (# 0) v
            step (lift zero , q) = sym q
            step (lift (suc ()) , _)

          entry∈ : (z : S) → fst z ≡ pr (# 0) v → ⟨ fst z ∈ envOne v ⟩
          entry∈ z q = ∣ lift zero , sym q ∣₁

          envOneAt-in : fst E ≡ envOne v → ⟨ γ ⊨ envOneAt e y ⟩
          envOneAt-in q = extAt-in-both e (tagAtL zero 0 (suc y)) γ fwd bwd
            where
            fwd : (z : S) → ⟨ fst z ∈ fst E ⟩ → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩
            fwd z z∈ = subst ⟨_⟩ (sym (tagAtL-adequate zero 0 (suc y) (z ∷ γ)))
              (readEntry z (subst (λ w → ⟨ fst z ∈ w ⟩) q z∈))

            bwd : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩ → ⟨ fst z ∈ fst E ⟩
            bwd z h = subst (λ w → ⟨ fst z ∈ w ⟩) (sym q)
              (entry∈ z (subst ⟨_⟩ (tagAtL-adequate zero 0 (suc y) (z ∷ γ)) h))

          envOneAt-out : ⟨ γ ⊨ envOneAt e y ⟩ → fst E ≡ envOne v
          envOneAt-out h = extensionality (fst E) (envOne v) (sub₁ , sub₂)
            where
            sub₁ : ⟨ fst E ⊆ envOne v ⟩
            sub₁ w w∈ₛ = ∈∈ₛ {a = w} {b = envOne v} .fst
              (entry∈ wS (subst ⟨_⟩
                (tagAtL-adequate zero 0 (suc y) (wS ∷ γ))
                (extAt-out e (tagAtL zero 0 (suc y)) γ h wS w∈)))
              where
              w∈ : ⟨ w ∈ fst E ⟩
              w∈ = ∈∈ₛ {a = w} {b = fst E} .snd w∈ₛ

              wS : S
              wS = w , isL-trans {x = fst E} {y = w} w∈ (snd E)

            sub₂ : ⟨ envOne v ⊆ fst E ⟩
            sub₂ w w∈ₛ = ∈∈ₛ {a = w} {b = fst E} .fst
              (PT.rec (snd (w ∈ fst E)) step₂
                (∈∈ₛ {a = w} {b = envOne v} .snd w∈ₛ))
              where
              hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩
              hasKey = extAt-in e (tagAtL zero 0 (suc y)) γ h (keyOf 0 (lookup y γ))
                (subst ⟨_⟩
                  (sym (tagAtL-adequate zero 0 (suc y) (keyOf 0 (lookup y γ) ∷ γ)))
                  (keyOf-fst 0 (lookup y γ)))

              step₂ : Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin 1) ]
                        (pr (# (toℕ (lower li))) v ≡ w)
                    → ⟨ w ∈ fst E ⟩
              step₂ (lift zero , q) =
                subst (λ u → ⟨ u ∈ fst E ⟩) (keyOf-fst 0 (lookup y γ) ∙ q) hasKey
              step₂ (lift (suc ()) , _)

      envOneAt-in : ∀ {n} (e y : Fin n) (γ : S ^ n)
                  → fst (lookup e γ) ≡ envOne (fst (lookup y γ))
                  → ⟨ γ ⊨ envOneAt e y ⟩
      envOneAt-in {n} e y γ = EnvOneReadings.envOneAt-in {n} e y γ

      envOneAt-out : ∀ {n} (e y : Fin n) (γ : S ^ n)
                   → ⟨ γ ⊨ envOneAt e y ⟩
                   → fst (lookup e γ) ≡ envOne (fst (lookup y γ))
      envOneAt-out {n} e y γ = EnvOneReadings.envOneAt-out {n} e y γ

      private
        module DefinesReadings {n : ℕ} (x w v : Fin n) (γ : S ^ n) where
          inner : Formula S (suc n)
          inner = ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

          body : Formula S (suc n)
          body = (var zero ∈̇ var (suc w)) ∧̇ inner

          readInner : (z : S) → ⟨ (z ∷ γ) ⊨ inner ⟩
                    → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
          readInner z = PT.rec (snd (envOne (fst z) ∈ fst (lookup v γ))) step
            where
            step : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ)
                     ⊨ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
                 → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
            step (E , (hE , E∈)) = subst (λ u → ⟨ u ∈ fst (lookup v γ) ⟩)
              (envOneAt-out zero (suc zero) (E ∷ z ∷ γ) hE) E∈

          fillInner : (z : S) → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
                    → ⟨ (z ∷ γ) ⊨ inner ⟩
          fillInner z h =
            ∣ E , (envOneAt-in zero (suc zero) (E ∷ z ∷ γ) refl , h) ∣₁
            where
            E : S
            E = envOne (fst z)
              , isL-trans {x = fst (lookup v γ)} {y = envOne (fst z)} h
                  (snd (lookup v γ))

          DefinesAt-out : ⟨ γ ⊨ DefinesAt x w v ⟩
                        → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → HoldsDef w v γ z
          DefinesAt-out h z z∈ = hz .fst , readInner z (hz .snd)
            where
            hz : ⟨ (z ∷ γ) ⊨ body ⟩
            hz = extAt-out x body γ h z z∈

          DefinesAt-in : ⟨ γ ⊨ DefinesAt x w v ⟩
                       → (z : S) → HoldsDef w v γ z → ⟨ fst z ∈ fst (lookup x γ) ⟩
          DefinesAt-in h z (hw , hv) =
            extAt-in x body γ h z (hw , fillInner z hv)

          DefinesAt-both : ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → HoldsDef w v γ z)
                         → ((z : S) → HoldsDef w v γ z → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                         → ⟨ γ ⊨ DefinesAt x w v ⟩
          DefinesAt-both f g = extAt-in-both x body γ
            (λ z z∈ → f z z∈ .fst , fillInner z (f z z∈ .snd))
            (λ z h → g z (h .fst , readInner z (h .snd)))

      DefinesAt-in : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                   → ⟨ γ ⊨ DefinesAt x w v ⟩
                   → (z : S) → HoldsDef w v γ z
                   → ⟨ fst z ∈ fst (lookup x γ) ⟩
      DefinesAt-in {n} x w v γ = DefinesReadings.DefinesAt-in {n} x w v γ

      DefinesAt-out : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                    → ⟨ γ ⊨ DefinesAt x w v ⟩
                    → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩
                    → HoldsDef w v γ z
      DefinesAt-out {n} x w v γ = DefinesReadings.DefinesAt-out {n} x w v γ

      DefinesAt-both : ∀ {n} (x w v : Fin n) (γ : S ^ n)
                     → ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → HoldsDef w v γ z)
                     → ((z : S) → HoldsDef w v γ z → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                     → ⟨ γ ⊨ DefinesAt x w v ⟩
      DefinesAt-both {n} x w v γ = DefinesReadings.DefinesAt-both {n} x w v γ
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
internalization frame as two named module telescopes (the witness atom and
the satisfaction graph; then the semantic readings), the tag and key atoms
and the three readings proved from them, and the one measured arm, `DefAt`'s
adequacy in both directions. Nothing imports a retiring master; the frame is
the interface the remaining blocks instantiate, and the arm is the pattern
they follow.
<!--zh-->
本章落下新鲜家园：双槽描述 `DefAt₂` 及其泛型 `DefAt` 文本，写在存活接口之上；内化框架作为两个具名模块望远镜 (先是见证原子与满足图，再是语义读式)；标签原子与键原子、以及由它们证出的三条读式；以及那一条被量过的一条臂，即 `DefAt` 双向的充分性。此处不导入任何退役主章；框架就是其余诸块所实例化的接口，而这条臂是它们所循的模式。
<!--/-->
