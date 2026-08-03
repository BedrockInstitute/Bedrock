# One Def stage inside the rud tower

<!--en-->
The bridge's reduction rests on three named facts, and the first of them is this
chapter's subject: a constructible stage that the rud tower already holds as a
member keeps that status one Def step later. Read at the level of sets rather
than of elements, the statement says that the **set** of all definable subsets of
a carrier is itself a rud member, which is a different question from the one the
satisfaction engine answers. The engine places each definable subset in the
closure, one formula at a time; placing their totality asks for the family to be
collected, and a family indexed by the syntax is not collected by any image or
separation of the sets the engine builds.

What is reachable is everything else, and it is proved here: the successor
collapse that turns the target into a statement about the definable power, the
stage bounding that finds a common rud stage for two members, the separation
that carves the definable power out of a bounding fragment, and the discharge of
the bridge's hypothesis from that fragment. The fragment itself is named, typed
and left standing.
<!--zh-->
桥的归约立在三条具名事实上，其中头一条正是本章的主题：初步函数塔已经作为成员收下的可构造阶段，再走一步 Def 之后仍保有该身份。若在集合而非元素的层面读它，该陈述说的是：某载体的全体可定义子集所成之**集**自身是初步函数成员，这与满足集引擎所答的问题并不相同。引擎把每个可定义子集放进闭包，一次一条公式；而放进它们的全体，要求把这个族收拢起来，而以语法为索引的族，不是引擎所造诸集的任何取像或分离所能收拢的。

可及者是其余一切，并在此证出：把目标转成关于可定义幂的陈述的后继坍缩、为两个成员找到共同初步函数阶段的阶段定界、从定界片段中刻出可定义幂的分离，以及从该片段兑付桥的假设。片段自身具名、定型，并原样留在那里。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.DefInJ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using
  ( Lset; Lset-in; Lset-out; Lset-layer; layer-trans
  ; 𝒟ₒ; 𝒟ₒ-inv; Lset⊆𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rud.Step {ℓ} lem A using
  ( step; Sset; Sset-out; Sset-mem; Sset-mono; Sset-suc; Sset-trans
  ; Jset-rud; limit-succ-mem )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; limit-mem-ord )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The successor collapse

A stage at a successor index is the definable power of the stage below it, on
the nose. Going up is the tower's own introduction at the index's largest
member; coming down splits a member of the successor into a strictly smaller
index or the index itself, and the strictly smaller case is absorbed because a
stage is one of its own definable subsets. The equation is what turns the
target into a statement about a single set.
<!--zh-->
## 后继坍缩

后继索引处的阶段，恰是其下阶段的可定义幂。上行是塔在该索引最大成员处自带的引入；下行把后继的一个成员分成严格更小的索引或索引自身，而严格更小的情形被吸收，因为阶段是自己的可定义子集之一。这条等式正是把目标转成关于单个集合的陈述之物。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

Lsuc≡Def : (ζ : S) → Lset (sucV ζ) ≡ 𝒟ₒ (Lset ζ)
Lsuc≡Def ζ = ext-⊆ sub sup
  where
  sub : (x : S) → ⟨ x ∈ˢ Lset (sucV ζ) ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩
  sub x h = PT.rec (snd (x ∈ˢ 𝒟ₒ (Lset ζ))) go (Lset-out (sucV ζ) x h)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ sucV ζ ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩
    go (δ , δ∈ , hx) = ∈sucV-elim {A = ζ} {x = δ}
      (snd (x ∈ˢ 𝒟ₒ (Lset ζ))) δ∈
      (λ δ∈ζ → Lset⊆𝒟ₒ ζ x (Lset-in ζ δ x δ∈ζ hx))
      (λ δ≡ζ → subst (λ w → ⟨ x ∈ˢ 𝒟ₒ (Lset w) ⟩) δ≡ζ hx)
  sup : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
  sup x h = Lset-in (sucV ζ) ζ x (self∈sucV ζ) h
```

<!--en-->
## Stage bounding

A member of a limit level of the rud tower enters at some level strictly below,
and two members enter at a common one: the two entry indices are ordinals, so
trichotomy picks the larger and monotonicity carries the other one up. This is
the rud-tower twin of the constructible common-stage lemma the bridge already
uses, and it is what supplies the transitive carrier the separation runs over.
<!--zh-->
## 阶段定界

初步函数塔某极限层的成员，在其下某层严格进场；两个成员则在同一层进场：两个进场索引都是序数，故三歧取较大者，单调性把另一个抬上去。这是桥已在使用的可构造共同阶段引理在初步函数塔一侧的孪生，也正是分离所跨越的传递载体的供给者。
<!--/-->

```agda
Sstage : (γ : S) → ⟨ isLimit γ ⟩ → (x : S) → ⟨ x ∈ˢ Sset γ ⟩
       → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Sset δ ⟩) ∥₁
Sstage γ limγ x h = PT.map go (Sset-out γ x h)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩)
     → Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Sset δ ⟩)
  go (δ , δ∈γ , hx) = sucV δ
    , ( limit-succ-mem γ δ limγ δ∈γ
      , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) hx )

Sstage₂ : (γ : S) → ⟨ isLimit γ ⟩ → (x y : S)
        → ⟨ x ∈ˢ Sset γ ⟩ → ⟨ y ∈ˢ Sset γ ⟩
        → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Sset δ ⟩ × ⟨ y ∈ˢ Sset δ ⟩) ∥₁
Sstage₂ γ limγ x y hx hy = PT.rec PT.squash₁ atX (Sstage γ limγ x hx)
  where
  G : Type (ℓ-suc ℓ)
  G = Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Sset δ ⟩ × ⟨ y ∈ˢ Sset δ ⟩)
  atX : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Sset δ ⟩) → ∥ G ∥₁
  atX (δ₁ , δ₁∈γ , x∈) = PT.map atY (Sstage γ limγ y hy)
    where
    atY : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ y ∈ˢ Sset δ ⟩) → G
    atY (δ₂ , δ₂∈γ , y∈) = pick (ord-tri δ₁ (limit-mem-ord γ limγ δ₁ δ₁∈γ)
                                         δ₂ (limit-mem-ord γ limγ δ₂ δ₂∈γ))
      where
      pick : ⟨ δ₁ ∈ˢ δ₂ ⟩ ⊎ ((δ₁ ≡ δ₂) ⊎ ⟨ δ₂ ∈ˢ δ₁ ⟩) → G
      pick (inl δ₁∈δ₂) = δ₂
        , (δ₂∈γ , Sset-mono {α = δ₂} {β = δ₁} δ₁∈δ₂ x x∈ , y∈)
      pick (inr (inl δ₁≡δ₂)) = δ₂
        , (δ₂∈γ , subst (λ w → ⟨ x ∈ˢ Sset w ⟩) δ₁≡δ₂ x∈ , y∈)
      pick (inr (inr δ₂∈δ₁)) = δ₁
        , (δ₁∈γ , x∈ , Sset-mono {α = δ₁} {β = δ₂} δ₂∈δ₁ y y∈)
```

<!--en-->
## Separation over a rud stage

The satisfaction engine is abstract in its carrier, so it applies to a rud stage
just as well as to a constructible one: every definable subset of a stage the
tower holds as a member is again a member of the limit level above it. The
formula spent here is the one that says "a member of the fragment all of whose
members lie in the carrier", two constants and one bounded quantifier, and the
quantifier is complete because the fragment's members are members of the stage.
Both directions of its membership are read once, because both are consumed.
<!--zh-->
## 初步函数阶段上的分离

满足集引擎对其载体是抽象的，故它施于初步函数阶段与施于可构造阶段一样合用：塔作为成员收下的阶段，其每个可定义子集仍是其上极限层的成员。此处所花的公式，说的是「片段的一个成员，其全部成员都落在载体里」，两个常量加一个有界量词，而该量词是完全的，因为片段的成员就是该阶段的成员。它的隶属两个方向各读一次，因为两个方向都要被消费。
<!--/-->

```agda
module Sep (γ : S) (limγ : ⟨ isLimit γ ⟩) (δ : S) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
           (C F : S) (C∈ : ⟨ C ∈ˢ Sset δ ⟩) (F∈ : ⟨ F ∈ˢ Sset δ ⟩) where

  W : S
  W = Sset δ

  Wtr : (u v : S) → ⟨ u ∈ˢ v ⟩ → ⟨ v ∈ˢ W ⟩ → ⟨ u ∈ˢ W ⟩
  Wtr u v u∈v v∈W = Sset-trans δ {x = v} {y = u} u∈v v∈W

  Jtr : (u v : S) → ⟨ v ∈ˢ Sset γ ⟩ → ⟨ u ∈ˢ v ⟩ → ⟨ u ∈ˢ Sset γ ⟩
  Jtr u v v∈J u∈v = Sset-trans γ {x = v} {y = u} u∈v v∈J

  W∈J : ⟨ W ∈ˢ Sset γ ⟩
  W∈J = Sset-mem {α = γ} {β = δ} δ∈γ

  module SW = Sat W Wtr (λ z → ⟨ z ∈ˢ Sset γ ⟩) Jtr (Jset-rud γ limγ) W∈J

  open DefOf W using ( SM; defSet; defSet-mem; defSet⊆A; ι; _⊨ᵐ_ )

  fC : Σ[ m ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ m ≡ C)
  fC = ∈-asFiber {a = C} {b = W} C∈

  fF : Σ[ m ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ m ≡ F)
  fF = ∈-asFiber {a = F} {b = W} F∈

  Φ : Formula ⟪ W ⟫ 1
  Φ = (var zero ∈̇ con (fF .fst))
      ∧̇ (∀̇∈ (var zero) (var zero ∈̇ con (fC .fst)))

  sep : S
  sep = defSet Φ

  sep∈J : ⟨ sep ∈ˢ Sset γ ⟩
  sep∈J = SW.defSet-InJ Φ

  sep-write : (y : S) → ⟨ y ∈ˢ F ⟩
            → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ C ⟩) → ⟨ y ∈ˢ sep ⟩
  sep-write y y∈F sub =
    subst (λ w → ⟨ w ∈ˢ sep ⟩) (fy .snd)
      (subst ⟨_⟩ (sym (defSet-mem Φ (fy .fst))) (inF , inC))
    where
    y∈W : ⟨ y ∈ˢ W ⟩
    y∈W = Wtr y F y∈F F∈
    fy : Σ[ m ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ m ≡ y)
    fy = ∈-asFiber {a = y} {b = W} y∈W
    inF : ⟨ ⟪ W ⟫↪ (fy .fst) ∈ˢ ⟪ W ⟫↪ (fF .fst) ⟩
    inF = subst (λ w → ⟨ ⟪ W ⟫↪ (fy .fst) ∈ˢ w ⟩) (sym (fF .snd))
            (subst (λ w → ⟨ w ∈ˢ F ⟩) (sym (fy .snd)) y∈F)
    inC : (v : SM) → ⟨ v .fst ∈ˢ ⟪ W ⟫↪ (fy .fst) ⟩
        → ⟨ v .fst ∈ˢ ⟪ W ⟫↪ (fC .fst) ⟩
    inC v h = subst (λ w → ⟨ v .fst ∈ˢ w ⟩) (sym (fC .snd))
      (sub (v .fst) (subst (λ w → ⟨ v .fst ∈ˢ w ⟩) (fy .snd) h))

  sep-read : (y : S) → ⟨ y ∈ˢ sep ⟩
           → ⟨ y ∈ˢ F ⟩ × ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ C ⟩)
  sep-read y y∈sep = outF , outC
    where
    y∈W : ⟨ y ∈ˢ W ⟩
    y∈W = defSet⊆A Φ y y∈sep
    fy : Σ[ m ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ m ≡ y)
    fy = ∈-asFiber {a = y} {b = W} y∈W
    sat : ⟨ (ι (fy .fst) ∷ []) ⊨ᵐ Φ ⟩
    sat = subst ⟨_⟩ (defSet-mem Φ (fy .fst))
      (subst (λ w → ⟨ w ∈ˢ sep ⟩) (sym (fy .snd)) y∈sep)
    outF : ⟨ y ∈ˢ F ⟩
    outF = subst (λ w → ⟨ w ∈ˢ F ⟩) (fy .snd)
      (subst (λ w → ⟨ ⟪ W ⟫↪ (fy .fst) ∈ˢ w ⟩) (fF .snd) (sat .fst))
    outC : (w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ C ⟩
    outC w w∈y = subst (λ t → ⟨ w ∈ˢ t ⟩) (fC .snd)
      (sat .snd (w , Wtr w y w∈y y∈W)
        (subst (λ t → ⟨ w ∈ˢ t ⟩) (sym (fy .snd)) w∈y))
```

<!--en-->
## The definable subsets of a stage, one at a time

The engine's own statement, read at a constructible carrier and an arbitrary
limit level of the rud tower that already holds it: every definable subset of
the carrier is a member of that level. This is the delivered half of the
bounding fragment, and it is delivered only where a limit level is available,
which is exactly the condition the fragment types below make visible.
<!--zh-->
## 阶段的可定义子集，一次一个

引擎自身的陈述，在可构造载体与初步函数塔某个已收下它的任意极限层处读出：载体的每个可定义子集都是该层的成员。这是定界片段中已交付的那一半，而它只在有极限层可用之处交付，那正是下方诸片段类型所显明的条件。
<!--/-->

```agda
defs-in-limit : (ζ μ : S) → (limμ : ⟨ isLimit μ ⟩) → ⟨ Lset ζ ∈ˢ Sset μ ⟩
              → (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ y ∈ˢ Sset μ ⟩
defs-in-limit ζ μ limμ L∈ y y∈𝒟 =
  PT.rec (snd (y ∈ˢ Sset μ)) go (𝒟ₒ-inv (Lset ζ) y y∈𝒟)
  where
  Ltr : (u v : S) → ⟨ u ∈ˢ v ⟩ → ⟨ v ∈ˢ Lset ζ ⟩ → ⟨ u ∈ˢ Lset ζ ⟩
  Ltr u v u∈v v∈L = layer-trans (Lset-layer ζ) {x = v} {y = u} u∈v v∈L
  Jtr : (u v : S) → ⟨ v ∈ˢ Sset μ ⟩ → ⟨ u ∈ˢ v ⟩ → ⟨ u ∈ˢ Sset μ ⟩
  Jtr u v v∈J u∈v = Sset-trans μ {x = v} {y = u} u∈v v∈J
  module Sζ = Sat (Lset ζ) Ltr (λ z → ⟨ z ∈ˢ Sset μ ⟩) Jtr
                  (Jset-rud μ limμ) L∈
  go : Σ[ φ ∈ Formula ⟪ Lset ζ ⟫ 1 ] (DefOf.defSet (Lset ζ) φ ≡ y)
     → ⟨ y ∈ˢ Sset μ ⟩
  go (φ , eq) = subst (λ w → ⟨ w ∈ˢ Sset μ ⟩) eq (Sζ.defSet-InJ φ)
```

<!--en-->
## The bounding fragment, and the discharge

The residue is one statement and it is stated twice, in a general and in a
sharpened form. The general form asks for a **bounding fragment**: a member of
the limit level that contains every definable subset of the carrier and contains
no subset of the carrier that is not definable over it. Given one, the target
follows: the two sets enter the tower at a common stage, the separation carves
the definable power out of the fragment there, and the successor collapse
rewrites the result into the bridge's conclusion.

The general form is not a weakening: taking the fragment to be the definable
power itself turns it back into the target, so the two are equivalent. Its
content is that the residue may be discharged by an **approximation** loose in
both directions, which is how the classical argument proceeds, rather than by
an exact construction of the definable power inside the tower.

The sharpened form replaces the fragment by a **limit level below the target
level**, at which the containment half is free by the engine and only the
converse half, "a subset of the carrier lying in the fragment is definable over
it", remains. That converse is the classical block statement. This form is
sufficient and not necessary, and writing it down puts its room condition where
it can be seen: it demands a limit level strictly below `γ` that already holds
the carrier, and `γ = ω` has no limit below it at all, so the sharpened form is
refutable there. The same refutation reaches every fragment that is asked to be
closed under the sixteen operations, because such a fragment contains an
infinite chain of singletons while every member of `Sset ω` is finite.
<!--zh-->
## 定界片段与兑付

存留只有一条陈述，但陈述两遍，一遍一般、一遍加锐。一般形式索取一个**定界片段**：极限层的一个成员，它含有载体的每个可定义子集，且不含载体的任何非可定义子集。给定它，目标随之而来：两个集合在共同阶段进场，分离在那里从片段中刻出可定义幂，后继坍缩再把结果改写成桥的结论。

一般形式并非削弱：把片段取作可定义幂自身，它就变回目标，故二者等价。它的内容在于，存留可以由一个两头都松的**逼近**来兑付，经典论证正是这样走的，而不必在塔内精确地造出可定义幂。

加锐形式把片段换成**目标层之下的一个极限层**，在那里包含的那一半由引擎免费给出，只剩反向的那一半，即「落在片段里的载体子集在其上可定义」。那个反向陈述就是经典的整块陈述。该形式充分而不必要，把它写下来则把它的余地条件摆到明处：它索取严格位于 `γ` 之下、且已收下载体的极限层，而 `γ = ω` 之下根本没有极限，故加锐形式在那里可反驳。同一反驳触及每个被要求对十六运算封闭的片段，因为这样的片段含有一条无穷的单点集链，而 `Sset ω` 的每个成员都是有限的。
<!--/-->

```agda
private
  Frag : S → S → Type (ℓ-suc ℓ)
  Frag ζ γ = Σ[ F ∈ S ] ( ⟨ F ∈ˢ Sset γ ⟩
    × (((y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ y ∈ˢ F ⟩)
    × ((y : S) → ⟨ y ∈ˢ F ⟩
      → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ Lset ζ ⟩)
      → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩)))

  LFrag : S → S → Type (ℓ-suc ℓ)
  LFrag ζ γ = Σ[ μ ∈ S ] ( ⟨ μ ∈ˢ γ ⟩
    × (Σ[ limμ ∈ ⟨ isLimit μ ⟩ ] ( ⟨ Lset ζ ∈ˢ Sset μ ⟩
    × ((y : S) → ⟨ y ∈ˢ Sset μ ⟩
      → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ Lset ζ ⟩)
      → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩))))

DefFragment : Type (ℓ-suc ℓ)
DefFragment = (ζ γ : S) → ⟨ isLimit γ ⟩ → ⟨ ζ ∈ˢ γ ⟩ → ⟨ Lset ζ ∈ˢ Sset γ ⟩
            → ∥ Frag ζ γ ∥₁

LimitFragment : Type (ℓ-suc ℓ)
LimitFragment = (ζ γ : S) → ⟨ isLimit γ ⟩ → ⟨ ζ ∈ˢ γ ⟩ → ⟨ Lset ζ ∈ˢ Sset γ ⟩
              → ∥ LFrag ζ γ ∥₁

fragment-from-limit : LimitFragment → DefFragment
fragment-from-limit lf ζ γ limγ ζ∈γ L∈ = PT.map go (lf ζ γ limγ ζ∈γ L∈)
  where
  go : LFrag ζ γ → Frag ζ γ
  go (μ , μ∈γ , limμ , L∈μ , back) = Sset μ
    , ( Sset-mem {α = γ} {β = μ} μ∈γ
      , (defs-in-limit ζ μ limμ L∈μ , back) )

module Discharge (frag : DefFragment) where

  defStage∈J : (ζ γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ ζ ∈ˢ γ ⟩
             → ⟨ Lset ζ ∈ˢ Sset γ ⟩ → ⟨ Lset (sucV ζ) ∈ˢ Sset γ ⟩
  defStage∈J ζ γ limγ ζ∈γ L∈ =
    subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sym (Lsuc≡Def ζ))
      (PT.rec (snd (𝒟ₒ (Lset ζ) ∈ˢ Sset γ)) atFrag (frag ζ γ limγ ζ∈γ L∈))
    where
    atFrag : Frag ζ γ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
    atFrag (F , F∈J , into , outof) =
      PT.rec (snd (𝒟ₒ (Lset ζ) ∈ˢ Sset γ)) atStage
        (Sstage₂ γ limγ (Lset ζ) F L∈ F∈J)
      where
      atStage : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ Lset ζ ∈ˢ Sset δ ⟩ × ⟨ F ∈ˢ Sset δ ⟩)
              → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
      atStage (δ , δ∈γ , C∈ , F∈) =
        subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sym eq) SP.sep∈J
        where
        module SP = Sep γ limγ δ δ∈γ (Lset ζ) F C∈ F∈
        eq : 𝒟ₒ (Lset ζ) ≡ SP.sep
        eq = ext-⊆
          (λ x hx → SP.sep-write x (into x hx) (𝒟ₒ∋⊆ (Lset ζ) x hx))
          (λ x hx → outof x (SP.sep-read x hx .fst) (SP.sep-read x hx .snd))
```

<!--en-->
## Recap

One Def stage up is the definable power, so the bridge's first hypothesis is the
statement that a definable power is a rud member. Three of its four parts are
proved outright: the successor collapse, the common rud stage for two members,
and the separation of a bounding fragment by a two-constant Δ₀ formula whose
`defSet` the satisfaction engine places in the limit level. The fourth part is
the bounding fragment itself, stated in two forms with a reduction between them,
and it stays open: the engine realizes one formula's satisfaction set at a time,
and no image or separation of those sets collects a family indexed by the
syntax.
<!--zh-->
## 小结

上升一个 Def 阶段就是取可定义幂，故桥的第一条假设，说的正是可定义幂是初步函数成员。它四个部分中的三个当场证出：后继坍缩、两个成员的共同初步函数阶段，以及用一条两常量 Δ₀ 公式对定界片段作分离，而该公式的 `defSet` 由满足集引擎放进极限层。第四部分是定界片段自身，以两种形式陈述、并给出二者之间的归约，它仍然敞着：引擎一次实现一条公式的满足集，而那些集合的任何取像或分离都收拢不了以语法为索引的族。
<!--/-->
