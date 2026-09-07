<!--en-->
# Bounded subsets appear at controlled stages

The bounded subset theorem locates a constructible subset once its elements and defining parameters are bounded. This internal form is the bridge from definability to the stage estimate used in the GCH argument.
<!--zh-->
# 有界子集在受控阶段出现

有界子集定理在元素与定义参数已有界时，确定一个可构造子集出现的位置。它的内部形式把可定义性连接到 GCH 论证所需的阶段估计。
<!--ja-->
# 有界部分集合が現れる段階を制御する

有界部分集合定理は、要素と定義パラメータが有界ならば、構成可能な部分集合が現れる位置を定める。この内部版が、定義可能性と GCH の議論で使う段階評価を結ぶ。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.BoundedSubset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( pairʟ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem
  using ( InternalBoundedSubset; inclusion-coded; injl-trans )
open import L.GCH.SkolemHull {ℓ} lem
  using ( module UnionKit; module HullStage; module HullElemDown )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prodL; ω⊆; Goal; module Step )
open import L.GCH.AdequateStages {ℓ} lem using ( superadequate-above; Superadequate )
open import L.GCH.StageCountingTools {ℓ} lem using ( move )
open import L.GCH.StageInjection {ℓ} lem using ( stage-counted; module Site )
open import L.GCH.OmegaRecursion {ℓ} lem using ( pairʟ-in )
open import L.GCH.HullCounting {ℓ} lem
  using ( ord⊆Lset; module Union2; tag-union; module Point; module Count )

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet; ⁅_⁆s )
open InfinitySet {ℓ} using ( #_; ω; sucV )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

open hPropStructure 𝒮ʟ using ( S )
```

The site. An infinite L-cardinal `κ` and a subset `y` of `κ`, both elements of
L. The start `X = L_κ ∪ {y}` is transitive and an element of L; `λ` is a
superadequate stage above `κ` and above `y`; the Skolem hull `M` of `X` in
`L_λ` collapses to a stage `L_β` (src/L/GCH/StageCounted.lagda.md `Site`); `y`
is fixed by the collapse, so `y ∈ L_β`; and `β ⊆ L_β = πX ↪ M ↪ κ`, the last by
src/L/GCH/HullCount.lagda.md.

```agda
```

<!--en-->
## Bounding a constructible subset of a cardinal

Fix an internal cardinal `κ` and a subset `y` of it. A defining formula for `y` uses only finitely many parameters; collecting their birth stages produces one ordinal `β` into which both the parameters and the relevant satisfaction data fit.
<!--zh-->
## 为基数的可构造子集取界

固定内部基数 `κ` 及其子集 `y`。定义 `y` 的公式只使用有限多个参数；收集这些参数的诞生阶段，便得到一个同时容纳参数与相关满足关系数据的序数 `β`。
<!--ja-->
## 基数の構成可能な部分集合を有界化する

内部基数 `κ` とその部分集合 `y` を固定する。`y` を定義する論理式が使うパラメータは有限個なので、その誕生段階を集めると、パラメータと必要な充足関係のデータを収める一つの順序数 `β` が得られる。
<!--/-->

```agda
module At (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
          (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
          (y : S) (y⊆κ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩) where

  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)

  Lκ : S
  Lκ = LsetS (fst κ) oκ
```

1. THE STAGE `λ`. `α₀` is the stage of the pair `{κ, y}`; `λ` is the
superadequate stage above `α₀`. Sealed: every consumer wants `λ` as an atom.

```agda
  private
    P₀ : S
    P₀ = pairʟ κ y

    α₀ : V ℓ
    α₀ = stage (fst P₀) (snd P₀)

    oα₀ : IsOrd α₀
    oα₀ = stage-ord (fst P₀) (snd P₀)

    κ∈Lα₀ : ⟨ fst κ ∈ˢ Lset α₀ ⟩
    κ∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst κ}
      (pairʟ-in κ y κ (inl refl)) (stage-mem (fst P₀) (snd P₀))

    y∈Lα₀ : ⟨ fst y ∈ˢ Lset α₀ ⟩
    y∈Lα₀ = layer-trans (Lset-layer α₀) {x = fst P₀} {y = fst y}
      (pairʟ-in κ y y (inr refl)) (stage-mem (fst P₀) (snd P₀))

    sa = superadequate-above α₀ oα₀

  opaque
    lam : V ℓ
    lam = sa .fst

    ordλ : IsOrd lam
    ordλ = sa .snd .fst

    succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
    succλ = sa .snd .snd .snd .fst .snd .fst

    sup : Superadequate lam
    sup = sa .snd .snd .snd .snd

    κ∈λ : ⟨ fst κ ∈ˢ lam ⟩
    κ∈λ = ordλ .fst (ord∈Lset→∈ α₀ oα₀ (fst κ) oκ κ∈Lα₀) (sa .snd .snd .fst)

    y∈Lλ : ⟨ fst y ∈ˢ Lset lam ⟩
    y∈Lλ = Lset-mono {α = lam} {β = α₀} (sa .snd .snd .fst) y∈Lα₀
```

2. THE START `X = L_κ ∪ {y}`, transitive, an element of L.

```agda
  y⊆Lκ : (z : V ℓ) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  y⊆Lκ z hz = ord⊆Lset (fst κ) oκ z (y⊆κ z hz)

  module UK = UnionKit (fst κ) lam (fst y) oκ ordλ κ∈λ y⊆Lκ y∈Lλ κ∉ω
    using ( X; X⊆Lλ; ∅∈λ; Lα∈X; x∈X; X-mem; sgl≡; Xtr )

  X : V ℓ
  X = UK.X
```

`X` as the model's own union of `L_κ` and `{y}`.

```agda
  module Pt = Point κ (num∈κ 0) y using ( Y; Y-out; Y-in; injL )
  module U = Union2 Lκ Pt.Y using ( D; out; in₁; in₂ )

  Xʟ : S
  Xʟ = U.D

  Xʟ-eq : fst Xʟ ≡ X
  Xʟ-eq = extensionalV {a = fst Xʟ} {b = X} (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : V ℓ) → ⟨ z ∈ˢ fst Xʟ ⟩ → ⟨ z ∈ˢ X ⟩
    fwd z h = PT.rec (snd (z ∈ˢ X)) go (U.out zS h)
      where
      zS : S
      zS = z , isL-trans {x = fst Xʟ} {y = z} h (snd Xʟ)
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ fst Pt.Y ⟩ → ⟨ z ∈ˢ X ⟩
      go (inl hz) = UK.Lα∈X z hz
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ X ⟩) (sym (Pt.Y-out zS hz)) UK.x∈X
    bwd : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
    bwd z h = PT.rec (snd (z ∈ˢ fst Xʟ)) go (UK.X-mem z h)
      where
      go : ⟨ z ∈ˢ Lset (fst κ) ⟩ ⊎ ⟨ z ∈ˢ ⁅ fst y ⁆s ⟩ → ⟨ z ∈ˢ fst Xʟ ⟩
      go (inl hz) = U.in₁ (z , isL-trans {x = Lset (fst κ)} {y = z} hz (snd Lκ)) hz
      go (inr hz) = subst (λ w → ⟨ w ∈ˢ fst Xʟ ⟩) (sym (UK.sgl≡ z hz)) (U.in₂ y Pt.Y-in)

  X-isL : ⟨ isL X ⟩
  X-isL = subst (λ w → ⟨ isL w ⟩) Xʟ-eq (snd Xʟ)

  XS : S
  XS = X , X-isL
```

3. THE START IS COUNTED: `L_κ ↪ κ` and `{y} ↪ κ`, tagged, then paired.

The pairing at `κ`: src/L/GCH/Pairing.lagda.md's square law.

```agda
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

  base : InjL XS κ
  base = move Xʟ XS κ κ Xʟ-eq refl
    (injl-trans Xʟ (prodL κ) κ
      (tag-union κ (num∈κ 0) (num∈κ 1) Lκ Pt.Y (stage-counted κ Lκ oκ κ∉ω refl) Pt.injL)
      pairκ)
```

4. ELEMENTARITY OF THE HULL: the hull's Tarski-Vaught instance reads the code of
each constant off the hull membership, so the start needs no ambient count here
(src/L/GCH/Hull.lagda.md).

```agda
  elem = HullElemDown.elem lam ordλ X UK.X⊆Lλ UK.∅∈λ
```

5. THE HULL, ITS COLLAPSE `L_β`, AND ITS COUNT.

Read at the source, applied to the telescope: no module application, so nothing
of `Count` is copied.

```agda
  hull↪κ = Count.hull↪κ lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL κ oκ cκ κ∉ω base
```

The collapse stage `L_β` and the inverse collapse `L_β ↪ M`, at the same
telescope (src/L/GCH/StageCounted.lagda.md `Site`).

```agda
  module St = Site lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ elem sup X-isL
    using ( β; oβ; ext; Lβ; βL; hullL; Lβ↪M )
```

The hull stage, its collapse and the collapse graph, read at the source modules
`Site` copies from.

```agda
  module HS = HullStage lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X UK.X⊆Lλ UK.∅∈λ
    using ( πX; π; fixes; πX-intro )
```

5.1 `y` is a member of `L_β`: `y ∈ X ⊆ M`, `X` is transitive, so the collapse
fixes `y` (src/V/Collapse.lagda.md `fixes`).

```agda
  y∈M : ⟨ fst y ∈ˢ HS.M ⟩
  y∈M = HSH.X⊆M (fst y) UK.x∈X

  πy : HSC.π (fst y) ≡ fst y
  πy = HSC.fixes X
    (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst (HSH.X⊆M a (∈∈ₛ {a = a} {b = X} .snd a∈ₛX)))
    UK.Xtr (fst y) UK.x∈X

  y∈Lβ : ⟨ fst y ∈ˢ Lset St.β ⟩
  y∈Lβ = subst (λ w → ⟨ w ∈ˢ Lset St.β ⟩) πy
    (subst (λ w → ⟨ HSC.π (fst y) ∈ˢ w ⟩) St.ext (HSC.πX-intro (fst y) y∈M))
```

5.2 THE CHAIN: `β ⊆ L_β ↪ M ↪ κ`.

```agda
  β↪κ : InjL St.βL κ
  β↪κ = injl-trans St.βL St.Lβ κ
    (inclusion-coded St.βL St.Lβ (λ z hz → ord⊆Lset St.β St.oβ z hz))
    (injl-trans St.Lβ St.hullL κ St.Lβ↪M hull↪κ)

  result : Σ[ b ∈ S ] (IsOrd (fst b) × ⟨ fst y ∈ˢ Lset (fst b) ⟩ × InjL b κ)
  result = St.βL , St.oβ , y∈Lβ , β↪κ
```

The theorem: hypothesis 2 of src/L/GCH/Assembly.lagda.md.

```agda
internal-bounded-subset : InternalBoundedSubset
internal-bounded-subset κ oκ cκ κ∉ω y y⊆κ =
  ∣ At.result κ oκ cκ κ∉ω y y⊆κ ∣₁
```
