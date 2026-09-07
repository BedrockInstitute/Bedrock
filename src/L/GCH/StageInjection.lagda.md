<!--en-->
# Injecting an infinite constructible stage into its index

This chapter proves the main stage estimate used by GCH: at an infinite ordinal, the corresponding constructible stage injects into that ordinal inside `L`.
<!--zh-->
# 把无穷可构造阶段单射到其指标

本章证明 GCH 所用的主要阶段估计：在一个无穷序数处，相应的可构造阶段在 `L` 内部单射到该序数。
<!--ja-->
# 無限構成可能段階をその添字へ単射する

本章では GCH に用いる主要な段階評価を示す。無限順序数に対応する構成可能段階から、その順序数自身への内部単射を `L` の中で構成する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.StageInjection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isExt )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( #∈ω; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem
  using ( StageCountedCoded; inclusion-coded; injl-trans )
open import L.GCH.CardinalRepresentative {ℓ} lem using ( cardOf )
open import L.GCH.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.SkolemHull {ℓ} lem
  using ( module Frame; module HullStage; module HullElemDown )
open import L.GCH.ConstructibleHull {ℓ} lem using ( module PiIn; module Condense′ )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( ordL; ω⊆; no-fin; module Shift )
open import L.GCH.AdequateStages {ℓ} lem using ( superadequate-above; Superadequate )
open import L.GCH.StageCountingTools {ℓ} lem using ( move )
open import L.GCH.HullCounting {ℓ} lem using ( ord⊆Lset; module Count; S≡ )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

open hPropStructure 𝒮ʟ using ( S )

open FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using () renaming ( _⊨ᵐ_ to _⊨_ )
```

Every module application below names what it takes.

```agda
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )
```

The hull site, without a target: the telescope of src/L/GCH/HullIn.lagda.md
`Condense′`, a superadequate stage `λ`, a start `X` inside `L_λ` that is an
element of L, and the elementarity of the hull. What comes out is the collapse
stage `L_β` and the inverse collapse `L_β ↪ M`, a definable map on `L_β`. No
count of `X` appears here, so the same site serves both consumers of the hull.

```agda
```

<!--en-->
## Counting the hull at a strengthened adequate stage

At a strengthened adequate stage above `δ`, start the Skolem hull from `Lset δ` together with the witnesses needed by the hierarchy description. The hull-count theorem keeps this enlarged set injectable into `δ`.
<!--zh-->
## 在超充分阶段计数 Skolem 壳

在 `δ` 之上的超充分阶段，以 `Lset δ` 连同层级描述所需的见证为起点构造 Skolem 壳。壳计数定理保证这个扩大的集合仍可单射到 `δ`。
<!--ja-->
## 強化された十分な段階で Skolem 包を数える

`δ` より上の強化された十分な段階で、`Lset δ` と階層記述に必要な証人から Skolem 包を作る。包の計数定理により、この拡大した集合も `δ` へ単射できる。
<!--/-->

```agda
module Site (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : V ℓ) (X⊆Lλ : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩) where

  condenses′ = Condense′.condenses′ lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
  M-isL = Condense′.M-isL lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
```

The hull stage, its collapse, and the collapse graph, read at the source
modules `Cn` copies from.

```agda
  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆Lλ ∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X X⊆Lλ ∅∈λ
    using ( πX; π; fixes; πX-intro; πX-member )
  module P = PiIn (HS.M , M-isL) using ( piFo; up; good-at; piFo-val )

  β : V ℓ
  β = condenses′ .fst

  oβ : IsOrd β
  oβ = condenses′ .snd .fst

  ext : HSC.πX ≡ Lset β
  ext = condenses′ .snd .snd

  Lβ : S
  Lβ = LsetS β oβ

  βL : S
  βL = ordL β oβ

  hullL : S
  hullL = Condense′.hullL lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL

  M≡ : fst hullL ≡ HS.M
  M≡ = Condense′.hullL-spec lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL

  Mext : isExt HS.M
  Mext = Frame.Mext lam ordλ succλ X X⊆Lλ ∅∈λ

  module CI = HullStage.C.InjExt lam ordλ succλ X X⊆Lλ ∅∈λ Mext using ( π-inj )
```

5.2 The inverse collapse, `L_β ↪ M`, as a definable map: `v` ↦ the member of
`M` collapsing to `v`. The graph, over `(x ∷ v ∷ [])`: "`x ∈ M` and the collapse
graph holds at `(v, x)`", the latter being src/L/GCH/HullIn.lagda.md
`PiIn.piFo` read at `(v ∷ x ∷ [])`.

```agda
  Pre : S → Type (ℓ-suc ℓ)
  Pre v = Σ[ x ∈ V ℓ ] (⟨ x ∈ˢ HS.M ⟩ × (HSC.π x ≡ fst v))

  isPropPre : (v : S) → isProp (Pre v)
  isPropPre v (x , mx , e) (x' , mx' , e') =
    Σ≡Prop (λ x → isProp× (snd (x ∈ˢ HS.M)) (setIsSet _ _)) (CI.π-inj x x' mx mx' (e ∙ sym e'))

  Mem : S → Type (ℓ-suc ℓ)
  Mem v = ⟨ fst v ∈ˢ fst Lβ ⟩

  pre : (v : S) → Mem v → Pre v
  pre v m = PT.rec (isPropPre v) (λ w → w)
    (HSC.πX-member (fst v) (subst (λ w → ⟨ fst v ∈ˢ w ⟩) (sym ext) m))

  fn : (v : S) → Mem v → S
  fn v m = pre v m .fst
         , isL-trans {x = fst hullL} {y = pre v m .fst}
             (subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)) (snd hullL)

  ρ : Fin 2 → Fin 2
  ρ zero = suc zero
  ρ (suc zero) = zero

  private
    ag : (x v : S) → Ren.Agrees ρ (x ∷ v ∷ []) (v ∷ x ∷ [])
    ag x v zero = refl
    ag x v (suc zero) = refl

    rn : (x v : S) → ⟨ (x ∷ v ∷ []) ⊨ renameFo ρ P.piFo ⟩ ≡ ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
    rn x v = cong ⟨_⟩ (Ren.⊨-rename ρ P.piFo (x ∷ v ∷ []) (v ∷ x ∷ []) (ag x v))

  invFo : Formula S 2
  invFo = (var zero ∈̇ con hullL) ∧̇ renameFo ρ P.piFo
```

The collapse graph holds at `(π x, x)` for `x ∈ M`.

```agda
  π-graph : (x : S) (mx : ⟨ fst x ∈ˢ HS.M ⟩) (v : S) → HSC.π (fst x) ≡ fst v
          → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
  π-graph x mx v e = PT.rec (snd ((v ∷ x ∷ []) ⊨ P.piFo)) read M-isL
    where
    read : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ HS.M ∈ˢ Lset α ⟩) → ⟨ (v ∷ x ∷ []) ⊨ P.piFo ⟩
    read (α , oα , M∈Lα) =
      subst2 (λ a b → ⟨ (a ∷ b ∷ []) ⊨ P.piFo ⟩)
        (S≡ {x = HSC.π (fst x) , G .fst} {y = v} e) (S≡ {x = P.up (fst x) mx} {y = x} refl)
        (G .snd mx)
      where
      G = P.good-at α oα (fst x) mx (layer-trans (Lset-layer α) {x = HS.M} {y = fst x} mx M∈Lα)

  defines : (v : S) (m : Mem v) → ⟨ (fn v m ∷ v ∷ []) ⊨ invFo ⟩
  defines v m =
      subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
    , transport (sym (rn (fn v m) v)) (π-graph (fn v m) (pre v m .snd .fst) v (pre v m .snd .snd))

  only : (v : S) (m : Mem v) (x' : S) → ⟨ (x' ∷ v ∷ []) ⊨ invFo ⟩ → x' ≡ fn v m
  only v m x' (hx , hp) = S≡ (CI.π-inj (fst x') (pre v m .fst) mx' (pre v m .snd .fst)
    (sym (P.piFo-val x' mx' v (transport (rn x' v) hp)) ∙ sym (pre v m .snd .snd)))
    where
    mx' : ⟨ fst x' ∈ˢ HS.M ⟩
    mx' = subst (λ w → ⟨ fst x' ∈ˢ w ⟩) M≡ hx

  Dmap : DefinableMap
  Dmap = record
    { dom = Lβ ; cod = hullL ; fn = fn
    ; into = λ v m → subst (λ w → ⟨ pre v m .fst ∈ˢ w ⟩) (sym M≡) (pre v m .snd .fst)
    ; graph = invFo ; defines = defines ; only = only }

  inj : (v : S) (m : Mem v) (v' : S) (m' : Mem v') → fst (fn v m) ≡ fst (fn v' m') → fst v ≡ fst v'
  inj v m v' m' q = sym (pre v m .snd .snd) ∙ cong HSC.π q ∙ pre v' m' .snd .snd

  Lβ↪M : InjL Lβ hullL
  Lβ↪M = Inj.injL Dmap inj
```

The site at an infinite ordinal `δ`. The start is `X = δ+1`, transitive because
it is an ordinal, and an element of L. `λ` is the superadequate stage above the
stage of `δ`, so `δ ∈ λ` and `δ+1 ∈ λ`. The start is counted at `μ`, the
internal cardinal of `δ`: `δ+1 ↪ δ` by src/L/GCH/Pairing.lagda.md `Shift`, then
`δ ↪ μ`. The collapse fixes `δ` pointwise, so `δ ∈ L_β`, hence `δ ∈ β`, hence
`L_δ ⊆ L_β`; and the chain `L_δ ↪ L_β ↪ M ↪ μ ↪ δ` is the row.

```agda
```

<!--en-->
## Collapsing the hull back to the original stage

Condensation identifies the counted hull with a lower constructible stage. Because the hull contains `Lset δ` and `δ` is an infinite cardinal index, ordinal comparison forces that lower stage to be no larger than `δ`, yielding the coded stage injection.
<!--zh-->
## 把 Skolem 壳塌缩回原阶段

凝聚把已计数的 Skolem 壳识别为一个更低的可构造阶段。因为该壳包含 `Lset δ`，且 `δ` 是无穷基数指标，序数比较迫使较低阶段不超过 `δ`，从而得到阶段的编码单射。
<!--ja-->
## Skolem 包を元の段階へ崩壊して戻す

凝縮によって、数えられた Skolem 包はより低い構成可能段階と同定される。包は `Lset δ` を含み、`δ` は無限基数の添字なので、順序数の比較から低い段階は `δ` を超えず、段階の符号化された単射が得られる。
<!--/-->

```agda
module At (δL : S) (oδ : IsOrd (fst δL)) (δ∉ω : ⟨ fst δL ∈ˢ ω ⟩ → Empty.⊥)
          (μ : S) (oμ : IsOrd (fst μ)) (cμ : IsCardinalL μ)
          (μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥)
          (δ↪μ : InjL δL μ) (μ↪δ : InjL μ δL) where

  δ : V ℓ
  δ = fst δL
```

1. The stage `λ`, above the stage of `δ`. Sealed: every consumer wants `λ` as
an atom.

```agda
  private
    α₀ : V ℓ
    α₀ = stage δ (snd δL)

    oα₀ : IsOrd α₀
    oα₀ = stage-ord δ (snd δL)

    δ∈Lα₀ : ⟨ δ ∈ˢ Lset α₀ ⟩
    δ∈Lα₀ = stage-mem δ (snd δL)

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

    δ∈λ : ⟨ δ ∈ˢ lam ⟩
    δ∈λ = ordλ .fst (ord∈Lset→∈ α₀ oα₀ δ oδ δ∈Lα₀) (sa .snd .snd .fst)
```

2. The start `X = δ+1`, an ordinal below `λ`, an element of L.

```agda
  X : V ℓ
  X = sucV δ

  sucδ∈λ : ⟨ X ∈ˢ lam ⟩
  sucδ∈λ = succλ δ δ∈λ

  X⊆Lλ : (z : V ℓ) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  X⊆Lλ z hz = ord⊆Lset lam ordλ z (ordλ .fst hz sucδ∈λ)

  ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩
  ∅∈λ = ordλ .fst (ω⊆ δ oδ δ∉ω ∅ (#∈ω zero)) δ∈λ

  X-isL : ⟨ isL X ⟩
  X-isL = subst (λ w → ⟨ isL w ⟩) (sucʟ-fst δL) (snd (sucʟ δL))

  XS : S
  XS = X , X-isL
```

3. The start is counted: `δ+1 ↪ δ ↪ μ`.

```agda
  base : InjL XS μ
  base = injl-trans XS δL μ
    (move (sucʟ δL) XS δL δL (sucʟ-fst δL) refl (Shift.injL δL oδ δ∉ω))
    δ↪μ
```

4. The hull, its collapse `L_β`, and its count.

```agda
  elem = HullElemDown.elem lam ordλ X X⊆Lλ ∅∈λ

  hull↪μ = Count.hull↪κ lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL μ oμ cμ μ∉ω base

  module St = Site lam ordλ succλ X X⊆Lλ ∅∈λ elem sup X-isL
    using ( β; oβ; ext; Lβ; hullL; Lβ↪M )

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆Lλ ∅∈λ using ( X⊆M )
  module HSC = HullStage.C lam ordλ succλ X X⊆Lλ ∅∈λ
    using ( π; fixes; πX-intro )
```

5. `δ` is a member of `L_β`: `δ ∈ X ⊆ M`, `X` is transitive, so the collapse
fixes `δ` (src/V/Collapse.lagda.md `fixes`).

```agda
  δ∈X : ⟨ δ ∈ˢ X ⟩
  δ∈X = self∈sucV δ

  δ∈M : ⟨ δ ∈ˢ HS.M ⟩
  δ∈M = HSH.X⊆M δ δ∈X

  πδ : HSC.π δ ≡ δ
  πδ = HSC.fixes X
    (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst (HSH.X⊆M a (∈∈ₛ {a = a} {b = X} .snd a∈ₛX)))
    (suc-ord oδ .fst) δ δ∈X

  δ∈Lβ : ⟨ δ ∈ˢ Lset St.β ⟩
  δ∈Lβ = subst (λ w → ⟨ w ∈ˢ Lset St.β ⟩) πδ
    (subst (λ w → ⟨ HSC.π δ ∈ˢ w ⟩) St.ext (HSC.πX-intro δ δ∈M))
```

6. The chain: `L_δ ⊆ L_β ↪ M ↪ μ ↪ δ`.

```agda
  δ∈β : ⟨ δ ∈ˢ St.β ⟩
  δ∈β = ord∈Lset→∈ St.β St.oβ δ oδ δ∈Lβ

  Lδ : S
  Lδ = LsetS δ oδ

  result : InjL Lδ δL
  result = injl-trans Lδ St.Lβ δL
    (inclusion-coded Lδ St.Lβ (λ z hz → Lset-mono {α = St.β} {β = δ} δ∈β hz))
    (injl-trans St.Lβ St.hullL δL St.Lβ↪M
      (injl-trans St.hullL μ δL hull↪μ μ↪δ))
```

The theorem: hypothesis 1 of src/L/GCH/Assembly.lagda.md, at the internal
cardinal of `δ`.

```agda
stage-counted : StageCountedCoded
stage-counted δ Lδ oδ δ∉ω q = PT.rec squash₁ build (cardOf δ oδ)
  where
  build : Σ[ μ ∈ S ]
            ( IsOrd (fst μ) × IsCardinalL μ
            × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst δ ⟩)
            × InjL δ μ × InjL μ δ )
        → InjL Lδ δ
  build (μ , oμ , cμ , μ⊆δ , δ↪μ , μ↪δ) =
    move (LsetS (fst δ) oδ) Lδ δ δ (sym q) refl
      (At.result δ oδ δ∉ω μ oμ cμ μ∉ω δ↪μ μ↪δ)
    where
    μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
    μ∉ω h = no-fin δ μ oδ δ∉ω oμ h δ↪μ
```
