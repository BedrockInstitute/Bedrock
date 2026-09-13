<!--en-->
# Counting a Skolem hull from a counted start

Closing a small set under definable least witnesses should keep it small. This chapter makes that expectation internal to `L`: if the starting set injects into an infinite cardinal, then so does its Skolem hull.
<!--zh-->
# 从已计数的起点计数 Skolem 壳

把一个小集合对可定义公式的最小见证封闭，仍应保持其小性。本章在 `L` 内部证明这一点：若起始集合单射到一个无穷基数，则其 Skolem 壳也单射到该基数。
<!--ja-->
# 数えられた始集合から Skolem 包を数える

小さな集合を定義可能な最小の証人について閉じても、その小ささは保たれるはずである。本章ではこれを `L` の内部で示す。始集合が無限基数へ単射するなら、その Skolem 包も同じ基数へ単射する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.GCH.HullCounting {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; unionʟ )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; appAt; appAt-adequate; svAt-out; domAt-in )
open import L.Coding.Expressions {ℓ} using ( numL; tagAtL; tagAtL-adequate )
open import L.Coding.CodeConstructibility {ℓ}
  using ( sglʟ; sglʟ-in; sglʟ-out; cupʟ; cupʟ-inl; cupʟ-inr; cupʟ-out )
open import L.Coding.Injection {ℓ} lem using ( injAt-out; module Extract )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.LeastWitnessMap {ℓ} lem using ( module Least )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prodL; prodL-in; module Relation )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )
open import L.Stage {ℓ} lem using ( LeastOrd; isPropLeastOrd; leastOrd; stage; stage-ord; stage-mem )
open import L.Ordinal using ( boundingOrd )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet; envSet-in )
open import L.GCH.AdequateStages {ℓ} lem using ( Superadequate )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
open import L.GCH.SkolemHull {ℓ} lem using ( module Frame; module HullStage )
open import L.GCH.ConstructibleHull {ℓ} lem using ( module Condense′; module Telescope )
open import L.GCH.StageCountingTools {ℓ} lem
  using ( isPropInjCode; injcode-resp; injFo; module InjFo; pinAt; pin-in; pin-out; seq-map; Lω
        ; limit-stage-counted )
open import L.GCH.FiniteSequenceCoding {ℓ} lem using ( seqL; seqL-in; seq-count )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prod-inj; ω⊆; Goal; module Step )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import V.Hierarchy {ℓ} using ( regularityV )
import Cubical.Induction.WellFounded as WF
open import Cubical.Foundations.Prelude using ( subst2 )

open import Cubical.Data.Nat.Properties using ( znots; snotz )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

"The pair `(x, y)` is a member of `F`", the shape every clause reads.

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

The numeral `k` as an element of L.

```agda
nn : ℕ → S
nn k = # k , numL k

S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))

isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5
  i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
  i7 = suc i6
```

Section 0. Two small facts.

An ordinal is a subset of its own stage.

```agda
ord⊆Lset : (α : V ℓ) → IsOrd α → (z : V ℓ) → ⟨ z ∈ α ⟩ → ⟨ z ∈ Lset α ⟩
ord⊆Lset α oα z z∈α =
  Lset-cumul z α oz oα z∈α (ord∈Lset-suc z oz)
  where
  oz : IsOrd z
  oz = mem-ord {A = α} oα z z∈α
```

The shared constructible binary union, with the local names used below.

```agda
module Union2 (D₁ D₂ : S) where

  D : S
  D = cupʟ D₁ D₂

  in₁ : (z : S) → ⟨ fst z ∈ fst D₁ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₁ z = cupʟ-inl D₁ D₂ (fst z)

  in₂ : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₂ z = cupʟ-inr D₁ D₂ (fst z)

  out : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ ⟨ fst z ∈ fst D₁ ⟩ ⊎ ⟨ fst z ∈ fst D₂ ⟩ ∥₁
  out z = cupʟ-out D₁ D₂ (fst z)
```

Section 1. Two coded injections into `κ`, tagged into the product.

`z ↦ (0, E₁ z)` on `D₁`, and `z ↦ (1, E₂ z)` off `D₁`. The graph, over
`(y ∷ z ∷ [])`: "`z ∈ D₁` and some `v` has `(z, v) ∈ E₁` and `y = (0, v)`, or
`z ∉ D₁` and some `v` has `(z, v) ∈ E₂` and `y = (1, v)`". Inside the binder `v`
is 0, `y` is 1, `z` is 2.

```agda
module TagUnion (κ : S) (0∈κ : ⟨ # 0 ∈ fst κ ⟩) (1∈κ : ⟨ # 1 ∈ fst κ ⟩)
                (D₁ D₂ E₁ E₂ : S) (c₁ : InjCode E₁ D₁ κ) (c₂ : InjCode E₂ D₂ κ) where

  open Union2 D₁ D₂ public using ( D; in₁; in₂; out )

  module X₁ = Extract E₁ D₁ (fst c₁) (fst (snd c₁)) using ( toFun; toFun-graph )
  module X₂ = Extract E₂ D₂ (fst c₂) (fst (snd c₂)) using ( toFun; toFun-graph )

  Mem : S → Type (ℓ-suc ℓ)
  Mem z = ⟨ fst z ∈ fst D ⟩

  Case : S → Type (ℓ-suc ℓ)
  Case z = ⟨ fst z ∈ fst D₁ ⟩ ⊎ (⟨ fst z ∈ fst D₁ ⟩ → Empty.⊥)

  decide : (z : S) → Case z
  decide z = lem (fst z ∈ fst D₁)

  off : (z : S) → Mem z → (⟨ fst z ∈ fst D₁ ⟩ → Empty.⊥) → ⟨ fst z ∈ fst D₂ ⟩
  off z m no = PT.rec (snd (fst z ∈ fst D₂))
    (λ { (inl h) → Empty.rec (no h) ; (inr h) → h }) (out z m)

  val : (z : S) → Mem z → Case z → S
  val z m (inl h)  = prʟ (nn 0) (X₁.toFun (z , h))
  val z m (inr no) = prʟ (nn 1) (X₂.toFun (z , off z m no))

  fn : (z : S) → Mem z → S
  fn z m = val z m (decide z)
```

The graph and its host reading.

```agda
  Wit : (y z : S) → Type (ℓ-suc ℓ)
  Wit y z =
      (⟨ fst z ∈ fst D₁ ⟩
        × ∥ Σ[ v ∈ S ] (Holds E₁ z v × (fst y ≡ pr (# 0) (fst v))) ∥₁)
    ⊎ ((⟨ fst z ∈ fst D₁ ⟩ → Empty.⊥)
        × ∥ Σ[ v ∈ S ] (Holds E₂ z v × (fst y ≡ pr (# 1) (fst v))) ∥₁)

  opaque
    fo : Formula S 2
    fo = ((var i1 ∈̇ con D₁) ∧̇ ∃̇ (appC E₁ i2 i0 ∧̇ tagAtL i1 0 i0))
       ∨̇ ((¬̇ (var i1 ∈̇ con D₁)) ∧̇ ∃̇ (appC E₂ i2 i0 ∧̇ tagAtL i1 1 i0))

    private
      rd : (E : S) (k : ℕ) (y z v : S)
         → ⟨ (v ∷ y ∷ z ∷ []) ⊨ appC E i2 i0 ⟩ → ⟨ (v ∷ y ∷ z ∷ []) ⊨ tagAtL i1 k i0 ⟩
         → Holds E z v × (fst y ≡ pr (# k) (fst v))
      rd E k y z v ha ht =
          subst ⟨_⟩ (appC-adequate E i2 i0 (v ∷ y ∷ z ∷ [])) ha
        , subst ⟨_⟩ (tagAtL-adequate i1 k i0 (v ∷ y ∷ z ∷ [])) ht

      wr : (E : S) (k : ℕ) (y z v : S)
         → Holds E z v → fst y ≡ pr (# k) (fst v)
         → ⟨ (v ∷ y ∷ z ∷ []) ⊨ appC E i2 i0 ⟩ × ⟨ (v ∷ y ∷ z ∷ []) ⊨ tagAtL i1 k i0 ⟩
      wr E k y z v ha ht =
          subst ⟨_⟩ (sym (appC-adequate E i2 i0 (v ∷ y ∷ z ∷ []))) ha
        , subst ⟨_⟩ (sym (tagAtL-adequate i1 k i0 (v ∷ y ∷ z ∷ []))) ht

    fo-out : (y z : S) → ⟨ (y ∷ z ∷ []) ⊨ fo ⟩ → ∥ Wit y z ∥₁
    fo-out y z = PT.map
      (λ { (inl (h , hv)) → inl (h , PT.map (λ { (v , (ha , ht)) → v , rd E₁ 0 y z v ha ht }) hv)
         ; (inr (h , hv)) → inr ((λ z∈ → lower (h z∈))
             , PT.map (λ { (v , (ha , ht)) → v , rd E₂ 1 y z v ha ht }) hv) })

    fo-in : (y z : S) → Wit y z → ⟨ (y ∷ z ∷ []) ⊨ fo ⟩
    fo-in y z (inl (h , hv)) =
      ∣ inl (h , PT.map (λ { (v , (ha , ht)) → v , wr E₁ 0 y z v ha ht }) hv) ∣₁
    fo-in y z (inr (h , hv)) =
      ∣ inr ((λ z∈ → lift (h z∈))
          , PT.map (λ { (v , (ha , ht)) → v , wr E₂ 1 y z v ha ht }) hv) ∣₁

  private
    sv₁ : (x y y' : S) → Holds E₁ x y → Holds E₁ x y' → fst y ≡ fst y'
    sv₁ = svAt-out zero (E₁ ∷ D₁ ∷ []) (fst c₁)
    sv₂ : (x y y' : S) → Holds E₂ x y → Holds E₂ x y' → fst y ≡ fst y'
    sv₂ = svAt-out zero (E₂ ∷ D₂ ∷ []) (fst c₂)
    ij₁ : (y x x' : S) → Holds E₁ x y → Holds E₁ x' y → fst x ≡ fst x'
    ij₁ = injAt-out zero (E₁ ∷ D₁ ∷ []) (fst (snd (snd c₁)))
    ij₂ : (y x x' : S) → Holds E₂ x y → Holds E₂ x' y → fst x ≡ fst x'
    ij₂ = injAt-out zero (E₂ ∷ D₂ ∷ []) (fst (snd (snd c₂)))
    ran₁ : (x y : S) → Holds E₁ x y → ⟨ fst y ∈ fst κ ⟩
    ran₁ = snd (snd (snd c₁))
    ran₂ : (x y : S) → Holds E₂ x y → ⟨ fst y ∈ fst κ ⟩
    ran₂ = snd (snd (snd c₂))

  wit : (z : S) (m : Mem z) (c : Case z) → Wit (val z m c) z
  wit z m (inl h)  = inl (h , ∣ X₁.toFun (z , h)
    , (X₁.toFun-graph (z , h) , prʟ-fst (nn 0) (X₁.toFun (z , h))) ∣₁)
  wit z m (inr no) = inr (no , ∣ X₂.toFun (z , off z m no)
    , (X₂.toFun-graph (z , off z m no) , prʟ-fst (nn 1) (X₂.toFun (z , off z m no))) ∣₁)

  only : (z : S) (m : Mem z) (c : Case z) (y : S) → Wit y z → fst y ≡ fst (val z m c)
  only z m (inl h) y (inl (_ , hv)) = PT.rec (setIsSet _ _)
    (λ { (v , (hg , hy)) →
       hy ∙ cong (pr (# 0)) (sv₁ z v (X₁.toFun (z , h)) hg (X₁.toFun-graph (z , h)))
          ∙ sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) }) hv
  only z m (inl h) y (inr (no , _)) = Empty.rec (no h)
  only z m (inr no) y (inl (h , _)) = Empty.rec (no h)
  only z m (inr no) y (inr (_ , hv)) = PT.rec (setIsSet _ _)
    (λ { (v , (hg , hy)) →
       hy ∙ cong (pr (# 1)) (sv₂ z v (X₂.toFun (z , off z m no)) hg (X₂.toFun-graph (z , off z m no)))
          ∙ sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m no))) }) hv

  into : (z : S) (m : Mem z) (c : Case z) → ⟨ fst (val z m c) ∈ˢ fst (prodL κ) ⟩
  into z m (inl h) = subst (λ w → ⟨ w ∈ˢ fst (prodL κ) ⟩) (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))))
    (prodL-in κ (nn 0) (X₁.toFun (z , h)) 0∈κ (ran₁ z (X₁.toFun (z , h)) (X₁.toFun-graph (z , h))))
  into z m (inr no) = subst (λ w → ⟨ w ∈ˢ fst (prodL κ) ⟩) (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m no))))
    (prodL-in κ (nn 1) (X₂.toFun (z , off z m no)) 1∈κ
      (ran₂ z (X₂.toFun (z , off z m no)) (X₂.toFun-graph (z , off z m no))))

  Dmap : DefinableMap
  Dmap = record
    { dom = D ; cod = prodL κ ; fn = fn
    ; into = λ z m → into z m (decide z)
    ; graph = fo
    ; defines = λ z m → fo-in (fn z m) z (wit z m (decide z))
    ; only = λ z m y h → S≡ (PT.rec (setIsSet _ _) (only z m (decide z) y) (fo-out y z h)) }

  inj : (z : S) (m : Mem z) (z' : S) (m' : Mem z') → fst (fn z m) ≡ fst (fn z' m') → fst z ≡ fst z'
  inj z m z' m' = go (decide z) (decide z')
    where
    go : (c : Case z) (c' : Case z') → fst (val z m c) ≡ fst (val z' m' c') → fst z ≡ fst z'
    go (inl h) (inl h') q = ij₁ (X₁.toFun (z , h)) z z' (X₁.toFun-graph (z , h))
      (subst (λ w → ⟨ pr (fst z') w ∈ fst E₁ ⟩) (sym (snd p)) (X₁.toFun-graph (z' , h')))
      where
      p : (# 0 ≡ # 0) × (fst (X₁.toFun (z , h)) ≡ fst (X₁.toFun (z' , h')))
      p = pr-inj (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) ∙ q ∙ prʟ-fst (nn 0) (X₁.toFun (z' , h')))
    go (inl h) (inr no') q = Empty.rec (znots (#-inj 0 1 (fst
      (pr-inj (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) ∙ q ∙ prʟ-fst (nn 1) (X₂.toFun (z' , off z' m' no')))))))
    go (inr no) (inl h') q = Empty.rec (snotz (#-inj 1 0 (fst
      (pr-inj (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m no))) ∙ q ∙ prʟ-fst (nn 0) (X₁.toFun (z' , h')))))))
    go (inr no) (inr no') q = ij₂ (X₂.toFun (z , off z m no)) z z' (X₂.toFun-graph (z , off z m no))
      (subst (λ w → ⟨ pr (fst z') w ∈ fst E₂ ⟩) (sym (snd p)) (X₂.toFun-graph (z' , off z' m' no')))
      where
      p : (# 1 ≡ # 1) × (fst (X₂.toFun (z , off z m no)) ≡ fst (X₂.toFun (z' , off z' m' no')))
      p = pr-inj (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m no))) ∙ q
                  ∙ prʟ-fst (nn 1) (X₂.toFun (z' , off z' m' no')))

  injL : InjL D (prodL κ)
  injL = Inj.injL Dmap inj
```

The lemma: two internal injections into `κ` give one on the union.

```agda
tag-union : (κ : S) → ⟨ # 0 ∈ fst κ ⟩ → ⟨ # 1 ∈ fst κ ⟩
          → (D₁ D₂ : S) → InjL D₁ κ → InjL D₂ κ
          → InjL (unionʟ (pairʟ D₁ D₂)) (prodL κ)
tag-union κ h0 h1 D₁ D₂ = PT.rec2 squash₁
  (λ { (E₁ , c₁) (E₂ , c₂) → TagUnion.injL κ h0 h1 D₁ D₂ E₁ E₂ c₁ c₂ })
```

Section 2. The least preimage. `G` is a set of pairs `(p, z)` whose first
components lie in `P ⊆ L_γ`, and every `z ∈ D` has a preimage. `z ↦` the
stage-order-least `p` with `(p, z) ∈ G` is a definable map `D → P`, its graph is
a set of L, and when `G` is functional in the sense "`(p, z)`, `(p, z') ∈ G`
force `z = z'`" the map is injective. The selection, the graph and the table are
`L.GCH.LeastWitnessMap` at `γ`, `D` and the predicate "`(p, z) ∈ G`", over `(p ∷ z ∷ [])`.

```agda
module LeastPre (γ : V ℓ) (oγ : IsOrd γ) (G D P : S)
  (inP : (p z : S) → Holds G p z → ⟨ fst p ∈ fst P ⟩)
  (P⊆L : (p : S) → ⟨ fst p ∈ fst P ⟩ → ⟨ fst p ∈ Lset γ ⟩)
  (have : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁) where

  Mem : S → Type (ℓ-suc ℓ)
  Mem z = ⟨ fst z ∈ fst D ⟩

  private
    graphFo : Formula S 2
    graphFo = appC G i0 i1

    have-γ : (z : S) → Mem z
           → ∥ Σ[ p ∈ S ] (⟨ fst p ∈ Lset γ ⟩ × ⟨ (p ∷ z ∷ []) ⊨ graphFo ⟩) ∥₁
    have-γ z m = PT.map
      (λ { (p , h) → p , P⊆L p (inP p z h)
                       , subst ⟨_⟩ (sym (appC-adequate G i0 i1 (p ∷ z ∷ []))) h })
      (have z m)

    module Ls = Least γ oγ D graphFo have-γ using ( fn; fn-holds; Dmap; T; T-in; T-out )

  fn : (z : S) → Mem z → S
  fn = Ls.fn

  fn-holds : (z : S) (m : Mem z) → Holds G (fn z m) z
  fn-holds z m = subst ⟨_⟩ (appC-adequate G i0 i1 (fn z m ∷ z ∷ [])) (Ls.fn-holds z m)

  Dmap : DefinableMap
  Dmap = record Ls.Dmap { cod = P ; into = λ z m → inP (fn z m) z (fn-holds z m) }
```

THE TABLE: the set of pairs `(z, e_z)`, `z ∈ D`.

```agda
  T : S
  T = Ls.T

  T-in : (z : S) (m : Mem z) → ⟨ pr (fst z) (fst (fn z m)) ∈ fst T ⟩
  T-in = Ls.T-in

  T-out : (z e : S) → ⟨ pr (fst z) (fst e) ∈ fst T ⟩
        → Σ[ m ∈ Mem z ] (fst e ≡ fst (fn z m))
  T-out = Ls.T-out
```

THE INJECTION, when `G` is functional.

```agda
  module Functional
    (funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z') where

    inj : (z : S) (m : Mem z) (z' : S) (m' : Mem z')
        → fst (fn z m) ≡ fst (fn z' m') → fst z ≡ fst z'
    inj z m z' m' q = funct (fn z m) z z' (fn-holds z m)
      (subst (λ w → ⟨ pr w (fst z') ∈ fst G ⟩) (sym q) (fn-holds z' m'))

    injL : InjL D P
    injL = Inj.injL Dmap inj
```

Section 3. A singleton injects into an infinite ordinal: the one member goes to
0. The graph, over `(y ∷ z ∷ [])`: "`y = ∅`".

```agda
module Point (κ : S) (0∈κ : ⟨ # 0 ∈ fst κ ⟩) (a : S) where

  Y : S
  Y = sglʟ a

  Y-in : ⟨ fst a ∈ fst Y ⟩
  Y-in = sglʟ-in a (fst a) refl

  Y-out : (z : S) → ⟨ fst z ∈ fst Y ⟩ → fst z ≡ fst a
  Y-out z = sglʟ-out a (fst z)

  fo : Formula S 2
  fo = var i0 ≐ con ∅ʟ

  Dmap : DefinableMap
  Dmap = record
    { dom = Y ; cod = κ ; fn = λ _ _ → nn 0
    ; into = λ _ _ → 0∈κ
    ; graph = fo
    ; defines = λ z m → refl
    ; only = λ z m y h → S≡ h }

  inj : (z : S) (m : ⟨ fst z ∈ fst Y ⟩) (z' : S) (m' : ⟨ fst z' ∈ fst Y ⟩)
      → fst (nn 0) ≡ fst (nn 0) → fst z ≡ fst z'
  inj z m z' m' _ = Y-out z m ∙ sym (Y-out z' m')

  injL : InjL Y κ
  injL = Inj.injL Dmap inj
```

<!--en-->
## Counting every finite closure step

Starting from an injection of `X` into an infinite cardinal `κ`, each hull step is encoded by a formula shape and a finite parameter sequence. The shape count and sequence coding keep every iterate, and hence their union, injectable into `κ` inside `L`.
<!--zh-->
## 计数每一步有限闭包

从 `X` 到无穷基数 `κ` 的单射出发，每一步壳闭包都由公式形状与有限参数序列编码。形状计数与序列编码分别控制各次迭代，并进一步控制它们的并集，从而在 `L` 内部构造到 `κ` 的单射。
<!--ja-->
## 有限な閉包の各段階を数える

`X` から無限基数 `κ` への単射を出発点とし、包の各閉包段階を論理式の形状と有限なパラメータ列で符号化する。形状の数え上げと列の符号化により、各反復とその合併を `L` の内部で `κ` へ単射できる。
<!--/-->

Section 4. The hull of a counted start. The telescope of
src/L/GCH/ConstructibleHull.lagda.md `Condense′`, plus an infinite L-cardinal `κ` and an
internal injection of the start `X` into `κ`. Each iterate of the hull is
counted by induction: the new members of a step are the least satisfiers of a
key at a parameter environment over the last iterate, and `z ↦` the least such
(key, environment) pair is a definable injection (section 2), while the pairs
are counted by the limit stage and the finite sequences
(src/L/GCH/FiniteSequenceCoding.lagda.md).

```agda
module Count (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : V ℓ) (X⊆L : (x : V ℓ) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩)
  (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  (base : InjL (X , X-isL) κ) where
```

`Condense′` supplies the hull and its iterates together with their inclusion in
the hull. The telescope's least-witness relation supplies the formula, parameter
decoding and uniqueness needed to count each step.

```agda
  module Cn = Condense′ lam ordλ succλ X X⊆L ∅∈λ elem sup X-isL
    using ( hullStep; hullL; hullStep⊆Hull )
  module B = Telescope.Build lam ordλ succλ X X⊆L ∅∈λ
    using ( A; Body
          ; LeastWitness; leastWitnessFo; leastWitness-in; leastWitness-out
          ; LeastWitnessData; leastWitness-data; leastWitness-unique; witFo-leastWitness
          ; Φ; Φ-out; λ-isL; ω-num; pack )
  module SM = SatGraph B.A using ( pairs; pairs-out; valOf )
```

A member of the graph, read as a pair of a code and its value.

```agda
  module It = Telescope.HullIter.It lam ordλ succλ X X⊆L ∅∈λ X-isL B.pack
    using ( Num; iter; iter-in; iter-out; iterUnion-out; ω-num )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ using ( Hull⊆L )
  open Cn using ( hullStep; hullL )
```

Section 4.0. Facts about `κ`.

```agda
  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)
```

The pairing at `κ` (src/L/GCH/CardinalSquareLaw.lagda.md's square law).

```agda
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

  Lω↪κ : InjL Lω κ
  Lω↪κ = injl-trans Lω ωʟ κ limit-stage-counted
    (inclusion-coded ωʟ κ (λ z hz → ω⊆ (fst κ) oκ κ∉ω z hz))
```

Section 4.1. ONE STEP. `Z` is an iterate (a subset of the stage) with a coded
injection `E : Z ↪ κ`; `Φ Z` is counted.

```agda
  module OneStep (Z : S) (Z⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                 (E : S) (cE : InjCode E Z κ) where

    ΦZ : S
    ΦZ = B.Φ Z
```

The new members; among them the junk value and the witnesses.

The three separation specifications are sealed apart from their readers. If a
reader opens `hasSeparationL` while conversion checks its result, this block alone
runs past 120 seconds. Through the named specifications, a fresh check of this
module takes 12.17 seconds.

```agda
    opaque
      D₂ : S
      D₂ = hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .fst

      D₂-spec : (z : S) → (fst z ∈ fst D₂)
              ≡ ((fst z ∈ fst ΦZ) ⊓ ((z ∷ []) ⊨ ¬̇ (var i0 ∈̇ con Z)))
      D₂-spec z = hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .snd z

    opaque
      D₂-in : (z : S) → ⟨ fst z ∈ fst ΦZ ⟩ → (⟨ fst z ∈ fst Z ⟩ → Empty.⊥) → ⟨ fst z ∈ fst D₂ ⟩
      D₂-in z h no = subst ⟨_⟩ (sym (D₂-spec z)) (h , λ z∈ → lift (no z∈))

      D₂-out : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst ΦZ ⟩ × (⟨ fst z ∈ fst Z ⟩ → Empty.⊥)
      D₂-out z h = r .fst , λ z∈ → lower (r .snd z∈)
        where
        r : ⟨ fst z ∈ fst ΦZ ⟩
          × ⟨ (z ∷ []) ⊨ ¬̇ (var i0 ∈̇ con Z) ⟩
        r = subst ⟨_⟩ (D₂-spec z) h

    opaque
      D∅ : S
      D∅ = hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .fst

      D∅-spec : (z : S) → (fst z ∈ fst D∅)
              ≡ ((fst z ∈ fst D₂) ⊓ ((z ∷ []) ⊨ var i0 ≐ con ∅ʟ))
      D∅-spec z = hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .snd z

    opaque
      D∅-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → fst z ≡ ∅ → ⟨ fst z ∈ fst D∅ ⟩
      D∅-in z h e = subst ⟨_⟩ (sym (D∅-spec z)) (h , e)

      D∅-out : (z : S) → ⟨ fst z ∈ fst D∅ ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅)
      D∅-out z h = subst ⟨_⟩ (D∅-spec z) h

    opaque
      Dw : S
      Dw = hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .fst

      Dw-spec : (z : S) → (fst z ∈ fst Dw)
              ≡ ((fst z ∈ fst D₂) ⊓ ((z ∷ []) ⊨ ¬̇ (var i0 ≐ con ∅ʟ)))
      Dw-spec z = hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .snd z

    opaque
      Dw-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → (fst z ≡ ∅ → Empty.⊥) → ⟨ fst z ∈ fst Dw ⟩
      Dw-in z h ne = subst ⟨_⟩ (sym (Dw-spec z)) (h , λ q → lift (ne q))

      Dw-out : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅ → Empty.⊥)
      Dw-out z h = r .fst , λ q → lower (r .snd q)
        where
        r : ⟨ fst z ∈ fst D₂ ⟩
          × ⟨ (z ∷ []) ⊨ ¬̇ (var i0 ≐ con ∅ʟ) ⟩
        r = subst ⟨_⟩ (Dw-spec z) h
    module U₁ = Union2 Z D₂ using ( D; in₁; in₂ )
    module U₃ = Union2 D∅ Dw using ( D; in₁; in₂ )

    ΦZ⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst ΦZ ⟩ → ⟨ z ∈ˢ fst U₁.D ⟩
    ΦZ⊆ z h = go (lem (z ∈ fst Z))
      where
      zS : S
      zS = z , isL-trans {x = fst ΦZ} {y = z} h (snd ΦZ)
      go : ⟨ z ∈ fst Z ⟩ ⊎ (⟨ z ∈ fst Z ⟩ → Empty.⊥) → ⟨ z ∈ fst U₁.D ⟩
      go (inl hz) = U₁.in₁ zS hz
      go (inr no) = U₁.in₂ zS (D₂-in zS h no)

    D₂⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst D₂ ⟩ → ⟨ z ∈ˢ fst U₃.D ⟩
    D₂⊆ z h = go (lem ((z ≡ ∅) , setIsSet z ∅))
      where
      zS : S
      zS = z , isL-trans {x = fst D₂} {y = z} h (snd D₂)
      go : (z ≡ ∅) ⊎ (z ≡ ∅ → Empty.⊥) → ⟨ z ∈ fst U₃.D ⟩
      go (inl e)  = U₃.in₁ zS (D∅-in zS h e)
      go (inr ne) = U₃.in₂ zS (Dw-in zS h ne)
```

The junk value is `0 ∈ κ`.

```agda
    D∅↪κ : InjL D∅ κ
    D∅↪κ = inclusion-coded D∅ κ
      (λ z hz → subst (λ w → ⟨ w ∈ fst κ ⟩)
        (sym (D∅-out (z , isL-trans {x = fst D∅} {y = z} hz (snd D∅)) hz .snd)) (num∈κ 0))
```

THE WITNESS PAIRS. `p = (s, e)`: `s` the key of a parameter-free formula (a
member of `L_ω`), `e` the parameter environment over `Z` (a member of `seqL Z`).
`(p, z) ∈ G` when `z` is the least satisfier of `s` at `e`, in the words of
src/L/GCH/ConstructibleHull.lagda.md `bodyFo`.

The separating description, over `(q ∷ [])`: "`q = (p, z)`, `p ∈ PB`, `p = (s,
e)`, and for `Z` pinned, some `k`, `e'`, `T` make `bodyFo` hold". Binders,
outermost first: `p`, `z`, `s`, `e`, `Z`, `k`, `e'`, `T`. Inside all of them:
`T` is 0, `e'` is 1, `k` is 2, `Z` is 3, `e` is 4, `s` is 5, `z` is 6, `p` is 7,
`q` is 8; `bodyFo` reads `(T ∷ e' ∷ e ∷ s ∷ k ∷ w ∷ Z ∷ [])`.

```agda
    module U₂ = Union2 Lω (seqL Z) using ( D; in₁; in₂ )

    PB : S
    PB = prodL U₂.D

```

`Z` pinned, sealed.

```agda
    opaque
      pin₅ : Formula S 5
      pin₅ = pinAt Z B.leastWitnessFo

      pin₅-in : (e s z p q : S) → B.LeastWitness Z e s z
              → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
      pin₅-in e s z p q h =
        pin-in Z B.leastWitnessFo (e ∷ s ∷ z ∷ p ∷ q ∷ [])
          (B.leastWitness-in Z e s z p q h)

      pin₅-out : (e s z p q : S) → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
               → B.LeastWitness Z e s z
      pin₅-out e s z p q h =
        B.leastWitness-out Z e s z p q
          (pin-out Z B.leastWitnessFo (e ∷ s ∷ z ∷ p ∷ q ∷ []) h)
```

The host reading of a witness pair.

```agda
    GW : (p z : S) → Type (ℓ-suc ℓ)
    GW p z = ∥ Σ[ s ∈ S ] Σ[ e ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × B.LeastWitness Z e s z) ∥₁
```

`s` and `e` bound, sealed.

```agda
    opaque
      se₃ : Formula S 3
      se₃ = ∃̇ (∃̇ (prAtL i3 i1 i0 ∧̇ pin₅))

      se₃-in : (z p q s e : S) → fst p ≡ pr (fst s) (fst e)
             → B.LeastWitness Z e s z → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩
      se₃-in z p q s e qp h =
        ∣ s , ∣ e , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ []))) qp
                    , pin₅-in e s z p q h ) ∣₁ ∣₁

      se₃-out : (z p q : S) → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩ → GW p z
      se₃-out z p q = PT.rec squash₁ at₁
        where
        at₂ : (s : S) → Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                   × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) → GW p z
        at₂ s (e , (qp , h)) = ∣ s , e
          , ( subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ [])) qp
            , pin₅-out e s z p q h ) ∣₁
        at₁ : Σ[ s ∈ S ] ∥ Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                      × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) ∥₁ → GW p z
        at₁ (s , h) = PT.rec squash₁ (at₂ s) h
```

The separating description, sealed.

```agda
    private
      module WitnessGraph = Relation PB Dw ((var i1 ∈̇ con PB) ∧̇ se₃)
        (λ p z → (fst p ∈ fst PB) ⊓ (GW p z , squash₁))
        (λ p z q h → h .fst , se₃-out z p q (h .snd))
        (λ p z q h → h .fst , PT.rec (snd ((z ∷ p ∷ q ∷ []) ⊨ se₃))
          (λ { (s , e , qp , hw) → se₃-in z p q s e qp hw }) (h .snd))

    G : S
    G = WitnessGraph.rel

    G-in : (p z : S) → ⟨ fst p ∈ fst PB ⟩ → ⟨ fst z ∈ fst Dw ⟩
         → (s e : S) → fst p ≡ pr (fst s) (fst e)
         → B.LeastWitness Z e s z → Holds G p z
    G-in p z hp hz s e qp h =
      WitnessGraph.into p z hp hz (hp , ∣ s , e , qp , h ∣₁)

    G-out : (p z : S) → Holds G p z → ⟨ fst p ∈ fst PB ⟩ × GW p z
    G-out = WitnessGraph.pair-out
```

The relation is carved from the bound on `PB × Dw`; its pair reading is supplied
by `Relation`.

EXISTENCE: every witness has a pair. The key is a member of `L_ω` (it is the
arity numeral paired with a hereditarily finite code), and the environment is a
finite sequence over `Z`.

The semantic reading supplies the formula key and the parameter environment;
the counting layer only places those two objects in its product bound.

```agda
    have : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
    have z hz = PT.rec squash₁ body (B.Φ-out Z z (D₂-out z (Dw-out z hz .fst) .fst))
      where
      body : B.Body Z z → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
      body (inl h) = Empty.rec (D₂-out z (Dw-out z hz .fst) .snd h)
      body (inr (inl e)) = Empty.rec (Dw-out z hz .snd e)
      body (inr (inr hw)) = PT.rec squash₁ read (B.witFo-leastWitness z Z hw)
        where
        read : Σ[ e ∈ S ] Σ[ s ∈ S ] B.LeastWitness Z e s z
             → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
        read (e , s , hw') = PT.map at (B.leastWitness-data Z e s z hw')
          where
          at : B.LeastWitnessData Z e s → Σ[ p ∈ S ] Holds G p z
          at (n , g , qe , hs) = prʟ s e
            , G-in (prʟ s e) z
                (subst (λ w → ⟨ w ∈ fst PB ⟩) (sym (prʟ-fst s e))
                  (prodL-in U₂.D s e (U₂.in₁ s hs)
                    (U₂.in₂ e (seqL-in Z n e
                      (subst (λ w → ⟨ w ∈ˢ fst (envSet Z n) ⟩) (sym qe) (envSet-in Z g))))))
                hz s e (prʟ-fst s e) hw'
```

<!--en-->
## Uniqueness for a witness key

A formula key together with its parameter environment selects at most one least witness. Thus equal pair codes force equal witnesses, which makes the witness graph functional.
<!--zh-->
## 见证键的唯一性

公式键与其参数环境至多选出一个最小见证。因此，相等的对编码迫使见证相等，从而使见证图成为函数图。
<!--ja-->
## 証人キーに対する一意性

論理式のキーとそのパラメータ環境は、最小の証人を高々一つ選びます。したがって、対のコードが等しければ証人も等しくなり、証人グラフは関数的になります。
<!--/-->

```agda
    funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z'
    funct p z z' h h' = PT.rec2 (setIsSet (fst z) (fst z')) read (G-out p z h .snd) (G-out p z' h' .snd)
      where
      read : Σ[ s ∈ S ] Σ[ e ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × B.LeastWitness Z e s z)
           → Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ]
               ((fst p ≡ pr (fst s₂) (fst e₂)) × B.LeastWitness Z e₂ s₂ z')
           → fst z ≡ fst z'
      read (s , e , q , hw) (s₂ , e₂ , q₂ , hw₂) =
        B.leastWitness-unique Z e s z z' hw hw₂'
        where
        ee : (fst s₂ ≡ fst s) × (fst e₂ ≡ fst e)
        ee = pr-inj (sym q₂ ∙ q)
        hw₂' : B.LeastWitness Z e s z'
        hw₂' = subst2 (λ e' s' → B.LeastWitness Z e' s' z')
          (S≡ {x = e₂} {y = e} (snd ee)) (S≡ {x = s₂} {y = s} (fst ee)) hw₂
```

THE STEP COUNT.

The stage of the pair bound.

```agda
    γG : V ℓ
    γG = stage (fst PB) (snd PB)

    oγG : IsOrd γG
    oγG = stage-ord (fst PB) (snd PB)

    PB⊆Lγ : (p : S) → ⟨ fst p ∈ fst PB ⟩ → ⟨ fst p ∈ Lset γG ⟩
    PB⊆Lγ p hp = layer-trans (Lset-layer γG) {x = fst PB} {y = fst p} hp (stage-mem (fst PB) (snd PB))

    module LP = LeastPre γG oγG G Dw PB (λ p z h → G-out p z h .fst) PB⊆Lγ have
      using ( module Functional )

    Dw↪PB : InjL Dw PB
    Dw↪PB = LP.Functional.injL funct

    seq↪κ : InjL (seqL Z) κ
    seq↪κ = injl-trans (seqL Z) (seqL κ) κ (seq-map Z κ E cE) (seq-count κ oκ κ∉ω)

    PB↪κ : InjL PB κ
    PB↪κ = injl-trans PB (prodL κ) κ
      (prod-inj U₂.D κ
        (injl-trans U₂.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) Lω (seqL Z) Lω↪κ seq↪κ) pairκ))
      pairκ

    Dw↪κ : InjL Dw κ
    Dw↪κ = injl-trans Dw PB κ Dw↪PB PB↪κ

    D₂↪κ : InjL D₂ κ
    D₂↪κ = injl-trans D₂ U₃.D κ (inclusion-coded D₂ U₃.D D₂⊆)
      (injl-trans U₃.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) D∅ Dw D∅↪κ Dw↪κ) pairκ)

    result : InjL ΦZ κ
    result = injl-trans ΦZ U₁.D κ (inclusion-coded ΦZ U₁.D ΦZ⊆)
      (injl-trans U₁.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) Z D₂ ∣ E , cE ∣₁ D₂↪κ) pairκ)

  step-count : (Z : S) → ((z : V ℓ) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             → InjL Z κ → InjL (B.Φ Z) κ
  step-count Z Z⊆ = PT.rec squash₁ (λ { (E , cE) → OneStep.result Z Z⊆ E cE })
```

Every iterate is counted.

```agda
  iter⊆L : (n : ℕ) (z : V ℓ) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  iter⊆L n z hz = HSH.Hull⊆L z (Cn.hullStep⊆Hull n z hz)

  counted : (n : ℕ) → InjL (hullStep n) κ
  counted zero    = base
  counted (suc n) = step-count (hullStep n) (iter⊆L n) (counted n)
```

Section 4.2. THE TABLE OF LEAST CODES, `n ↦ e_n`, as a set of L. A stage `γ`
holds one code for every `n` (the least stage holding one is a function of `n`,
and `γ` bounds those), and `e_n` is the stage-order-least member of `L_γ` coding
an injection of the n-th iterate into `κ`: the least preimage under the relation
"`(F, n)`: `F ∈ L_γ` codes an injection of the iterate at `n` into `κ`".

The relation's description, over `(q ∷ [])`: "`q = (F, n)`, `F ∈ L_γ`, and some
`B` has `(n, B)` in the iteration table and `F` an injection code from `B` into
`κ`". Inside: `B` is 0, `n` is 1, `F` is 2, `q` is 3.

```agda
  HoldsAt : ℕ → V ℓ → hProp (ℓ-suc ℓ)
  HoldsAt n σ = ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset σ ⟩ × InjCode F (hullStep n) κ) ∥₁ , squash₁

  opaque
    ls : (n : ℕ) → LeastOrd (HoldsAt n)
    ls n = PT.rec (isPropLeastOrd (HoldsAt n)) from (counted n)
      where
      from : Σ[ F ∈ S ] InjCode F (hullStep n) κ → LeastOrd (HoldsAt n)
      from (F , code) = leastOrd (HoldsAt n)
        ∣ stage (fst F) (snd F) , stage-ord (fst F) (snd F)
        , ∣ F , stage-mem (fst F) (snd F) , code ∣₁ ∣₁

  opaque
    γ : V ℓ
    γ = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst) .fst

    oγ : IsOrd γ
    oγ = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst) .snd .fst

    bnd-in : (n : ℕ) → ⟨ ls n .fst ∈ γ ⟩
    bnd-in n = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst)
                 .snd .snd (lift n)

  code-at-γ : (n : ℕ) → ⟨ HoldsAt n γ ⟩
  code-at-γ n = PT.map raise (ls n .snd .snd .fst)
    where
    raise : Σ[ F ∈ S ] (⟨ fst F ∈ Lset (ls n .fst) ⟩ × InjCode F (hullStep n) κ)
          → Σ[ F ∈ S ] (⟨ fst F ∈ Lset γ ⟩ × InjCode F (hullStep n) κ)
    raise (F , h , code) = F , Lset-mono {α = γ} {β = ls n .fst} (bnd-in n) h , code
```

Sealed: the elements that reach a slot.

```agda
  opaque
    Lγ : S
    Lγ = LsetS γ oγ

    Lγ-fst : fst Lγ ≡ Lset γ
    Lγ-fst = refl

    Iter : S
    Iter = It.iter

    Iter-in : (n : ℕ) → ⟨ pr (# n) (fst (hullStep n)) ∈ fst Iter ⟩
    Iter-in = It.iter-in

    Iter-out : (y : S) → ⟨ fst y ∈ fst Iter ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ pr (# n) (fst (hullStep n))) ∥₁
    Iter-out = It.iter-out

  TabWit : (F n : S) → Type (ℓ-suc ℓ)
  TabWit F n = ⟨ fst F ∈ Lset γ ⟩ × ∥ Σ[ Zn ∈ S ] (Holds Iter n Zn × InjCode F Zn κ) ∥₁

  opaque
    tabBody : Formula S 3
    tabBody = (var i1 ∈̇ con Lγ) ∧̇ ∃̇ (appC Iter i1 i0 ∧̇ injFo κ i2 i0)

    tab-read : (F n q : S) → ⟨ (n ∷ F ∷ q ∷ []) ⊨ tabBody ⟩ → TabWit F n
    tab-read F n q (hF , h) = subst (λ w → ⟨ fst F ∈ w ⟩) Lγ-fst hF
      , PT.map (λ { (Zn , hI , hc) → Zn
          , subst ⟨_⟩ (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ [])) hI
          , InjFo.read κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) hc }) h

    tab-fill : (F n q : S) → TabWit F n → ⟨ (n ∷ F ∷ q ∷ []) ⊨ tabBody ⟩
    tab-fill F n q (hF , h) = subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF
      , PT.map (λ { (Zn , hI , hc) → Zn
          , subst ⟨_⟩ (sym (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ []))) hI
          , InjFo.fill κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) hc }) h

  private
    module TableGraph = Relation Lγ ωʟ tabBody
      (λ F n → TabWit F n , isProp× (snd (fst F ∈ Lset γ)) squash₁) tab-read tab-fill

  Gt : S
  Gt = TableGraph.rel

  Gt-in : (F n Zn : S) → ⟨ fst F ∈ Lset γ ⟩ → ⟨ fst n ∈ fst ωʟ ⟩
        → Holds Iter n Zn → InjCode F Zn κ → Holds Gt F n
  Gt-in F n Zn hF hn hI code = TableGraph.into F n
    (subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF) hn (hF , ∣ Zn , hI , code ∣₁)

  Gt-out : (F n : S) → Holds Gt F n → TabWit F n
  Gt-out = TableGraph.pair-out

  have-code : (n : S) → ⟨ fst n ∈ fst ωʟ ⟩ → ∥ Σ[ F ∈ S ] Holds Gt F n ∥₁
  have-code n hn = PT.rec squash₁ at (It.ω-num n hn)
    where
    at : It.Num n → ∥ Σ[ F ∈ S ] Holds Gt F n ∥₁
    at (k , qk) = PT.map
      (λ { (F , hF , code) → F
         , Gt-in F n (hullStep k) hF hn
             (subst (λ w → ⟨ pr w (fst (hullStep k)) ∈ fst Iter ⟩) (cong fst qk) (Iter-in k)) code })
      (code-at-γ k)

  module Tb = LeastPre γ oγ Gt ωʟ Lγ
    (λ F n h → subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) (Gt-out F n h .fst))
    (λ F hF → subst (λ w → ⟨ fst F ∈ w ⟩) Lγ-fst hF)
    have-code
    using ( T; fn; T-in; T-out; fn-holds )
```

THE TABLE, and its entries.

```agda
  Te : S
  Te = Tb.T

  eS : (n : S) → ⟨ fst n ∈ fst ωʟ ⟩ → S
  eS = Tb.fn

  Te-in : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩) → ⟨ pr (fst n) (fst (eS n m)) ∈ fst Te ⟩
  Te-in = Tb.T-in

  Te-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst Te ⟩
         → Σ[ m ∈ ⟨ fst n ∈ fst ωʟ ⟩ ] (fst F ≡ fst (eS n m))
  Te-out = Tb.T-out
```

The entry at `n` codes an injection of some iterate recorded at `n`.

```agda
  e-wit : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩)
        → ∥ Σ[ Zn ∈ S ] (Holds Iter n Zn × InjCode (eS n m) Zn κ) ∥₁
  e-wit n m = Gt-out (eS n m) n (Tb.fn-holds n m) .snd
```

The entry at the numeral `k` codes an injection of the k-th iterate.

```agda
  e-code : (k : ℕ) → InjCode (eS (nn k) (#∈ω k)) (hullStep k) κ
  e-code k = PT.rec (isPropInjCode (eS (nn k) (#∈ω k)) (hullStep k) κ) read (e-wit (nn k) (#∈ω k))
    where
    F : S
    F = eS (nn k) (#∈ω k)
    read : Σ[ Zn ∈ S ] (Holds Iter (nn k) Zn × InjCode F Zn κ) → InjCode F (hullStep k) κ
    read (Zn , hI , code) = PT.rec (isPropInjCode F (hullStep k) κ) at
      (Iter-out (prʟ (nn k) Zn) (subst (λ w → ⟨ w ∈ fst Iter ⟩) (sym (prʟ-fst (nn k) Zn)) hI))
      where
      at : Σ[ k' ∈ ℕ ] (fst (prʟ (nn k) Zn) ≡ pr (# k') (fst (hullStep k'))) → InjCode F (hullStep k) κ
      at (k' , q) = injcode-resp F F Zn (hullStep k) κ refl
        (snd ee ∙ cong (λ j → fst (hullStep j)) (sym (#-inj k k' (fst ee)))) code
        where
        ee : (# k ≡ # k') × (fst Zn ≡ fst (hullStep k'))
        ee = pr-inj (sym (prʟ-fst (nn k) Zn) ∙ q)
```

Section 4.3. THE HULL INJECTS INTO `κ`. `z ↦` the least `(n, v)` with `z` at the
n-th iterate and `(z, v)` an entry of `e_n`, into `prodL κ`, then the pairing at
`κ`. The relation "`((n, v), z)`: `n ∈ ω`, `(n, F) ∈ Te`, `(z, v) ∈ F`" is
functional in the sense of section 2, since each `e_n` is injective.

Its description, over `(q ∷ [])`: binders `p`, `z`, then `n`, `v`, then `F`.
Inside: `F` is 0, `v` is 1, `n` is 2, `z` is 3, `p` is 4, `q` is 5.

```agda
  FinWit : (p z : S) → Type (ℓ-suc ℓ)
  FinWit p z = ∥ Σ[ n ∈ S ] Σ[ v ∈ S ] Σ[ F ∈ S ]
      ((fst p ≡ pr (fst n) (fst v)) × ⟨ fst n ∈ fst ωʟ ⟩ × Holds Te n F × Holds F z v) ∥₁
```

The innermost conjunction, sealed with its readings.

```agda
  opaque
    inner₆ : Formula S 6
    inner₆ = appC Te i2 i0 ∧̇ appAt i0 i3 i1

    inner₆-in : (F v n z p q : S) → Holds Te n F → Holds F z v
              → ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩
    inner₆-in F v n z p q ht hv =
        subst ⟨_⟩ (sym (appC-adequate Te i2 i0 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []))) ht
      , subst ⟨_⟩ (sym (appAt-adequate i0 i3 i1 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []))) hv

    inner₆-out : (F v n z p q : S) → ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩
               → Holds Te n F × Holds F z v
    inner₆-out F v n z p q (ht , hv) =
        subst ⟨_⟩ (appC-adequate Te i2 i0 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ [])) ht
      , subst ⟨_⟩ (appAt-adequate i0 i3 i1 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ [])) hv
```

`n`, `v` and `F` bound, sealed.

```agda
  opaque
    nv₃ : Formula S 3
    nv₃ = ∃̇ (∃̇ (prAtL i3 i1 i0 ∧̇ ((var i1 ∈̇ con ωʟ) ∧̇ ∃̇ inner₆)))

    nv₃-in : (z p q n v F : S) → fst p ≡ pr (fst n) (fst v) → ⟨ fst n ∈ fst ωʟ ⟩
           → Holds Te n F → Holds F z v → ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩
    nv₃-in z p q n v F qp hn ht hv =
      ∣ n , ∣ v , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (v ∷ n ∷ z ∷ p ∷ q ∷ []))) qp
                  , ( hn , ∣ F , inner₆-in F v n z p q ht hv ∣₁ ) ) ∣₁ ∣₁

    nv₃-out : (z p q : S) → ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩ → FinWit p z
    nv₃-out z p q = PT.rec squash₁ at₁
      where
      Inner : (n v : S) → Type (ℓ-suc ℓ)
      Inner n v = ⟨ (v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                × ( ⟨ fst n ∈ fst ωʟ ⟩ × ∥ Σ[ F ∈ S ] ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩ ∥₁ )
      at₃ : (n v : S) → Inner n v → FinWit p z
      at₃ n v (qp , (hn , h)) = PT.map
        (λ { (F , hi) → n , v , F
           , ( subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (v ∷ n ∷ z ∷ p ∷ q ∷ [])) qp
             , hn , inner₆-out F v n z p q hi ) }) h
      at₂ : (n : S) → Σ[ v ∈ S ] Inner n v → FinWit p z
      at₂ n (v , h) = at₃ n v h
      at₁ : Σ[ n ∈ S ] ∥ Σ[ v ∈ S ] Inner n v ∥₁ → FinWit p z
      at₁ (n , h) = PT.rec squash₁ (at₂ n) h

  private
    module FinalGraph = Relation (prodL κ) hullL nv₃ (λ p z → FinWit p z , squash₁)
      (λ p z q → nv₃-out z p q)
      (λ p z q → PT.rec (snd ((z ∷ p ∷ q ∷ []) ⊨ nv₃))
        (λ { (n , v , F , qp , hn , ht , hv) → nv₃-in z p q n v F qp hn ht hv }))

  Gf : S
  Gf = FinalGraph.rel

  Gf-in : (p z n v F : S) → ⟨ fst p ∈ fst (prodL κ) ⟩ → ⟨ fst z ∈ fst hullL ⟩
        → fst p ≡ pr (fst n) (fst v) → ⟨ fst n ∈ fst ωʟ ⟩ → Holds Te n F → Holds F z v
        → Holds Gf p z
  Gf-in p z n v F hp hz qp hn ht hv = FinalGraph.into p z hp hz ∣ n , v , F , qp , hn , ht , hv ∣₁

  Gf-out : (p z : S) → Holds Gf p z → FinWit p z
  Gf-out = FinalGraph.pair-out
```

A value of the entry at `n` is a member of `κ`.

```agda
  entry-ran : (n F z v : S) → Holds Te n F → Holds F z v → ⟨ fst v ∈ fst κ ⟩
  entry-ran n F z v ht hv = PT.rec (snd (fst v ∈ fst κ))
    (λ { (Zn , _ , code) → snd (snd (snd code)) z v
          (subst (λ w → ⟨ pr (fst z) (fst v) ∈ w ⟩) (Te-out n F ht .snd) hv) })
    (e-wit n (Te-out n F ht .fst))

  inPκ : (p z : S) → Holds Gf p z → ⟨ fst p ∈ fst (prodL κ) ⟩
  inPκ p z h = PT.rec (snd (fst p ∈ fst (prodL κ)))
    (λ { (n , v , F , (qp , hn , ht , hv)) →
       subst (λ w → ⟨ w ∈ fst (prodL κ) ⟩) (sym qp)
         (prodL-in κ n v (ω⊆ (fst κ) oκ κ∉ω (fst n) hn) (entry-ran n F z v ht hv)) })
    (Gf-out p z h)

  have-fin : (z : S) → ⟨ fst z ∈ fst hullL ⟩ → ∥ Σ[ p ∈ S ] Holds Gf p z ∥₁
  have-fin z hz = PT.rec squash₁ at (It.iterUnion-out z hz)
    where
    at : Σ[ n ∈ ℕ ] ⟨ fst z ∈ fst (hullStep n) ⟩ → ∥ Σ[ p ∈ S ] Holds Gf p z ∥₁
    at (n , hn) = PT.map val (domAt-in zero (suc zero) (F ∷ hullStep n ∷ []) (fst (snd (e-code n))) z hn)
      where
      F : S
      F = eS (nn n) (#∈ω n)
      val : Σ[ v ∈ S ] Holds F z v → Σ[ p ∈ S ] Holds Gf p z
      val (v , hv) = prʟ (nn n) v
        , Gf-in (prʟ (nn n) v) z (nn n) v F
            (subst (λ w → ⟨ w ∈ fst (prodL κ) ⟩) (sym (prʟ-fst (nn n) v))
              (prodL-in κ (nn n) v (num∈κ n) (snd (snd (snd (e-code n))) z v hv)))
            hz (prʟ-fst (nn n) v) (#∈ω n) (Te-in (nn n) (#∈ω n)) hv

  funct-fin : (p z z' : S) → Holds Gf p z → Holds Gf p z' → fst z ≡ fst z'
  funct-fin p z z' h h' = PT.rec2 (setIsSet (fst z) (fst z')) read (Gf-out p z h) (Gf-out p z' h')
    where
    read : Σ[ n ∈ S ] Σ[ v ∈ S ] Σ[ F ∈ S ]
             ((fst p ≡ pr (fst n) (fst v)) × ⟨ fst n ∈ fst ωʟ ⟩ × Holds Te n F × Holds F z v)
         → Σ[ n' ∈ S ] Σ[ v' ∈ S ] Σ[ F' ∈ S ]
             ((fst p ≡ pr (fst n') (fst v')) × ⟨ fst n' ∈ fst ωʟ ⟩ × Holds Te n' F' × Holds F' z' v')
         → fst z ≡ fst z'
    read (n , v , F , (qp , hn , ht , hv)) (n' , v' , F' , (qp' , hn' , ht' , hv')) =
      PT.rec (setIsSet (fst z) (fst z'))
        (λ { (Zn , _ , code) →
           injAt-out zero (eS n m ∷ Zn ∷ []) (fst (snd (snd code))) v z z'
             (subst (λ w → ⟨ pr (fst z) (fst v) ∈ w ⟩) (Te-out n F ht .snd) hv)
             (subst2 (λ u w → ⟨ pr (fst z') u ∈ w ⟩) (sym (snd ee)) qF hv') })
        (e-wit n m)
      where
      ee : (fst n ≡ fst n') × (fst v ≡ fst v')
      ee = pr-inj (sym qp ∙ qp')
      m : ⟨ fst n ∈ fst ωʟ ⟩
      m = Te-out n F ht .fst
```

The table value at the same index is the same value.

```agda
      pth : _≡_ {A = Σ[ c ∈ S ] ⟨ fst c ∈ fst ωʟ ⟩} (n' , Te-out n' F' ht' .fst) (n , m)
      pth = Σ≡Prop (λ c → snd (fst c ∈ fst ωʟ)) (S≡ {x = n'} {y = n} (sym (fst ee)))

      qF : fst F' ≡ fst (eS n m)
      qF = Te-out n' F' ht' .snd ∙ (λ i → fst (eS (fst (pth i)) (snd (pth i))))

  γf : V ℓ
  γf = stage (fst (prodL κ)) (snd (prodL κ))

  oγf : IsOrd γf
  oγf = stage-ord (fst (prodL κ)) (snd (prodL κ))

  prodκ⊆Lγ : (p : S) → ⟨ fst p ∈ fst (prodL κ) ⟩ → ⟨ fst p ∈ Lset γf ⟩
  prodκ⊆Lγ p hp =
    layer-trans (Lset-layer γf) {x = fst (prodL κ)} {y = fst p} hp (stage-mem (fst (prodL κ)) (snd (prodL κ)))

  module LF = LeastPre γf oγf Gf hullL (prodL κ) inPκ prodκ⊆Lγ have-fin using ( module Functional )
```

THE THEOREM OF THIS SECTION: the hull injects into `κ`, internally.

```agda
  hull↪κ : InjL hullL κ
  hull↪κ = injl-trans hullL (prodL κ) κ (LF.Functional.injL funct-fin) pairκ
```
