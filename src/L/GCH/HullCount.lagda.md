# The Skolem hull of a counted start is counted, internally

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.HullCount {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ; isL-Lset )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; unionʟ )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; numL; appAt; appAt-adequate
        ; svAt-out; domAt-in; domAt-out; tagAtL; tagAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt-out; module Extract )
open import L.Choice.Step {ℓ} lem using ( orderAt; relOf ) renaming ( Mem to MemOf )
open import L.Choice.Order {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; leastOf; lt; eq; gt ) renaming ( Tri to Tri∙ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap; module Inj; module Graph )
open import L.GCH.Pairing {ℓ} lem using ( prodL; prodL-in; prodL-out; isL-ord; ordL )
open import L.GCH.OmegaRec {ℓ} lem using ( pairʟ-in; pairʟ-out; unionʟ-in; unionʟ-out )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate; module PairBound )
open import L.Stage {ℓ} lem using ( LeastOrd; isPropLeastOrd; leastOrd; stage; stage-ord; stage-mem )
open import L.Ordinal using ( boundingOrd )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-in; module Recover )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Choice.Name {ℓ} lem using ( limitCode; numeral∈limit; pr∈limit )
open import L.Choice.Internal {ℓ} lem using ( freeCode-out )
open import L.GCH.Complete {ℓ} lem using ( Superadequate; module SatMap )
open import L.GCH.Frame {ℓ} lem using ( module Frame )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import L.GCH.HullIn {ℓ} lem using ( module Condense′; module Telescope )
open import L.GCH.StageCount {ℓ} lem
  using ( isPropInjCode; injcode-resp; injFo; module InjFo; pinAt; pin-in; pin-out; seq-map; Lω )
open import L.GCH.Sequences {ℓ} lem using ( seqL; seqL-in; seq-count )
open import L.GCH.CountableBase {ℓ} lem using ( limit-stage-counted )
open import L.GCH.Pairing {ℓ} lem using ( prod-inj; ω⊆; Goal; module Step )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import V.Hierarchy {ℓ} using ( regularityV )
import Cubical.Induction.WellFounded as WF
open import Cubical.Foundations.Prelude using ( subst2; isProp→PathP )

open import Cubical.Data.Nat.Properties using ( znots; snotz )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ3; isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Renaming, read at the same satisfaction as `_⊨_` (as HullIn does).
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )

-- "The pair (x, y) is a member of F", the shape every clause reads.
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

-- The numeral k as an element of L.
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
  i8 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))
  i8 = suc i7

  -- The renaming of section 4.1's body into its nine slots, and its
  -- agreement, at the top level.  Measured: the same clauses cost
  -- 3.4 s and 5.3 s inside `Count.OneStep`, 0.5 s and 1.4 s here, and
  -- 13 ms and 36 ms in a probe file that imports only their context;
  -- the cost of a clause grows with what the module already holds.
  -- Slots, outermost first: T is 0, e' is 1, k is 2, Z is 3, e is 4,
  -- s is 5, z is 6, p is 7, q is 8; the body reads
  -- (T ∷ e' ∷ e ∷ s ∷ k ∷ z ∷ Z ∷ []).
  ρ₉ : Fin 7 → Fin 9
  ρ₉ zero = i0
  ρ₉ (suc zero) = i1
  ρ₉ (suc (suc zero)) = i4
  ρ₉ (suc (suc (suc zero))) = i5
  ρ₉ (suc (suc (suc (suc zero)))) = i2
  ρ₉ (suc (suc (suc (suc (suc zero))))) = i6
  ρ₉ (suc (suc (suc (suc (suc (suc zero)))))) = i3

  ag₉ : (T e' k Zv e s z p q : S)
      → Ren.Agrees ρ₉ (T ∷ e' ∷ k ∷ Zv ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) (T ∷ e' ∷ e ∷ s ∷ k ∷ z ∷ Zv ∷ [])
  ag₉ T e' k Zv e s z p q zero = refl
  ag₉ T e' k Zv e s z p q (suc zero) = refl
  ag₉ T e' k Zv e s z p q (suc (suc zero)) = refl
  ag₉ T e' k Zv e s z p q (suc (suc (suc zero))) = refl
  ag₉ T e' k Zv e s z p q (suc (suc (suc (suc zero)))) = refl
  ag₉ T e' k Zv e s z p q (suc (suc (suc (suc (suc zero))))) = refl
  ag₉ T e' k Zv e s z p q (suc (suc (suc (suc (suc (suc zero)))))) = refl

-- =====================================================================
-- SECTION 0.  TWO SMALL FACTS.
-- =====================================================================

-- An ordinal is a subset of its own stage.
ord⊆Lset : (α : V ℓ) → IsOrd α → (z : V ℓ) → ⟨ z ∈ α ⟩ → ⟨ z ∈ Lset α ⟩
ord⊆Lset α oα z z∈α =
  Lset-cumul z α oz oα z∈α (ord∈Lset-suc z oz)
  where
  oz : IsOrd z
  oz = mem-ord {A = α} oα z z∈α

-- Membership in the model's binary union of two elements.
module Union2 (D₁ D₂ : S) where

  D : S
  D = unionʟ (pairʟ D₁ D₂)

  in₁ : (z : S) → ⟨ fst z ∈ fst D₁ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₁ z h = unionʟ-in (pairʟ D₁ D₂) z D₁ (pairʟ-in D₁ D₂ D₁ (inl refl)) h

  in₂ : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₂ z h = unionʟ-in (pairʟ D₁ D₂) z D₂ (pairʟ-in D₁ D₂ D₂ (inr refl)) h

  out : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ ⟨ fst z ∈ fst D₁ ⟩ ⊎ ⟨ fst z ∈ fst D₂ ⟩ ∥₁
  out z h = PT.rec squash₁ step (unionʟ-out (pairʟ D₁ D₂) z h)
    where
    P : S
    P = pairʟ D₁ D₂
    step : Σ[ B ∈ V ℓ ] (⟨ B ∈ fst P ⟩ × ⟨ fst z ∈ B ⟩)
         → ∥ ⟨ fst z ∈ fst D₁ ⟩ ⊎ ⟨ fst z ∈ fst D₂ ⟩ ∥₁
    step (B , (hB , hz)) = PT.map
      (λ { (inl q) → inl (subst (λ w → ⟨ fst z ∈ w ⟩) q hz)
         ; (inr q) → inr (subst (λ w → ⟨ fst z ∈ w ⟩) q hz) })
      (pairʟ-out D₁ D₂ (B , isL-trans {x = fst P} {y = B} hB (snd P)) hB)

-- =====================================================================
-- SECTION 1.  TWO CODED INJECTIONS INTO κ, TAGGED INTO THE PRODUCT.
--
--   z ↦ (0, E₁ z) on D₁, and z ↦ (1, E₂ z) off D₁.  The graph, over
--   (y ∷ z ∷ []): "z ∈ D₁ and some v has (z, v) ∈ E₁ and y = (0, v), or
--   z ∉ D₁ and some v has (z, v) ∈ E₂ and y = (1, v)".  Inside the
--   binder v is 0, y is 1, z is 2.
-- =====================================================================

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

  -- The graph and its host reading.
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
         ; (inr (h , hv)) → inr (h , PT.map (λ { (v , (ha , ht)) → v , rd E₂ 1 y z v ha ht }) hv) })

    fo-in : (y z : S) → Wit y z → ⟨ (y ∷ z ∷ []) ⊨ fo ⟩
    fo-in y z (inl (h , hv)) =
      ∣ inl (h , PT.map (λ { (v , (ha , ht)) → v , wr E₁ 0 y z v ha ht }) hv) ∣₁
    fo-in y z (inr (h , hv)) =
      ∣ inr (h , PT.map (λ { (v , (ha , ht)) → v , wr E₂ 1 y z v ha ht }) hv) ∣₁

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

-- THE LEMMA: two internal injections into κ give one on the union.
tag-union : (κ : S) → ⟨ # 0 ∈ fst κ ⟩ → ⟨ # 1 ∈ fst κ ⟩
          → (D₁ D₂ : S) → InjL D₁ κ → InjL D₂ κ
          → InjL (unionʟ (pairʟ D₁ D₂)) (prodL κ)
tag-union κ h0 h1 D₁ D₂ = PT.rec2 squash₁
  (λ { (E₁ , c₁) (E₂ , c₂) → TagUnion.injL κ h0 h1 D₁ D₂ E₁ E₂ c₁ c₂ })

-- =====================================================================
-- SECTION 2.  THE LEAST PREIMAGE.  G is a set of pairs (p, z) whose
-- first components lie in P ⊆ L_γ, and every z ∈ D has a preimage.
-- z ↦ the stage-order-least p with (p, z) ∈ G is a definable map
-- D → P, its graph is a set of L, and when G is functional in the
-- sense "(p, z), (p, z') ∈ G force z = z'" the map is injective.
--
--   The graph, over (p ∷ z ∷ []): "(p, z) ∈ G, p ∈ L_γ, and no p' ∈ L_γ
--   below p in the stage order has (p', z) ∈ G".  Inside the bounded
--   binder p' is 0, p is 1, z is 2.
-- =====================================================================

module LeastPre (γ : V ℓ) (oγ : IsOrd γ) (G D P : S)
  (inP : (p z : S) → Holds G p z → ⟨ fst p ∈ fst P ⟩)
  (P⊆L : (p : S) → ⟨ fst p ∈ fst P ⟩ → ⟨ fst p ∈ Lset γ ⟩)
  (have : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁) where

  -- Sealed: the elements that reach a slot.
  opaque
    Lγ : S
    Lγ = LsetS γ oγ

    Lγ-fst : fst Lγ ≡ Lset γ
    Lγ-fst = refl

    hγ : ⟨ isL γ ⟩
    hγ = isL-ord γ oγ

  Rγ : S
  Rγ = relL γ hγ oγ

  Mγ : Type (ℓ-suc ℓ)
  Mγ = MemOf (Lset γ)

  memS : Mγ → S
  memS c = fst c , Lset→isL γ oγ (fst c) (snd c)

  Good : S → Mγ → hProp (ℓ-suc ℓ)
  Good z c = ∥ Σ[ p ∈ S ] ((fst p ≡ fst c) × Holds G p z) ∥₁ , squash₁

  Mem : S → Type (ℓ-suc ℓ)
  Mem z = ⟨ fst z ∈ fst D ⟩

  module AtZ (z : S) (m : Mem z) where

    nonempty : ∥ Σ[ c ∈ Mγ ] ⟨ Good z c ⟩ ∥₁
    nonempty = PT.map (λ { (p , h) → (fst p , P⊆L p (inP p z h)) , ∣ p , refl , h ∣₁ })
      (have z m)

    -- The selection, sealed with its two facts.
    opaque
      c : Mγ
      c = fst (leastOf (orderAt γ oγ) lem (Good z) nonempty)

      c-good : ⟨ Good z c ⟩
      c-good = fst (snd (leastOf (orderAt γ oγ) lem (Good z) nonempty))

      minimal : (c' : Mγ) → ⟨ Good z c' ⟩ → relOf (orderAt γ oγ) c' c → Empty.⊥
      minimal = snd (snd (leastOf (orderAt γ oγ) lem (Good z) nonempty))

    e : S
    e = memS c

    e-holds : Holds G e z
    e-holds = PT.rec (snd (pr (fst e) (fst z) ∈ fst G))
      (λ { (p , q , h) → subst (λ w → ⟨ pr w (fst z) ∈ fst G ⟩) q h }) c-good

    e∈P : ⟨ fst e ∈ fst P ⟩
    e∈P = inP e z e-holds

    e∈Lγ : ⟨ fst e ∈ Lset γ ⟩
    e∈Lγ = snd c

  fn : (z : S) → Mem z → S
  fn z m = AtZ.e z m

  -- The graph and its host reading.
  TWit : (p z : S) → Type (ℓ-suc ℓ)
  TWit p z =
      Holds G p z
    × ⟨ fst p ∈ Lset γ ⟩
    × ((p' : S) → ⟨ fst p' ∈ Lset γ ⟩ → Holds G p' z
        → ⟨ pr (fst p') (fst p) ∈ fst Rγ ⟩ → Empty.⊥)

  opaque
    private
      leastFo : Formula S 2
      leastFo = ∀̇∈ (con Lγ) (¬̇ (appC G i0 i2 ∧̇ appC Rγ i0 i1))

    fo : Formula S 2
    fo = appC G i0 i1 ∧̇ ((var i0 ∈̇ con Lγ) ∧̇ leastFo)

    fo-out : (p z : S) → ⟨ (p ∷ z ∷ []) ⊨ fo ⟩ → TWit p z
    fo-out p z (hg , (hl , hm)) =
        subst ⟨_⟩ (appC-adequate G i0 i1 (p ∷ z ∷ [])) hg
      , subst (λ w → ⟨ fst p ∈ w ⟩) Lγ-fst hl
      , λ p' hp' hg' hr → hm p' (subst (λ w → ⟨ fst p' ∈ w ⟩) (sym Lγ-fst) hp')
          ( subst ⟨_⟩ (sym (appC-adequate G i0 i2 (p' ∷ p ∷ z ∷ []))) hg'
          , subst ⟨_⟩ (sym (appC-adequate Rγ i0 i1 (p' ∷ p ∷ z ∷ []))) hr )

    fo-in : (p z : S) → TWit p z → ⟨ (p ∷ z ∷ []) ⊨ fo ⟩
    fo-in p z (hg , hl , mn) =
        subst ⟨_⟩ (sym (appC-adequate G i0 i1 (p ∷ z ∷ []))) hg
      , subst (λ w → ⟨ fst p ∈ w ⟩) (sym Lγ-fst) hl
      , λ p' hp' hc → mn p' (subst (λ w → ⟨ fst p' ∈ w ⟩) Lγ-fst hp')
          (subst ⟨_⟩ (appC-adequate G i0 i2 (p' ∷ p ∷ z ∷ [])) (fst hc))
          (subst ⟨_⟩ (appC-adequate Rγ i0 i1 (p' ∷ p ∷ z ∷ [])) (snd hc))

  private
    defines : (z : S) (m : Mem z) → ⟨ (fn z m ∷ z ∷ []) ⊨ fo ⟩
    defines z m = fo-in (fn z m) z (Z.e-holds , Z.e∈Lγ , mn)
      where
      module Z = AtZ z m using ( c; e; e-holds; e∈Lγ; minimal )
      mn : (p' : S) → ⟨ fst p' ∈ Lset γ ⟩ → Holds G p' z
         → ⟨ pr (fst p') (fst Z.e) ∈ fst Rγ ⟩ → Empty.⊥
      mn p' hp' hg' hr = Z.minimal (fst p' , hp') ∣ p' , refl , hg' ∣₁
        (relL-rep γ hγ oγ (fst p' , hp') Z.c hr)

    only : (z : S) (m : Mem z) (p' : S) → ⟨ (p' ∷ z ∷ []) ⊨ fo ⟩ → p' ≡ fn z m
    only z m p' h = S≡ (read (fo-out p' z h))
      where
      module Z = AtZ z m using ( c; e; e-holds; e∈Lγ; minimal )
      read : TWit p' z → fst p' ≡ fst (fn z m)
      read (hg , hp' , mn') = go (SWO.tri∙ (orderAt γ oγ) c' Z.c)
        where
        c' : Mγ
        c' = fst p' , hp'
        go : Tri∙ (relOf (orderAt γ oγ) c' Z.c) (c' ≡ Z.c) (relOf (orderAt γ oγ) Z.c c')
           → fst p' ≡ fst (fn z m)
        go (lt h') = Empty.rec (Z.minimal c' ∣ p' , refl , hg ∣₁ h')
        go (eq q)  = cong fst q
        go (gt h') = Empty.rec (mn' Z.e Z.e∈Lγ Z.e-holds (relL-fill γ hγ oγ Z.c c' h'))

  Dmap : DefinableMap
  Dmap = record
    { dom = D ; cod = P ; fn = fn
    ; into = λ z m → AtZ.e∈P z m
    ; graph = fo ; defines = defines ; only = only }

  module Gr = Graph Dmap using ( F; F-in; pair-out )

  -- THE TABLE: the set of pairs (z, e_z), z ∈ D.
  T : S
  T = Gr.F

  T-in : (z : S) (m : Mem z) → ⟨ pr (fst z) (fst (fn z m)) ∈ fst T ⟩
  T-in = Gr.F-in

  T-out : (z e : S) → ⟨ pr (fst z) (fst e) ∈ fst T ⟩
        → Σ[ m ∈ Mem z ] (fst e ≡ fst (fn z m))
  T-out = Gr.pair-out

  -- THE INJECTION, when G is functional.
  module Functional
    (funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z') where

    inj : (z : S) (m : Mem z) (z' : S) (m' : Mem z')
        → fst (fn z m) ≡ fst (fn z' m') → fst z ≡ fst z'
    inj z m z' m' q = funct (fn z m) z z' (AtZ.e-holds z m)
      (subst (λ w → ⟨ pr w (fst z') ∈ fst G ⟩) (sym q) (AtZ.e-holds z' m'))

    injL : InjL D P
    injL = Inj.injL Dmap inj

-- =====================================================================
-- SECTION 3.  A SINGLETON INJECTS INTO AN INFINITE ORDINAL: the one
-- member goes to 0.  The graph, over (y ∷ z ∷ []): "y = ∅".
-- =====================================================================

module Point (κ : S) (0∈κ : ⟨ # 0 ∈ fst κ ⟩) (a : S) where

  Y : S
  Y = pairʟ a a

  Y-in : ⟨ fst a ∈ fst Y ⟩
  Y-in = pairʟ-in a a a (inl refl)

  Y-out : (z : S) → ⟨ fst z ∈ fst Y ⟩ → fst z ≡ fst a
  Y-out z h = PT.rec (setIsSet _ _) (λ { (inl q) → q ; (inr q) → q }) (pairʟ-out a a z h)

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

## The count of the hull

```agda
-- =====================================================================
-- SECTION 4.  THE HULL OF A COUNTED START.  The telescope of
-- src/L/GCH/HullIn.lagda.md `Condense′`, plus an infinite L-cardinal κ
-- and an internal injection of the start X into κ.  Each iterate of
-- the hull is counted by induction: the new members of a step are the
-- least satisfiers of a key at a parameter environment over the last
-- iterate, and z ↦ the least such (key, environment) pair is a
-- definable injection (section 2), while the pairs are counted by the
-- limit stage and the finite sequences (src/L/GCH/Sequences.lagda.md).
-- =====================================================================

module Count (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : V ℓ) (X⊆L : (x : V ℓ) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩)
  (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  (base : InjL (X , X-isL) κ) where

  -- Every module application carries a `using` list (an unrestricted
  -- one copies the whole module into this interface); the step
  -- builder, the iteration and the hull stage are taken from
  -- src/L/GCH/HullIn.lagda.md `Telescope` directly, not through copies
  -- of `Condense′`'s copies.
  module Cn = Condense′ lam ordλ succλ X X⊆L ∅∈λ elem sup X-isL using ( hullStep; hullL )
  module B = Telescope.Build lam ordλ succλ X X⊆L ∅∈λ
    using ( A; Body; module BodyRd; C₀; Env; module KeyIn; bodyFo; wL; witFo-out
          ; Φ; Φ-out; λ-isL; ω-num; pack )
  module SM = SatMap B.A using ( pairs; pairs-out; valOf )
  module It = Telescope.HullIter.It lam ordλ succλ X X⊆L ∅∈λ X-isL B.pack
    using ( Num; iter; iter-in; iter-out; iterUnion-out; ω-num )
  module HI = Telescope.HullIter lam ordλ succλ X X⊆L ∅∈λ X-isL B.pack using ( hullStep⊆Hull )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ using ( Hull⊆L )
  open Cn using ( hullStep; hullL )

  -- -------------------------------------------------------------------
  -- 4.0  Facts about κ.
  -- -------------------------------------------------------------------

  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)

  -- The pairing at κ (src/L/GCH/Pairing.lagda.md's square law).
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

  Lω↪κ : InjL Lω κ
  Lω↪κ = injl-trans Lω ωʟ κ limit-stage-counted
    (inclusion-coded ωʟ κ (λ z hz → ω⊆ (fst κ) oκ κ∉ω z hz))

  -- -------------------------------------------------------------------
  -- 4.1  ONE STEP.  Z is an iterate (a subset of the stage) with a
  -- coded injection E : Z ↪ κ; Φ Z is counted.
  -- -------------------------------------------------------------------

  module OneStep (Z : S) (Z⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                 (E : S) (cE : InjCode E Z κ) where

    ΦZ : S
    ΦZ = B.Φ Z

    -- The new members; among them the junk value and the witnesses.
    opaque
      D₂ : S
      D₂ = hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .fst

      D₂-in : (z : S) → ⟨ fst z ∈ fst ΦZ ⟩ → (⟨ fst z ∈ fst Z ⟩ → Empty.⊥) → ⟨ fst z ∈ fst D₂ ⟩
      D₂-in z h no = subst ⟨_⟩ (sym (hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .snd z)) (h , no)

      D₂-out : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst ΦZ ⟩ × (⟨ fst z ∈ fst Z ⟩ → Empty.⊥)
      D₂-out z h = subst ⟨_⟩ (hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .snd z) h

      D∅ : S
      D∅ = hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .fst

      D∅-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → fst z ≡ ∅ → ⟨ fst z ∈ fst D∅ ⟩
      D∅-in z h e = subst ⟨_⟩ (sym (hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .snd z)) (h , e)

      D∅-out : (z : S) → ⟨ fst z ∈ fst D∅ ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅)
      D∅-out z h = subst ⟨_⟩ (hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .snd z) h

      Dw : S
      Dw = hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .fst

      Dw-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → (fst z ≡ ∅ → Empty.⊥) → ⟨ fst z ∈ fst Dw ⟩
      Dw-in z h ne = subst ⟨_⟩ (sym (hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .snd z)) (h , ne)

      Dw-out : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅ → Empty.⊥)
      Dw-out z h = subst ⟨_⟩ (hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .snd z) h

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

    -- The junk value is 0 ∈ κ.
    D∅↪κ : InjL D∅ κ
    D∅↪κ = inclusion-coded D∅ κ
      (λ z hz → subst (λ w → ⟨ w ∈ fst κ ⟩)
        (sym (D∅-out (z , isL-trans {x = fst D∅} {y = z} hz (snd D∅)) hz .snd)) (num∈κ 0))

    -- -----------------------------------------------------------------
    -- THE WITNESS PAIRS.  p = (s, e): s the key of a parameter-free
    -- formula (a member of L_ω), e the parameter environment over Z (a
    -- member of seqL Z).  (p, z) ∈ G when z is the least satisfier of
    -- s at e, in the words of src/L/GCH/HullIn.lagda.md `bodyFo`.
    --
    --   The separating description, over (q ∷ []): "q = (p, z), p ∈ PB,
    --   p = (s, e), and for Z pinned, some k, e', T make bodyFo hold".
    --   Binders, outermost first: p, z, s, e, Z, k, e', T.  Inside all
    --   of them: T is 0, e' is 1, k is 2, Z is 3, e is 4, s is 5, z is
    --   6, p is 7, q is 8; bodyFo reads (T ∷ e' ∷ e ∷ s ∷ k ∷ w ∷ Z ∷ []).
    -- -----------------------------------------------------------------

    module U₂ = Union2 Lω (seqL Z) using ( D; in₁; in₂ )

    PB : S
    PB = prodL U₂.D

    module PBd = PairBound PB Dw using ( bnd; below )

    Γ : (T e' k Zv e s z p q : S) → S ^ 9
    Γ T e' k Zv e s z p q = T ∷ e' ∷ k ∷ Zv ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []

    -- The body, renamed, sealed with its reading.
    opaque
      body₉ : Formula S 9
      body₉ = renameFo ρ₉ B.bodyFo

      body₉-read : (T e' k Zv e s z p q : S)
                 → ⟨ Γ T e' k Zv e s z p q ⊨ body₉ ⟩ ≡ ⟨ B.Env T e' e s k z Zv ⊨ B.bodyFo ⟩
      body₉-read T e' k Zv e s z p q =
        cong ⟨_⟩ (Ren.⊨-rename ρ₉ B.bodyFo (Γ T e' k Zv e s z p q) (B.Env T e' e s k z Zv)
                    (ag₉ T e' k Zv e s z p q))

    -- Three plain binders, sealed with their readings.
    opaque
      wit₆ : Formula S 6
      wit₆ = ∃̇ (∃̇ (∃̇ body₉))

      wit₆-in : (Zv e s z p q T e' k : S) → ⟨ B.Env T e' e s k z Zv ⊨ B.bodyFo ⟩
              → ⟨ (Zv ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ wit₆ ⟩
      wit₆-in Zv e s z p q T e' k h =
        ∣ k , ∣ e' , ∣ T , transport (sym (body₉-read T e' k Zv e s z p q)) h ∣₁ ∣₁ ∣₁

      wit₆-out : (Zv e s z p q : S) → ⟨ (Zv ∷ e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ wit₆ ⟩
               → ∥ Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ k ∈ S ] ⟨ B.Env T e' e s k z Zv ⊨ B.bodyFo ⟩ ∥₁
      wit₆-out Zv e s z p q = PT.rec squash₁ at₁
        where
        Out : Type (ℓ-suc ℓ)
        Out = ∥ Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ k ∈ S ] ⟨ B.Env T e' e s k z Zv ⊨ B.bodyFo ⟩ ∥₁
        at₃ : (k e' : S) → Σ[ T ∈ S ] ⟨ Γ T e' k Zv e s z p q ⊨ body₉ ⟩ → Out
        at₃ k e' (T , h) = ∣ T , e' , k , transport (body₉-read T e' k Zv e s z p q) h ∣₁
        at₂ : (k : S) → Σ[ e' ∈ S ] ∥ Σ[ T ∈ S ] ⟨ Γ T e' k Zv e s z p q ⊨ body₉ ⟩ ∥₁ → Out
        at₂ k (e' , h) = PT.rec squash₁ (at₃ k e') h
        at₁ : Σ[ k ∈ S ] ∥ Σ[ e' ∈ S ] ∥ Σ[ T ∈ S ] ⟨ Γ T e' k Zv e s z p q ⊨ body₉ ⟩ ∥₁ ∥₁ → Out
        at₁ (k , h) = PT.rec squash₁ (at₂ k) h

    -- Z pinned, sealed.
    opaque
      pin₅ : Formula S 5
      pin₅ = pinAt Z wit₆

      pin₅-in : (e s z p q T e' k : S) → ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩
              → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
      pin₅-in e s z p q T e' k h =
        pin-in Z wit₆ (e ∷ s ∷ z ∷ p ∷ q ∷ []) (wit₆-in Z e s z p q T e' k h)

      pin₅-out : (e s z p q : S) → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
               → ∥ Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ k ∈ S ] ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩ ∥₁
      pin₅-out e s z p q h = wit₆-out Z e s z p q (pin-out Z wit₆ (e ∷ s ∷ z ∷ p ∷ q ∷ []) h)

    -- The host reading of a witness pair.
    GW : (p z : S) → Type (ℓ-suc ℓ)
    GW p z = ∥ Σ[ s ∈ S ] Σ[ e ∈ S ] Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ k ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩) ∥₁

    -- s and e bound, sealed.
    opaque
      se₃ : Formula S 3
      se₃ = ∃̇ (∃̇ (prAtL i3 i1 i0 ∧̇ pin₅))

      se₃-in : (z p q s e T e' k : S) → fst p ≡ pr (fst s) (fst e)
             → ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩ → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩
      se₃-in z p q s e T e' k qp h =
        ∣ s , ∣ e , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ []))) qp
                    , pin₅-in e s z p q T e' k h ) ∣₁ ∣₁

      se₃-out : (z p q : S) → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩ → GW p z
      se₃-out z p q = PT.rec squash₁ at₁
        where
        at₂ : (s : S) → Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                   × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) → GW p z
        at₂ s (e , (qp , h)) = PT.map
          (λ { (T , e' , k , hb) → s , e , T , e' , k
             , ( subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ [])) qp , hb ) })
          (pin₅-out e s z p q h)
        at₁ : Σ[ s ∈ S ] ∥ Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                      × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) ∥₁ → GW p z
        at₁ (s , h) = PT.rec squash₁ (at₂ s) h

    -- The separating description, sealed.
    opaque
      gFo : Formula S 1
      gFo = ∃̇ (∃̇ (prAtL i2 i1 i0 ∧̇ ((var i1 ∈̇ con PB) ∧̇ se₃)))

      gFo-in : (q p z : S) → fst q ≡ pr (fst p) (fst z) → ⟨ fst p ∈ fst PB ⟩
             → (s e T e' k : S) → fst p ≡ pr (fst s) (fst e)
             → ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩ → ⟨ (q ∷ []) ⊨ gFo ⟩
      gFo-in q p z qq hp s e T e' k qp h =
        ∣ p , ∣ z , ( subst ⟨_⟩ (sym (prAtL-adequate i2 i1 i0 (z ∷ p ∷ q ∷ []))) qq
                    , ( hp , se₃-in z p q s e T e' k qp h ) ) ∣₁ ∣₁

      gFo-out : (q : S) → ⟨ (q ∷ []) ⊨ gFo ⟩
              → ∥ Σ[ p ∈ S ] Σ[ z ∈ S ] ((fst q ≡ pr (fst p) (fst z)) × ⟨ fst p ∈ fst PB ⟩ × GW p z) ∥₁
      gFo-out q = PT.rec squash₁ at₁
        where
        Out : Type (ℓ-suc ℓ)
        Out = ∥ Σ[ p ∈ S ] Σ[ z ∈ S ] ((fst q ≡ pr (fst p) (fst z)) × ⟨ fst p ∈ fst PB ⟩ × GW p z) ∥₁
        at₂ : (p : S) → Σ[ z ∈ S ] ( ⟨ (z ∷ p ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                   × (⟨ fst p ∈ fst PB ⟩ × ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩) ) → Out
        at₂ p (z , (qq , (hp , h))) =
          ∣ p , z , ( subst ⟨_⟩ (prAtL-adequate i2 i1 i0 (z ∷ p ∷ q ∷ [])) qq , hp , se₃-out z p q h ) ∣₁
        at₁ : Σ[ p ∈ S ] ∥ Σ[ z ∈ S ] ( ⟨ (z ∷ p ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                      × (⟨ fst p ∈ fst PB ⟩ × ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩) ) ∥₁ → Out
        at₁ (p , h) = PT.rec squash₁ (at₂ p) h

    -- THE RELATION, carved out of the pair bound.
    opaque
      G : S
      G = hasSeparationL PBd.bnd gFo .fst .fst

      G-in : (p z : S) → ⟨ fst p ∈ fst PB ⟩ → ⟨ fst z ∈ fst Dw ⟩
           → (s e T e' k : S) → fst p ≡ pr (fst s) (fst e)
           → ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩ → Holds G p z
      G-in p z hp hz s e T e' k qp h =
        subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst p z)
          (subst ⟨_⟩ (sym (hasSeparationL PBd.bnd gFo .fst .snd (prʟ p z)))
            ( subst (λ w → ⟨ w ∈ fst PBd.bnd ⟩) (sym (prʟ-fst p z)) (PBd.below p z hp hz)
            , gFo-in (prʟ p z) p z (prʟ-fst p z) hp s e T e' k qp h ))

      G-out : (p z : S) → Holds G p z → ⟨ fst p ∈ fst PB ⟩ × GW p z
      G-out p z h = PT.rec (isProp× (snd (fst p ∈ fst PB)) squash₁) read
        (gFo-out (prʟ p z)
          (subst ⟨_⟩ (hasSeparationL PBd.bnd gFo .fst .snd (prʟ p z))
            (subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst p z)) h) .snd))
        where
        read : Σ[ p' ∈ S ] Σ[ z' ∈ S ]
                 ((fst (prʟ p z) ≡ pr (fst p') (fst z')) × ⟨ fst p' ∈ fst PB ⟩ × GW p' z')
             → ⟨ fst p ∈ fst PB ⟩ × GW p z
        read (p' , z' , (qq , hp , gw)) =
            subst (λ w → ⟨ w ∈ fst PB ⟩) (sym (fst ee)) hp
          , subst2 GW (S≡ {x = p'} {y = p} (sym (fst ee))) (S≡ {x = z'} {y = z} (sym (snd ee))) gw
          where
          ee : (fst p ≡ fst p') × (fst z ≡ fst z')
          ee = pr-inj (sym (prʟ-fst p z) ∙ qq)

    -- -----------------------------------------------------------------
    -- EXISTENCE: every witness has a pair.  The key is a member of L_ω
    -- (it is the arity numeral paired with a hereditarily finite code),
    -- and the environment is a finite sequence over Z.
    -- -----------------------------------------------------------------

    -- The body is read through src/L/GCH/HullIn.lagda.md `BodyRd`, at
    -- this variable environment.
    module AtBody (z T e' e s k : S) (hb : ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩) where

      γ₇ : S ^ 7
      γ₇ = B.Env T e' e s k z Z

      module Rd = B.BodyRd T e' e s k z Z using ( b-num; b-key; b-env; b-cons; b-tab; b-mem; b-stage )

      h1 : ⟨ fst k ∈ fst ωʟ ⟩
      h1 = Rd.b-num hb

      h6 : ⟨ fst e' ∈ fst T ⟩
      h6 = Rd.b-mem hb

      h7 : ⟨ fst z ∈ fst B.A ⟩
      h7 = Rd.b-stage hb

      module AtNum (n : ℕ) (qk : fst k ≡ # n) where

        s∈Lω : ⟨ fst s ∈ Lset ω ⟩
        s∈Lω = PT.rec (snd (fst s ∈ Lset ω)) read (kr .snd)
          where
          kr = B.KeyIn.keyIn-out i3 i4 γ₇ n qk (Rd.b-key hb)
          read : Σ[ c ∈ V ℓ ] (fst s ≡ pr (# (suc n)) c) → ⟨ fst s ∈ Lset ω ⟩
          read (c , qs) = PT.rec (snd (fst s ∈ Lset ω))
            (λ { (χ , qc) → subst (λ w → ⟨ w ∈ Lset ω ⟩) (sym qs)
                   (pr∈limit (# (suc n)) c (numeral∈limit (suc n))
                     (subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym qc) (snd (limitCode χ)))) })
            (freeCode-out (suc n) c (subst (λ u → ⟨ u ∈ fst B.C₀ ⟩) qs (kr .fst)))

        module R = Recover Z n γ₇ i2 i4 i6 qk refl (Rd.b-env hb) using ( g; recovers )

        g′ : Fin n → V ℓ
        g′ i = ⟪ fst Z ⟫↪ (R.g i)

        hE : fst e ≡ env g′
        hE = R.recovers

        e∈seq : ⟨ fst e ∈ fst (seqL Z) ⟩
        e∈seq = seqL-in Z n e (subst (λ w → ⟨ w ∈ˢ fst (envSet Z n) ⟩) (sym R.recovers) (envSet-in Z R.g))

        p∈PB : ⟨ pr (fst s) (fst e) ∈ fst PB ⟩
        p∈PB = prodL-in U₂.D s e (U₂.in₁ s s∈Lω) (U₂.in₂ e e∈seq)

    have : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
    have z hz = PT.rec squash₁ body (B.Φ-out Z z (D₂-out z (Dw-out z hz .fst) .fst))
      where
      body : B.Body Z z → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
      body (inl h) = Empty.rec (D₂-out z (Dw-out z hz .fst) .snd h)
      body (inr (inl e)) = Empty.rec (Dw-out z hz .snd e)
      body (inr (inr hw)) = PT.rec squash₁ read (B.witFo-out z Z hw)
        where
        read : Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ e ∈ S ] Σ[ s ∈ S ] Σ[ k ∈ S ]
                 ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩
             → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
        read (T , e' , e , s , k , hb) = PT.map at (B.ω-num k (AB.h1))
          where
          module AB = AtBody z T e' e s k hb using ( h1; module AtNum )
          at : Σ[ n ∈ ℕ ] (fst k ≡ # n) → Σ[ p ∈ S ] Holds G p z
          at (n , qk) = prʟ s e
            , G-in (prʟ s e) z (subst (λ w → ⟨ w ∈ fst PB ⟩) (sym (prʟ-fst s e)) (AB.AtNum.p∈PB n qk))
                hz s e T e' k (prʟ-fst s e) hb

    -- -----------------------------------------------------------------
    -- FUNCTIONALITY: one key and one environment have one least
    -- satisfier.  The two satisfaction sets are the same table value,
    -- the two extended environments are the cons of each satisfier
    -- onto the one environment, and each minimality clause refutes the
    -- other satisfier being below.
    -- -----------------------------------------------------------------

    private
      same-val : (x x' : S) (m : ⟨ fst x ∈ fst (AllCodes B.A) ⟩) (m' : ⟨ fst x' ∈ fst (AllCodes B.A) ⟩)
               → fst x ≡ fst x' → fst (SM.valOf x m) ≡ fst (SM.valOf x' m')
      same-val x x' m m' q =
        subst (λ x'' → (m'' : ⟨ fst x'' ∈ fst (AllCodes B.A) ⟩) → fst (SM.valOf x m) ≡ fst (SM.valOf x'' m''))
          (S≡ q) (λ m'' → cong (λ v → fst (SM.valOf x v)) (snd (fst x ∈ fst (AllCodes B.A)) m m'')) m'

    module Unique (z T e' e s k : S) (hb : ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩)
                  (z' T₂ e'₂ k₂ : S) (hb₂ : ⟨ B.Env T₂ e'₂ e s k₂ z' Z ⊨ B.bodyFo ⟩)
                  (n : ℕ) (qk : fst k ≡ # n) where

      module A₁ = AtBody z T e' e s k hb using ( h6; h7; module Rd; module AtNum )
      module A₂ = AtBody z' T₂ e'₂ e s k₂ hb₂ using ( h6; h7; module Rd )
      module N = A₁.AtNum n qk using ( g′; hE )

      zS z'S : Telescope.SL lam ordλ succλ X X⊆L ∅∈λ
      zS  = fst z , A₁.h7
      z'S = fst z' , A₂.h7

      e'≡ : fst e' ≡ env (cons (fst z) N.g′)
      e'≡ = A₁.Rd.b-cons N.g′ N.hE hb

      e'₂≡ : fst e'₂ ≡ env (cons (fst z') N.g′)
      e'₂≡ = A₂.Rd.b-cons N.g′ N.hE hb₂

      -- the two satisfaction sets agree
      T≡ : fst T ≡ fst T₂
      T≡ = PT.rec2 (setIsSet (fst T) (fst T₂)) read
        (SM.pairs-out (pr (fst s) (fst T)) (A₁.Rd.b-tab hb))
        (SM.pairs-out (pr (fst s) (fst T₂)) (A₂.Rd.b-tab hb₂))
        where
        read : Σ[ x ∈ S ] Σ[ m ∈ ⟨ fst x ∈ fst (AllCodes B.A) ⟩ ] (pr (fst s) (fst T) ≡ pr (fst x) (fst (SM.valOf x m)))
             → Σ[ x' ∈ S ] Σ[ m' ∈ ⟨ fst x' ∈ fst (AllCodes B.A) ⟩ ] (pr (fst s) (fst T₂) ≡ pr (fst x') (fst (SM.valOf x' m')))
             → fst T ≡ fst T₂
        read (x , m , q) (x' , m' , q') =
          pr-inj q .snd ∙ same-val x x' m m' (sym (pr-inj q .fst) ∙ pr-inj q' .fst) ∙ sym (pr-inj q' .snd)

      -- neither satisfier is below the other
      not-below : (a b : S) (ha : ⟨ fst a ∈ fst B.A ⟩) (hb' : ⟨ fst b ∈ fst B.A ⟩)
                  (Ta e'a ka : S) (hba : ⟨ B.Env Ta e'a e s ka a Z ⊨ B.bodyFo ⟩)
                  (e'b : S) → fst e'b ≡ env (cons (fst b) N.g′) → ⟨ fst e'b ∈ fst Ta ⟩
                → relOf B.wL (fst b , hb') (fst a , ha) → Empty.⊥
      not-below a b ha hb' Ta e'a ka hba e'b qe hm b<a =
        B.BodyRd.b-min Ta e'a e s ka a Z N.g′ N.hE hba b hb' e'b qe hm
          (relL-fill lam B.λ-isL ordλ (fst b , hb') (fst a , ha) b<a)

      result : fst z ≡ fst z'
      result = go (SWO.tri∙ B.wL zS z'S)
        where
        go : Tri∙ (relOf B.wL zS z'S) (zS ≡ z'S) (relOf B.wL z'S zS) → fst z ≡ fst z'
        go (lt h) = Empty.rec (not-below z' z A₂.h7 A₁.h7 T₂ e'₂ k₂ hb₂ e' e'≡
                      (subst (λ t → ⟨ fst e' ∈ t ⟩) T≡ A₁.h6) h)
        go (eq q) = cong fst q
        go (gt h) = Empty.rec (not-below z z' A₁.h7 A₂.h7 T e' k hb e'₂ e'₂≡
                      (subst (λ t → ⟨ fst e'₂ ∈ t ⟩) (sym T≡) A₂.h6) h)

    funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z'
    funct p z z' h h' = PT.rec2 (setIsSet (fst z) (fst z')) read (G-out p z h .snd) (G-out p z' h' .snd)
      where
      read : Σ[ s ∈ S ] Σ[ e ∈ S ] Σ[ T ∈ S ] Σ[ e' ∈ S ] Σ[ k ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × ⟨ B.Env T e' e s k z Z ⊨ B.bodyFo ⟩)
           → Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ] Σ[ T₂ ∈ S ] Σ[ e'₂ ∈ S ] Σ[ k₂ ∈ S ]
               ((fst p ≡ pr (fst s₂) (fst e₂)) × ⟨ B.Env T₂ e'₂ e₂ s₂ k₂ z' Z ⊨ B.bodyFo ⟩)
           → fst z ≡ fst z'
      read (s , e , T , e' , k , (q , hb)) (s₂ , e₂ , T₂ , e'₂ , k₂ , (q₂ , hb₂)) =
        PT.rec (setIsSet (fst z) (fst z')) (λ { (n , qk) → Unique.result z T e' e s k hb z' T₂ e'₂ k₂ hb₂' n qk })
          (B.ω-num k (B.BodyRd.b-num T e' e s k z Z hb))
        where
        ee : (fst s₂ ≡ fst s) × (fst e₂ ≡ fst e)
        ee = pr-inj (sym q₂ ∙ q)
        hb₂' : ⟨ B.Env T₂ e'₂ e s k₂ z' Z ⊨ B.bodyFo ⟩
        hb₂' = subst2 (λ s' e'' → ⟨ B.Env T₂ e'₂ e'' s' k₂ z' Z ⊨ B.bodyFo ⟩)
                 (S≡ {x = s₂} {y = s} (fst ee)) (S≡ {x = e₂} {y = e} (snd ee)) hb₂

    -- -----------------------------------------------------------------
    -- THE STEP COUNT.
    -- -----------------------------------------------------------------

    -- the stage of the pair bound
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

  -- Every iterate is counted.
  iter⊆L : (n : ℕ) (z : V ℓ) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  iter⊆L n z hz = HSH.Hull⊆L z (HI.hullStep⊆Hull n z hz)

  counted : (n : ℕ) → InjL (hullStep n) κ
  counted zero    = base
  counted (suc n) = step-count (hullStep n) (iter⊆L n) (counted n)

  -- -------------------------------------------------------------------
  -- 4.2  THE TABLE OF LEAST CODES, n ↦ e_n, as a set of L.  A stage γ
  -- holds one code for every n (the least stage holding one is a
  -- function of n, and γ bounds those), and e_n is the stage-order-
  -- least member of L_γ coding an injection of the n-th iterate into κ:
  -- the least preimage under the relation "(F, n): F ∈ L_γ codes an
  -- injection of the iterate at n into κ".
  --
  --   The relation's description, over (q ∷ []): "q = (F, n), F ∈ L_γ,
  --   and some B has (n, B) in the iteration table and F an injection
  --   code from B into κ".  Inside: B is 0, n is 1, F is 2, q is 3.
  -- -------------------------------------------------------------------

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

  -- Sealed: the elements that reach a slot.
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
    tabFo : Formula S 1
    tabFo = ∃̇ (∃̇ (prAtL i2 i1 i0 ∧̇ ((var i1 ∈̇ con Lγ) ∧̇ ∃̇ (appC Iter i1 i0 ∧̇ injFo κ i2 i0))))

    tabFo-in : (q F n Zn : S) → fst q ≡ pr (fst F) (fst n) → ⟨ fst F ∈ Lset γ ⟩
             → Holds Iter n Zn → InjCode F Zn κ → ⟨ (q ∷ []) ⊨ tabFo ⟩
    tabFo-in q F n Zn qq hF hI code =
      ∣ F , ∣ n , ( subst ⟨_⟩ (sym (prAtL-adequate i2 i1 i0 (n ∷ F ∷ q ∷ []))) qq
                  , ( subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF
                    , ∣ Zn , ( subst ⟨_⟩ (sym (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ []))) hI
                             , InjFo.fill κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) code ) ∣₁ ) ) ∣₁ ∣₁

    tabFo-out : (q : S) → ⟨ (q ∷ []) ⊨ tabFo ⟩
              → ∥ Σ[ F ∈ S ] Σ[ n ∈ S ] ((fst q ≡ pr (fst F) (fst n)) × TabWit F n) ∥₁
    tabFo-out q = PT.rec squash₁ at₁
      where
      Out : Type (ℓ-suc ℓ)
      Out = ∥ Σ[ F ∈ S ] Σ[ n ∈ S ] ((fst q ≡ pr (fst F) (fst n)) × TabWit F n) ∥₁
      at₂ : (F : S) → Σ[ n ∈ S ] ( ⟨ (n ∷ F ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                 × ( ⟨ fst F ∈ fst Lγ ⟩
                                   × ⟨ (n ∷ F ∷ q ∷ []) ⊨ ∃̇ (appC Iter i1 i0 ∧̇ injFo κ i2 i0) ⟩ ) ) → Out
      at₂ F (n , (qq , (hF , h))) =
        ∣ F , n , ( subst ⟨_⟩ (prAtL-adequate i2 i1 i0 (n ∷ F ∷ q ∷ [])) qq
                  , ( subst (λ w → ⟨ fst F ∈ w ⟩) Lγ-fst hF
                    , PT.map (λ { (Zn , (hI , hc)) → Zn
                        , ( subst ⟨_⟩ (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ [])) hI
                          , InjFo.read κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) hc ) }) h ) ) ∣₁
      at₁ : Σ[ F ∈ S ] ∥ Σ[ n ∈ S ] ( ⟨ (n ∷ F ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                    × ( ⟨ fst F ∈ fst Lγ ⟩
                                      × ⟨ (n ∷ F ∷ q ∷ []) ⊨ ∃̇ (appC Iter i1 i0 ∧̇ injFo κ i2 i0) ⟩ ) ) ∥₁ → Out
      at₁ (F , h) = PT.rec squash₁ (at₂ F) h

  module Tbd = PairBound Lγ ωʟ using ( bnd; below )

  opaque
    Gt : S
    Gt = hasSeparationL Tbd.bnd tabFo .fst .fst

    Gt-in : (F n Zn : S) → ⟨ fst F ∈ Lset γ ⟩ → ⟨ fst n ∈ fst ωʟ ⟩
          → Holds Iter n Zn → InjCode F Zn κ → Holds Gt F n
    Gt-in F n Zn hF hn hI code =
      subst (λ w → ⟨ w ∈ fst Gt ⟩) (prʟ-fst F n)
        (subst ⟨_⟩ (sym (hasSeparationL Tbd.bnd tabFo .fst .snd (prʟ F n)))
          ( subst (λ w → ⟨ w ∈ fst Tbd.bnd ⟩) (sym (prʟ-fst F n))
              (Tbd.below F n (subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF) hn)
          , tabFo-in (prʟ F n) F n Zn (prʟ-fst F n) hF hI code ))

    Gt-out : (F n : S) → Holds Gt F n → TabWit F n
    Gt-out F n h = PT.rec (isProp× (snd (fst F ∈ Lset γ)) squash₁) read
      (tabFo-out (prʟ F n)
        (subst ⟨_⟩ (hasSeparationL Tbd.bnd tabFo .fst .snd (prʟ F n))
          (subst (λ w → ⟨ w ∈ fst Gt ⟩) (sym (prʟ-fst F n)) h) .snd))
      where
      read : Σ[ F' ∈ S ] Σ[ n' ∈ S ] ((fst (prʟ F n) ≡ pr (fst F') (fst n')) × TabWit F' n')
           → TabWit F n
      read (F' , n' , (qq , tw)) = subst2 TabWit (S≡ {x = F'} {y = F} (sym (fst ee))) (S≡ {x = n'} {y = n} (sym (snd ee))) tw
        where
        ee : (fst F ≡ fst F') × (fst n ≡ fst n')
        ee = pr-inj (sym (prʟ-fst F n) ∙ qq)

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
    using ( T; fn; T-in; T-out; module AtZ )

  -- THE TABLE, and its entries.
  Te : S
  Te = Tb.T

  eS : (n : S) → ⟨ fst n ∈ fst ωʟ ⟩ → S
  eS = Tb.fn

  Te-in : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩) → ⟨ pr (fst n) (fst (eS n m)) ∈ fst Te ⟩
  Te-in = Tb.T-in

  Te-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst Te ⟩
         → Σ[ m ∈ ⟨ fst n ∈ fst ωʟ ⟩ ] (fst F ≡ fst (eS n m))
  Te-out = Tb.T-out

  -- The entry at n codes an injection of some iterate recorded at n.
  e-wit : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩)
        → ∥ Σ[ Zn ∈ S ] (Holds Iter n Zn × InjCode (eS n m) Zn κ) ∥₁
  e-wit n m = Gt-out (eS n m) n (Tb.AtZ.e-holds n m) .snd

  -- The entry at the numeral k codes an injection of the k-th iterate.
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

  -- -------------------------------------------------------------------
  -- 4.3  THE HULL INJECTS INTO κ.  z ↦ the least (n, v) with z at the
  -- n-th iterate and (z, v) an entry of e_n, into prodL κ, then the
  -- pairing at κ.  The relation "((n, v), z): n ∈ ω, (n, F) ∈ Te,
  -- (z, v) ∈ F" is functional in the sense of section 2, since each
  -- e_n is injective.
  --
  --   Its description, over (q ∷ []): binders p, z, then n, v, then F.
  --   Inside: F is 0, v is 1, n is 2, z is 3, p is 4, q is 5.
  -- -------------------------------------------------------------------

  FinWit : (p z : S) → Type (ℓ-suc ℓ)
  FinWit p z = ∥ Σ[ n ∈ S ] Σ[ v ∈ S ] Σ[ F ∈ S ]
      ((fst p ≡ pr (fst n) (fst v)) × ⟨ fst n ∈ fst ωʟ ⟩ × Holds Te n F × Holds F z v) ∥₁

  -- The innermost conjunction, sealed with its readings.
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

  -- n, v and F bound, sealed.
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

  opaque
    finFo : Formula S 1
    finFo = ∃̇ (∃̇ (prAtL i2 i1 i0 ∧̇ nv₃))

    finFo-in : (q p z n v F : S) → fst q ≡ pr (fst p) (fst z) → fst p ≡ pr (fst n) (fst v)
             → ⟨ fst n ∈ fst ωʟ ⟩ → Holds Te n F → Holds F z v → ⟨ (q ∷ []) ⊨ finFo ⟩
    finFo-in q p z n v F qq qp hn ht hv =
      ∣ p , ∣ z , ( subst ⟨_⟩ (sym (prAtL-adequate i2 i1 i0 (z ∷ p ∷ q ∷ []))) qq
                  , nv₃-in z p q n v F qp hn ht hv ) ∣₁ ∣₁

    finFo-out : (q : S) → ⟨ (q ∷ []) ⊨ finFo ⟩
              → ∥ Σ[ p ∈ S ] Σ[ z ∈ S ] ((fst q ≡ pr (fst p) (fst z)) × FinWit p z) ∥₁
    finFo-out q = PT.rec squash₁ at₁
      where
      Out : Type (ℓ-suc ℓ)
      Out = ∥ Σ[ p ∈ S ] Σ[ z ∈ S ] ((fst q ≡ pr (fst p) (fst z)) × FinWit p z) ∥₁
      at₂ : (p : S) → Σ[ z ∈ S ] ( ⟨ (z ∷ p ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                 × ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩ ) → Out
      at₂ p (z , (qq , h)) =
        ∣ p , z , ( subst ⟨_⟩ (prAtL-adequate i2 i1 i0 (z ∷ p ∷ q ∷ [])) qq , nv₃-out z p q h ) ∣₁
      at₁ : Σ[ p ∈ S ] ∥ Σ[ z ∈ S ] ( ⟨ (z ∷ p ∷ q ∷ []) ⊨ prAtL i2 i1 i0 ⟩
                                    × ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩ ) ∥₁ → Out
      at₁ (p , h) = PT.rec squash₁ (at₂ p) h

  module Fbd = PairBound (prodL κ) hullL using ( bnd; below )

  opaque
    Gf : S
    Gf = hasSeparationL Fbd.bnd finFo .fst .fst

    Gf-in : (p z n v F : S) → ⟨ fst p ∈ fst (prodL κ) ⟩ → ⟨ fst z ∈ fst hullL ⟩
          → fst p ≡ pr (fst n) (fst v) → ⟨ fst n ∈ fst ωʟ ⟩ → Holds Te n F → Holds F z v
          → Holds Gf p z
    Gf-in p z n v F hp hz qp hn ht hv =
      subst (λ w → ⟨ w ∈ fst Gf ⟩) (prʟ-fst p z)
        (subst ⟨_⟩ (sym (hasSeparationL Fbd.bnd finFo .fst .snd (prʟ p z)))
          ( subst (λ w → ⟨ w ∈ fst Fbd.bnd ⟩) (sym (prʟ-fst p z)) (Fbd.below p z hp hz)
          , finFo-in (prʟ p z) p z n v F (prʟ-fst p z) qp hn ht hv ))

    Gf-out : (p z : S) → Holds Gf p z → FinWit p z
    Gf-out p z h = PT.rec squash₁ read
      (finFo-out (prʟ p z)
        (subst ⟨_⟩ (hasSeparationL Fbd.bnd finFo .fst .snd (prʟ p z))
          (subst (λ w → ⟨ w ∈ fst Gf ⟩) (sym (prʟ-fst p z)) h) .snd))
      where
      read : Σ[ p' ∈ S ] Σ[ z' ∈ S ] ((fst (prʟ p z) ≡ pr (fst p') (fst z')) × FinWit p' z')
           → FinWit p z
      read (p' , z' , (qq , fw)) = subst2 FinWit (S≡ {x = p'} {y = p} (sym (fst ee))) (S≡ {x = z'} {y = z} (sym (snd ee))) fw
        where
        ee : (fst p ≡ fst p') × (fst z ≡ fst z')
        ee = pr-inj (sym (prʟ-fst p z) ∙ qq)

  -- A value of the entry at n is a member of κ.
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
      -- the table value at the same index is the same value
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

  -- THE THEOREM OF THIS SECTION: the hull injects into κ, internally.
  hull↪κ : InjL hullL κ
  hull↪κ = injl-trans hullL (prodL κ) κ (LF.Functional.injL funct-fin) pairκ
```
