# The assembly of GCH from four internal hypotheses

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Assembly {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.Axioms.Basic {ℓ} using ( isL-Lset )
open import L.Cardinal {ℓ} lem
  using ( InjCode; IsCardinalL; module LeastCardInjL )
open import L.CardinalAbove {ℓ} lem using ( CardAboveL )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier: `Lset` and the ambient membership live here.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier: `GCHStatement` lives here.
module SL = hPropStructure 𝒮ʟ
-- The instance src/L/GCH.lagda.md names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE FOUR HYPOTHESES, ALL INTERNAL TO L.
-- =====================================================================

-- 1.  The stage at an INFINITE ordinal δ is coded into δ.  The row is
--     false at finite δ, so the infinity premise is part of the type.
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
  → fst Lδ ≡ Lset (fst δ) → InjL Lδ δ

-- 2.  The bounded subset theorem, internally: a subset y of an infinite
--     L-cardinal κ appears at a stage whose index injects into κ.
InternalBoundedSubset : Type (ℓ-suc ℓ)
InternalBoundedSubset =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (y : SL.S) → ((z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩)
  → ∥ Σ[ β ∈ SL.S ]
       (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ) ∥₁

-- 3.  The successor cardinal injects into the power set.
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥) → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- 4.  The successor cardinal exists.  Section 2 proves it.
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

-- =====================================================================
-- SECTION 2.  HYPOTHESIS 4 IS A THEOREM.
--
--   `CardAboveL` (src/L/CardinalAbove.lagda.md) gives SOME ordinal
--   L-cardinal above κ; the least one is selected along the ordinal
--   well-order on the tower at `sucV θ`, and its minimality is the
--   leastness clause of `SuccCardL` (src/L/GCH.lagda.md:50-53).
-- =====================================================================

module Reduce (κ : SL.S) (oκ : IsOrd (fst κ))
              (θ : SL.S) (oθ : IsOrd (fst θ))
              (cθ : IsCardinalL θ) (κ∈θ : ⟨ fst κ ∈ˢ fst θ ⟩) where

  open LeastCardInjL θ oθ using ( up; self; self-eq )

  A : Type ℓ
  A = ⟪ sucV (fst θ) ⟫

  -- Sealed: unsealed, this selection is measured at over a hundred
  -- seconds at the same site (agents/tasks/LJ-1-526/runs/s4-2.out).
  opaque
    w : SWO A
    w = ordSWO (sucV (fst θ)) (suc-ord oθ)

  opaque
    unfolding w
    w-lt : (m n : A) → SWO._<∙_ w m n
         ≡ ⟨ ⟪ sucV (fst θ) ⟫↪ m ∈ˢ ⟪ sucV (fst θ) ⟫↪ n ⟩
    w-lt m n = refl

  isPropIsCardinalL : (x : SL.S) → isProp (IsCardinalL x)
  isPropIsCardinalL x =
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → Empty.isProp⊥)))

  Good : A → hProp (ℓ-suc ℓ)
  Good b = (IsCardinalL (up b) × ⟨ fst κ ∈ˢ fst (up b) ⟩)
         , isProp× (isPropIsCardinalL (up b)) (snd (fst κ ∈ˢ fst (up b)))

  upSelf : up self ≡ θ
  upSelf = Σ≡Prop (λ x → snd (isL x)) self-eq

  nonempty : ∥ Σ[ b ∈ A ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ self
            , subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upSelf) (cθ , κ∈θ) ∣₁

  least : Σ[ b ∈ A ] IsLeast w Good b
  least = leastOf w lem Good nonempty

  δ : SL.S
  δ = up (fst least)

  δ∈sθ : ⟨ fst δ ∈ˢ sucV (fst θ) ⟩
  δ∈sθ = member (sucV (fst θ)) (fst least)

  oδ : IsOrd (fst δ)
  oδ = mem-ord {A = sucV (fst θ)} (suc-ord oθ) (fst δ) δ∈sθ

  cδ : IsCardinalL δ
  cδ = fst (fst (snd least))

  κ∈δ : ⟨ fst κ ∈ˢ fst δ ⟩
  κ∈δ = snd (fst (snd least))

  δ-min : (b : A) → ⟨ Good b ⟩ → (SWO._<∙_ w b (fst least) → Empty.⊥)
  δ-min = snd (snd least)

  leastness : (c : SL.S) → IsOrd (fst c) → IsCardinalL c
            → ⟨ fst κ ∈ˢ fst c ⟩
            → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
  leastness c oc cc κ∈c = go (ord-tri (fst δ) oδ (fst c) oc)
    where
    go : Tri (fst δ) (fst c)
       → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
    go (inl δ∈c)       x x∈δ = oc .fst x∈δ δ∈c
    go (inr (inl e))   x x∈δ = subst (λ v → ⟨ fst x ∈ˢ v ⟩) e x∈δ
    go (inr (inr c∈δ)) x x∈δ = Empty.rec (δ-min b bGood b<δ)
      where
      c∈sθ : ⟨ fst c ∈ˢ sucV (fst θ) ⟩
      c∈sθ = suc-ord oθ .fst c∈δ δ∈sθ
      b : A
      b = fiber (sucV (fst θ)) c∈sθ .fst
      be : ⟪ sucV (fst θ) ⟫↪ b ≡ fst c
      be = fiber (sucV (fst θ)) c∈sθ .snd
      upb : up b ≡ c
      upb = Σ≡Prop (λ v → snd (isL v)) be
      bGood : ⟨ Good b ⟩
      bGood = subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upb) (cc , κ∈c)
      b<δ : SWO._<∙_ w b (fst least)
      b<δ = transport (λ i → sym (w-lt b (fst least)) i)
              (subst (λ v → ⟨ v ∈ˢ fst δ ⟩) (sym be) c∈δ)

succCardExists : SuccCardExists
succCardExists κ oκ cκ κ∉ω = PT.map build (CardAboveL κ oκ cκ κ∉ω)
  where
  build : Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
        → Σ[ δ ∈ SL.S ] SuccCardL δ κ
  build (θ , oθ , cθ , κ∈θ) = R.δ , R.oδ , R.cδ , R.κ∈δ , R.leastness
    where module R = Reduce κ oκ θ oθ cθ κ∈θ

-- =====================================================================
-- SECTION 3.  THREE ROWS src/ PAYS.
-- =====================================================================

-- The stage at an ordinal is constructible (src/L/Axioms/Basic.lagda.md).
stage-is-L : (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩
stage-is-L δ ordδ = isL-Lset (fst δ) ordδ

-- An inclusion is an internal injection (src/L/InjChain.lagda.md, row 3).
inclusion-coded : (a b : SL.S)
                → ((z : SV.S) → ⟨ z ∈ˢ fst a ⟩ → ⟨ z ∈ˢ fst b ⟩)
                → InjL a b
inclusion-coded a b sub = ∣ I.G , (I.sv , I.dm , I.ij , I.ran) ∣₁
  where module I = InclGraph a b sub

-- Internal injections compose (src/L/InjChain.lagda.md, row 1).
injl-trans : (a b c : SL.S) → InjL a b → InjL b c → InjL a c
injl-trans a b c = PT.rec2 PT.squash₁ step
  where
  step : Σ[ F ∈ SL.S ] InjCode F a b
       → Σ[ H ∈ SL.S ] InjCode H b c
       → InjL a c
  step (F , svF , dmF , ijF , ranF) (H , svH , dmH , ijH , ranH) =
    ∣ K.K , (K.svK , K.dmK , K.ijK , K.ranK) ∣₁
    where
    module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH

-- A member z of a member y of the internal power set of an ordinal κ:
-- z is constructible, a member of κ, and an ordinal.
--
--   `𝒫 κ = ℩ (hasPower κ)` and `hasPower` realizes the class
--   `λ x → x ⊆ˢ κ` (src/FOL/ZFModel.lagda.md), where `⊆ˢ` is the
--   INTERNAL subset relation: it quantifies over SL.S only.  So the
--   power-set hypothesis only speaks about CONSTRUCTIBLE members of
--   `y`, and `z` arrives ambient.  The bridge is transitivity of the
--   class `isL` (src/L/Constructible.lagda.md).
zStrongest : ModelL.isZFModel → Type (ℓ-suc ℓ)
zStrongest zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩
  → (⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z)
  where open ModelL.isZFModel zf using ( 𝒫 )

z-strongest : (zf : ModelL.isZFModel) → zStrongest zf
z-strongest zf κ y ordκ y∈𝒫κ z z∈y = isLz , z∈κ , mem-ord {A = fst κ} ordκ z z∈κ
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )

  -- z is constructible, because y is and L is transitive.
  isLz : ⟨ isL z ⟩
  isLz = isL-trans z∈y (snd y)

  -- The power-set specification, read off `℩-spec`; `𝒫 κ` IS
  -- `℩ (hasPower κ)` by definition, so no transport is needed.
  y⊆κ : ⟨ y ModelL.⊆ˢ κ ⟩
  y⊆κ = subst ⟨_⟩ (ModelL.℩-spec (hasPower κ) y) y∈𝒫κ

  -- z re-enters the internal subset relation as the L-element (z , isLz).
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = y⊆κ (z , isLz) z∈y

-- =====================================================================
-- SECTION 4.  THE LANDING: A SUBSET OF κ LIES IN THE STAGE AT κ⁺.
--
--   Hypothesis 2 places y at some stage β with β injecting into κ.
--   By trichotomy β ∈ δ, since β ≡ δ or δ ∈ β would inject δ into κ
--   against `IsCardinalL δ` at κ ∈ δ.  Then `Lset-mono` lifts y to δ.
-- =====================================================================

stage-landing :
    (zf : ModelL.isZFModel) → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (δ : SL.S) → SuccCardL δ κ
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
  → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
stage-landing zf ibs κ ordκ cardκ κ∉ω δ (ordδ , cardδ , κ∈δ , _) y y∈𝒫κ =
  PT.rec (snd (fst y ∈ˢ Lset (fst δ))) place (ibs κ ordκ cardκ κ∉ω y y⊆κ)
  where
  y⊆κ : (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ fst κ ⟩
  y⊆κ z z∈y = z-strongest zf κ y ordκ y∈𝒫κ z z∈y .snd .fst

  -- An internal injection of δ into κ is absurd: δ is an L-cardinal
  -- and κ is a member of it.
  no-δ↪κ : InjL δ κ → Empty.⊥
  no-δ↪κ = cardδ κ κ∈δ

  place : Σ[ β ∈ SL.S ]
            (IsOrd (fst β) × ⟨ fst y ∈ˢ Lset (fst β) ⟩ × InjL β κ)
        → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  place (β , ordβ , y∈Lβ , β↪κ) = go (ord-tri (fst β) ordβ (fst δ) ordδ)
    where
    go : Tri (fst β) (fst δ) → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
    go (inl β∈δ)       = Lset-mono β∈δ y∈Lβ
    go (inr (inl e))   = Empty.rec (no-δ↪κ (subst (λ b → InjL b κ) β≡δ β↪κ))
      where
      β≡δ : β ≡ δ
      β≡δ = Σ≡Prop (λ x → snd (isL x)) e
    go (inr (inr δ∈β)) = Empty.rec (no-δ↪κ
      (injl-trans δ β κ (inclusion-coded δ β δ⊆β) β↪κ))
      where
      δ⊆β : (z : SV.S) → ⟨ z ∈ˢ fst δ ⟩ → ⟨ z ∈ˢ fst β ⟩
      δ⊆β z z∈δ = ordβ .fst z∈δ δ∈β

-- =====================================================================
-- SECTION 5.  THE POWER SET INJECTS INTO THE SUCCESSOR.
-- =====================================================================

power-into-succ :
    (zf : ModelL.isZFModel) → StageCountedCoded → InternalBoundedSubset
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (δ : SL.S) → SuccCardL δ κ
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc@(ordδ , _ , κ∈δ , _) =
  injl-trans (𝒫 κ) Lδ δ (inclusion-coded (𝒫 κ) Lδ into)
    (scc δ Lδ ordδ δ∉ω refl)
  where
  open ModelL.isZFModel zf using ( 𝒫 )

  Lδ : SL.S
  Lδ = Lset (fst δ) , stage-is-L δ ordδ

  -- ω is transitive, so κ ∈ δ ∈ ω would put κ in ω.
  δ∉ω : ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
  δ∉ω δ∈ω = κ∉ω (ω-ord .fst {x = fst δ} {y = fst κ} κ∈δ δ∈ω)

  -- Every member of the model's power set is constructible, because L
  -- is transitive, and then it lands at δ by section 4.
  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ =
    stage-landing zf ibs κ ordκ cardκ κ∉ω δ sc (z , isL-trans z∈ (snd (𝒫 κ))) z∈

-- =====================================================================
-- SECTION 6.  THE THEOREM.
-- =====================================================================

gch-from-internal-bill :
    (zf : ModelL.isZFModel)
  → StageCountedCoded → InternalBoundedSubset → SuccIntoPower zf
  → GCHStatement zf
gch-from-internal-bill zf scc ibs sip κ ordκ cardκ κ∉ω =
  PT.map step (succCardExists κ ordκ cardκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) =
    δ , sc , power-into-succ zf scc ibs κ ordκ cardκ κ∉ω δ sc , sip κ δ κ∉ω sc
```
