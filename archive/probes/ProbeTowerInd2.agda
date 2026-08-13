{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeTowerInd2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber; ↪-inj; member )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-mono; Lset-in; Lset-out; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; numeral-ord; mem-ord )
open import L.Ordinal.SquareLaw {ℓ} lem
  using ( module Initial; module InitialCore; module CoreAtω; module FiniteBase; Init; sq )
open import L.Ordinal.Pairing {ℓ} lem using ( ordSWO )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.CardinalCount {ℓ} lem using ( module Bound )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; _≊_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
open import Cubical.HITs.SetQuotients using ( _/_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- D-10, premise 2: Init ω is UNINHABITED. Init's second conjunct is the
-- strict membership ⟨ ω ∈ˢ α ⟩, so Init ω needs ω ∈ ω, refuted by
-- ∈-irrefl (src/V/Hierarchy.lagda.md:155).

Initω-false : Init ω → Empty.⊥
Initω-false i = ∈-irrefl ω (i .snd .fst)

-- D-10, premise 1, positive half: at the TRANSPARENT level (DefOf.Def A,
-- which is 𝒟 A by src/L/Constructible.lagda.md:53-54), the member type
-- ⟪ DefOf.Def A ⟫ IS the defSet-value quotient
--   Formula ⟪ A ⟫ 1 / (λ φ ψ → defSet A φ ≊ defSet A ψ)
-- definitionally (Cubical/HITs/CumulativeHierarchy/Properties.agda:146-153,
-- sett-repr's Kernel is ix x ≊ ix y). The identity lands as `refl`.
-- The negative half (⟪ 𝒟ₒ A ⟫ is NOT definitionally Formula ⟪ A ⟫ 1) is
-- checked in a separate probe (ProbeT85neg.agda), because it must FAIL.

D10-good : (A : S) → ⟪ DefOf.Def A ⟫
         → Formula ⟪ A ⟫ 1 / (λ φ ψ → DefOf.defSet A φ ≊ DefOf.defSet A ψ)
D10-good A x = x

-- Negative control, GENERIC: the lower injection α ⊆ Lset α at every
-- Init α (T59's ω control generalized; the successor-closure clause of
-- Init replaces the concrete #∈ω step, and ord∈Lset-suc places each
-- member at the stage after itself).

lower-inj : (α : S) → Init α → ⟪ α ⟫ ↪ ⟪ Lset α ⟫
lower-inj α iα = f , inj
  where
  oα : IsOrd α
  oα = iα .fst
  f : ⟪ α ⟫ → ⟪ Lset α ⟫
  f m = fiber (Lset α) (Lset-mono {α = α} {β = sucV (⟪ α ⟫↪ m)}
          (iα .snd .snd .fst (⟪ α ⟫↪ m) (member α m))
          (ord∈Lset-suc (⟪ α ⟫↪ m) (mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)))) .fst
  inj : (m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = α}
    (sym (fiber (Lset α) (Lset-mono {α = α} {β = sucV (⟪ α ⟫↪ m)}
             (iα .snd .snd .fst (⟪ α ⟫↪ m) (member α m))
             (ord∈Lset-suc (⟪ α ⟫↪ m) (mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)))) .snd)
      ∙ cong (⟪ Lset α ⟫↪) e
      ∙ fiber (Lset α) (Lset-mono {α = α} {β = sucV (⟪ α ⟫↪ n)}
             (iα .snd .snd .fst (⟪ α ⟫↪ n) (member α n))
             (ord∈Lset-suc (⟪ α ⟫↪ n) (mem-ord {A = α} oα (⟪ α ⟫↪ n) (member α n)))) .snd)

-- The generic successor step: at every Init α, the next stage's index
-- injects into ⟪ α ⟫, given the induction hypothesis at α. The route is
-- entirely membership-level, no quotient naming anywhere:
-- (1) Bound.formula-bound at β = α bounds Formula ⟪ Lset α ⟫ 1 by
--     ⟪ α ⟫ (pairing = Initial.square α iα, the opaque delivered sq α);
-- (2) each member of 𝒟ₒ (Lset α) is merely some defSet φ, by the
--     delivered characterization 𝒟ₒ-inv;
-- (3) leastOf over ordSWO picks the least count value in the class.
-- Injectivity uses count-injectivity and ↪-inj only.

module Successor (α : S) (iα : Init α) (g : ⟪ Lset α ⟫ ↪ ⟪ α ⟫) where

  oα : IsOrd α
  oα = iα .fst

  module B = Bound α oα (iα .snd .fst) (Initial.square α iα)

  count : Formula ⟪ Lset α ⟫ 1 ↪ ⟪ α ⟫
  count = B.formula-bound {K = ⟪ Lset α ⟫} g

  class-pred : (m : ⟪ 𝒟ₒ (Lset α) ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred m y = ( ∥ Σ[ φ ∈ Formula ⟪ Lset α ⟫ 1 ]
                        ( ( DefOf.defSet (Lset α) φ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ m )
                        × ( fst count φ ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (m : ⟪ 𝒟ₒ (Lset α) ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred m y ⟩ ∥₁
  nonempty m = PT.map
    (λ { (φ , e) → fst count φ , ∣ φ , (e , refl) ∣₁ })
    (𝒟ₒ-inv (Lset α) (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (member (𝒟ₒ (Lset α)) m))

  h : ⟪ 𝒟ₒ (Lset α) ⟫ → ⟪ α ⟫
  h m = fst (leastOf (ordSWO α oα) lem (class-pred m) (nonempty m))

  h-inj : (m n : ⟪ 𝒟ₒ (Lset α) ⟫) → h m ≡ h n → m ≡ n
  h-inj m n e = ↪-inj {a = 𝒟ₒ (Lset α)} (go pm)
    where
    lm = leastOf (ordSWO α oα) lem (class-pred m) (nonempty m)
    ln = leastOf (ordSWO α oα) lem (class-pred n) (nonempty n)
    pm : ⟨ class-pred m (fst ln) ⟩
    pm = subst (λ y → ⟨ class-pred m y ⟩) e (fst (snd lm))
    pn : ⟨ class-pred n (fst ln) ⟩
    pn = fst (snd ln)
    go : ⟨ class-pred m (fst ln) ⟩
       → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
    go = PT.rec (isSetS (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (⟪ 𝒟ₒ (Lset α) ⟫↪ n)) go₁
      where
      go₁ : Σ[ φ ∈ Formula ⟪ Lset α ⟫ 1 ]
              ( ( DefOf.defSet (Lset α) φ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ m )
              × ( fst count φ ≡ fst ln ) )
          → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
      go₁ (φ , (eφ , ec)) =
        PT.rec (isSetS (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (⟪ 𝒟ₒ (Lset α) ⟫↪ n)) go₂ pn
        where
        go₂ : Σ[ ψ ∈ Formula ⟪ Lset α ⟫ 1 ]
                ( ( DefOf.defSet (Lset α) ψ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n )
                × ( fst count ψ ≡ fst ln ) )
            → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
        go₂ (ψ , (eψ , ec')) =
          sym eφ ∙ cong (DefOf.defSet (Lset α)) (snd count φ ψ (ec ∙ sym ec')) ∙ eψ

op-step : (α : S) → Init α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
        → ⟪ 𝒟ₒ (Lset α) ⟫ ↪ ⟪ α ⟫
op-step α iα g = Successor.h α iα g , Successor.h-inj α iα g

successor-step : (α : S) → Init α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
              → ⟪ Lset (sucV α) ⟫ ↪ ⟪ α ⟫
successor-step α iα g = subst
  (λ A → Σ[ f ∈ (⟪ A ⟫ → ⟪ α ⟫) ] ((x y : ⟪ A ⟫) → f x ≡ f y → x ≡ y))
  (sym (Lset-suc α)) (op-step α iα g)
