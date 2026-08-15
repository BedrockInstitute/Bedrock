{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-281.TreatedParam {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The ambient injection type, as the square-law chain carries it.
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- A1.  The least cardinal, in the ambient-injection form.
--
--   The ambient square-law chain's `LeastCardInj` restated over the
--   L-carrier: α is an L-element, the per-site hypothesis is the
--   ordinal certificate `oα`, and the crossing `up` lifts a member of
--   the tower at `sucV (fst α)` into the L-carrier.  The lift is where
--   the three delivered L-lemmas surface: `ord∈Lset-suc` and `Lset→isL`
--   give level-hood of the stage, `isL-trans` pushes it down.
-- =====================================================================

module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where

  Inj : S → Type ℓ
  Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  -- `⟨ isL α ⟩` alone does not give level-hood of `sucV (fst α)`;
  -- it comes from an ordinal appearing at the stage after itself,
  -- plus membership in a stage being level-hood.
  hSucα : ⟨ isL (sucV (fst α)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst α))) (suc-ord (suc-ord oα)) (sucV (fst α))
            (ord∈Lset-suc (sucV (fst α)) (suc-ord oα))

  -- `isL-trans` propagates level-hood down to the members, turning a
  -- member of the tower into an L-element.
  up : ⟪ sucV (fst α) ⟫ → S
  up m = ⟪ sucV (fst α) ⟫↪ m
       , isL-trans (member (sucV (fst α)) m) hSucα

  InjP' : ⟪ sucV (fst α) ⟫ → hProp ℓ
  InjP' γ = InjP (up γ)

  w : SWO (⟪ sucV (fst α) ⟫)
  w = ordSWO (sucV (fst α)) (suc-ord oα)

  self : ⟪ sucV (fst α) ⟫
  self = fiber (sucV (fst α)) (self∈sucV (fst α)) .fst

  self-eq : ⟪ sucV (fst α) ⟫↪ self ≡ fst α
  self-eq = fiber (sucV (fst α)) (self∈sucV (fst α)) .snd

  idInj : ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sucV (fst α) ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq)
                ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sucV (fst α) ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sucV (fst α) ⟫
  γ-card = fst least

  κ : S
  κ = up γ-card

  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = sucV (fst α)} (suc-ord oα) (fst κ)
         (member (sucV (fst α)) γ-card)

  κ∈sα : ⟨ fst κ ∈ˢ sucV (fst α) ⟩
  κ∈sα = member (sucV (fst α)) γ-card

  -- The witness, an injection, still truncated, still not an hProp.
  κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sucV (fst α) ⟫) → ⟨ InjP' b ⟩
        → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  κ-min-at : (δ : S) (b : ⟪ sucV (fst α) ⟫) (bδ : ⟪ sucV (fst α) ⟫↪ b ≡ fst δ)
           → ⟨ fst δ ∈ˢ fst κ ⟩
           → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-at δ b bδ δ∈κ α↪δ = κ-min b bInjP b<γ
    where
    bInjP : ⟨ InjP' b ⟩
    bInjP = subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym bδ) α↪δ
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ fst κ ⟩) (sym bδ) δ∈κ

