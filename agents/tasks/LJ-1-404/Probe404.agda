{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.404] PROBE.  The selected cardinal of an ordinal that holds ω,
-- and successor-closure of that cardinal.  It runs in
-- agents/tasks/LJ-1-404/ and lands nothing in src/.
--
-- W3, FIRST: `infinite-or-omega`, the consumer bridge.  The consumer
-- `L.StageCardinal` quantifies sq over δ with (⟨ δ ∈ ω ⟩ → Empty.⊥),
-- which allows δ ≡ ω, while both obligations here want ⟨ ω ∈ fst a ⟩.
-- This term is stated alone and run before anything else, per the brief.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-404.Probe404 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; suc∈or≡ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( module FiniteBase )
open FiniteBase using ( finite-excl; ω-mem→numeral )
open import L.InjChain {ℓ} lem using ( ω-limit; ω∉β )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3, FIRST.  The consumer bridge.  Trichotomy of δ against ω, and the
--   finite case is the hypothesis's negation.
-- =====================================================================

infinite-or-omega : (δ : V ℓ) → IsOrd δ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                  → (δ ≡ ω) ⊎ ⟨ ω ∈ δ ⟩
infinite-or-omega δ oδ ¬δ∈ω = tri (ord-tri δ oδ ω ω-ord)
  where
  tri : ⟨ δ ∈ ω ⟩ ⊎ ((δ ≡ ω) ⊎ ⟨ ω ∈ δ ⟩) → (δ ≡ ω) ⊎ ⟨ ω ∈ δ ⟩
  tri (inl δ∈ω)       = Empty.rec (¬δ∈ω δ∈ω)
  tri (inr (inl δ≡ω)) = inl δ≡ω
  tri (inr (inr ω∈δ)) = inr ω∈δ

-- =====================================================================
-- The generic pairing that adapts a plain injection to finite-excl's
-- square.  Cost: 6 code lines.  It needs a member of the target.
-- =====================================================================

pair-const : {A B : Type ℓ} → B → (A → B) → (A → B × B)
pair-const b f x = f x , b

pair-const-inj : {A B : Type ℓ} (b : B) (f : A → B)
               → ((x y : A) → f x ≡ f y → x ≡ y)
               → (x y : A) → pair-const b f x ≡ pair-const b f y → x ≡ y
pair-const-inj _ f finj x y e = finj x y (cong fst e)

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

beta-lifts : (κ : S) (β : V ℓ) → ⟨ β ∈ fst κ ⟩ → S
beta-lifts κ β β∈κ = β , isL-trans β∈κ (snd κ)

-- The hotel shift at ω.  ShiftAbs asks that γ is not a numeral and that
-- every numeral is a member; both hold at ω.  This is the injection
-- ⟪ sucV ω ⟫ ↪ ⟪ ω ⟫, which suc-absorb cannot give (it wants ω ∈ γ).
module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) #∈ω

-- The same shift at a generic infinite ordinal (ω ∈ γ).
shift-at : (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩ → ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
shift-at γ oγ ω∈γ = SA.shift↪
  where
  module SA = ShiftAbs γ oγ (λ γ∈ω → ω∉β γ γ∈ω ω∈γ)
                        (λ k → oγ .fst (#∈ω k) ω∈γ)

-- Plain injection into a finite ordinal, adapted to finite-excl.
-- The dummy member exists once the target is a positive numeral; the
-- zero numeral is the empty set and is killed directly.
plain-excl : (α : V ℓ) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ α ⟩)
           → (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩
           → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥
plain-excl α oα ω∈α β oβ β∈ω inj =
  PT.rec Empty.isProp⊥ (go inj) (ω-mem→numeral β β∈ω)
  where
  src : ⟪ α ⟫
  src = fiber α ω∈α .fst
  go : ⟪ α ⟫ ↪ ⟪ β ⟫ → Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (f , _) (zero , p) =
    ∅-empty (⟪ ∅ ⟫↪ gsrc) (∈ₛ⟪ ∅ ⟫↪ gsrc)
    where
    gsrc : ⟪ ∅ ⟫
    gsrc = subst (λ w → ⟪ w ⟫) p (f src)
  go (f , finj) (suc n , p) =
    finite-excl α oα ω∈α β oβ β∈ω
      (pair-const dummy f) (pair-const-inj dummy f finj)
    where
    dummy : ⟪ β ⟫
    dummy = subst (λ w → ⟪ w ⟫) (sym p)
              (fiber (# (suc n)) (self∈sucV (# n)) .fst)

-- =====================================================================
-- The honest infiniteness of κ: it is not a numeral.  Membership
-- spelling: ∈ˢ, matching κ-min-at at src/L/Cardinal.lagda.md:140-142.
-- The truncation of κ-inj is free because the conclusion is Empty.⊥.
-- =====================================================================

kappa-not-finite :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst a ⟩
  → ⟨ fst (LeastCardInjL.κ a oa) ∈ˢ ω ⟩ → Empty.⊥
kappa-not-finite a oa ω∈a κ∈ω =
  PT.rec Empty.isProp⊥
    (λ inj → plain-excl (fst a) oa ω∈a (fst κ) oκ κ∈ω inj)
    κ-inj
  where
  open LeastCardInjL a oa

-- =====================================================================
-- TERM 1, AS THE BRIEF STATES IT.  REFUTED: see PART 3.  The brief's
-- reasoning kills only κ ∈ ω.  The remaining case κ ≡ ω is possible,
-- and at a := sucV ω it is actual, so ω ∈ κ is ω ∈ ω.
-- =====================================================================

kappa-infinite :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst a ⟩
  → ⟨ ω ∈ˢ fst (LeastCardInjL.κ a oa) ⟩
kappa-infinite = ?

-- =====================================================================
-- PART 3.  THE REFUTATION.  The site is a := sucV ω.
--
--   fst κ is a member of sucV (sucV ω), so it is sucV ω, or ω, or a
--   numeral.  A numeral is kappa-not-finite.  sucV ω is κ-min-at at
--   δ := ω through Shiftω.shift↪.  So fst κ ≡ ω, and ω ∈ ω dies.
-- =====================================================================

aω : S
aω = sucV ω ,
  Lset→isL (sucV (sucV ω)) (suc-ord (suc-ord ω-ord)) (sucV ω)
    (ord∈Lset-suc (sucV ω) (suc-ord ω-ord))

oaω : IsOrd (fst aω)
oaω = suc-ord ω-ord

module R = LeastCardInjL aω oaω

ω∈aω : ⟨ ω ∈ˢ fst aω ⟩
ω∈aω = self∈sucV ω

κ-not-sucω : fst R.κ ≡ sucV ω → Empty.⊥
κ-not-sucω e =
  R.κ-min-at (beta-lifts R.κ ω ω∈κ) ω∈κ ∣ Shiftω.shift↪ ∣₁
  where
  ω∈κ : ⟨ ω ∈ fst R.κ ⟩
  ω∈κ = subst (λ w → ⟨ ω ∈ w ⟩) (sym e) (self∈sucV ω)

κ≡ω : fst R.κ ≡ ω
κ≡ω = ∈sucV-elim (setIsSet (fst R.κ) ω) R.κ∈sα
  (λ κ∈sω → ∈sucV-elim (setIsSet (fst R.κ) ω) κ∈sω
     (λ κ∈ω → Empty.rec (kappa-not-finite aω oaω ω∈aω κ∈ω))
     (λ e → e))
  (λ e → Empty.rec (κ-not-sucω e))

kappa-infinite-refuted :
    ((a : S) (oa : IsOrd (fst a))
     → ⟨ ω ∈ˢ fst a ⟩
     → ⟨ ω ∈ˢ fst (LeastCardInjL.κ a oa) ⟩)
   → Empty.⊥
kappa-infinite-refuted ki =
  ∈-irrefl ω (subst (λ w → ⟨ ω ∈ w ⟩) κ≡ω (ki aω oaω ω∈aω))

-- =====================================================================
-- TERM 2.  Successor closure of κ, given ω ∈ a.  Membership spelling
--   ∈ˢ, matching κ-min-at.  Three-way split of κ against ω, then of
--   γ against ω:
--     κ ∈ ω     kappa-not-finite
--     κ ≡ ω     ω-limit (every member is a numeral)
--     ω ∈ κ     split γ:
--       γ ∈ ω   ω-limit, then transitivity through ω ∈ κ
--       γ ≡ ω   suc∈or≡ at ω; equality dies on Shiftω plus κ-min-at
--       ω ∈ γ   suc∈or≡ at γ; equality dies on shift-at plus κ-min-at
-- =====================================================================

kappa-is-limit⁺ :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst a ⟩
  → (γ : V ℓ) → ⟨ γ ∈ˢ fst (LeastCardInjL.κ a oa) ⟩
  → ⟨ sucV γ ∈ˢ fst (LeastCardInjL.κ a oa) ⟩
kappa-is-limit⁺ a oa ω∈a γ γ∈κ = κ-tri (ord-tri (fst κ) oκ ω ω-ord)
  where
  open LeastCardInjL a oa
  oγ : IsOrd γ
  oγ = mem-ord {A = fst κ} oκ γ γ∈κ

  sω∈κ : ⟨ ω ∈ fst κ ⟩ → ⟨ sucV ω ∈ fst κ ⟩
  sω∈κ ω∈κ = Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-ω e))
    (suc∈or≡ ω (fst κ) ω-ord oκ ω∈κ)
    where
    eq-ω : sucV ω ≡ fst κ → Empty.⊥
    eq-ω e =
      κ-min-at (beta-lifts κ ω ω∈κ) ω∈κ
        (PT.map (λ f → comp-inj f (subst (λ z → ⟪ z ⟫ ↪ ⟪ ω ⟫) e
          Shiftω.shift↪)) κ-inj)

  κ-tri : ⟨ fst κ ∈ ω ⟩ ⊎ ((fst κ ≡ ω) ⊎ ⟨ ω ∈ fst κ ⟩)
        → ⟨ sucV γ ∈ fst κ ⟩
  κ-tri (inl κ∈ω) = Empty.rec (kappa-not-finite a oa ω∈a κ∈ω)
  κ-tri (inr (inl κ≡ω)) =
    subst (λ w → ⟨ sucV γ ∈ w ⟩) (sym κ≡ω)
      (ω-limit γ (subst (λ w → ⟨ γ ∈ w ⟩) κ≡ω γ∈κ))
  κ-tri (inr (inr ω∈κ)) = γ-tri (ord-tri γ oγ ω ω-ord)
    where
    γ-tri : ⟨ γ ∈ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ γ ⟩) → ⟨ sucV γ ∈ fst κ ⟩
    γ-tri (inl γ∈ω) = oκ .fst (ω-limit γ γ∈ω) ω∈κ
    γ-tri (inr (inl γ≡ω)) =
      subst (λ w → ⟨ sucV w ∈ fst κ ⟩) (sym γ≡ω) (sω∈κ ω∈κ)
    γ-tri (inr (inr ω∈γ)) =
      Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-γ e))
        (suc∈or≡ γ (fst κ) oγ oκ γ∈κ)
      where
      eq-γ : sucV γ ≡ fst κ → Empty.⊥
      eq-γ e =
        κ-min-at (beta-lifts κ γ γ∈κ) γ∈κ
          (PT.map (λ f → comp-inj f (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e
            (shift-at γ oγ ω∈γ))) κ-inj)
