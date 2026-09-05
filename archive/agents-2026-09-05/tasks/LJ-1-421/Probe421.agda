{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.421] PROBE.  Does case four close from the untruncated ambient
-- arrow at κ, with d := κ and no coded detour?
--
--   W3 FIRST  `d-is-kappa`.  descent-data at [LJ-1.413]'s delivered
--              telescope, applied with d := κ and nothing else
--              supplied.  The tree-arrow fill is the diagnostic at
--              runs/w3-from-tree.out: the DATA arrow is the argument
--              that fails, at type ⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫.
--
--   TERM      `descent-from-data`.  The induction step at a generic
--              infinite ordinal, from IH as data.  Case three spends
--              init-at-kappa (paid).  Case four spends d := κ.
--
--   MODULE HYPOTHESES.  kappa-arrow-data is the question.  init-at-kappa
--              is listed plumbing, at [LJ-1.406]'s delivered type.
--              No amb-to-coded, no coded-descent, no IsCardinalL.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-421.Probe421 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( ΣPathP )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SMALL DELIVERED-FACT HELPERS, rebuilt from src/ primitives.
-- Same as [LJ-1.413] Probe413.agda:66-90.  Not imported.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

mem-incl : (d k : V ℓ) → IsOrd d → ⟨ k ∈ d ⟩ → ⟪ k ⟫ ↪ ⟪ d ⟫
mem-incl d k od k∈d = ι , ι-inj
  where
  raise : (m : ⟪ k ⟫) → ⟨ ⟪ k ⟫↪ m ∈ d ⟩
  raise m = fst od (member k m) k∈d

  ι : ⟪ k ⟫ → ⟪ d ⟫
  ι m = fst (fiber d (raise m))

  ι-inj : (m n : ⟪ k ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = k}
    (sym (snd (fiber d (raise m)))
     ∙ cong (⟪ d ⟫↪) e
     ∙ snd (fiber d (raise n)))

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- =====================================================================
-- PART 1.  descent-data at [LJ-1.413]'s delivered form.
-- Probe413.agda:123-129.  Rebuilt, not imported.
-- =====================================================================

descent-core : (δ κ : S)
             → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
             → sq (fst κ)
             → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫
             → sq (fst δ)
descent-core δ κ incl (g , g-inj) down = f , f-inj
  where
  f : ⟪ fst δ ⟫ × ⟪ fst δ ⟫ → ⟪ fst δ ⟫
  f (x , y) = fst incl (g (fst down x , fst down y))

  f-inj : (p q : ⟪ fst δ ⟫ × ⟪ fst δ ⟫) → f p ≡ f q → p ≡ q
  f-inj (x₁ , y₁) (x₂ , y₂) e = ΣPathP (ex , ey)
    where
    step : (fst down x₁ , fst down y₁) ≡ (fst down x₂ , fst down y₂)
    step = g-inj _ _ (snd incl _ _ e)

    ex : x₁ ≡ x₂
    ex = snd down x₁ x₂ (cong fst step)

    ey : y₁ ≡ y₂
    ey = snd down y₁ y₂ (cong snd step)

descent-data : (x d : S) (ox : IsOrd (fst x))
             → ⟨ fst d ∈ˢ fst x ⟩
             → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
             → sq (fst d)
             → sq (fst x)
descent-data x d ox d∈x down sqd =
  descent-core x d (mem-incl (fst x) (fst d) ox d∈x) sqd down

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- Same seal [LJ-1.406] Probe406.agda:81-90 and [LJ-1.413]
-- Probe413.agda:135-146.  This site does not re-measure the wall.
-- =====================================================================
opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ∈sucL : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ sucV (fst a) ⟩
  κ∈sucL a oa = LeastCardInjL.κ∈sα a oa

  κ-injL : (a : S) (oa : IsOrd (fst a)) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  κ-injL a oa = LeastCardInjL.κ-inj a oa

-- =====================================================================
-- W3.  d-is-kappa.  Apply descent-data with d := κ and nothing else
-- supplied.  The remaining telescope is membership, the DATA arrow,
-- and sq at κ.  The tree-arrow fill is recorded at
-- runs/w3-from-tree.out.
-- =====================================================================

d-is-kappa :
    (x : S) (ox : IsOrd (fst x))
  → ⟨ fst (κL x ox) ∈ˢ fst x ⟩
  → (⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫)
  → sq (fst (κL x ox))
  → sq (fst x)
d-is-kappa x ox = descent-data x (κL x ox) ox

-- Diagnostic run `runs/w3-from-tree.out`, exit 42, UnequalTerms:
-- κ-injL x ox has type ∥ ⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫ ∥₁
-- and descent-data wants ⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫.
-- That is the argument that fails.  The obligation fills it from
-- kappa-arrow-data.

-- =====================================================================
-- Plumbing, rebuilt from [LJ-1.413] Probe413.agda:150-195.
-- kappa-not-fin spends the truncated κ-injL; the goal is Empty.⊥.
-- kappa-decides splits fst κ ≡ x from ⟨ fst κ ∈ x ⟩.
-- =====================================================================

kappa-not-fin : (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
              → (⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ ω ⟩ → Empty.⊥)
kappa-not-fin x ox ω∈x κ∈ω =
  PT.rec Empty.isProp⊥
    (λ down → finite-excl-ω (fst κ) oκ κ∈ω
                (λ t → fst (ω↪κ down) t , fst (ω↪κ down) t)
                (λ t u e → snd (ω↪κ down) t u (cong fst e)))
    (κ-injL a ox)
  where
  a : S
  a = x , isL-ord x ox
  κ : S
  κ = κL a ox
  oκ : IsOrd (fst κ)
  oκ = κoL a ox
  ω↪κ : (⟪ x ⟫ ↪ ⟪ fst κ ⟫) → (⟪ ω ⟫ ↪ ⟪ fst κ ⟫)
  ω↪κ down = comp-inj (mem-incl x ω ox ω∈x) down

kappa-decides : (a : S) (oa : IsOrd (fst a))
  → (fst (κL a oa) ≡ fst a)
  ⊎ ⟨ fst (κL a oa) ∈ fst a ⟩
kappa-decides a oa = go (ord-tri (fst κ) oκ (fst a) oa)
  where
  κ : S
  κ = κL a oa
  oκ : IsOrd (fst κ)
  oκ = κoL a oa
  κ∈sα : ⟨ fst κ ∈ sucV (fst a) ⟩
  κ∈sα = κ∈sucL a oa

  go : ⟨ fst κ ∈ fst a ⟩ ⊎ ((fst κ ≡ fst a) ⊎ ⟨ fst a ∈ fst κ ⟩)
     → (fst κ ≡ fst a) ⊎ ⟨ fst κ ∈ fst a ⟩
  go (inl κ∈a) = inr κ∈a
  go (inr (inl κ≡a)) = inl κ≡a
  go (inr (inr a∈κ)) = Empty.rec*
    (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* κ∈sα cycle self)
    where
    cycle : ⟨ fst κ ∈ fst a ⟩ → Empty.⊥* {ℓ-suc ℓ}
    cycle κ∈a = lift (∈-irrefl (fst a) (oa .fst a∈κ κ∈a))
    self : fst κ ≡ fst a → Empty.⊥* {ℓ-suc ℓ}
    self κ≡a = lift (∈-irrefl (fst a) (subst (λ w → ⟨ fst a ∈ w ⟩) κ≡a a∈κ))

-- =====================================================================
-- THE OBLIGATION.  One question-hypothesis: kappa-arrow-data, the
-- untruncated form of κ-injL ([LJ-1.406] Probe406.agda:88-89).
-- init-at-kappa is listed plumbing, at [LJ-1.406] Probe406.agda:180-185.
-- No amb-to-coded, no coded-descent, no IsCardinalL.
-- =====================================================================

module _
  (kappa-arrow-data :
      (a : S) (oa : IsOrd (fst a))
    → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
  (init-at-kappa :
      (a : S) (oa : IsOrd (fst a))
    → ⟨ ω ∈ˢ fst (κL a oa) ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
         → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
    → Init (fst (κL a oa)))
  where

  descent-from-data :
      (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x
  descent-from-data x ox ω∈x ih = splitOwn (kappa-decides a ox)
    where
    a : S
    a = x , isL-ord x ox
    κ : S
    κ = κL a ox

    ω∈κ : fst κ ≡ x → ⟨ ω ∈ˢ fst κ ⟩
    ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ˢ w ⟩) (sym κ≡x) ω∈x

    members : fst κ ≡ x
            → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩
            → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
    members κ≡x β oβ β∈κ infβ =
      ∣ ih β (subst (λ w → ⟨ β ∈ˢ w ⟩) κ≡x β∈κ) oβ infβ ∣₁

    -- Case 3: x is its own ambient least cardinal.  Paid.  No code.
    by-init : fst κ ≡ x → sq x
    by-init κ≡x =
      subst sq κ≡x
        (via-col-square (fst κ)
          (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x)))

    -- Case 4: fst κ ∈ x.  d := κ.  The arrow is kappa-arrow-data.
    by-descent : ⟨ fst κ ∈ x ⟩ → sq x
    by-descent κ∈x = d-is-kappa a ox κ∈x down sqκ
      where
      down : ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫
      down = kappa-arrow-data a ox
      sqκ : sq (fst κ)
      sqκ = ih (fst κ) κ∈x (κoL a ox) (kappa-not-fin x ox ω∈x)

    splitOwn : (fst κ ≡ x) ⊎ ⟨ fst κ ∈ x ⟩ → sq x
    splitOwn (inl κ≡x) = by-init κ≡x
    splitOwn (inr κ∈x) = by-descent κ∈x

