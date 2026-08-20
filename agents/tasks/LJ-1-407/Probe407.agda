{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.407] PROBE.  The TRUNCATED square law at every band ordinal,
-- with NO residue.  It runs in agents/tasks/LJ-1-407/ and lands
-- nothing in src/.
--
--   W3 FIRST  `kappa-not-fin`.  Infiniteness of the descent target:
--             ω ∈ x implies fst κ ∉ ω.  Stated alone and run before
--             the recursion, per the brief.
--
--   TERM      `sq-trunc`.  ∈-induction with motive
--             Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁.
--             Four cases, no IsCardinalL split, no residue.
--
--   HYPOTHESIS  `init-at-kappa`, at the type [LJ-1.406] names.  Not
--               imported and not rebuilt.
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

module LJ-1-407.Probe407 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( isPropIsOrd; 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω; finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ; Σ-syntax; ΣPathP )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SMALL DELIVERED-FACT HELPERS, rebuilt from src/ primitives.
-- =====================================================================

-- Every ordinal is an L-element ([LJ-1.386]'s `isL-ord`, one line).
-- Sealed (opaque): its body reduces to an `∈-induction` via
-- `ord∈Lset-suc`, and leaving it transparent forces that recursion
-- inside every conversion check on `(α , isL-ord α oα)` (P-i, R-36).
opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- A member of an ordinal injects its index into the ordinal
-- ([LJ-1.390]'s `mem-incl`, from `member`, `fiber`, `↪-inj`).
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

-- Composition of two ambient injections.
comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- `fst (LeastCardInjL.κ a oa)` reduces through `leastOf`'s body to a
-- large stuck term; left transparent, every conversion check between
-- two spellings of `fst κ` re-runs that reduction and explodes.  The
-- seal makes `fst (κL a oa)` a small atom.  `κ-injL` is sealed in the
-- same block so its target is the sealed `κ`, not the transparent one.
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
-- PART 1.  W3, THE PROBE.  Infiniteness of the descent target.
-- [LJ-1.404] REFUTED ⟨ ω ∈ fst κ ⟩.  The honest statement is fst κ ∉ ω.
-- The truncation of κ-inj is free because the conclusion is Empty.⊥.
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

-- =====================================================================
-- PART 2.  The second positive split: decide whether a site is its own
-- ambient least cardinal.  Copied from [LJ-1.398] at Probe398.agda:141.
-- =====================================================================

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
-- PART 3.  THE DESCENT PAYOFF, rebuilt from [LJ-1.390] Probe390.agda:110.
-- The descending arrow is a variable.  Nothing about codes is formed.
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

-- The consumer's band membership produces the ordinal certificate the
-- chapter does not ask for.  Port of Probe398.agda:286-289.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

-- =====================================================================
-- PART 4.  THE RECURSION.  `init-at-kappa` is the one module hypothesis,
-- at the type [LJ-1.406] names.  Not imported and not rebuilt.
-- =====================================================================

module _
  (init-at-kappa :
      (a : S) (oa : IsOrd (fst a))
    → ⟨ ω ∈ˢ fst (κL a oa) ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
         → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
    → Init (fst (κL a oa)))
  where

  -- The motive carries the ordinal certificate and the infinitude, and
  -- no band membership (no supplier reads one at a member).
  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁

  step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    a : S
    a = x , isL-ord x ox

    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → ∥ sq x ∥₁
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = ∣ subst sq (sym x≡ω) squareω ∣₁
    go (inr (inr ω∈x)) = splitOwn (kappa-decides a ox)
      where
      κ : S
      κ = κL a ox
      oκ : IsOrd (fst κ)
      oκ = κoL a ox

      ω∈κ : fst κ ≡ x → ⟨ ω ∈ fst κ ⟩
      ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ w ⟩) (sym κ≡x) ω∈x

      members : fst κ ≡ x
              → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩
              → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
      members κ≡x β oβ β∈κ infβ =
        ih β (subst (λ w → ⟨ β ∈ w ⟩) κ≡x β∈κ) oβ infβ

      -- Case 3: x is its own ambient least cardinal.
      by-init : fst κ ≡ x → ∥ sq x ∥₁
      by-init κ≡x =
        ∣ subst sq κ≡x
            (via-col-square (fst κ)
              (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x))) ∣₁

      -- Case 4: fst κ ∈ x.  κ-inj is truncated; the conclusion is
      -- truncated, so PT.map2 spends it.  No IsCardinalL split.
      by-descent : ⟨ fst κ ∈ x ⟩ → ∥ sq x ∥₁
      by-descent κ∈x =
        PT.map2
          (λ down sqκ → descent-core a κ (mem-incl x (fst κ) ox κ∈x) sqκ down)
          (κ-injL a ox)
          (ih (fst κ) κ∈x oκ (kappa-not-fin x ox ω∈x))

      splitOwn : (fst κ ≡ x) ⊎ ⟨ fst κ ∈ x ⟩ → ∥ sq x ∥₁
      splitOwn (inl κ≡x) = by-init κ≡x
      splitOwn (inr κ∈x) = by-descent κ∈x

  sq-trunc :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → ∥ sq δ ∥₁
  sq-trunc δ δ∈ infδ = ∈-induction {P = Goal} step δ (band-ord δ δ∈) infδ

  -- ===================================================================
  -- PART 5.  THE CONSUMER MATCH, CHECKED MECHANICALLY.
  -- StageCardinal's module parameter with ∥ ∥₁ around its Sigma and
  -- nothing else changed.
  -- ===================================================================

  ConsumerShape : Type (ℓ-suc ℓ)
  ConsumerShape =
    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → ∥ Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y) ∥₁

  plugs-in : ConsumerShape
  plugs-in δ δ∈ infδ = sq-trunc δ δ∈ infδ
