{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.413] PROBE.  The square law as DATA at every band ordinal,
-- with ONE residue.  It runs in agents/tasks/LJ-1-413/ and lands
-- nothing in src/.
--
--   W3 FIRST  `descent-data`.  Case four at data level: membership,
--             the descending arrow, and `sq` at the target, all as
--             data.  Stated alone and run before the recursion.
--
--   TERM      `sq-data`.  ∈-induction with motive
--             Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x.
--             Four cases.  No ∥ ∥₁ in the conclusion.
--
--   THREE MODULE HYPOTHESES, not imported, not rebuilt:
--             `init-at-kappa` at [LJ-1.406]'s type,
--             `coded-descent` at [LJ-1.412]'s type,
--             `amb-to-coded`, the residue, as the brief names it.
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

module LJ-1-413.Probe413 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( isPropIsOrd; 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω; finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL; module LeastCardInjL )
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
-- PART 1.  W3, THE PROBE.  Case four at data level.
-- Three payload hypotheses: membership, the descending arrow, `sq` at
-- the target.  `IsOrd` of the site is the recursion's own certificate
-- and `mem-incl` spends it; it is not a fourth payload.
-- Rebuilt from [LJ-1.390] Probe390.agda:110 and :135.  Not imported.
-- =====================================================================

-- The composite, with the descending arrow held OUTSIDE as a variable.
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
-- Same seal [LJ-1.407] used.  This site does not re-measure the wall.
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

-- Infiniteness of the ambient least cardinal, rebuilt from
-- [LJ-1.407] Probe407.agda:117.  The residue spends it.
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
-- The second positive split: decide whether a site is its own
-- ambient least cardinal.  Copied from [LJ-1.407] Probe407.agda:140.
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

-- The consumer's band membership produces the ordinal certificate the
-- chapter does not ask for.  Port of Probe407.agda:193-196.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

-- Band membership of a member, rebuilt from κ-min-at
-- (src/L/Cardinal.lagda.md:145).  Not carried into coded-descent.
band-down : (x d : V ℓ) → IsOrd x → ⟨ x ∈ sucV α₀ ⟩ → ⟨ d ∈ x ⟩
          → ⟨ d ∈ sucV α₀ ⟩
band-down x d ox x∈ d∈x = ∈sucV-elim (snd (d ∈ sucV α₀)) x∈
  (λ x∈α₀ → ∈sucV-inl (oα₀ .fst d∈x x∈α₀))
  (λ x≡α₀ → ∈sucV-inl (subst (λ w → ⟨ d ∈ w ⟩) x≡α₀ d∈x))

-- =====================================================================
-- PART 4.  THE RECURSION.  Three module hypotheses.  Not imported.
-- `init-at-kappa` at [LJ-1.406]'s type.  `coded-descent` at
-- [LJ-1.412]'s type.  `amb-to-coded` is the residue; this task does
-- not attempt it.
-- =====================================================================

module _
  (init-at-kappa :
      (a : S) (oa : IsOrd (fst a))
    → ⟨ ω ∈ˢ fst (κL a oa) ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
         → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
    → Init (fst (κL a oa)))
  (coded-descent :
      (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
    → (IsCardinalL κ → Empty.⊥)
    → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ˢ fst κ ⟩
                 × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                 × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) ))
  (amb-to-coded :
      (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
    → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
    → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
    → (IsCardinalL x → Empty.⊥))
  where

  -- The motive carries the ordinal certificate and the infinitude, and
  -- no band membership (no supplier reads one at a member).  DATA, no
  -- ∥ ∥₁.  [LJ-1.407]'s motive was the same Sigma under a truncation.
  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

  step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    a : S
    a = x , isL-ord x ox

    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = subst sq (sym x≡ω) squareω
    go (inr (inr ω∈x)) = splitOwn (kappa-decides a ox)
      where
      κ : S
      κ = κL a ox

      ω∈κ : fst κ ≡ x → ⟨ ω ∈ fst κ ⟩
      ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ w ⟩) (sym κ≡x) ω∈x

      members : fst κ ≡ x
              → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩
              → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
      members κ≡x β oβ β∈κ infβ =
        ∣ ih β (subst (λ w → ⟨ β ∈ w ⟩) κ≡x β∈κ) oβ infβ ∣₁

      -- Case 3: x is its own ambient least cardinal.  DATA.  Do not wrap.
      by-init : fst κ ≡ x → sq x
      by-init κ≡x =
        subst sq κ≡x
          (via-col-square (fst κ)
            (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x)))

      -- Case 4: fst κ ∈ x.  Residue turns the truncated ambient arrow
      -- into ¬ IsCardinalL; coded-descent returns d and the arrow as
      -- data; IH at d; descent-data gives sq x.
      by-descent : ⟨ fst κ ∈ x ⟩ → sq x
      by-descent κ∈x = descent-data a d ox d∈x down sqd
        where
        notCard : IsCardinalL a → Empty.⊥
        notCard = amb-to-coded a ox ω∈x κ κ∈x
                    (kappa-not-fin x ox ω∈x) (κ-injL a ox)

        pack : Σ[ δ ∈ S ] ( ⟨ fst δ ∈ˢ fst a ⟩
                          × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                          × (⟪ fst a ⟫ ↪ ⟪ fst δ ⟫) )
        pack = coded-descent a ox ω∈x notCard

        d : S
        d = fst pack
        d∈x : ⟨ fst d ∈ˢ fst a ⟩
        d∈x = fst (snd pack)
        d-inf : ⟨ fst d ∈ˢ ω ⟩ → Empty.⊥
        d-inf = fst (snd (snd pack))
        down : ⟪ fst a ⟫ ↪ ⟪ fst d ⟫
        down = snd (snd (snd pack))

        od : IsOrd (fst d)
        od = mem-ord {A = x} ox (fst d) d∈x

        sqd : sq (fst d)
        sqd = ih (fst d) d∈x od d-inf

      splitOwn : (fst κ ≡ x) ⊎ ⟨ fst κ ∈ x ⟩ → sq x
      splitOwn (inl κ≡x) = by-init κ≡x
      splitOwn (inr κ∈x) = by-descent κ∈x

  sq-data :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → sq δ
  sq-data δ δ∈ infδ = ∈-induction {P = Goal} step δ (band-ord δ δ∈) infδ

  -- ===================================================================
  -- PART 5.  THE CONSUMER MATCH, CHECKED MECHANICALLY.
  -- StageCardinal's module parameter, verbatim, with NO ∥ ∥₁.
  -- ===================================================================

  ConsumerShape : Type (ℓ-suc ℓ)
  ConsumerShape =
    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)

  plugs-in : ConsumerShape
  plugs-in δ δ∈ infδ = sq-data δ δ∈ infδ
