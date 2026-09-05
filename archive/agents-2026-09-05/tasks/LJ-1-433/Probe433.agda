{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.433] PROBE.  Below the ambient least cardinal, Init is FALSE.
--
--   W3 FIRST  `omega-in-suc-kappa`.  κ is not finite (kappa-not-fin).
--              Trichotomy then leaves ⟨ ω ∈ˢ κ ⟩ or ω ≡ κ, and both
--              land in ⟨ ω ∈ˢ sucV κ ⟩.
--
--   TERM      `init-fails-below`.  Init x and ⟨ κ ∈ˢ x ⟩ imply Empty.⊥.
--              Consumes conjunct 3, refutes conjunct 4.  The arrow
--              stays truncated: PT.rec spends κ-injL, goal is Empty.⊥.
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

module LJ-1-433.Probe433 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( Init )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SMALL DELIVERED-FACT HELPERS, rebuilt from src/ primitives.
-- Same as [LJ-1.421] Probe421.agda:61-82.  Not imported.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- A member of an ordinal embeds its index
-- (src/L/BoundedSubset.lagda.md:1371-1379).  Rebuilt, not imported.
ord-emb : (a b : V ℓ) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
      ∙ cong (⟪ b ⟫↪) e
      ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- Same seal [LJ-1.421] Probe421.agda:125-135.  Four projections.
-- This site does not re-measure the wall.
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
-- Plumbing, rebuilt from [LJ-1.421] Probe421.agda:164-180.
-- kappa-not-fin spends the truncated κ-injL; the goal is Empty.⊥.
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
  ω↪κ down = comp-inj (ord-emb ω x ox ω∈x) down

-- =====================================================================
-- W3, FIRST.  ω lands in sucV κ, from infinitude of κ and trichotomy.
-- The obligation is omitted.  Both surviving cases of ord-tri must
-- close: ∈sucV-inl, or self∈sucV after subst.
-- =====================================================================

omega-in-suc-kappa :
    (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
  → ⟨ ω ∈ˢ sucV (fst (κL (x , isL-ord x ox) ox)) ⟩
omega-in-suc-kappa x ox ω∈x = go (ord-tri ω ω-ord (fst κ) oκ)
  where
  a : S
  a = x , isL-ord x ox
  κ : S
  κ = κL a ox
  oκ : IsOrd (fst κ)
  oκ = κoL a ox

  go : ⟨ ω ∈ˢ fst κ ⟩ ⊎ ((ω ≡ fst κ) ⊎ ⟨ fst κ ∈ˢ ω ⟩)
     → ⟨ ω ∈ˢ sucV (fst κ) ⟩
  go (inl ω∈κ) = ∈sucV-inl ω∈κ
  go (inr (inl ω≡κ)) =
    subst (λ w → ⟨ ω ∈ˢ sucV w ⟩) ω≡κ (self∈sucV ω)
  go (inr (inr κ∈ω)) = Empty.rec (kappa-not-fin x ox ω∈x κ∈ω)

-- =====================================================================
-- THE OBLIGATION.  Init x fails when the ambient least cardinal of x
-- is a proper member of x.  Consumes conjunct 3, refutes conjunct 4.
-- The arrow stays truncated: PT.rec spends κ-injL; the goal is Empty.⊥.
-- =====================================================================

init-fails-below :
    (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
  → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ x ⟩
  → Init x → Empty.⊥
init-fails-below x ox ω∈x κ∈x ix =
  PT.rec Empty.isProp⊥ from-down (κ-injL a ox)
  where
  a : S
  a = x , isL-ord x ox
  κ : S
  κ = κL a ox
  oκ : IsOrd (fst κ)
  oκ = κoL a ox
  sucκ : V ℓ
  sucκ = sucV (fst κ)
  osucκ : IsOrd sucκ
  osucκ = suc-ord oκ
  sucκ∈x : ⟨ sucκ ∈ˢ x ⟩
  sucκ∈x = ix .snd .snd .fst (fst κ) κ∈x
  ω∈sucκ : ⟨ ω ∈ˢ sucκ ⟩
  ω∈sucκ = omega-in-suc-kappa x ox ω∈x
  noinj² = ix .snd .snd .snd

  from-down : (⟪ x ⟫ ↪ ⟪ fst κ ⟫) → Empty.⊥
  from-down down = noinj² sucκ osucκ sucκ∈x ω∈sucκ f finj
    where
    e : ⟪ x ⟫ ↪ ⟪ sucκ ⟫
    e = comp-inj down (ord-emb (fst κ) sucκ osucκ (self∈sucV (fst κ)))
    f : ⟪ x ⟫ → ⟪ sucκ ⟫ × ⟪ sucκ ⟫
    f m = (fst e m , fst e m)
    finj : (m n : ⟪ x ⟫) → f m ≡ f n → m ≡ n
    finj m n p = snd e m n (cong fst p)
