{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.406] PROBE.  Init at the ambient least cardinal, from a
-- TRUNCATED induction hypothesis.  It runs in agents/tasks/LJ-1-406/
-- and lands nothing in src/.
--
--   W3 FIRST  `clause4-at-kappa`.  Conjunct 4 of Init at fst (κL a oa),
--              with `ih` and `κ-inj` as the only inputs.  The IH is
--              truncated (`∥ sq β ∥₁`); the conclusion is Empty.⊥, so
--              PT.rec eliminates the truncation.  Nothing untruncates.
--
--   TERM      `init-at-kappa`.  The four conjuncts of Init at the
--              sealed ambient least cardinal: oκ, the infinitude
--              hypothesis, successor-closure, and conjunct 4.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-406.Probe406 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; suc-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; suc∈or≡ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.InjChain {ℓ} lem using ( ω-limit; ω∉β )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SEALED HELPERS, rebuilt from src/ primitives.
-- =====================================================================

-- Every ordinal is an L-element ([LJ-1.386]'s `isL-ord`, one line).
-- Sealed (opaque): its body reduces to an `∈-induction` via
-- `ord∈Lset-suc`, and leaving it transparent forces that recursion
-- inside every conversion check on `(α , isL-ord α oα)` (P-i, R-36).
opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- Composition of two ambient injections.
comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- An ordinal that contains ω is not below ω.
inf-member : (b : V ℓ) → ⟨ ω ∈ˢ b ⟩ → (⟨ b ∈ˢ ω ⟩ → Empty.⊥)
inf-member b ω∈b h = ∈-irrefl ω (ω-ord .fst ω∈b h)

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- `fst (LeastCardInjL.κ a oa)` reduces through `leastOf`'s body to a
-- large stuck term; left transparent, every conversion check between
-- two spellings of `fst κ` re-runs that reduction and explodes.  The
-- seal makes `fst (κL a oa)` a small atom.  The two consumers of that
-- atom, `κ-inj` and `κ-min-at`, are sealed with it so their types name
-- the atom and not the transparent `LeastCardInjL.κ`.
-- =====================================================================
opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ-injL : (a : S) (oa : IsOrd (fst a))
         → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  κ-injL a oa = LeastCardInjL.κ-inj a oa

  κ-min-atL : (a : S) (oa : IsOrd (fst a))
            → (δ : S) → ⟨ fst δ ∈ˢ fst (κL a oa) ⟩
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-atL a oa = LeastCardInjL.κ-min-at a oa

-- =====================================================================
-- W3, FIRST.  Conjunct 4 of Init at fst (κL a oa).  Inputs: the
-- truncated IH and the truncated κ-inj.  Conclusion: Empty.⊥.
-- Nothing in this term untruncates anything.
-- =====================================================================

clause4-at-kappa :
    (a : S) (oa : IsOrd (fst a))
  → (κ-inj : ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁)
  → (ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
        → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
  → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩ → ⟨ ω ∈ˢ β ⟩
  → (f : ⟪ fst (κL a oa) ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
  → ((m n : ⟪ fst (κL a oa) ⟫) → f m ≡ f n → m ≡ n)
  → Empty.⊥
clause4-at-kappa a oa κ-inj ih β oβ β∈κ ω∈β f finj =
  PT.rec Empty.isProp⊥ from-sq (ih β oβ β∈κ (inf-member β ω∈β))
  where
  from-sq : sq β → Empty.⊥
  from-sq (g , g-inj) = κ-min-atL a oa (β , isL-ord β oβ) β∈κ a↪β
    where
    κ↪β : ⟪ fst (κL a oa) ⟫ ↪ ⟪ β ⟫
    κ↪β = (λ m → g (f m)) , λ m n e → finj m n (g-inj (f m) (f n) e)

    a↪β : ∥ ⟪ fst a ⟫ ↪ ⟪ β ⟫ ∥₁
    a↪β = PT.map (λ iaκ → comp-inj iaκ κ↪β) κ-inj

-- =====================================================================
-- Conjunct 3.  Successor-closure of κ, given ω ∈ κ.  The ω ∈ κ branch
-- of [LJ-1.404]'s `kappa-is-limit⁺` (`Probe404.agda:229-243`), restated
-- at the sealed `κL`.  The cases κ ∈ ω and κ ≡ ω are not needed: this
-- brief's hypothesis is ω ∈ κ.
-- =====================================================================

module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) #∈ω

shift-at : (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ˢ γ ⟩ → ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
shift-at γ oγ ω∈γ = SA.shift↪
  where
  module SA = ShiftAbs γ oγ (λ γ∈ω → ω∉β γ γ∈ω ω∈γ)
                        (λ k → oγ .fst (#∈ω k) ω∈γ)

kappa-limit :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst (κL a oa) ⟩
  → (γ : V ℓ) → ⟨ γ ∈ˢ fst (κL a oa) ⟩
  → ⟨ sucV γ ∈ˢ fst (κL a oa) ⟩
kappa-limit a oa ω∈κ γ γ∈κ = γ-tri (ord-tri γ oγ ω ω-ord)
  where
  oγ : IsOrd γ
  oγ = mem-ord {A = fst (κL a oa)} (κoL a oa) γ γ∈κ

  sω∈κ : ⟨ sucV ω ∈ˢ fst (κL a oa) ⟩
  sω∈κ = Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-ω e))
    (suc∈or≡ ω (fst (κL a oa)) ω-ord (κoL a oa) ω∈κ)
    where
    eq-ω : sucV ω ≡ fst (κL a oa) → Empty.⊥
    eq-ω e =
      κ-min-atL a oa (ω , isL-ord ω ω-ord) ω∈κ
        (PT.map (λ f → comp-inj f (subst (λ z → ⟪ z ⟫ ↪ ⟪ ω ⟫) e
          Shiftω.shift↪)) (κ-injL a oa))

  γ-tri : ⟨ γ ∈ˢ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩)
        → ⟨ sucV γ ∈ˢ fst (κL a oa) ⟩
  γ-tri (inl γ∈ω) = κoL a oa .fst (ω-limit γ γ∈ω) ω∈κ
  γ-tri (inr (inl γ≡ω)) =
    subst (λ w → ⟨ sucV w ∈ˢ fst (κL a oa) ⟩) (sym γ≡ω) sω∈κ
  γ-tri (inr (inr ω∈γ)) =
    Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-γ e))
      (suc∈or≡ γ (fst (κL a oa)) oγ (κoL a oa) γ∈κ)
    where
    eq-γ : sucV γ ≡ fst (κL a oa) → Empty.⊥
    eq-γ e =
      κ-min-atL a oa (γ , isL-ord γ oγ) γ∈κ
        (PT.map (λ f → comp-inj f (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e
          (shift-at γ oγ ω∈γ))) (κ-injL a oa))

-- =====================================================================
-- THE OBLIGATION.  Init at the sealed ambient least cardinal, from a
-- truncated IH.  Conjunct 1 is κoL, conjunct 2 is the hypothesis,
-- conjunct 3 is kappa-limit, conjunct 4 is clause4-at-kappa.
-- =====================================================================

init-at-kappa :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst (κL a oa) ⟩
  → (ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
        → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
  → Init (fst (κL a oa))
init-at-kappa a oa ω∈κ ih =
  κoL a oa ,
  ω∈κ ,
  (λ γ γ∈κ → kappa-limit a oa ω∈κ γ γ∈κ) ,
  clause4-at-kappa a oa (κ-injL a oa) ih
