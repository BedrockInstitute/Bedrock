{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.396] PROBE.  `AmbCard` has a producer, at the SELECTED κ and at no
-- other ordinal.  It runs in agents/tasks/LJ-1-396/ and lands nothing in
-- src/.
--
-- The producer is ONE composition under a truncation, and the truncation
-- is free because the conclusion is Empty.⊥.  TERM 1, `amb-card-at-kappa`,
-- builds `AmbCard (fst (LeastCardInjL.κ a oa))` at a GENERIC ordinal:
-- κ-inj is truncated, comp-inj lifts it to β under the truncation, and
-- κ-min-at refutes it.  TERM 2, `kappa-is-limit`, is what the brief states
-- and it is REFUTED at the finite site a := sucV ∅ (see PART 3).  The
-- repaired form `kappa-is-limit-ω∈γ` is PART 4, the same move
-- [LJ-1.392] used for `amb-limit-ω∈γ`: restrict to members that contain
-- ω, then suc∈or≡, and the equality case dies on suc-absorb plus TERM 1.
--
-- W3, FIRST: `beta-lifts`, the one step that carries a bare member β into
-- κ-min-at's `δ : S` argument.  It is stated alone below and run before
-- anything else, per the brief's order.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( ω; sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-396.Probe396 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (suc-absorb :
     (γ : V ℓ) → IsOrd γ → ⟨ ω ∈ γ ⟩
     → Σ[ f ∈ (⟪ sucV γ ⟫ → ⟪ γ ⟫) ]
         ((m n : ⟪ sucV γ ⟫) → f m ≡ f n → m ≡ n)) where

open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; suc∈or≡ )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open import Cubical.Data.Sum as Sum using ( rec )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3, FIRST.  The lift of a bare member β of fst κ to an L-element.
--   `isL-trans` needs a membership in a level: β ∈ fst κ and the level
--   proof snd κ give isL β.  This one step is what the brief names the
--   widest unmeasured term, stated alone and run before anything else.
-- =====================================================================

beta-lifts : (κ : S) (β : V ℓ) → ⟨ β ∈ fst κ ⟩ → S
beta-lifts κ β β∈κ = β , isL-trans β∈κ (snd κ)

-- =====================================================================
-- The two generic pieces the producer composes with.
--
--   `comp-inj` composes two ambient injections.  It is the term
--   `L.StageCardinal.Upper.comp-inj` (src/L/StageCardinal.lagda.md:500)
--   written INLINE, because that module takes the square-law parameter
--   this probe does not have and must not assume.
--
--   `AmbCard` is [LJ-1.393]'s notion, spelled UNFOLDED, exactly as that
--   task did (agents/tasks/LJ-1-393/Probe393.agda:102-104).  It is a
--   DEFINITION here, not a producer.
-- =====================================================================

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

AmbCard : V ℓ → Type (ℓ-suc ℓ)
AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
          → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

-- =====================================================================
-- TERM 1.  The producer.  One composition under a truncation, and the
--   truncation is free because the conclusion is Empty.⊥.
--
--   1. κ-inj gives ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁.
--   2. PT.map carries comp-inj with e under the truncation.
--   3. beta-lifts turns β into an L-element, and κ-min-at refutes it.
-- =====================================================================

amb-card-at-kappa : (a : S) (oa : IsOrd (fst a))
                  → AmbCard (fst (LeastCardInjL.κ a oa))
amb-card-at-kappa a oa = go
  where
  open LeastCardInjL a oa
  go : AmbCard (fst κ)
  go β oβ β∈κ ω∈β e =
    κ-min-at (beta-lifts κ β β∈κ) β∈κ
      (PT.map (λ f → comp-inj f e) κ-inj)

-- =====================================================================
-- TERM 2, AS THE BRIEF STATES IT.  REFUTED: see PART 3.
-- =====================================================================

kappa-is-limit :
    (a : S) (oa : IsOrd (fst a))
  → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩
  → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩
kappa-is-limit = ?

-- =====================================================================
-- PART 3.  THE REFUTATION.  The site is a := sucV ∅, the ordinal 1.
--
--   fst κ = |fst a| = sucV ∅.  A member of sucV (sucV ∅) is ∅ or sucV ∅;
--   fst κ is not ∅ (κ-inj gives an injection of the inhabited ⟪ sucV ∅ ⟫
--   into ⟪ fst κ ⟫, which cannot be empty), so fst κ = sucV ∅.  Then the
--   member γ := ∅ gives the conclusion sucV ∅ ∈ sucV ∅, and ∈-irrefl
--   kills it.
-- =====================================================================

a1 : S
a1 = sucV ∅ ,
  Lset→isL (sucV (sucV ∅)) (suc-ord (suc-ord ∅-ord)) (sucV ∅)
    (ord∈Lset-suc (sucV ∅) (suc-ord ∅-ord))

o1 : IsOrd (fst a1)
o1 = suc-ord ∅-ord

module R = LeastCardInjL a1 o1

-- ⟪ sucV ∅ ⟫ is inhabited (∅ ∈ sucV ∅) and ⟪ ∅ ⟫ is empty, so no injection.
noInjEmpty : ⟪ sucV ∅ ⟫ ↪ ⟪ ∅ ⟫ → Empty.⊥
noInjEmpty (f , _) = Empty.rec (∅-empty (⟪ ∅ ⟫↪ (f m)) (∈ₛ⟪ ∅ ⟫↪ (f m)))
  where
  m : ⟪ sucV ∅ ⟫
  m = fiber (sucV ∅) (self∈sucV ∅) .fst

κ-not-∅ : fst R.κ ≡ ∅ → Empty.⊥
κ-not-∅ κ≡∅ =
  PT.rec Empty.isProp⊥
    (λ inj → noInjEmpty (subst (λ w → ⟪ sucV ∅ ⟫ ↪ ⟪ w ⟫) κ≡∅ inj))
    R.κ-inj

κ≡suc∅ : fst R.κ ≡ sucV ∅
κ≡suc∅ = ∈sucV-elim (setIsSet (fst R.κ) (sucV ∅)) R.κ∈sα
  (λ κ∈suc∅ → ∈sucV-elim (setIsSet (fst R.κ) (sucV ∅)) κ∈suc∅
     (λ κ∈∅ → Empty.rec (∅-empty (fst R.κ) (∈∈ₛ {a = fst R.κ} {b = ∅} .fst κ∈∅)))
     (λ κ≡∅ → Empty.rec (κ-not-∅ κ≡∅)))
  (λ κ≡suc∅ → κ≡suc∅)

kappa-is-limit-refuted :
    ((a : S) (oa : IsOrd (fst a))
     → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩
     → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩)
   → Empty.⊥
kappa-is-limit-refuted kil =
  ∈-irrefl (sucV ∅) (subst (λ w → ⟨ sucV ∅ ∈ w ⟩) κ≡suc∅ (kil a1 o1 ∅ ∅∈κ))
  where
  ∅∈κ : ⟨ ∅ ∈ fst R.κ ⟩
  ∅∈κ = subst (λ w → ⟨ ∅ ∈ w ⟩) (sym κ≡suc∅) (self∈sucV ∅)

-- =====================================================================
-- PART 4.  THE REPAIRED STATEMENT, GREEN.  Restrict the conclusion to
--   members γ that CONTAIN ω.  Then suc∈or≡ (src/L/Ordinal/Stages.lagda.md:137)
--   delivers both cases: the first IS the goal, the second contradicts
--   AmbCard at β := γ through suc-absorb itself.  No case split on γ:
--   this is [LJ-1.392]'s `amb-limit-ω∈γ` (Probe392.agda:255-266) at the
--   selected κ, with TERM 1 supplying the no-injection hypothesis.
-- =====================================================================

kappa-is-limit-ω∈γ :
    (a : S) (oa : IsOrd (fst a))
  → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩ → ⟨ ω ∈ γ ⟩
  → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩
kappa-is-limit-ω∈γ a oa γ γ∈κ ω∈γ =
  Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec
    (amb-card-at-kappa a oa γ oγ γ∈κ ω∈γ
      (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e (suc-absorb γ oγ ω∈γ))))
  (suc∈or≡ γ (fst κ) oγ oκ γ∈κ)
  where
  open LeastCardInjL a oa
  oγ : IsOrd γ
  oγ = mem-ord {A = fst κ} oκ γ γ∈κ
