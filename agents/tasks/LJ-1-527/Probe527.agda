{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.527] PROBE.  ROW TWO of the six-row chain [LJ-1.525] laid out:
-- the bounded body `StepB.bodyB` becomes the machine's own `StepBody`.
-- It runs in agents/tasks/LJ-1-527/ and lands nothing in src/.
--
--   W3, FIRST      the index match, written alone in runs/W3.agda and
--                  typechecked before this file existed.  `sh4` IS
--                  suc⁴, at both slots.  THEY MEET.
--   REBUILT        row one, [LJ-1.525]'s `leaf-unbounds`, at its
--                  delivered type (agents/tasks/LJ-1-525/Probe525.agda
--                  :150-165).  The brief orders a rebuild and not an
--                  import, so nothing of [LJ-1.525] is imported here.
--                  Its five hypotheses ride into the conclusion of the
--                  obligation, undischarged and unhidden.
--   DELIVERED      body-unbounds, the briefed obligation.
--
-- WHAT IS IMPORTED FROM A PREDECESSOR: `defPow-closed-noCode` and
-- `IsLimit` from [LJ-1.522], which is what row one is BUILT FROM and
-- not row one itself.  Rebuilding that too would rebuild the whole leg.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-527.Probe527 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Model {ℓ} using ( extAt; appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody; DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem
  using ( extAtB; extAtB→extAt; module StepB )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  ROW ONE, REBUILT.
--
-- Copied at type from agents/tasks/LJ-1-525/Probe525.agda:64-165, which
-- reports GO (agents/tasks/LJ-1-525/lj-1.525-report.md:3).  It is NOT
-- imported: the brief orders the rebuild so that this file's obligation
-- stands on a term this file typechecks.  Nothing here is new
-- mathematics and nothing here is claimed as this task's work.
-- ---------------------------------------------------------------------

-- The machine's leaf condition: `DefAt`'s own body
-- (src/L/Coding/Powerset.lagda.md:443).
leafFo : ∀ {n} → Fin n → Formula S (suc n)
leafFo w = ∃̇ (∃̇ (DefBody w))

-- The bounded leaf's condition: the shape `leafB` puts under `extAtB`
-- (src/L/Condensation.lagda.md:2399-2402).
leafBFo : ∀ {n} → Fin n → Formula S (suc (suc (suc n))) → Formula S (suc n)
leafBFo K ψB = ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) ψB)

leaf-inK :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                   → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩
leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd x hx =
  PT.rec (snd (fst x ∈ fst (lookup K γ)))
    (λ { (c , (cK , hc)) → PT.rec (snd (fst x ∈ fst (lookup K γ)))
      (λ { (val , (vK , hv)) →
        defPow-closed-noCode α lim w K γ qK W∈K x c val vK
          (leafFwd x c val hv) })
      hc })
    (bwd x hx)

leaf-fwd :
    ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                   → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩ → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
leaf-fwd w K ψB γ leafFwd x =
  PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
    (λ { (c , (_ , hc)) →
      PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
        (λ { (val , (_ , hv)) → ∣ c , ∣ val , leafFwd x c val hv ∣₁ ∣₁ })
        hc })

leaf-unbounds-gen :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (y K w : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                   → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → ⟨ γ ⊨ extAtB y K (leafBFo K ψB) ⟩
  → ⟨ γ ⊨ DefAt y w ⟩
leaf-unbounds-gen α lim y K w ψB γ qK W∈K leafFwd bwd =
  extAtB→extAt y K (leafBFo K ψB) (leafFo w) γ
    (leaf-fwd w K ψB γ leafFwd)
    bwd
    (leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd)

-- ROW ONE AT THE SITE.  `StepB.leafB` becomes the third conjunct of the
-- machine's `StepBody` (src/L/Coding/Sequence.lagda.md:116).
leaf-unbounds :
    (α : V ℓ) → IsLimit α
  → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b f K : Fin m)
  → (γ : S ^ (4 + m))
  → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
  → ⟨ fst (lookup (suc zero) γ)
      ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
  → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                   → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
             → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
  → ⟨ γ ⊨ StepB.leafB {m} ψ sv b f K ⟩
  → ⟨ γ ⊨ DefAt zero (suc zero) ⟩
leaf-unbounds α lim ψ sv b f K γ qK W∈K leafFwd bwd =
  leaf-unbounds-gen α lim zero (suc (suc (suc (suc K)))) (suc zero) ψ γ
    qK W∈K leafFwd bwd

-- ---------------------------------------------------------------------
-- SECTION 2.  THE FRAME, AND THE CONGRUENCE AT A GENERIC CARRIER (W2).
--
-- W3 typechecked `bodyB-at` and `stepBody-at` (runs/W3.agda:66-81):
-- BOTH sides are this one frame, with the two index slots supplied as
-- suc⁴ b and suc⁴ f, and they differ in the LEAF SLOT ONLY.  So row two
-- is a congruence over the leaf slot and nothing else.
--
-- W2: the congruence below fixes no arity, no index and no leaf.  The
-- obligation of section 3 is an instantiation of it and adds no
-- content.  Note that it is not even a fact about the STEP frame: it is
-- a fact about a conjunction with a hole, and it would carry any other
-- frame of the same shape at the same price.
-- ---------------------------------------------------------------------
stepFrameAt : ∀ {m} (B F : Fin (4 + m))
            → Formula S (4 + m) → Formula S (4 + m)
stepFrameAt B F leaf =
  (var (suc (suc zero)) ∈̇ var B)
  ∧̇ ( appAt F (suc (suc zero)) (suc zero)
     ∧̇ ( leaf ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

frame-cong :
    ∀ {m} (B F : Fin (4 + m)) (leaf leaf' : Formula S (4 + m))
  → (γ : S ^ (4 + m))
  → (⟨ γ ⊨ leaf ⟩ → ⟨ γ ⊨ leaf' ⟩)
  → ⟨ γ ⊨ stepFrameAt B F leaf ⟩
  → ⟨ γ ⊨ stepFrameAt B F leaf' ⟩
frame-cong B F leaf leaf' γ mp h =
    h .fst
  , ( h .snd .fst
    , ( mp (h .snd .snd .fst)
      , h .snd .snd .snd ) )

-- ---------------------------------------------------------------------
-- SECTION 3.  THE OBLIGATION.
--
-- Row two: the bounded body reaches the machine's own body, at the same
-- environment.  The five hypotheses are row one's, carried in
-- UNCHANGED and UNDISCHARGED.  `sv` and `K` occur only in row one's
-- site instance; `b` and `f` are the two slots the machine's `StepBody`
-- names.
-- ---------------------------------------------------------------------
body-unbounds :
    (α : V ℓ) → IsLimit α
  → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b f K : Fin m)
  → (γ : S ^ (4 + m))
  → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
  → ⟨ fst (lookup (suc zero) γ)
      ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
  → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                   → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
             → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
  → ⟨ γ ⊨ StepB.bodyB {m} ψ sv b f K ⟩
  → ⟨ γ ⊨ StepBody b f ⟩
body-unbounds α lim ψ sv b f K γ qK W∈K leafFwd bwd =
  frame-cong (suc (suc (suc (suc b)))) (suc (suc (suc (suc f))))
    (StepB.leafB ψ sv b f K) (DefAt zero (suc zero)) γ
    (leaf-unbounds α lim ψ sv b f K γ qK W∈K leafFwd bwd)
