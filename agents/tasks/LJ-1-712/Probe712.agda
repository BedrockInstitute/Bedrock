{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.712] PROBE.  The carve re-bounded, at the stage the door needs.
-- Lands nothing in src/.
--
--   THE OBLIGATION  carve-rebounded.  NOT INHABITED.  The corrected
--                   target named by [LJ-1.706] was priced for truth
--                   (D-10) and is FALSE at general gamma: the
--                   relativized pair-graph pins NUMERAL constants
--                   (con (numeralL k), k = 0..11) into its spine, and
--                   at gamma := emptyset the pin k = 11 does not fit
--                   under step 2 emptyset.  The refutation is a term
--                   in section 4.  review-of-carve-rebounded.md
--                   states the stop and the corrected target beside
--                   the original.
--   DELIVERED       Section 1: the frame, restated types from [LJ-1.693],
--                   [LJ-1.698], [LJ-1.706].
--                   Section 2: the door is GENERAL in the stage: it
--                   fires wherever a certificate is presented.  This
--                   is the W3 question answered by a term.
--                   Section 3: the two constants [LJ-1.706] counted,
--                   the ordinal and the stage, DO fit at step 2 gamma.
--                   Section 4: the pin the review did not count, and
--                   its refutation.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.  Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-712.Probe712 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Relativize using ( relativize )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono; 𝒟ₒ-inv; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅∈L; Lset-suc )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage; Below′ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import LJ-1-693.Probe693 {ℓ} lem using ( step; door-next; isL-ord; Door )
import LJ-1-698.Probe698 {ℓ} lem as P698
open import LJ-1-706.Probe706 {ℓ} lem
  using ( Below; Identified; Bound-in-tower )

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE FRAME.  [LJ-1.698]'s formula and its mkBoundedFo
-- bound, imported, not rebuilt.  The re-bounding target is
-- tau := step 2 gamma: at that stage the door lands in
-- Lset (sucV tau) = Lset (step 3 gamma), exactly Below's stage, BY
-- COMPUTATION on step:  sucV (step 2 gamma) and step 3 gamma reduce
-- to the same term, so no comparison row is owed on the way up.
-- =====================================================================

-- The formula whose bound is at issue, and its mkBoundedFo bound.
-- Both imported from [LJ-1.698]; recordedFo and Carved were delivered
-- green there (Probe698.agda:73-101, :107-129).
φᵣ : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → Formula CS.S 1
φᵣ γ oγ hγ = relativize (LsetS γ oγ) (P698.recordedFo (γ , hγ))

-- =====================================================================
-- SECTION 2.  THE DOOR IS GENERAL IN THE STAGE.  [LJ-1.698]'s Carved
-- fixed sigma := mkBoundedFo's first projection.  AtStage is general
-- in sigma, and carve∈𝒟ₒ / 𝒟ₒ-inv never ask where a certificate came
-- from, so the same three lines fire at ANY sigma a certificate is
-- presented for.  This is the W3 question the brief asked, answered
-- by a term: the door is NOT tied to the stage mkBoundedFo chose.
-- =====================================================================

module AtCert (τ : V ℓ) (oτ : IsOrd τ) where
  open AtStage τ oτ

  rebound-carve : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
                → BoundedFo (Below′ τ) (φᵣ γ oγ hγ) → V ℓ
  rebound-carve γ oγ hγ h = carve (RL.liftFo (φᵣ γ oγ hγ) h)

  rebound-door : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
                 (h : BoundedFo (Below′ τ) (φᵣ γ oγ hγ))
               → Door (Lset τ) (rebound-carve γ oγ hγ h)
  rebound-door γ oγ hγ h =
    𝒟ₒ-inv (Lset τ) (rebound-carve γ oγ hγ h)
      (carve∈𝒟ₒ (RL.liftFo (φᵣ γ oγ hγ) h))

rebound-lands : (τ : V ℓ) (oτ : IsOrd τ) (γ : V ℓ) (oγ : IsOrd γ)
                (hγ : ⟨ isL γ ⟩) (h : BoundedFo (Below′ τ) (φᵣ γ oγ hγ))
              → ⟨ AtCert.rebound-carve τ oτ γ oγ hγ h ∈ˢ Lset (sucV τ) ⟩
rebound-lands τ oτ γ oγ hγ h =
  door-next τ (AtCert.rebound-carve τ oτ γ oγ hγ h)
    (AtCert.rebound-door τ oτ γ oγ hγ h)

-- =====================================================================
-- SECTION 3.  THE TWO CONSTANTS THE REVIEW COUNTED, AT step 2 gamma.
-- [LJ-1.706] priced the constants of phi_r as the ordinal and the
-- stage and found both fit (review-of-below-from-carved.md, 'The
-- constants themselves fit').  Both fits are inhabited here, in the
-- exact form the certificate asks for them.
-- =====================================================================

-- The stage's own membership, one line, from Basic's own pieces
-- (src/L/Axioms/Basic.lagda.md:157-158, :196): Lset gamma is the
-- defSet of truth, so it lies in the definable powerset of itself,
-- which is Lset (sucV gamma) by Lset-suc.
Lset∈suc : (γ : V ℓ) (oγ : IsOrd γ) → ⟨ Lset γ ∈ Lset (sucV γ) ⟩
Lset∈suc γ oγ =
  subst (λ W → ⟨ Lset γ ∈ W ⟩) (sym (Lset-suc γ))
    (𝒟ₒ-intro (Lset γ) (Lset γ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset γ) ∣₁)

mono-up : (γ : V ℓ) {x : V ℓ} → ⟨ x ∈ Lset (sucV γ) ⟩
        → ⟨ x ∈ Lset (sucV (sucV γ)) ⟩
mono-up γ = Lset-mono (self∈sucV (sucV γ))

-- The ordinal constant fits.  BoundedTm P (con c) computes to P c
-- (src/FOL/Manipulation/Bounding.lagda.md:63-64), so the certificate
-- piece for con (gamma , hgamma) IS the membership below.
gamma-fit : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
          → Below′ (step 2 γ) (γ , hγ)
gamma-fit γ oγ hγ =
  mono-up γ {x = γ} (ord∈Lset-suc γ oγ)

-- The stage constant fits.  fst (LsetS γ oγ) is Lset gamma by the
-- definition of LsetS (src/L/Axioms/Basic.lagda.md:160-161).
stage-fit : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
          → Below′ (step 2 γ) (LsetS γ oγ)
stage-fit γ oγ hγ =
  mono-up γ {x = Lset γ} (Lset∈suc γ oγ)

-- =====================================================================
-- SECTION 4.  THE PIN THE REVIEW DID NOT COUNT.
--
-- The readers under DefBody pin NUMERAL constants into the spine.
-- tagAtL is `∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL ...)'
-- (src/L/Coding/Model.lagda.md:585-586); it carries con (numeralL k)
-- for every k its callers pin.  The callers under phi_r pin
-- k = 1 (keyArityAtL, src/L/Coding/CodeSet.lagda.md:135), k = 0
-- (envOneAt, src/L/Coding/Powerset.lagda.md:128-129), and
-- k = 2,3,4,5,8,9,10,11 (closedAt's eight clauses,
-- src/L/Coding/Model.lagda.md:2172-2189), besides the twelve-shape
-- reader (src/L/Coding/Shape.lagda.md:160-189).  So the certificate
-- at ANY tau carries a piece for pin k = 11:
--
--   BoundedTm (Below′ tau) (con (numeralL 11))
--
-- and at tau := step 2 gamma that piece is FALSE at general gamma.
-- The refutation below is a term.
-- =====================================================================

ord# : (n : ℕ) → IsOrd (# n)
ord# zero    = ∅-ord
ord# (suc n) = suc-ord (ord# n)

climb : (m n : ℕ) → ⟨ # m ∈ # (suc n) ⟩ → ⟨ # m ∈ # (suc (suc n)) ⟩
climb m n = ∈sucV-inl

#2∈#11 : ⟨ # 2 ∈ # 11 ⟩
#2∈#11 = climb 2 9 (climb 2 8 (climb 2 7 (climb 2 6 (climb 2 5
         (climb 2 4 (climb 2 3 (climb 2 2 (self∈sucV (# 2)))))))))

#1∈#11 : ⟨ # 1 ∈ # 11 ⟩
#1∈#11 = climb 1 9 (climb 1 8 (climb 1 7 (climb 1 6 (climb 1 5
         (climb 1 4 (climb 1 3 (climb 1 2 (climb 1 1
           (self∈sucV (# 1))))))))))

-- The core: pin 11 does not sit in step 2 of the empty ordinal.
no-11 : ⟨ # 11 ∈ Lset (step 2 ∅) ⟩ → Empty.⊥
no-11 h = Empty.rec*
  (∈sucV-elim {A = sucV ∅} {x = # 11} {P = Empty.⊥* {ℓ = ℓ-suc ℓ}}
    Empty.isProp⊥*
    (ord∈Lset→∈ (step 2 ∅) (suc-ord (suc-ord ∅-ord)) (# 11) (ord# 11) h)
    (λ q₁ →
      ∈sucV-elim {A = ∅} {x = # 11} {P = Empty.⊥* {ℓ = ℓ-suc ℓ}}
        Empty.isProp⊥* q₁
        (λ q₂ → Empty.rec
          (∅-empty (# 11) (∈∈ₛ {a = # 11} {b = ∅} .fst q₂)))
        (λ e₂ → Empty.rec
          (∅-empty (# 1)
            (∈∈ₛ {a = # 1} {b = ∅} .fst
              (subst (λ w → ⟨ (# 1) ∈ w ⟩) e₂ #1∈#11)))))
    (λ e₁ →
      ∈sucV-elim {A = ∅} {x = # 2} {P = Empty.⊥* {ℓ = ℓ-suc ℓ}}
        Empty.isProp⊥*
        (subst (λ w → ⟨ (# 2) ∈ w ⟩) e₁ #2∈#11)
        (λ q₂ → Empty.rec
          (∅-empty (# 2) (∈∈ₛ {a = # 2} {b = ∅} .fst q₂)))
        (λ e₂ → Empty.rec
          (∅-empty (# 1)
            (∈∈ₛ {a = # 1} {b = ∅} .fst
              (subst (λ w → ⟨ (# 1) ∈ w ⟩) e₂ (self∈sucV (# 1))))))))

-- The certificate piece the re-bounding would need, for every gamma.
pin-11 : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → Type (ℓ-suc ℓ)
pin-11 γ oγ hγ = Below′ (step 2 γ) (numeralL 11)

-- The piece is refuted at general gamma: gamma := the empty ordinal
-- kills it.  THIS IS THE ROW THAT KILLS THE TARGET AS NAMED.
refuted-pin : ((γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → pin-11 γ oγ hγ)
             → Empty.⊥
refuted-pin u = no-11
  (subst (λ w → ⟨ w ∈ Lset (step 2 ∅) ⟩) (numeralL-fst 11)
    (u ∅ ∅-ord ∅∈L))

-- =====================================================================
-- SECTION 5.  THE OBLIGATION NAME IS ABSENT ON PURPOSE.  No postulate
-- stands in for it.  carve-rebounded, the certificate at tau :=
-- step 2 gamma together with the door it feeds, is refuted by
-- refuted-pin above.  The door itself is general (section 2): what is
-- tied down is the CERTIFICATE, and the readers, not the door.
-- review-of-carve-rebounded.md states the stop, the corrected target
-- beside the original, and the constant inventory with sites.
-- =====================================================================
