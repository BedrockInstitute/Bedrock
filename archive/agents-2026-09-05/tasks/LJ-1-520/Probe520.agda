{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.520] PROBE.  A Levy grade for the level graph.
-- It runs in agents/tasks/LJ-1-520/ and lands nothing in src/.
--
--   W3, FIRST      the bound on the existential, written alone in
--                  runs/W3.agda and typechecked before this file
--                  existed.  IT BOUNDS.
--   DELIVERED      levelFo-Σ₁, the briefed obligation: one formula of
--                  Formula S n with a Σ₁ witness, at variable slots.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-520.Probe520 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊥̇; ∃̇_; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-∧; δ-⊥; δ-∀∈; Σ₁; σ-Δ₀; σ-∃ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Coding.Model {ℓ} using ( sucAtL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Condensation {ℓ} lem using
  ( module GraphB; DefBodyB; Δ₀-DefBodyB; Δ₀-sucAtL )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- THE BOUNDED MATRIX, GENERIC IN EVERY SLOT.  W2: the mathematics is
-- written once here, at a generic arity and generic slots, and the
-- obligation instantiates it.  Nothing below is specific to a stage.
--
-- The two leaf environments are fixed by the delivered step frame
-- (src/L/Condensation.lagda.md:2394-2397): the leaf sits at
-- v' ∷ c' ∷ x ∷ d ∷ w ∷ c ∷ z ∷ γ', so an ambient slot travels five
-- binders at the graph's own step and seven at the step under the
-- approximation's two bounded universals.
-- ---------------------------------------------------------------------
module Matrix {m : ℕ} (w b K : Fin m)
              (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where
  private
    sh5 : Fin m → Fin (5 + m)
    sh5 i = suc (suc (suc (suc (suc i))))

    sh7 : Fin m → Fin (7 + m)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  -- The two term tags of tmValB (src/L/Condensation.lagda.md:508-517)
  -- are the numerals 0 and 1, which are N0 and N1.  No separate slot is
  -- needed and none is bound.
  ψs : Formula S (suc (suc (suc (5 + m))))
  ψs = DefBodyB {m} (suc zero) (sh5 K)
         (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
         (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
         (sh5 N0) (sh5 N1)

  ψa : Formula S (suc (suc (suc (7 + m))))
  ψa = DefBodyB {2 + m} (suc zero) (sh7 K)
         (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
         (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
         (sh7 N0) (sh7 N1)

  module G = GraphB {m} ψs ψa w b K

  Δ₀-ψs : Δ₀ ψs
  Δ₀-ψs = Δ₀-DefBodyB {m} (suc zero) (sh5 K)
            (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
            (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
            (sh5 N0) (sh5 N1)

  Δ₀-ψa : Δ₀ ψa
  Δ₀-ψa = Δ₀-DefBodyB {2 + m} (suc zero) (sh7 K)
            (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
            (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
            (sh7 N0) (sh7 N1)

  -- K IS TRANSITIVE.  This is what makes the bound do work rather than
  -- merely exist: a satisfier reached through a member of K is itself in
  -- K, which is the site fact every extAtB→extAt conversion asks for
  -- (src/L/Condensation.lagda.md:2514-2518).
  transK : Formula S m
  transK = ∀̇∈ (var K) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc K))))

  Δ₀-transK : Δ₀ transK
  Δ₀-transK = δ-∀∈ (δ-∀∈ δ-∈)

  -- THE TWELVE TAG SLOTS HOLD THE TWELVE NUMERALS, SAID IN THE OBJECT
  -- LANGUAGE.  N0 has no member, so it is ∅ = # 0; and each next slot is
  -- the successor of the one before, so N_k is # k
  -- (Cubical.HITs.CumulativeHierarchy.Constructions, InfinitySet:163-165).
  -- The twelve machine rows carry exactly these numerals, 0 through 11
  -- in this order (src/L/Coding/Model.lagda.md:1788, :1791, :1118,
  -- :1121, :1276, :1172, :1279, :1282, :1615, :1618, :1947, :1950).
  pins : Formula S m
  pins = ∀̇∈ (var N0) ⊥̇
       ∧̇ ( sucAtL N0 N1 ∧̇ ( sucAtL N1 N2 ∧̇ ( sucAtL N2 N3
       ∧̇ ( sucAtL N3 N4 ∧̇ ( sucAtL N4 N5 ∧̇ ( sucAtL N5 N6
       ∧̇ ( sucAtL N6 N7 ∧̇ ( sucAtL N7 N8 ∧̇ ( sucAtL N8 N9
       ∧̇ ( sucAtL N9 N10 ∧̇ sucAtL N10 N11 ))))))))))

  Δ₀-pins : Δ₀ pins
  Δ₀-pins =
    δ-∧ (δ-∀∈ δ-⊥)
      (δ-∧ (Δ₀-sucAtL N0 N1) (δ-∧ (Δ₀-sucAtL N1 N2) (δ-∧ (Δ₀-sucAtL N2 N3)
      (δ-∧ (Δ₀-sucAtL N3 N4) (δ-∧ (Δ₀-sucAtL N4 N5) (δ-∧ (Δ₀-sucAtL N5 N6)
      (δ-∧ (Δ₀-sucAtL N6 N7) (δ-∧ (Δ₀-sucAtL N7 N8) (δ-∧ (Δ₀-sucAtL N8 N9)
      (δ-∧ (Δ₀-sucAtL N9 N10) (Δ₀-sucAtL N10 N11)))))))))))

  -- THE WHOLE MATRIX, AND IT IS Δ₀.
  matrix : Formula S m
  matrix = transK ∧̇ ( pins ∧̇ G.graphBndAt )

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = δ-∧ Δ₀-transK (δ-∧ Δ₀-pins (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa))

-- ---------------------------------------------------------------------
-- THE OBLIGATION.  The thirteen slots the bounded matrix needs are not
-- free variables of the answer: they are BOUND, by a prenex block of
-- thirteen unbounded existentials, which is the one shape Σ₁ admits
-- (src/FOL/LevyHierarchy.lagda.md:73-75).  The bound K is the outermost;
-- the twelve tag slots follow, N11 first, so that N_k lands at slot k.
-- ---------------------------------------------------------------------
module Slots {n : ℕ} (w b : Fin n) where
  private
    M : ℕ
    M = 13 + n

    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 kk : Fin M
    n0  = zero
    n1  = suc zero
    n2  = suc (suc zero)
    n3  = suc (suc (suc zero))
    n4  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc (suc (suc zero))))
    n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    kk  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

    sh : Fin n → Fin M
    sh i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

  module Mx = Matrix {M} (sh w) (sh b) kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

  levelFo : Formula S n
  levelFo =
    ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (Mx.matrix)))))))))))))

  Σ₁-levelFo : Σ₁ levelFo
  Σ₁-levelFo =
    σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-∃ (σ-Δ₀ Mx.Δ₀-matrix)))))))))))))

-- THE BRIEFED OBLIGATION.
levelFo-Σ₁ : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ
levelFo-Σ₁ w b = Slots.levelFo w b , Slots.Σ₁-levelFo w b

-- ---------------------------------------------------------------------
-- WHAT THE FORMULA MUST MEAN, AS A TYPE.  The brief forbids buying a
-- grade by weakening the meaning, and requires the equivalence stated
-- whether or not it is proved.  Two statements, and NEITHER IS PROVED
-- HERE: the transport is another task's obligation (AD12).
--
-- The first is the semantic reading, in the shape the tree already uses
-- for the delivered graph (src/L/Condensation.lagda.md:422-431).
-- ---------------------------------------------------------------------
SaysLevel : {n : ℕ} (w b : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
SaysLevel w b γ =
    ( ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → IsOrd (fst (lookup b γ))
      → fst (lookup w γ) ≡ Lset (fst (lookup b γ)) )
  × ( IsOrd (fst (lookup b γ)) → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
      → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ )

-- The second is the syntactic reading: the graded formula and the
-- delivered ungraded one say the same thing at the same environment.
SameAsGraph : {n : ℕ} (w b : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
SameAsGraph w b γ =
    ( ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩ )
  × ( ⟨ γ ⊨ LsetGraphAt w b ⟩ → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ )

-- THE CONTRAST, MACHINE-CHECKED IN THIS FILE AND NOT READ FROM A
-- REPORT.  [LJ-1.516] refuted the grade at the delivered formula
-- (agents/tasks/LJ-1-516/Probe516.agda:162-164); the same refutation is
-- rerun here, beside the term that carries the grade, so the two stand
-- in one run.
no-Σ₁-graph : {n : ℕ} (w b : Fin n) → Σ₁ (LsetGraphAt w b) → ⊥* {ℓ}
no-Σ₁-graph w b (σ-Δ₀ ())
no-Σ₁-graph w b (σ-∃ (σ-Δ₀ (δ-∧ (δ-∧ _ ()) _)))
