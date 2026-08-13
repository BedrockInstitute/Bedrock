{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.36] IS THE LEAF READING REALLY 2 SECONDS PER CLAUSE?
--
-- [LJ-1.35] measured ONE clause's leaf reading, the `DefBody` leaf of
-- the condensation step, and projected the other eleven at about
-- 2 seconds each.  This probe measures the leaf reading for MORE
-- clauses, chosen for DIFFERENT body shapes, and reports SECONDS PER
-- CLAUSE net of the module-load cone (the control is
-- src/ProbeLJ136Ctrl.agda).
--
-- The measured clauses:
--   ANCHOR  the DefBody leaf reading, copied from [LJ-1.35] (code-read
--           and graph-read), for a same-session comparison.
--   STEP    the full step clause reading through the delivered
--           StepAt-out: from the satisfaction of the built StepAt,
--           extract the step payload StepOf.
--   ROWS    four rows of the twelve-clause satisfaction table, read
--           out of the built twelveAt conjunction and through the
--           delivered row readers (negClause-out, impClause-out,
--           topClause-out, botClause-out).  The rows differ in body
--           shape: imp has three nested unbounded universals, neg has
--           two, top has one, bot has none, and the projection depth
--           in twelveAt differs (mem at depth 1, exIn at depth 12).
--
-- SECTION 4 measures the graph witness's own existentials: the code
-- set C, the table T and the carrier b need K-membership in the
-- substrate's bounded restatement ([LJ-1.35] uncertainty 2).
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ136 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt
        ; unClauseAt; unClause-out; subValAt; envSetAt; diffAt )
open import L.Coding.Powerset {ℓ} lem
  using ( DefBody; codeAt-out )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.Graph {ℓ} lem
  using ( GraphWitAt; graphAt-out; twelveAt )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepAt-out; StepOf; PowOK )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

-- =====================================================================
-- SECTION 1: THE ANCHOR.  The DefBody leaf reading from [LJ-1.35],
-- copied verbatim, for a same-session comparison.  The leaf
-- environment is (v' ∷ c' ∷ x ∷ δ); the carrier is slot (suc zero) of
-- δ and the K bound is slot (suc (suc (suc (suc zero)))) of δ.
-- =====================================================================
module LeafAnchor {n : ℕ} (A : S) (δ : S ^ (5 + n)) where
  private
    qcar : Type (ℓ-suc ℓ)
    qcar = fst (lookup (suc zero) δ) ≡ fst A

  -- The code fact: the code is a key over the carrier.
  code-read : qcar → (c' v' x : S)
            → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} (suc zero) ⟩
            → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                  (fst c' ≡ fst (keyS A ψ))) ∥₁
  code-read qc c' v' x h =
    codeAt-out A (suc zero) (sh3 (suc zero)) (v' ∷ c' ∷ x ∷ δ) qc (h .fst)

  -- The graph witness over the carrier, via the delivered existence
  -- direction.
  graph-read : (c' v' x : S)
             → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} (suc zero) ⟩
             → ∥ GraphWitAt (sh3 (suc zero)) (suc zero) zero
                  (v' ∷ c' ∷ x ∷ δ) ∥₁
  graph-read c' v' x h =
    graphAt-out (sh3 (suc zero)) (suc zero) zero (v' ∷ c' ∷ x ∷ δ) (h .snd .fst)

-- =====================================================================
-- SECTION 2: THE STEP CLAUSE.  The full step clause reading through
-- the delivered StepAt-out: the satisfaction of the built StepAt gives
-- the step payload StepOf.  This is the outer layer of the measured
-- clause; [LJ-1.34-R] priced its generic decode near zero, so this
-- row tests whether the outer layer stays cheap with the built body in
-- the type.
-- =====================================================================
module StepRead {n : ℕ} (v b f : Fin n) (γ : S ^ n) where
  step-read : PowOK b f γ → (z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩
            → ⟨ γ ⊨ StepAt v b f ⟩ → ∥ StepOf b f γ z ∥₁
  step-read ok z z∈ h = StepAt-out v b f γ h ok z z∈

-- =====================================================================
-- SECTION 3: THE TABLE ROWS.  Each row is read out of the built
-- twelveAt conjunction by projection (the projection's type conversion
-- walks the built conjunction), and the deep rows are read further
-- through the delivered row readers.  The types of the reader
-- applications mention private relation bodies, so those definitions
-- carry no signature and Agda infers them; the probe is never
-- imported, so the inferred types are harmless.
-- =====================================================================
module RowProject {n : ℕ} (C T B : Fin n) (γ : S ^ n) where
  -- The atom row, depth 1 in twelveAt.
  mem-row : ⟨ γ ⊨ twelveAt C T B ⟩ → ⟨ γ ⊨ memClauseAt C T B ⟩
  mem-row h = h .fst

  -- The implication row, depth 4; three unbounded universals inside.
  imp-row : ⟨ γ ⊨ twelveAt C T B ⟩ → ⟨ γ ⊨ impClauseAt C T B ⟩
  imp-row h = h .snd .snd .snd .snd .fst

  -- The negation row, depth 5; two unbounded universals inside.
  neg-row : ⟨ γ ⊨ twelveAt C T B ⟩ → ⟨ γ ⊨ negClauseAt C T B ⟩
  neg-row h = h .snd .snd .snd .snd .snd .fst

  -- The bounded-existential row, depth 12; the deepest projection.
  exIn-row : ⟨ γ ⊨ twelveAt C T B ⟩ → ⟨ γ ⊨ exInClauseAt C T B ⟩
  exIn-row h =
    h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd

-- =====================================================================
-- SECTION 3B: THE RE-DERIVED NEGATION SHAPE.  The delivered relation
-- bodies are private, so an outside reading of the delivered rows never
-- unfolds them.  The substrate may instead write the relation fresh
-- (its own bounded story is fresh anyway, P-v), so this row measures
-- the reading of a re-derived two-universal relation through the
-- delivered unClause-out frame.  All names are public.
-- =====================================================================
module ReNeg {n : ℕ} (C T B : Fin n) where
  private
    sh6 : Fin n → Fin (6 + n)
    sh6 i = suc (suc (suc (suc (suc (suc i)))))

    ar6 a6 yc6 ya6 E6 : Fin (6 + n)
    ar6 = suc (suc (suc (suc zero)))
    a6  = suc (suc (suc zero))
    yc6 = suc (suc zero)
    ya6 = suc zero
    E6  = zero

  neg-rel : Formula S (4 + n)
  neg-rel =
    ∀̇ (∀̇ ( subValAt (sh6 T) ar6 a6 ya6
         ⇒̇ ( envSetAt E6 ar6 (sh6 B)
         ⇒̇ diffAt yc6 E6 ya6 )))

  reneg-clause : Formula S n
  reneg-clause = unClauseAt C T 5 neg-rel

  reneg-read : (γ : S ^ n)
            → ⟨ γ ⊨ reneg-clause ⟩
            → (c ar a yc : S)
            → ⟨ fst c ∈ fst (lookup C γ) ⟩
            → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
            → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
            → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ neg-rel ⟩
  reneg-read γ h = unClause-out C T 5 neg-rel γ h

-- =====================================================================
-- SECTION 4: THE WITNESS MEMBERSHIPS.  The graph witness's own
-- existentials, the code set C, the table T and the carrier b, need
-- K-membership in the substrate's bounded restatement.  The site
-- facts are hypotheses, exactly as [LJ-1.35] took codes-in-K and
-- witness-vals-in-K; the extractions below measure whether the
-- witness memberships behave like the story's own quantifiers (cheap
-- assembly) or worse.
-- =====================================================================
module WitnessMems {n : ℕ} (A : S) (δ : S ^ (5 + n)) where
  private
    K-slot : Fin (5 + n)
    K-slot = suc (suc (suc (suc zero)))

    qcar : Type (ℓ-suc ℓ)
    qcar = fst (lookup (suc zero) δ) ≡ fst A

    -- THE SITE FACTS, stated once and not built here.
    codes-in-K : Type (ℓ-suc ℓ)
    codes-in-K = (C T b : S) → fst b ≡ fst A
               → ⟨ fst C ∈ fst (lookup K-slot δ) ⟩

    tables-in-K : Type (ℓ-suc ℓ)
    tables-in-K = (C T b : S) → fst b ≡ fst A
                → ⟨ fst T ∈ fst (lookup K-slot δ) ⟩

    carriers-in-K : Type (ℓ-suc ℓ)
    carriers-in-K = (b : S) → fst b ≡ fst A
                  → ⟨ fst b ∈ fst (lookup K-slot δ) ⟩

  -- The three extractions: projections of the witness, discharged by
  -- the site facts.
  wcode-in-K : qcar → codes-in-K → (c' v' x : S)
             → (w : GraphWitAt (sh3 (suc zero)) (suc zero) zero
                    (v' ∷ c' ∷ x ∷ δ))
             → ⟨ fst (fst w) ∈ fst (lookup K-slot δ) ⟩
  wcode-in-K qc ck c' v' x w =
    ck (w .fst) (w .snd .fst) (w .snd .snd .fst)
       (w .snd .snd .snd .fst ∙ qc)

  wtable-in-K : qcar → tables-in-K → (c' v' x : S)
              → (w : GraphWitAt (sh3 (suc zero)) (suc zero) zero
                     (v' ∷ c' ∷ x ∷ δ))
              → ⟨ fst (w .snd .fst) ∈ fst (lookup K-slot δ) ⟩
  wtable-in-K qc tk c' v' x w =
    tk (w .fst) (w .snd .fst) (w .snd .snd .fst)
       (w .snd .snd .snd .fst ∙ qc)

  wcarrier-in-K : qcar → carriers-in-K → (c' v' x : S)
                → (w : GraphWitAt (sh3 (suc zero)) (suc zero) zero
                       (v' ∷ c' ∷ x ∷ δ))
                → ⟨ fst (w .snd .snd .fst) ∈ fst (lookup K-slot δ) ⟩
  wcarrier-in-K qc bk c' v' x w =
    bk (w .snd .snd .fst) (w .snd .snd .snd .fst ∙ qc)

  -- The row extractions from the graph witness, the substrate's actual
  -- shape.  The witness's twelveAt satisfaction mentions private
  -- indices, so these definitions carry no signature; the probe is
  -- never imported.
  wit-mem = λ (v' c' x : S) (w : GraphWitAt (sh3 (suc zero)) (suc zero)
                 zero (v' ∷ c' ∷ x ∷ δ)) → w .snd .snd .snd .snd .fst
  wit-exIn = λ (v' c' x : S) (w : GraphWitAt (sh3 (suc zero)) (suc zero)
                   zero (v' ∷ c' ∷ x ∷ δ)) →
    w .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd
      .snd .snd .snd
