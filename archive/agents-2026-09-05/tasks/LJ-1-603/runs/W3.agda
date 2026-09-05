{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  W3.  THE LIMIT CASE'S OWN INDEX, TYPE ONLY.
--
-- [LJ-1.601]'s report, on what its GO leaves
-- (agents/tasks/LJ-1-601/lj-1.601-report.md:52-56):
--
--   "Ingredient (iv) of [LJ-1.594]'s table is thereby re-priced downward
--    at its base only: the `ω`-base no longer blocks, so what remains
--    unmeasured in (iv) is the recursion at infinite member stages, and
--    ingredients (iii), the pairing, and (v), the coded copy, are
--    untouched by this task."
--
-- THE WIDEST UNMEASURED TERM IS THAT RECURSION'S OWN INDEX: the data
-- that indexes the recursion AT AN INFINITE MEMBER STAGE.  It is the
-- stage itself with its ordinal data, its position under the ambient
-- bound, its non-finiteness, and the witness `ω ∈ δ` that selects
-- the limit case of the branch
-- (src/L/StageCardinal.lagda.md:545, the `inr (inr ω∈δ)` case at
-- :555-556).  This slice states it as `InfStage` and NOTHING else is
-- built on it here except the statement.
--
-- THE INDEX IS A SIGMA AND NOT A RECORD, AND THAT IS A MEASUREMENT OF
-- THIS DISPATCH, NOT A STYLE CHOICE.  The record spelling of the same
-- five fields WALLS the pane's 2 GB cap: `runs/w3-1.out` (the record,
-- full slice), `runs/bisect-a.out` (record, statement removed),
-- `runs/bisect-b.out` (record + Ih + step-fn only) and
-- `runs/bisect-c.out` (record ALONE) all die at "Heap exhausted", 2048
-- MB, 24 to 28 s.  The Sigma spelling of the SAME content, with the
-- projections named once below, is GREEN at 1.32 s
-- (`runs/bisect-d.out`, then `runs/w3-2.out` for this whole file).
-- P-l read at this site: the record's generated structure in the
-- statement's type is a presentation cost, and the Sigma is the atom.
--
-- THE STATEMENT IS [LJ-1.597]'s `Graph` SHAPE
-- (agents/tasks/LJ-1-597/Probe597.agda:269-285), the shape [LJ-1.601]
-- also took (its runs/W3.agda, `TallyGraph`): a `Formula S 2`, value
-- variable FIRST and index variable SECOND, with BOTH readings the
-- internalization chapter's own `Definition` demands, `defines` and
-- `only` (src/L/Recursion.lagda.md:272-279).  The subject is the
-- function part of the route's delivered recursion AT the member
-- stage, read on the members of `Lset δ`, values lifted to
-- L-elements of the stage itself.
--
-- WHY `limit-step` AND NOT `stage-card-upper`: at an infinite member
-- stage the branch IS the induction hypothesis at that stage
-- (src/L/StageCardinal.lagda.md:555-556), and the assembly is
-- `stage-card-upper = ∈-induction step` (:566), so that hypothesis is
-- the step's own output one stage down.  [LJ-1.584] measured that
-- `step`, `branch` and `stage-card-upper` in a CONVERSION problem do
-- not terminate (agents/tasks/LJ-1-584/runs/w3b-1.out), so the
-- statement takes the step AT the member stage with the branch below
-- it abstract, exactly as [LJ-1.597]'s Graph took the step at the
-- ambient stage with IH a parameter.  `ω∈δ` sits in the index and in
-- no row of the value equation.
--
-- The brief: "Write it FIRST and typecheck it ALONE.  ESTIMATE: about
-- 12 lines, cap at two minutes."
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-603.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- 0.1  THE LIMIT CASE'S OWN INDEX.  An infinite member stage: an
--      ordinal stage under the ambient bound, NOT a member of `ω`, and
--      WITH `ω` as a member, which is the case selector the branch's
--      trichotomy hands to `go (inr (inr ω∈δ))`
--      (src/L/StageCardinal.lagda.md:545, :555-556).  Five components,
--      and the fifth is the one no predecessor statement ever carried.
--      A SIGMA, with the projections named once below; see the header
--      for the measurement that ruled the spelling.
InfStage : Type (ℓ-suc ℓ)
InfStage =
  Σ[ δ ∈ V ℓ ] Σ[ oδ ∈ IsOrd δ ] Σ[ δ∈suc ∈ ⟨ δ ∈ˢ sucV α₀ ⟩ ]
    Σ[ infδ ∈ (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) ] ⟨ ω ∈ˢ δ ⟩

δI : (i : InfStage) → V ℓ
δI i = fst i

oδI : (i : InfStage) → IsOrd (δI i)
oδI i = fst (snd i)

δ∈sucI : (i : InfStage) → ⟨ δI i ∈ˢ sucV α₀ ⟩
δ∈sucI i = fst (snd (snd i))

infδI : (i : InfStage) → (⟨ δI i ∈ˢ ω ⟩ → Empty.⊥)
infδI i = fst (snd (snd (snd i)))

ω∈δI : (i : InfStage) → ⟨ ω ∈ˢ δI i ⟩
ω∈δI i = snd (snd (snd (snd i)))

-- 0.2  THE LIFTS, one line each.  [LJ-1.561]'s discipline
--      (agents/tasks/LJ-1-561/Probe561.agda:107-115 re-typed both
--      rather than import them): importing a probe costs its whole
--      elaboration and these are one line each.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

up : (b : S) → ⟪ fst b ⟫ → S
up b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)

-- 0.3  THE RECURSION'S VALUE AT THE MEMBER STAGE, one unfolding.  The
--      branch below the member stage, abstract; the step AT the member
--      stage, delivered.  This is the same reading [LJ-1.597] fixed at
--      the ambient stage (`step-fn`, Probe597.agda:34-46), taken one
--      stage down.
Ih : (i : InfStage) → Type ℓ
Ih i = (m : ⟪ δI i ⟫) → ⟪ Lset (⟪ δI i ⟫↪ m) ⟫ ↪ ⟪ δI i ⟫

step-fn : (i : InfStage) → Ih i → ⟪ Lset (δI i) ⟫ → ⟪ δI i ⟫
step-fn i ih =
  fst (SC.limit-step (δI i) (δ∈sucI i) (oδI i) (infδI i) ih)

--      The domain and the codomain as L-elements.
dom : (i : InfStage) → S
dom i = LsetS (δI i) (oδI i)

cod : (i : InfStage) → S
cod i = δI i , isL-ord (δI i) (oδI i)

--      The graph's subject: the recursion's function part, read on the
--      members of the domain through their presentations, lifted to an
--      L-element of the stage.  `fst (dom i)` and `Lset (δI i)` are
--      the same term.
val : (i : InfStage) (ih : Ih i) (x : S) (m : ⟨ fst x ∈ fst (dom i) ⟩) → S
val i ih x m = up (cod i) (step-fn i ih (fiber (fst (dom i)) m .fst))

-- 0.4  THE STATEMENT.  THE OBLIGATION `rec-graph-at-infinite` IS A TERM
--      OF THIS TYPE AT AN INDEX AND A BRANCH.  This slice states it and
--      inhabits nothing: the main probe either builds the term under
--      this very type or states a stop against it, so the stated
--      statement and the measured one cannot drift.
RecGraphInf : (i : InfStage) (ih : Ih i) → Type (ℓ-suc ℓ)
RecGraphInf i ih =
  Σ[ ψ ∈ Formula S 2 ]
    ( ((x y : S) (m : ⟨ fst x ∈ fst (dom i) ⟩)
       → fst y ≡ fst (val i ih x m) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
    × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (m : ⟨ fst x ∈ fst (dom i) ⟩)
       → fst y ≡ fst (val i ih x m)) )
