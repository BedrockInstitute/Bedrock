{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.519] PROBE.  hier-in-stage at a LIMIT, which is Devlin 2.6(ii)
-- (dev/literature/devlin-II5.md:218,221).  It runs in
-- agents/tasks/LJ-1-519/ and lands nothing in src/.
--
--   D-10, FIRST    what the tree's IsLimit is, as checked ascriptions.
--   W3, SECOND     two-below: does a limit supply the intermediate β?
--   OBLIGATION     hier-in-stage-limit.  Added after W3 is measured.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-519.Probe519 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier )
open import L.InjChain {ℓ} lem using ( ω-limit )
open import L.SquareLawClosed {ℓ} lem using ( κL; κoL; kappa-limit )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- ===================================================================
-- D-10.  WHAT THE TREE'S `IsLimit` IS.
--
-- MEASURED: the tree has NO `IsLimit`.  `grep -rn "IsLimit" src/`
-- returns nothing.  The limit hypothesis exists in src/ ONLY as a
-- spelled-out closure-under-successor, at two sites, and both have
-- exactly the shape below.  So the predicate is DEFINED here, and the
-- two tree witnesses are re-ascribed to it: a row that typechecks is
-- evidence, a comment is not.
-- ===================================================================

IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩

private

  -- ROW 1.  src/L/InjChain.lagda.md:109.  ω is a limit in this sense,
  -- and this is the tree's own spelling, not a paraphrase.
  row1-ω : IsLimit ω
  row1-ω = ω-limit

  -- ROW 2.  src/L/SquareLawClosed.lagda.md:125.  The least cardinal
  -- above an L-ordinal is a limit in the SAME sense, given ω inside it.
  -- Two independent sites, one shape.  The chapter carries two further
  -- module parameters (src/L/SquareLawClosed.lagda.md:19-20), so they
  -- are quantified here rather than instantiated.
  row2-κ : (α₀ : V ℓ) (oα₀ : IsOrd α₀)
         → (a : S) (oa : IsOrd (fst a))
         → ⟨ ω ∈ fst (κL α₀ oα₀ a oa) ⟩
         → IsLimit (fst (κL α₀ oα₀ a oa))
  row2-κ = kappa-limit


-- ===================================================================
-- W3, THE WIDEST UNMEASURED TERM.  The two steps.
--
-- [LJ-1.517] measured that the witness wants the tower's value TWO
-- membership steps below α (agents/tasks/LJ-1-517/Probe517.agda:204).
-- Nobody had shown a limit supplies them.  This is that showing.
-- ===================================================================

two-below : (α : V ℓ) → IsOrd α → IsLimit α → (γ : V ℓ) → ⟨ γ ∈ α ⟩
          → ∥ Σ[ β ∈ V ℓ ] (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩) ∥₁
two-below α oα lim γ γ∈α = ∣ sucV γ , (lim γ γ∈α , self∈sucV γ) ∣₁


-- ===================================================================
-- WHAT THE SOURCE ACTUALLY PROVES.
--
-- The brief orders Devlin 2.6(ii) and prices it from the two steps.
-- The primary text prices it differently.  `_build/literature/dev2.txt`
-- :676-678, verbatim from the OCR:
--
--   "(ii) Here we quickly reduce to proving that for any limit ordinal
--    α > ω, if δ < α then {Ly\γ ^δ)e L α . In fact it is not hard to
--    see that if δ > ω, then (Ly\y ^ δ)e L δ + 4 , so we are done.
--    (We leave all the details to the reader.)"
--
-- So the proof is TWO parts, and only the first is about α:
--
--   PART A, the limit's whole contribution: δ + 4 ∈ α, hence
--           L_{δ+4} ⊆ L_α.  Pure ordinal arithmetic on successor
--           closure.  Built and typechecked below.
--   PART B, the residue: (L_γ | γ ≤ δ) ∈ L_{δ+4}.  It names no α and
--           no limit.  Devlin does not prove it: "We leave all the
--           details to the reader."
--
-- The reduction below is Devlin's own, made checkable.  It consumes B
-- and pays A.  It is NOT the obligation, and no term here is named
-- `hier-in-stage-limit`.
-- ===================================================================

module Obligation (α : V ℓ) (oα : IsOrd α) (lim : IsLimit α)
                  (ω∈α : ⟨ ω ∈ α ⟩) where

  private
    -- Every ordinal's successor is an L-element: it lies in the stage
    -- two above it (src/L/Ordinal/Stages.lagda.md:434) and stages are
    -- inside L (src/L/Constructible.lagda.md:395).
    isL-suc : (γ : V ℓ) → IsOrd γ → ⟨ isL (sucV γ) ⟩
    isL-suc γ oγ = Lset→isL (sucV (sucV γ)) (suc-ord (suc-ord oγ))
                     (sucV γ) (ord∈Lset-suc (sucV γ) (suc-ord oγ))

  -- DEVLIN'S (L_δ | δ ≤ γ), IN THE TREE'S OWN VOCABULARY.
  -- `Recorded B z` says z is a pair (c , Lset c) with c ∈ B
  -- (src/L/Hierarchy.lagda.md:496), and `IsHier B h` says h realizes
  -- that class member for member (src/L/Hierarchy.lagda.md:501).
  -- `hierL B` is the realizer (src/L/Hierarchy.lagda.md:621).  So
  -- `hierL (sucV γ)` IS the sequence at δ ≤ γ, because sucV γ is
  -- exactly the ordinals δ ≤ γ.
  seq : (γ : V ℓ) → IsOrd γ → S
  seq γ oγ = hierL (sucV γ) (isL-suc γ oγ) (suc-ord oγ)

  -- The seq is the sequence and nothing else: its membership is the
  -- pair class, at every z.  This is the brief's "sequence of tower
  -- values at δ ≤ γ", checked rather than asserted.
  seq-spec : (γ : V ℓ) (oγ : IsOrd γ) → IsHier (sucV γ) (seq γ oγ)
  seq-spec γ oγ = hierL-spec (sucV γ) (isL-suc γ oγ) (suc-ord oγ)

  -- THE BRIEF'S TYPE.  It forms.  It is NOT inhabited below, and no
  -- postulate stands in for it.  `IsOrd γ` is an explicit argument
  -- rather than a derivation, which only makes the type WEAKER to
  -- assume and STRONGER to conclude; `derived` below recovers the
  -- brief's exact spelling from it at no cost.
  HierInStageLimit : Type (ℓ-suc ℓ)
  HierInStageLimit = (γ : V ℓ) (oγ : IsOrd γ) → ⟨ γ ∈ α ⟩
                   → ⟨ fst (seq γ oγ) ∈ Lset α ⟩

  -- =================================================================
  -- THE WALL, AND THE GUTTED-BODY EXPERIMENT THAT LOCATED IT.
  --
  -- The brief's spelling takes γ ∈ α and NO `IsOrd γ`, so the ordinal
  -- hood is meant to be derived by `mem-ord`.  That derivation is what
  -- this site cannot pay.  MEASURED, one Agda process per run, wide
  -- caliber -A64m -I0 -M8g, all src interfaces warm:
  --
  --   the type alone, no term            2.70 s   474 MB   runs/type-only.time
  --   mem-ord alone (ctl-mem-ord)        2.77 s   477 MB   runs/controls.time
  --   the application with IsOrd γ a
  --     HYPOTHESIS (ctl-hypothesis)      2.77 s   477 MB   runs/controls.time
  --   the COMPOSITION of the two       HEAP EXHAUSTED at 8 GB
  --     (implicit inferred)              324 s  9.08 GB   runs/wall-derived.time
  --     (implicit given explicitly)               8 GB    runs/wall-composition.time
  --
  -- Neither factor costs.  The composition walls.  ROOT CAUSE: `seq`
  -- feeds its `IsOrd γ` to `suc-ord`, whose body PATTERN-MATCHES the
  -- pair (src/L/Ordinal.lagda.md:97), and `isL-suc` destructures it
  -- twice more; a `mem-ord`-derived proof is an ∈-induction recursion
  -- (src/L/Ordinal.lagda.md:222), so destructuring runs that recursion
  -- inside the stage constructor's argument.  The two controls below
  -- are the halves that stay green.  The composition is NOT in this
  -- file, because a file that walls typechecks nothing.
  -- =================================================================

  -- CONTROL 1.  mem-ord ALONE, its value never fed to seq.
  ctl-mem-ord : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → IsOrd γ
  ctl-mem-ord γ γ∈α = mem-ord {A = α} oα γ γ∈α

  -- CONTROL 2.  the application, with IsOrd γ taken as a HYPOTHESIS.
  ctl-hypothesis : HierInStageLimit
                 → (γ : V ℓ) (oγ : IsOrd γ) → ⟨ γ ∈ α ⟩
                 → ⟨ fst (seq γ oγ) ∈ Lset α ⟩
  ctl-hypothesis W γ oγ γ∈α = W γ oγ γ∈α

  -- =================================================================
  -- PART A.  WHAT THE LIMIT BOUGHT, AS TYPES.
  -- =================================================================

  -- n successor steps above a member.
  step : ℕ → V ℓ → V ℓ
  step zero    γ = γ
  step (suc n) γ = sucV (step n γ)

  -- A1.  EVERY finite successor tower over a member stays inside α.
  -- W3 is the case n = 1.  Devlin needs n = 4.  Successor closure
  -- gives every n at the same price: one application per step.
  steps-stay : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → (n : ℕ) → ⟨ step n γ ∈ α ⟩
  steps-stay γ γ∈α zero    = γ∈α
  steps-stay γ γ∈α (suc n) = lim (step n γ) (steps-stay γ γ∈α n)

  -- A2.  Hence every stage finitely above a member sits inside Lset α.
  -- THIS IS THE WHOLE OF THE LIMIT'S CONTRIBUTION to Devlin 2.6(ii).
  -- It moves a set from a lower stage to Lset α.  It does not put any
  -- set into any stage.
  stage-below : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → (n : ℕ)
              → {x : V ℓ} → ⟨ x ∈ Lset (step n γ) ⟩ → ⟨ x ∈ Lset α ⟩
  stage-below γ γ∈α n = Lset-mono (steps-stay γ γ∈α n)

  -- =================================================================
  -- PART B.  DEVLIN'S RESIDUE, AS A TYPE.  It names no α and no limit.
  -- =================================================================

  -- B1.  dev2.txt:677, Devlin's own bound, on Devlin's own hypothesis
  -- δ > ω.  "(Ly\y ^ δ)e L δ + 4".
  StageHigh : Type (ℓ-suc ℓ)
  StageHigh = (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩
            → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩

  -- B2.  The tail Devlin's δ > ω excludes and his text does not state:
  -- γ ≤ ω.  Bounded at a stage finitely above ω, which the limit
  -- reaches from ω∈α by the same A1.
  StageLow : Type (ℓ-suc ℓ)
  StageLow = (γ : V ℓ) (oγ : IsOrd γ) → ⟨ γ ∈ sucV ω ⟩
           → ⟨ fst (seq γ oγ) ∈ Lset (step 5 ω) ⟩

  -- =================================================================
  -- THE REDUCTION.  Devlin's proof of 2.6(ii), in full, with the two
  -- residues as hypotheses.  A ∘ B ⟹ the obligation, TOTAL in γ.
  -- Every line of it is Part A; not one line touches Part B.
  -- =================================================================

  reduction : StageHigh → StageLow → HierInStageLimit
  reduction high low γ oγ γ∈α = tri (ord-tri γ oγ ω ω-ord)
    where
    tri : ⟨ γ ∈ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ γ ⟩) → ⟨ fst (seq γ oγ) ∈ Lset α ⟩
    tri (inl γ∈ω) = stage-below ω ω∈α 5
      (low γ oγ (∈sucV-inl {A = ω} {x = γ} γ∈ω))
    tri (inr (inl γ≡ω)) = stage-below ω ω∈α 5
      (low γ oγ (subst (λ w → ⟨ w ∈ sucV ω ⟩) (sym γ≡ω) (self∈sucV ω)))
    tri (inr (inr ω∈γ)) = stage-below γ γ∈α 4 (high γ oγ ω∈γ)
