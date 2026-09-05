{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.647] PROBE.  Step 2 of [LJ-1.462]'s four: the hull is closed
-- under Lset, from [LJ-1.646]'s keystone TAKEN AS A HYPOTHESIS.
-- It runs in agents/tasks/LJ-1-647/ and lands nothing in src/.
--
-- THE OBLIGATION IS `hull-closed-lset`, at the foot of this file.
--
-- WHAT THE BRIEF'S PREMISE 2 SAYS, AND WHY IT IS FALSE.  The premise
-- reads: "`hull-closed` is the hull's ONLY closure rule and it takes a
-- `Formula Code 1`, so any closure demand needs the condition NAMED in
-- the hull's language" (src/L/Hull.lagda.md:415).  `hull-closed` is not
-- the only rule.  THE HULL IS THE IMAGE OF `Code` UNDER `val`, by its own
-- definition: `Hull = sett Code (λ c → toSet (val c))`
-- (src/L/Hull.lagda.md:114-115).  So `inHull` is a CONSTRUCTOR-level rule
-- with no formula in it, `val-in-Hull c = inHull c`
-- (src/L/Hull.lagda.md:341-342), and the reader back is the IDENTITY,
-- `hull-member x x∈H = x∈H` (src/L/Hull.lagda.md:339).  Hull membership
-- IS "is the value of a code", definitionally.  `hull-mem-is-code` below
-- pins that with `refl`.
--
-- SO THE FORMULA IS NEEDED ONLY WHEN NO CODE IS IN HAND.  `hull-closed`
-- buys an EXISTENTIAL SEARCH: given a formula satisfied by something,
-- it finds a hull member satisfying it.  A hypothesis that PRODUCES the
-- code has already done the search.  [LJ-1.646] produces the code.  The
-- `Formula Code 1` the brief priced at 70 to 150 lines is ZERO lines.
--
-- WHAT [LJ-1.479] AND [LJ-1.481] LACKED.  Both went down the formula
-- route and both stopped at the same place: "`IsOrd` has no source at a
-- hull member" (lj-1.481-report.md:80, lj-1.479-report.md:85).  This
-- task does not FIND that source.  The brief HANDS it over, as the
-- added `IsOrd y`, and the keystone consumes it.  Two hypotheses moved,
-- not one.  See lj-1.647-report.md.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-647.Probe647 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )

open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE TELESCOPE.  [LJ-1.462]'s HullStage, Probe462.agda:78-88, MINUS
-- `module C = Collapse M`, which step 2's statement does not name.
-- `succλ` is unused here and is KEPT, because the consumer site
-- (levelIn, inside BoundedSubset's `module Condense`) carries it and
-- [LJ-1.649] must be able to lift these terms verbatim.
-- =====================================================================

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; val )

  -- ===================================================================
  -- THE STRUCTURAL FACT THE WHOLE TASK RESTS ON.  `refl`, so it is a
  -- DEFINITIONAL identity and not a proved one: to be in the hull is to
  -- be the value of a code.  Read off src/L/Hull.lagda.md:337-339,
  -- where the proof of `hull-member` is `x∈H` itself.
  -- ===================================================================

  hull-mem-is-code : (x : S)
                   → ⟨ x ∈ˢ M ⟩ ≡ ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
  hull-mem-is-code x = refl

  -- ===================================================================
  -- THE TWO KEYSTONE TYPES, TAKEN AS HYPOTHESES AND NEVER BUILT.
  -- Verbatim from [LJ-1.462], Probe462.agda:109-112 and :118-121.
  -- [LJ-1.646] is the task that builds `LsetCodeOrd`.
  -- ===================================================================

  LsetCode : Type (ℓ-suc ℓ)
  LsetCode =
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- The TRUNCATED keystone.  [LJ-1.646] may only be able to deliver
  -- existence, not a chosen `d`.  It does not matter, and that is
  -- MEASURED below rather than assumed: `hull-closed-op` is proved from
  -- THIS weaker hypothesis and the untruncated one is its corollary.
  LsetCodeOrd∥ : Type (ℓ-suc ℓ)
  LsetCodeOrd∥ =
    (c : Code) → IsOrd (fst (val c))
    → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c))) ∥₁

  -- ===================================================================
  -- W2 (DD4).  THE MATHEMATICS ONCE, AT A GENERIC OPERATION, AND FROM
  -- THE WEAKEST HYPOTHESIS.  This is the ONLY proof in the file; every
  -- other term below is an instance or a corollary of it.  Nothing in
  -- it mentions `Lset`, `IsOrd`, or any stage: the hull is closed under
  -- ANY operation `F` that a code map names, under ANY side condition
  -- `P` that code map demands, whether or not the code map chooses.
  -- [LJ-1.648] and [LJ-1.650] can take THIS term and supply their own
  -- `F`.
  --
  -- WHY THE SECOND TRUNCATION IS FREE.  The goal `⟨ F y ∈ˢ M ⟩` is a
  -- mere proposition, so `PT.rec` eliminates into it with no choice
  -- principle at all.  This is HoTT Book Lemma 3.9.1, unique choice,
  -- recorded at dev/literature/truncation-and-selection.md:92, which
  -- calls it "the only free case" at :95.  It is free HERE because the
  -- hull's membership is ITSELF a truncation (src/L/Hull.lagda.md:114-115).
  -- ===================================================================

  hull-closed-op∥ : (F : S → S) (P : S → Type (ℓ-suc ℓ))
                  → ((c : Code) → P (fst (val c))
                     → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ F (fst (val c))) ∥₁)
                  → (y : S) → ⟨ y ∈ˢ M ⟩ → P y → ⟨ F y ∈ˢ M ⟩
  hull-closed-op∥ F P code y y∈M py =
    PT.rec (snd (F y ∈ˢ M)) go (H.hull-member y y∈M)
    where
    go : Σ[ c ∈ Code ] (fst (val c) ≡ y) → ⟨ F y ∈ˢ M ⟩
    go (c , q) =
      PT.rec (snd (F y ∈ˢ M))
             (λ dq → subst (λ z → ⟨ z ∈ˢ M ⟩)
                           (snd dq ∙ cong F q)
                           (H.val-in-Hull (fst dq)))
             (code c (subst P (sym q) py))

  -- The chosen form, as a corollary and not a second proof.
  hull-closed-op : (F : S → S) (P : S → Type (ℓ-suc ℓ))
                 → ((c : Code) → P (fst (val c))
                    → Σ[ d ∈ Code ] (fst (val d) ≡ F (fst (val c))))
                 → (y : S) → ⟨ y ∈ˢ M ⟩ → P y → ⟨ F y ∈ˢ M ⟩
  hull-closed-op F P code =
    hull-closed-op∥ F P (λ c pc → ∣ code c pc ∣₁)

  -- ===================================================================
  -- THE OBLIGATION.  Step 2 of [LJ-1.462]'s four (Probe462.agda:136),
  -- plus the `IsOrd y` the brief adds because levelIn's own argument
  -- carries it.  CONDITIONAL on [LJ-1.646]: step 2 is REDUCED to the
  -- keystone here, and it is NOT proved outright.
  -- ===================================================================

  hull-closed-lset : LsetCodeOrd
                   → (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩
  hull-closed-lset lco = hull-closed-op Lset IsOrd lco

  -- THE SAME CONCLUSION FROM THE TRUNCATED KEYSTONE.  If [LJ-1.646]
  -- returns existence only, step 2 still closes and nothing is lost.
  hull-closed-lset∥ : LsetCodeOrd∥
                    → (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩
  hull-closed-lset∥ lco = hull-closed-op∥ Lset IsOrd lco

  -- ===================================================================
  -- WHAT THE ADDED `IsOrd y` COSTS, MEASURED.  If [LJ-1.646] lands the
  -- UN-ordinal keystone instead, the goal needs no `IsOrd` at all: this
  -- is [LJ-1.462]'s step 2 exactly as written, with nothing added.  So
  -- the brief's added hypothesis is load-bearing ONLY through the
  -- keystone's own side condition, and it is free at every consumer
  -- that already carries ordinality.
  -- ===================================================================

  HullClosedLset : Type (ℓ-suc ℓ)
  HullClosedLset = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

  hull-closed-lset-plain : LsetCode → HullClosedLset
  hull-closed-lset-plain lc y y∈M =
    hull-closed-op Lset (λ _ → Unit*) (λ c _ → lc c) y y∈M tt*

  -- And the ordinal keystone gives the un-ordinal statement back at any
  -- y whose ordinality the consumer supplies, which is the shape
  -- [LJ-1.649] will meet: levelIn takes `IsOrd δ`.
  hull-closed-lset-at-ord : LsetCodeOrd
                          → (y : S) → IsOrd y → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩
  hull-closed-lset-at-ord lco y ordy y∈M = hull-closed-lset lco y y∈M ordy

-- =====================================================================
-- THE OBLIGATION AT THE TOP LEVEL, WHICH IS WHERE THE WITNESS METER
-- READS IT.  `witness = Target.<dotted-name>` (scripts/pod/witness.py:278)
-- resolves against the probe module and not into a nested one, so the
-- brief's declared name lives here.  The telescope is `HullStage`'s,
-- passed explicitly.  Same shape as [LJ-1.642]'s `clause-i-at-ord`.
-- =====================================================================

hull-closed-lset : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → HullStage.LsetCodeOrd lam ordλ succλ X X⊆L ∅∈λ
  → (y : S) → ⟨ y ∈ˢ HullStage.M lam ordλ succλ X X⊆L ∅∈λ ⟩ → IsOrd y
  → ⟨ Lset y ∈ˢ HullStage.M lam ordλ succλ X X⊆L ∅∈λ ⟩
hull-closed-lset lam ordλ succλ X X⊆L ∅∈λ =
  HullStage.hull-closed-lset lam ordλ succλ X X⊆L ∅∈λ
