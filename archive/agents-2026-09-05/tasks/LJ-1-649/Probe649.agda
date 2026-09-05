{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.649] PROBE.  `levelIn`, ASSEMBLED from [LJ-1.462]'s four steps.
-- It runs in agents/tasks/LJ-1-649/ and lands nothing in src/.
--
-- THE OBLIGATION IS `levelin-from-steps`, at the foot of this file.
--
-- WHAT THE TASK MEASURES, IN ONE SENTENCE.  The four-step decomposition
-- COMPOSES, no fifth fact is needed for it, and STEP 3 IS NOT A CONJUNCT
-- OF THE ASSEMBLY AT ALL: it is a producer for steps 2 and 4.  What DOES
-- need a fifth fact is the assembly from the step 2 that [LJ-1.647]
-- actually delivered, and that fifth fact is named here as
-- `PiReflectsOrd`.
--
-- [LJ-1.477] PREDICTED both halves of this and could not test either:
-- "That composition uses steps 1, 2 and 4. It does not use step 3.
-- Step 3 is a producer for 2 and 4, not a conjunct of this join.
-- I do not claim `levelIn`. I do not claim this composition
-- typechecks."
-- (agents/tasks/LJ-1-477/lj-1.477-report.md:265-268).  This file is the
-- test.  The prediction is CONFIRMED, and `[LJ-1.477]`'s own sketch
-- typechecks unchanged (`levelin-477-sketch` below).
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-649.Probe649 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE TELESCOPE.  [LJ-1.462]'s HullStage, Probe462.agda:78-88, which is
-- src/L/BoundedSubset.lagda.md:903-914 verbatim.  Nothing below
-- `module Condense` (:916) is copied.  `module C = Collapse M` is KEPT
-- here, unlike [LJ-1.647]'s trim, because the conclusion names `C.πX`.
-- `succλ` is unused by every term in this file and is KEPT, because the
-- consumer site carries it and the consumer must lift these terms
-- verbatim.
-- =====================================================================

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  open H.T using ( Code; val )

  -- ===================================================================
  -- THE FOUR STEPS, VERBATIM FROM [LJ-1.462].  Step 1 is the only one
  -- inhabited, and it is inhabited THERE too (Probe462.agda:134).
  --   step 1          Probe462.agda:130-134
  --   HullClosedLset  Probe462.agda:136-138
  --   lset-code       Probe462.agda:109-111
  --   πCommuteLset    Probe462.agda:140-142
  -- ===================================================================

  Step1 : Type (ℓ-suc ℓ)
  Step1 = (z : S) → ⟨ z ∈ˢ C.πX ⟩
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

  step1 : Step1
  step1 = C.πX-member

  HullClosedLset : Type (ℓ-suc ℓ)
  HullClosedLset = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

  LsetCode : Type (ℓ-suc ℓ)
  LsetCode =
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  PiCommuteLset : Type (ℓ-suc ℓ)
  PiCommuteLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

  -- ===================================================================
  -- W2 (DD4).  THE MATHEMATICS ONCE, AT A GENERIC OPERATION, AND THIS
  -- IS THE ONLY PROOF IN THE FILE.  Every term below is an instance of
  -- it.  Nothing in it mentions `Lset`, `IsOrd`, or any stage: the
  -- collapse's RANGE is closed under any operation `F` that the hull is
  -- closed under and that the collapse commutes with, PROVIDED the
  -- range-side side condition `Q` reflects back to the hull-side side
  -- condition `P`.
  --
  -- THE THREE HYPOTHESES ARE EXACTLY [LJ-1.462]'s STEPS 2 AND 4 PLUS
  -- ONE NEW ONE, `reflect`, AND `reflect` IS FREE WHENEVER `P` IS
  -- TRIVIAL.  That is the whole finding of this task, stated at the
  -- generality where it is true.
  --
  -- WHY `C.πX-intro` IS NOT A FIFTH STEP.  It is DELIVERED, at
  -- src/V/Collapse.lagda.md:86-87, and it is the only fact about the
  -- range this proof uses beyond step 1.  [LJ-1.462] did not list it
  -- among the four because it is not an obligation: it is the range's
  -- own introduction rule.
  -- ===================================================================

  pix-closed-op : (F : S → S) (P Q : S → Type (ℓ-suc ℓ))
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → Q (C.π y) → P y)
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → P y → ⟨ F y ∈ˢ M ⟩)
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → P y → C.π (F y) ≡ F (C.π y))
                → (δ : S) → Q δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ F δ ∈ˢ C.πX ⟩
  pix-closed-op F P Q reflect closed commute δ qδ δ∈πX =
    PT.rec (snd (F δ ∈ˢ C.πX)) go (step1 δ δ∈πX)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ δ)) → ⟨ F δ ∈ˢ C.πX ⟩
    go (y , y∈M , e) =
      subst (λ z → ⟨ F z ∈ˢ C.πX ⟩) e
        (subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (commute y y∈M py)
          (C.πX-intro (F y) (closed y y∈M py)))
      where
      py : P y
      py = reflect y y∈M (subst Q (sym e) qδ)

  -- ===================================================================
  -- THE OBLIGATION.  The brief's three hypotheses, and the conclusion
  -- is `levelIn` VERBATIM from src/L/BoundedSubset.lagda.md:917.
  --
  -- `lc` IS BOUND AND NEVER USED.  That is not sloppiness: the brief
  -- names step 3 a hypothesis of the assembly, and the assembly's job
  -- is to say whether it is one.  It is not.  `levelin-from-two` below
  -- is the same term with step 3 DELETED, and it is the deletion test.
  -- ===================================================================

  levelin-from-steps : HullClosedLset → LsetCode → PiCommuteLset
                     → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-from-steps hcl lc pcl δ oδ =
    pix-closed-op Lset (λ _ → Unit*) (λ _ → Unit*)
      (λ _ _ _ → tt*) (λ y y∈M _ → hcl y y∈M) (λ y y∈M _ → pcl y y∈M)
      δ tt*

  -- THE DELETION TEST.  Step 3 gone, and `IsOrd δ` gone with it.  Same
  -- conclusion, and `levelin-from-steps` is now visibly a weakening of
  -- this: two hypotheses suffice, not three, and the consumer's own
  -- `IsOrd δ` is not spent either.
  levelin-from-two : HullClosedLset → PiCommuteLset
                   → (δ : S) → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-from-two hcl pcl δ =
    pix-closed-op Lset (λ _ → Unit*) (λ _ → Unit*)
      (λ _ _ _ → tt*) (λ y y∈M _ → hcl y y∈M) (λ y y∈M _ → pcl y y∈M)
      δ tt*

  -- And the obligation is that weakening, written as one.
  levelin-is-a-weakening : HullClosedLset → LsetCode → PiCommuteLset
                         → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩
                         → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-is-a-weakening hcl lc pcl δ oδ = levelin-from-two hcl pcl δ

  -- ===================================================================
  -- [LJ-1.477]'s SKETCH, TYPECHECKED UNCHANGED.  Written at
  -- agents/tasks/LJ-1-477/lj-1.477-report.md:257-263 and never run.
  -- Kept beside the generic route because it is the SECOND proof in
  -- this file and W2 forbids a second proof of the same fact without a
  -- reason.  THE REASON: it settles a claim about a specific written
  -- term, which the generic route cannot settle.
  -- ===================================================================

  levelin-477-sketch : HullClosedLset → PiCommuteLset
                     → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩
                     → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-477-sketch hcl pcl δ oδ δ∈πX =
    PT.rec (snd (Lset δ ∈ˢ C.πX)) go (C.πX-member δ δ∈πX)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ δ)) → ⟨ Lset δ ∈ˢ C.πX ⟩
    go (y , y∈M , e) =
      subst (λ z → ⟨ Lset z ∈ˢ C.πX ⟩) e
        (subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (pcl y y∈M)
          (C.πX-intro (Lset y) (hcl y y∈M)))

  -- ===================================================================
  -- THE OTHER HALF, AND IT IS WHERE THE FIFTH FACT LIVES.  [LJ-1.462]'s
  -- step 2 is NOT the step 2 that [LJ-1.647] delivered.  647's term is
  --
  --   hull-closed-lset : LsetCodeOrd
  --                    → (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩
  --
  -- (agents/tasks/LJ-1-647/Probe647.agda:165-167), with an `IsOrd y`
  -- that 647 added because [LJ-1.646]'s keystone is ordinal-conditioned
  -- (agents/tasks/LJ-1-462/Probe462.agda:118-121, `lset-code-ord`).
  -- 647's own note says the added hypothesis "is free at every consumer
  -- that already carries ordinality" (Probe647.agda:180-181).
  --
  -- IT IS NOT FREE HERE, AND THAT IS THIS TASK'S FINDING.  This
  -- consumer carries `IsOrd δ`, on the RANGE side.  Step 2 wants
  -- `IsOrd y` on the HULL side, at the preimage step 1 hands over.  The
  -- two are joined by nothing in the tree.
  -- ===================================================================

  -- [LJ-1.647]'s delivered step 2, as a hypothesis.
  HullClosedLsetOrd : Type (ℓ-suc ℓ)
  HullClosedLsetOrd = (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩

  -- THE FIFTH FACT.  Not one of [LJ-1.462]'s four, and not needed by
  -- the assembly from 462's own step 2.  Needed by the assembly from
  -- 647's.  The collapse REFLECTS ordinality along the hull.
  PiReflectsOrd : Type (ℓ-suc ℓ)
  PiReflectsOrd = (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd (C.π y) → IsOrd y

  -- The assembly from what 647 actually built.  GREEN, and it spends
  -- the consumer's `IsOrd δ`, which the 462-shaped route did not.
  levelin-from-647 : PiReflectsOrd → HullClosedLsetOrd → PiCommuteLset
                   → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-from-647 rfl hcl pcl =
    pix-closed-op Lset IsOrd IsOrd rfl hcl (λ y y∈M _ → pcl y y∈M)

  -- AND THE COMMUTE MAY BE ORDINAL-CONDITIONED TOO, AT NO EXTRA COST.
  -- [LJ-1.477] closed NO-GO on the unconditioned `πCommuteLset` and
  -- wrote "A non-ordinal `y ∈ M` whose ..." at
  -- agents/tasks/LJ-1-477/lj-1.477-report.md:188.  If step 4 only ever
  -- lands at ordinals, this route still closes and nothing changes.
  PiCommuteLsetOrd : Type (ℓ-suc ℓ)
  PiCommuteLsetOrd =
    (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → C.π (Lset y) ≡ Lset (C.π y)

  levelin-from-647-ord-commute :
      PiReflectsOrd → HullClosedLsetOrd → PiCommuteLsetOrd
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-from-647-ord-commute rfl hcl pcl =
    pix-closed-op Lset IsOrd IsOrd rfl hcl pcl

  -- WHAT THE FIFTH FACT IS WORTH, THE OTHER WAY ROUND.  If [LJ-1.646]
  -- lands the UN-ordinal keystone, 647's `hull-closed-lset-plain`
  -- (Probe647.agda:187-189) gives `HullClosedLset` and the fifth fact
  -- is not needed at all.  So `PiReflectsOrd` is the PRICE OF THE
  -- ORDINAL KEYSTONE at this consumer, and nothing else.
  no-fifth-if-keystone-is-plain : HullClosedLset → PiCommuteLset
                                → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩
                                → ⟨ Lset δ ∈ˢ C.πX ⟩
  no-fifth-if-keystone-is-plain hcl pcl δ oδ = levelin-from-two hcl pcl δ

-- =====================================================================
-- THE OBLIGATION AT THE TOP LEVEL, WHICH IS WHERE THE WITNESS METER
-- READS IT.  `witness = Target.<dotted-name>` (scripts/pod/witness.py:278)
-- resolves against the probe module and not into a nested one, so the
-- brief's declared name lives here.  Same shape as [LJ-1.647]'s
-- top-level `hull-closed-lset`.
-- =====================================================================

levelin-from-steps : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → HullStage.HullClosedLset lam ordλ succλ X X⊆L ∅∈λ
  → HullStage.LsetCode lam ordλ succλ X X⊆L ∅∈λ
  → HullStage.PiCommuteLset lam ordλ succλ X X⊆L ∅∈λ
  → (δ : S) → IsOrd δ
  → ⟨ δ ∈ˢ Collapse.πX (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩
  → ⟨ Lset δ ∈ˢ Collapse.πX (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩
levelin-from-steps lam ordλ succλ X X⊆L ∅∈λ =
  HullStage.levelin-from-steps lam ordλ succλ X X⊆L ∅∈λ
