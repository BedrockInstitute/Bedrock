{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.592]  ANY CODED INJECTION OF `Lset α` INTO `α`.
--
-- VERDICT: NO-GO on `stage-counted`.
-- `agents/tasks/LJ-1-592/review-of-stage-counted.md` states it.  THE
-- OBLIGATION IS NOT IN THIS FILE and no weaker term is offered as one.
-- There is no hole and no postulate, `--safe` is on, so every reduction
-- below is a measurement and not a claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-592/runs/W3.agda.  IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3-1.out`, GREEN, 1.57 s).  It is IMPORTED
-- below and NOT restated, so the interface cannot drift.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA.  What `PT.rec` lets me
--               assume, and what the target's own type demands back.
--   Section 1.  THE TWO `[LJ-1.587]` PRODUCERS, TRIED.  Each is applied
--               at this pair and each states its own missing input.
--   Section 2.  WHAT ROUTE 1 REALLY BUYS.  The propositional motive
--               DISSOLVES `SqCollect`, and the residue is one CODED
--               INDUCTIVE STEP.  This section is `sq`-free by module
--               structure and not by assertion.
--   Section 3.  WHERE IT STOPS.  `module WithSq`, and the wall named.
--   Section 4.  THE PRODUCER SWEEP (C-42).
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-592.Probe592 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.StageBound {ℓ} lem using ( SqFam; SqCollect )
open import L.GCH {ℓ} lem using ( InjL )
open import L.CantorBernstein {ℓ} lem using ( readL; mutual-inj→bijection )
import L.SquareLawClosed
import L.StageCardinal
import LJ-1-561.Probe561
import LJ-1-587.Probe587
import LJ-1-592.runs.W3

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- W3, IMPORTED.  `Target`, `isPropTarget`, `untrunc-free`, `ordS` and
-- `isL-ord` all come from the slice that was checked alone.
open module W3 = LJ-1-592.runs.W3 {ℓ} lem
  using ( isL-ord; ordS; Target; isPropTarget; untrunc-free )

module P587 = LJ-1-587.Probe587 {ℓ} lem
module SLC = L.SquareLawClosed {ℓ} lem α₀ oα₀


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA.
--
--   The brief calls this "the freedom" and orders it stated at
--   `file:line`.  Two facts, and they point in OPPOSITE directions.
-- ===================================================================

-- 0.1  WHAT `PT.rec` LETS ME ASSUME.  ANYTHING TRUNCATED, at no cost.
--      `untrunc-free` (runs/W3.agda:70-72) is the whole permission: for
--      EVERY type `A`, a map `A → Target` gives `∥ A ∥₁ → Target`.  The
--      recursion is legal because `isPropTarget` (runs/W3.agda:64-65) is
--      inhabited, and that is `squash₁` and nothing more: `InjL a b` is
--      `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (src/L/GCH.lagda.md:37-38), so
--      the truncation is OUTSIDE the Σ.
--
--      NOTE WHAT THIS DOES NOT USE.  It does not use `isPropInjCode`
--      (agents/tasks/LJ-1-576/Probe576.agda:77-84).  The brief offers
--      that as the measured basis; it is a true fact about a DIFFERENT
--      type, and the permission does not rest on it.  The line below
--      records the two are not the same claim: `InjCode` propositional
--      is about the Σ's body, `Target` propositional is about the ∥_∥₁.
free-at-any-hypothesis :
    {ℓ' : Level} {A : Type ℓ'} (α : V ℓ) (oα : IsOrd α)
  → (A → Target α oα) → ∥ A ∥₁ → Target α oα
free-at-any-hypothesis = untrunc-free

-- 0.2  AND WHAT THE TARGET DEMANDS BACK.  `readL`
--      (src/L/CantorBernstein.lagda.md:33-38) reads any `InjCode`
--      witness back as an honest ambient injection.  So the target is
--      AT LEAST as strong as the ambient statement, at the SAME pair,
--      with no side condition anywhere.
target→ambient∥ :
    (α : V ℓ) (oα : IsOrd α)
  → Target α oα → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
target→ambient∥ α oα = PT.map (readL (LsetS α oα) (ordS α oα))

-- 0.3  AND THAT IS THE D-10 PRICE OF THE TYPE AS WRITTEN.
--      `[LJ-1.584]`'s `Reopener` (agents/tasks/LJ-1-584/Probe584.agda:250-251)
--      takes `IsOrd α` and NOTHING ELSE, so 0.2 holds at EVERY ordinal,
--      finite ones included.  The tree's only ambient injection at this
--      pair is `stage-card-upper` and it carries two side conditions,
--      `α ∈ˢ sucV α₀` and `α ∉ ω` (src/L/StageCardinal.lagda.md:564-565).
--
--      SO THE OBLIGATION IS STRICTLY STRONGER THAN WHAT `L.StageCardinal`
--      PROVES, AND THE EXCESS HAS NOTHING TO DO WITH CODING.  This is
--      not new: `[LJ-1.585]`'s `side-conditions-are-false`
--      (agents/tasks/LJ-1-585/Probe585.agda:219-227) refutes the SUPPLY
--      of those two conditions at δ := 0.  **I DO NOT CLAIM THE TARGET
--      IS FALSE.**  `[LJ-1.533]`'s review says in its own words that it
--      "did not prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named
--      finite δ" (agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55),
--      and this file does not prove it either.  The row below states
--      only the implication, which is what is measured.
Restricted : Type (ℓ-suc ℓ)
Restricted =
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Target δ oδ

full→restricted : ((δ : V ℓ) (oδ : IsOrd δ) → Target δ oδ) → Restricted
full→restricted f δ oδ _ _ = f δ oδ


-- ===================================================================
-- SECTION 1.  THE TWO `[LJ-1.587]` PRODUCERS, TRIED.
--
--   The brief calls them "the obvious material" and orders them tried
--   first, with an answer on whether they suffice.  Both are IMPORTED
--   and neither is rebuilt.  Each application below typechecks, so what
--   is measured is exactly the input each one still wants.
-- ===================================================================

-- 1.0  The ordinal sits inside its own stage.  This is
--      `src/L/StageCardinal.lagda.md:193-195` repeated, and it is
--      repeated rather than imported because the chapter that carries it
--      is parameterised by `sq` while this line is not.  Section 3.0
--      checks the repetition against the chapter's own term.
α⊆Lset : (α : V ℓ) (oα : IsOrd α) (β : V ℓ) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset α ⟩
α⊆Lset α oα β β∈α = Lset-cumul β α (mem-ord {A = α} oα β β∈α) oα β∈α
  (ord∈Lset-suc β (mem-ord {A = α} oα β β∈α))

-- 1.1  `injL-from-subset` (agents/tasks/LJ-1-587/Probe587.agda:255-257),
--      APPLIED AT THIS PAIR.  It typechecks, and its hypothesis is
--      `Lset α ⊆ α`.  THAT IS THE INPUT IT STILL WANTS, and nothing in
--      this file offers it.
subset-route :
    (α : V ℓ) (oα : IsOrd α)
  → ((z : V ℓ) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ α ⟩) → Target α oα
subset-route α oα = P587.injL-from-subset (LsetS α oα) (ordS α oα)

-- 1.2  AND THE TREE HAS THE OTHER INCLUSION, SO THE SAME PRODUCER PAYS
--      THE CONVERSE OUTRIGHT.  This term is GREEN with no hypothesis at
--      all: IN L, EVERY ORDINAL INJECTS INTO ITS OWN STAGE.
--
--      `[LJ-1.585]`'s `row1→gap` (agents/tasks/LJ-1-585/Probe585.agda:267-278)
--      reaches the same object through `InclGraph` directly.  The line
--      below is that object through the `[LJ-1.587]` producer the brief
--      names, so the two routes are on the record as agreeing.
ord-into-stage : (α : V ℓ) (oα : IsOrd α) → InjL (ordS α oα) (LsetS α oα)
ord-into-stage α oα = P587.injL-from-subset (ordS α oα) (LsetS α oα) (α⊆Lset α oα)

-- 1.3  SO THE TARGET IS WORTH A BIJECTION AND NOT MERELY AN INJECTION.
--      `mutual-inj→bijection` (src/L/CantorBernstein.lagda.md:51-55) is
--      the trophy's own Cantor-Schroeder-Bernstein, and 1.2 supplies its
--      second hypothesis for free.  THIS IS THE PRICE OF THE TARGET
--      STATED HONESTLY: whoever pays `Target` pays `∣Lset α∣ = ∣α∣`.
target→bijection :
    (α : V ℓ) (oα : IsOrd α) → Target α oα
  → ∥ Σ[ h ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
       (((x y : ⟪ Lset α ⟫) → h x ≡ h y → x ≡ y)
      × ((y : ⟪ α ⟫) → ∥ Σ[ x ∈ ⟪ Lset α ⟫ ] (h x ≡ y) ∥₁)) ∥₁
target→bijection α oα t =
  mutual-inj→bijection (LsetS α oα) (ordS α oα) t (ord-into-stage α oα)

-- 1.4  `injL-compose` (agents/tasks/LJ-1-587/Probe587.agda:259-261),
--      APPLIED AT THIS PAIR.  It typechecks, and it wants a MIDDLE `b`
--      together with BOTH legs.  The left leg is the target's own shape
--      with `b` in place of `α`, so the producer moves the problem and
--      does not reduce it unless some named `b` carries both.  NO SUCH
--      `b` IS OFFERED HERE.
compose-route :
    (α : V ℓ) (oα : IsOrd α) (b : S)
  → InjL (LsetS α oα) b → InjL b (ordS α oα) → Target α oα
compose-route α oα b = P587.injL-compose (LsetS α oα) (ordS α oα) b

-- 1.5  AND THE ONE MIDDLE THE TREE HANDS OVER FOR FREE IS THE WRONG WAY
--      ROUND.  1.2 gives `InjL (ordS α) (LsetS α)`, which is
--      `compose-route`'s legs with `α` and `Lset α` EXCHANGED.  The line
--      below is that reading, and it concludes at the CONVERSE target.
converse-composes :
    (α : V ℓ) (oα : IsOrd α) (b : S)
  → InjL (ordS α oα) b → InjL b (LsetS α oα)
  → InjL (ordS α oα) (LsetS α oα)
converse-composes α oα b = P587.injL-compose (ordS α oα) (LsetS α oα) b


-- ===================================================================
-- SECTION 2.  WHAT ROUTE 1 REALLY BUYS.
--
--   THIS SECTION IS `sq`-FREE BY MODULE STRUCTURE.  The top-level
--   module of this file takes `lem`, `α₀` and `oα₀` and NO square-law
--   family, unlike every predecessor at this site
--   (agents/tasks/LJ-1-561/Probe561.agda:44-49,
--   agents/tasks/LJ-1-568/Probe568.agda:45,
--   agents/tasks/LJ-1-584/Probe584.agda:38-43).  So a term here cannot
--   quietly consume the family, and section 3 is where the family
--   enters.
--
--   THE FINDING.  The old motive is `⟪ Lset α ⟫ ↪ ⟪ α ⟫`
--   (src/L/StageCardinal.lagda.md:564-565), which is NOT a proposition,
--   so its `∈-induction` needs the square law as DATA at every
--   sub-stage: that is `SqFam`, and the tree reaches `SqFam` only
--   through `SqCollect`, which `src/L/StageBound.lagda.md:42` marks
--   "Not inhabited".  THE TARGET IS A PROPOSITION, SO THAT COLLECTION
--   IS NOT NEEDED: the induction spends `sq-trunc-closed` POINTWISE.
-- ===================================================================

-- 2.1  WHAT `SqCollect` IS, pinned by the elaborator so the sentence
--      above rests on the type and not on a reading of the prose.
sqcollect-is-a-collection :
    (α : V ℓ) → SqCollect α
      ≡ ( ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
        → ∥ SqFam α ∥₁ )
sqcollect-is-a-collection α = refl

-- 2.2  AND THE POINTWISE TRUNCATION SPENDS AT THE TARGET WITH NO
--      COLLECTION AT ALL.  `sq-trunc-closed`
--      (src/L/SquareLawClosed.lagda.md:325-328) is the tree's own
--      producer and it is TRUNCATED AND POINTWISE, which is exactly
--      what `untrunc-free` consumes.
sq-trunc-spends :
    (α : V ℓ) (oα : IsOrd α) → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (sq α → Target α oα) → Target α oα
sq-trunc-spends α oα α∈ infα f =
  untrunc-free α oα f (SLC.sq-trunc-closed α α∈ infα)

-- 2.3  THE MOTIVE, AND IT IS A PROPOSITION.  This is the one line that
--      the old induction cannot write.
Motive : V ℓ → Type (ℓ-suc ℓ)
Motive δ =
  (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Target δ oδ

isPropMotive : (δ : V ℓ) → isProp (Motive δ)
isPropMotive δ = isPropΠ λ oδ → isPropΠ λ _ → isPropΠ λ _ → isPropTarget δ oδ

-- 2.4  THE RESIDUE, NAMED.  ONE CODED INDUCTIVE STEP: the square law at
--      δ as DATA (which 2.2 supplies), the induction hypothesis ALREADY
--      CODED at every member of δ, and the coded conclusion at δ.
CodedStep : Type (ℓ-suc ℓ)
CodedStep =
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → sq δ
  → ((β : V ℓ) → ⟨ β ∈ˢ δ ⟩ → Motive β)
  → Target δ oδ

-- 2.5  AND IT SUFFICES.  THIS TERM IS THE WHOLE OF WHAT ROUTE 1 EARNS,
--      AND IT IS GREEN.  `∈-induction` (src/V/Hierarchy.lagda.md:177-180)
--      over the propositional motive, spending `sq-trunc-closed` at each
--      stage through 2.2.  NO `SqFam`, NO `SqCollect`, NO `sq` module
--      parameter appears in it or in anything it calls.
coded-step→restricted : CodedStep → Restricted
coded-step→restricted cs δ oδ = ∈-induction step δ oδ
  where
  step : (γ : V ℓ) → ((β : V ℓ) → ⟨ β ∈ˢ γ ⟩ → Motive β) → Motive γ
  step γ ih oγ γ∈ infγ = sq-trunc-spends γ oγ γ∈ infγ (λ s → cs γ oγ γ∈ infγ s ih)

-- 2.6  AND WHAT THE INDUCTION HYPOTHESIS HANDS THE STEP, AMBIENTLY.
--      ONE TRUNCATION PER SUB-STAGE, AND NOT A FAMILY.  By 0.2 each
--      coded hypothesis reads back as `∥ ⟪ Lset β ⟫ ↪ ⟪ β ⟫ ∥₁`, and
--      the ambient injection type is NOT a proposition, so these do not
--      assemble into the family `limit-step` consumes
--      (src/L/StageCardinal.lagda.md:281 takes `ih` as data).  THE
--      COLLECTION 2.5 REMOVED AT THE SQUARE LAW REAPPEARS HERE, ONE
--      LEVEL DOWN, IF THE STEP IS BUILT AMBIENTLY.
ih→ambient∥ :
    (δ : V ℓ) → ((β : V ℓ) → ⟨ β ∈ˢ δ ⟩ → Motive β)
  → (β : V ℓ) → ⟨ β ∈ˢ δ ⟩ → (oβ : IsOrd β) → ⟨ β ∈ˢ sucV α₀ ⟩
  → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ ⟪ Lset β ⟫ ↪ ⟪ β ⟫ ∥₁
ih→ambient∥ δ ih β β∈δ oβ β∈ infβ = target→ambient∥ β oβ (ih β β∈δ oβ β∈ infβ)


-- ===================================================================
-- SECTION 3.  WHERE IT STOPS.
--
--   THE SQUARE-LAW FAMILY ENTERS HERE AND NOWHERE ABOVE.  Everything in
--   this module is under an explicit parameter, so nothing in sections
--   0 to 2 can have used it.
--
--   WHAT THIS SECTION MEASURES.  Give route 1 the family outright, as
--   DATA, which is strictly more than `sq-trunc-closed` supplies.  The
--   target is STILL not reached, and the term that is missing is not a
--   truncation.  It is `[LJ-1.561]`'s `W`.
-- ===================================================================

module WithSq
  (sqf : (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
       → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
           ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sqf
  module P561 = LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sqf

  -- 3.0  NO DRIFT.  The parameter IS the consumer's family
  --      (src/L/StageBound.lagda.md:36-40), and 1.0's repeated
  --      inclusion IS the chapter's own line
  --      (src/L/StageCardinal.lagda.md:193-195).  Both by the
  --      elaborator, not by inspection.
  family-is-SqFam : SqFam α₀
  family-is-SqFam = sqf

  incl-is-the-chapters : (α : V ℓ) (oα : IsOrd α)
                       → α⊆Lset α oα ≡ SC.Lower.α⊆Lset α oα
  incl-is-the-chapters α oα = refl

  -- 3.1  WHAT THE FAMILY BUYS, AT FULL STRENGTH.  An AMBIENT injection,
  --      and `stage-card-upper`'s own two side conditions come with it
  --      (src/L/StageCardinal.lagda.md:564-565).
  sqfam→ambient :
      (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
  sqfam→ambient = SC.Upper.stage-card-upper

  -- 3.2  AND THE STEP FROM THERE TO THE TARGET IS `W`, AT AN ARBITRARY
  --      PAIR.  `w→code` (agents/tasks/LJ-1-561/Probe561.agda:287) is IMPORTED
  --      and not rebuilt; it is the second component of `one-wall`
  --      (Probe561.agda:467-476).  `W` (Probe561.agda:160-163) is "the graph of every
  --      ambient injection between L-elements is in L", which is
  --      `[LJ-1.554]`'s missing input and `[LJ-1.533]`'s wall.
  ambient→target : P561.W → (a b : S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b
  ambient→target = P561.w→code

  -- 3.3  SO `W` ALREADY PAYS THE RESTRICTED ROW, AND IT DID SO IN
  --      `[LJ-1.561]`.  This line adds nothing mathematical: it checks
  --      that `[LJ-1.584]`'s `Reopener` and `[LJ-1.561]`'s `w→B9`
  --      (Probe561.agda:376-381) conclude at the SAME type, so the "reopener" the brief aims at
  --      is a type the tree has already priced.
  w→restricted : P561.W → Restricted
  w→restricted = P561.w→B9

  -- 3.4  AND THE UNTRUNCATION ADDS NOTHING TO IT.  Feed 3.1 through
  --      3.2 and the result is 3.3; feed `sq-trunc-closed` through 2.2
  --      instead and the SAME `W` is still the only way out of the
  --      ambient injection.  THE TWO ROUTES MEET AT `W`.
  trunc-route-meets-W :
      P561.W
    → (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    → Target δ oδ
  trunc-route-meets-W w δ oδ δ∈ infδ =
    ambient→target w (LsetS δ oδ) (ordS δ oδ) (sqfam→ambient δ oδ δ∈ infδ)

  -- 3.5  AND THE RESIDUE OF SECTION 2 IS PAID BY THE SAME `W`, WITH THE
  --      FAMILY.  So `CodedStep` is NOT a weaker demand than `W` on this
  --      route: what section 2 removed is the COLLECTION, not the CODE.
  w→coded-step : P561.W → CodedStep
  w→coded-step w δ oδ δ∈ infδ _ _ =
    ambient→target w (LsetS δ oδ) (ordS δ oδ) (sqfam→ambient δ oδ δ∈ infδ)


-- ===================================================================
-- SECTION 4.  THE C-42 SWEEP.  EVERY WAY THE TREE BUILDS AN `InjCode`.
--
--   C-42 orders the COUNT before the cure (dev/LESSONS.md:3752).  The
--   shape here is not a refutation's site: it is the brief's own
--   permission, "build ANY coded injection".  So the number that
--   settles the brief is HOW MANY WAYS THE TREE CAN BUILD ONE, and
--   this section is that count.
--
--   SIX files of `src/` name `InjCode`:
--     src/L/Cardinal.lagda.md        the definition (:223-228)
--     src/L/GCH.lagda.md             the truncation (:37-38)
--     src/FOL/Bernstein.lagda.md     a comment only (:106)
--     src/L/CantorBernstein.lagda.md a CONSUMER, `readL` (:33-38)
--     src/L/CodedShift.lagda.md      a producer (:40)
--     src/L/Absorption.lagda.md      the SAME producer (:614)
--   `[LJ-1.587]`'s `two-sites-one-term`
--   (agents/tasks/LJ-1-587/Probe587.agda:223-230) is the elaborator's
--   word that the last two are ONE term, by `refl`.
--
--   AND A GREP FOR THE NAME UNDERCOUNTS, which `[LJ-1.587]` section 4
--   already measured: `src/L/InjChain.lagda.md` carries two machines
--   that deliver the four conjuncts and never write the word.  Counting
--   those, THE TREE BUILDS A CODED INJECTION IN THREE WAYS AND NO MORE:
--
--     (a) ONE SEPARATION AT `inclFo D` (src/L/InjChain.lagda.md:480),
--         which describes the IDENTITY graph on `D`.  Its range
--         conjunct (:544-547) is where the subset witness is spent, so
--         this device NEEDS `D ⊆ C`.
--     (b) ONE SEPARATION AT `shiftFo D γ ω z`
--         (src/L/Absorption.lagda.md:413), the successor shift on an
--         ordinal.  Its pair is `(sucʟ γ , γ)`.
--     (c) COMPOSITION of two codes already held
--         (src/L/InjChain.lagda.md:314-446).
--
--   THERE IS NO FOURTH.  Every other `hasSeparationL` application in
--   `src/` carves something that is not an injection graph
--   (src/L/Axioms/Power.lagda.md:190, src/L/Choice/Before.lagda.md:232,
--   src/L/Choice/Table.lagda.md:785, src/L/Choice/Limit.lagda.md:608,
--   src/L/Coding/CodeSet.lagda.md:310, src/L/Coding/EnvSet.lagda.md:190),
--   and `src/L/Coding/Key.lagda.md:258` is a third `Carve` that names no
--   `InjCode`.
--
--   SO "ANY CODED INJECTION" IS NOT A FREE CHOICE.  A NEW coded
--   injection is A NEW `Formula S 1` PLUS A BOUND, separated.  That is
--   `[LJ-1.568]`'s `Def` (agents/tasks/LJ-1-568/Probe568.agda:189), and
--   `[LJ-1.584]` refuted it at the only injection this pair has.
-- ===================================================================

-- 4.1  (a) AND (c), AS TERMS, at an arbitrary pair.  IMPORTED from
--      `[LJ-1.587]`, not rebuilt.
producers-in-the-tree :
    ( ((D C : S) → ((z : V ℓ) → ⟨ z ∈ˢ fst D ⟩ → ⟨ z ∈ˢ fst C ⟩) → InjL D C)
    × ((a c b : S) → InjL a b → InjL b c → InjL a c) )
producers-in-the-tree = P587.injL-from-subset , P587.injL-compose

-- 4.2  AND THAT IS WHY SECTION 1 IS THE WHOLE OF WHAT THE BRIEF'S
--      "OBVIOUS MATERIAL" CAN SAY.  4.1 IS the material, and 1.1 and
--      1.4 are its two applications at this pair.  Neither closes,
--      because `Lset α` is not a subset of `α` and no middle is named.


-- ===================================================================
-- SECTION 5.  THE VERDICT.
--
--   NO TERM OF `Target` AT AN ARBITRARY ORDINAL IS OFFERED, AND NOTHING
--   ABOVE IS OFFERED AS ONE.  `coded-step→restricted` (2.5) carries
--   `CodedStep` to the left of its arrow.  `trunc-route-meets-W` and
--   `w→restricted` (3.4, 3.3) carry `W`.
--
--   WHAT ROUTE 1 WON, AND IT IS REAL.  The target is a proposition (W3),
--   so the induction that computes it may spend `sq-trunc-closed`
--   POINTWISE and never needs `SqCollect`, which the tree marks "Not
--   inhabited" (src/L/StageBound.lagda.md:42).  Section 2.5 is that
--   induction and it is green.
--
--   WHAT ROUTE 1 DID NOT WIN.  The residue `CodedStep` is a CODE, not a
--   truncation, and 3.5 shows `W` pays it.  The truncation was never the
--   obstruction: 0.2 reads the target back as an ambient injection, 3.1
--   builds the ambient injection from the family, and the arrow between
--   them in the missing direction is `W` and only `W`
--   (agents/tasks/LJ-1-561/Probe561.agda:160-163).
--
--   `agents/tasks/LJ-1-592/review-of-stage-counted.md` states the NO-GO.
-- ===================================================================
