{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.593]  THE CODED SQUARE LAW, AT THE SPELLING [LJ-1.589] DECIDED.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.
--
-- W3 IS `agents/tasks/LJ-1-593/runs/W3.agda`, written first and
-- typechecked alone (runs/w3-1.out:24, EXIT=0, 1.57 s).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-593.Probe593 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; numeral-mem; numeral-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.GCH {ℓ} lem using ( InjL )
import L.SquareLawClosed

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 1.  THE SPELLING, AND IT IS NOT MINE.
--
--   THE BRIEF NAMES THREE HYPOTHESES and says the spelling is
--   [LJ-1.589]'s.  Each is copied from its own site and not retyped
--   from memory:
--
--     `IsOrd (fst κ)`           src/L/GCH.lagda.md:61
--     `IsCardinalL κ`           src/L/GCH.lagda.md:63
--     `⟨ fst κ ∈ˢ ω ⟩ → ⊥`      src/L/GCH.lagda.md:64
--
--   [LJ-1.589] named the third `ClauseTrophy`
--   (agents/tasks/LJ-1-589/Probe589.agda:96-97) and measured it against
--   the two other spellings on the page.  THE TWO ADMISSIBLE ONES ARE
--   ITS SPELLING A AND ITS SPELLING C, and the one it REFUTED is its
--   spelling B, `⟨ ω ∈ fst κ ⟩` (Probe589.agda:161-162, refuted at ω).
--
--   I USED SPELLING A.  Section 1.2 says why in a term and not in a
--   sentence, and section 1.3 gives spelling C free, so the choice
--   costs the consumer nothing.
-- =====================================================================

-- SPELLING A, THE TROPHY'S.  src/L/GCH.lagda.md:64 letter for letter.
ClauseTrophy : S → Type (ℓ-suc ℓ)
ClauseTrophy κ = ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥

-- SPELLING C's TWO CONJUNCTS, src/L/CodedShift.lagda.md:38-39 letter
-- for letter.
ClauseCodedShift∉ : S → Type (ℓ-suc ℓ)
ClauseCodedShift∉ γ = ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥

ClauseCodedShiftNum : S → Type (ℓ-suc ℓ)
ClauseCodedShiftNum γ = (k : ℕ) → ⟨ (# k) ∈ fst γ ⟩

-- 1.1  A AND C's FIRST CONJUNCT ARE ONE TYPE.  Two identity functions,
-- as [LJ-1.589] section 2 measured them (Probe589.agda:127-131).  They
-- are rewritten here from `src/` rather than imported, so this file
-- pays no import for them.
trophy-is-cs∉ : (κ : S) → ClauseTrophy κ → ClauseCodedShift∉ κ
trophy-is-cs∉ κ x = x

cs∉-is-trophy : (κ : S) → ClauseCodedShift∉ κ → ClauseTrophy κ
cs∉-is-trophy κ x = x

-- 1.2  C's SECOND CONJUNCT IS FREE UNDER `IsOrd` AND A.  This is
-- [LJ-1.589]'s `numerals-from-trophy` (Probe589.agda:207-216), rebuilt
-- here at this file's own bindings, so the report's claim that the two
-- spellings are interderivable is a term of THIS file.
numerals-from-trophy :
    (γ : S) → IsOrd (fst γ) → ClauseTrophy γ → ClauseCodedShiftNum γ
numerals-from-trophy γ ordγ γ∉ω k =
  go (ord-tri (# k) (numeral-ord k) (fst γ) ordγ)
  where
  go : Tri (# k) (fst γ) → ⟨ (# k) ∈ fst γ ⟩
  go (inl #k∈γ)      = #k∈γ
  go (inr (inl e))   =
    Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (#∈ω k)))
  go (inr (inr γ∈#k)) =
    Empty.rec (γ∉ω (numeral-mem k (fst γ) γ∈#k))

-- 1.3  SO A STATEMENT AT SPELLING A PAYS THE SAME STATEMENT AT
-- SPELLING C, WITH NO EXTRA HYPOTHESIS.  `P` is any conclusion.
a-pays-c : (P : S → Type (ℓ-suc ℓ))
  → ((κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ → P κ)
  → ((κ : S) → IsOrd (fst κ) → IsCardinalL κ
     → ClauseCodedShift∉ κ → ClauseCodedShiftNum κ → P κ)
a-pays-c P f κ ordκ cardκ κ∉ω _ = f κ ordκ cardκ (cs∉-is-trophy κ κ∉ω)

c-pays-a : (P : S → Type (ℓ-suc ℓ))
  → ((κ : S) → IsOrd (fst κ) → IsCardinalL κ
     → ClauseCodedShift∉ κ → ClauseCodedShiftNum κ → P κ)
  → ((κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ → P κ)
c-pays-a P f κ ordκ cardκ κ∉ω =
  f κ ordκ cardκ (trophy-is-cs∉ κ κ∉ω) (numerals-from-trophy κ ordκ κ∉ω)

-- =====================================================================
-- SECTION 2.  THE AMBIENT SQUARE LAW IS FREE AT THIS SPELLING, AND
--             `IsCardinalL` IS NOT EVEN SPENT.
--
--   THIS IS THE MEASUREMENT NO PREDECESSOR ON THIS OBJECT RECORDED.
--   [LJ-1.556], [LJ-1.581] and this brief all treat the square law as
--   one thing.  IT IS TWO, and only the second is open.
--
--   `sq-trunc-closed` (src/L/SquareLawClosed.lagda.md:325-328) is
--   CLOSED: it is an `∈-induction` over the band and it takes no
--   induction hypothesis from its caller.  Its band parameter is a
--   MODULE parameter (src/L/SquareLawClosed.lagda.md:19-20), so a
--   caller that wants the law AT κ instantiates the band AT κ, and
--   `self∈sucV` (src/V/Model.lagda.md:236-237) discharges the band
--   membership with no hypothesis at all.
--
--   THE CONSEQUENCE.  Everything [LJ-1.556] section 4 called missing,
--   the induction hypothesis at every smaller ordinal
--   (agents/tasks/LJ-1-556/Probe556.agda:357-362), IS ALREADY PAID BY
--   `src/`, AMBIENTLY.  [LJ-1.581] refuted `SquareStep` as a TYPE
--   (agents/tasks/LJ-1-581/Probe581.agda:387) and it was right to; but
--   the hypothesis that type carries is not what the tree lacks.
-- =====================================================================

ambient-square :
    (κ : S) → IsOrd (fst κ) → ClauseTrophy κ → ∥ sq (fst κ) ∥₁
ambient-square κ ordκ κ∉ω =
  SLC.sq-trunc-closed (fst κ) (self∈sucV (fst κ)) κ∉ω
  where module SLC = L.SquareLawClosed {ℓ} lem (fst κ) ordκ

-- AND WITH THE THIRD HYPOTHESIS IN PLACE TOO, so the reader can see
-- that the obligation's own binder list reaches it.  `IsCardinalL κ`
-- is bound and DISCARDED: it buys nothing on this half.
ambient-square-at-spelling :
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ
  → ∥ sq (fst κ) ∥₁
ambient-square-at-spelling κ ordκ _ κ∉ω = ambient-square κ ordκ κ∉ω

-- =====================================================================
-- SECTION 3.  THE DOMAIN, AND IT IS [LJ-1.556]'s OBJECT AND NOT A COPY.
--
--   The brief says to copy what is green.  [LJ-1.556]'s section 1 is
--   green (agents/tasks/LJ-1-556/Probe556.agda:143-202) and its report
--   says so in those words: "Sections 1 and 2 are green Agda that a
--   chapter can copy" (agents/tasks/LJ-1-556/lj-1.556-report.md:311).
--   I TAKE IT AS THAT TASK DELIVERED IT, by import, so the lines are
--   not retyped and cannot drift.
--
--   WHAT I DO NOT TAKE FROM [LJ-1.556].  Its `BriefTarget`
--   (Probe556.agda:335) and its `SquareStep` (Probe556.agda:357-362)
--   are both FALSE, measured by [LJ-1.581] (`obligation-false`,
--   Probe581.agda:376; `squarestep-false`, :387).  Neither appears
--   below in any position.
-- =====================================================================

open import V.Presentation {ℓ} using ( member; ↪-inj )
open import L.Constructible {ℓ} using ( isL-trans )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )

import LJ-1-556.Probe556
module P556 = LJ-1-556.Probe556 {ℓ} lem

-- THE PAIRS OF KAPPA, AS AN L-SET.  [LJ-1.556] section 1, whole.
Pairs : S → S
Pairs κ = P556.Square.sqL κ

-- =====================================================================
-- SECTION 4.  THE OBLIGATION'S TYPE, WRITTEN OUT.
--
--   "A CODED injection of the pairs of κ into κ" is `InjCode F
--   (Pairs κ) κ`, truncated, which is `InjL (Pairs κ) κ`
--   (src/L/GCH.lagda.md:38).  [LJ-1.556] wrote the same conclusion as
--   `InternalSquare` (Probe556.agda:332-333); the two are ONE type and
--   two identity functions say so, so nothing turns on which name the
--   next brief uses.
-- =====================================================================

SquareCoded : S → Type (ℓ-suc ℓ)
SquareCoded κ = InjL (Pairs κ) κ

internal-is-injL : (κ : S) → P556.InternalSquare κ → SquareCoded κ
internal-is-injL κ x = x

injL-is-internal : (κ : S) → SquareCoded κ → P556.InternalSquare κ
injL-is-internal κ x = x

-- THE OBLIGATION, AT SPELLING A.
SquareCodedAt : Type (ℓ-suc ℓ)
SquareCodedAt =
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ
  → SquareCoded κ

-- AND AT SPELLING C, free by section 1.3.  Whichever the next brief
-- states, the other follows with no hypothesis added.
SquareCodedAtCS : Type (ℓ-suc ℓ)
SquareCodedAtCS =
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ
  → ClauseCodedShift∉ κ → ClauseCodedShiftNum κ
  → SquareCoded κ

a-pays-cs : SquareCodedAt → SquareCodedAtCS
a-pays-cs = a-pays-c SquareCoded

cs-pays-a : SquareCodedAtCS → SquareCodedAt
cs-pays-a = c-pays-a SquareCoded

-- =====================================================================
-- SECTION 5.  THE AMBIENT INJECTION AT THE DOMAIN ITSELF.
--
--   Section 2 delivers `sq (fst κ)`, which is a function on the INDEX
--   `⟪ fst κ ⟫ × ⟪ fst κ ⟫`.  The obligation is about the L-SET
--   `Pairs κ`.  This section moves the first to the second, using
--   [LJ-1.556]'s two readings and nothing else:
--
--     `Square.sqL-in`  (Probe556.agda:180-184)   pairs are members
--     `Square.sqL-out` (Probe556.agda:206-208)   members are pairs,
--                                                UNTRUNCATED
--
--   THE RESULT IS THE SHARPEST STATEMENT OF THIS TASK.  The pairs of
--   kappa DO inject into kappa, ambiently, at exactly the three
--   hypotheses the brief names, and `IsCardinalL` is again unspent.
--   So nothing about the SIZE of the domain is open.  What is open is
--   one thing and one thing only: the injection has no CODE.
-- =====================================================================

module Ambient (κ : S) where

  private
    module Sq = P556.Square κ

  -- A member of the pairs, as an element of L.
  toPairs : ⟪ fst (Pairs κ) ⟫ → S
  toPairs m = ⟪ fst (Pairs κ) ⟫↪ m
            , isL-trans {x = fst (Pairs κ)} {y = ⟪ fst (Pairs κ) ⟫↪ m}
                (member (fst (Pairs κ)) m) (snd (Pairs κ))

  -- Its two components, UNTRUNCATED, by [LJ-1.556]'s second reading.
  comp : (m : ⟪ fst (Pairs κ) ⟫) → Sq.Ix
  comp m = fst (Sq.sqL-out (toPairs m) (member (fst (Pairs κ)) m))

  comp-eq : (m : ⟪ fst (Pairs κ) ⟫)
          → ⟪ fst (Pairs κ) ⟫↪ m ≡ fst (Sq.pw (comp m))
  comp-eq m = snd (Sq.sqL-out (toPairs m) (member (fst (Pairs κ)) m))

  -- AND `comp` IS INJECTIVE, because a member of the pairs is
  -- DETERMINED by its two components.
  comp-inj : (m n : ⟪ fst (Pairs κ) ⟫) → comp m ≡ comp n → m ≡ n
  comp-inj m n e = ↪-inj {a = fst (Pairs κ)}
    (comp-eq m ∙ cong (λ p → fst (Sq.pw p)) e ∙ sym (comp-eq n))

  -- THE AMBIENT INJECTION OF THE PAIRS INTO KAPPA, given the ambient
  -- square law at kappa.
  from-sq : sq (fst κ) → (⟪ fst (Pairs κ) ⟫ ↪ ⟪ fst κ ⟫)
  from-sq (f , finj) = (λ m → f (comp m)) , inj
    where
    inj : (m n : ⟪ fst (Pairs κ) ⟫) → f (comp m) ≡ f (comp n) → m ≡ n
    inj m n e = comp-inj m n (finj (comp m) (comp n) e)

pairs-inject-ambiently :
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ
  → ∥ ⟪ fst (Pairs κ) ⟫ ↪ ⟪ fst κ ⟫ ∥₁
pairs-inject-ambiently κ ordκ _ κ∉ω =
  PT.map (Ambient.from-sq κ) (ambient-square κ ordκ κ∉ω)

-- =====================================================================
-- SECTION 6.  THE OBLIGATION, SPLIT.  ONE HALF IS PAID ABOVE AND THE
--             OTHER HALF IS ONE NAMED THING.
--
--   `CodeShape a b` is the wall in one line: "an ambient injection at
--   this pair, turned into a CODE at this pair".  It is not a new idea
--   of mine.  It is the shape [LJ-1.533] reported as already refuted
--   twice before it: "NOTHING CODES AN ARBITRARY AMBIENT INJECTION,
--   AND THIS WAS MEASURED TWICE BEFORE THIS TASK"
--   (agents/tasks/LJ-1-533/lj-1.533-report.md:29-31).
--
--   WRITING IT AS A TYPE IS WHAT MAKES THE SWEEP CHECKABLE.  Section 7
--   instantiates it at every pair the tree names, and the report
--   counts them.
-- =====================================================================

CodeShape : S → S → Type (ℓ-suc ℓ)
CodeShape a b = ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁ → InjL a b

-- THE RESIDUE OF THIS OBLIGATION, AND IT IS THE WHOLE OF WHAT IS LEFT.
SquareResidue : Type (ℓ-suc ℓ)
SquareResidue =
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ
  → CodeShape (Pairs κ) κ

-- AND THE RESIDUE PAYS THE OBLIGATION OUTRIGHT, because section 5 has
-- already supplied its argument.  NOTHING ELSE IS OWED.
residue-pays : SquareResidue → SquareCodedAt
residue-pays r κ ordκ cardκ κ∉ω =
  r κ ordκ cardκ κ∉ω (pairs-inject-ambiently κ ordκ cardκ κ∉ω)

-- =====================================================================
-- SECTION 7.  THE SWEEP (C-42), AS TYPES AND NOT AS A PARAGRAPH.
--
--   C-42 (dev/LESSONS.md:3752) says a refutation measures ONE site and
--   never says how far the shape extends, so the next action is the
--   sweep and the COUNT comes before the cure.  [LJ-1.533] refuted this
--   shape at B9.  This section asks how many other pairs in the tree
--   carry it.
--
--   FOUR PAIRS CARRY IT.  ONE IS PAID.  The report gives the table with
--   a `file:line` for every cell; the four types below are what makes
--   that table checkable rather than believable.
-- =====================================================================

open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.Constructible {ℓ} using ( Lset )
open import L.Cardinal {ℓ} lem using ( module LeastCardInjL )

-- SITE 1.  THE SHIFT, `sucʟ γ` INTO `γ`.  **PAID.**
site1-shift : S → Type (ℓ-suc ℓ)
site1-shift γ = CodeShape (sucʟ γ) γ

-- AND IT IS PAID AT EXACTLY THIS BRIEF'S SPELLING.  `shift-coded`
-- (src/L/CodedShift.lagda.md:37-40) wants `IsOrd`, the omega clause and
-- `numerals`; section 1.2 gives `numerals` free, so the two hypotheses
-- this brief shares with it are ENOUGH.  The ambient argument is
-- discarded: the code was never built from an ambient injection.  IT
-- WAS BUILT FROM A FORMULA.
shift-site-is-paid :
    (γ : S) → IsOrd (fst γ) → ClauseTrophy γ → CodeShape (sucʟ γ) γ
shift-site-is-paid γ ordγ γ∉ω _ =
  shift-coded γ ordγ (trophy-is-cs∉ γ γ∉ω) (numerals-from-trophy γ ordγ γ∉ω)

-- SITE 2.  THE STAGE COUNT, `Lset δ` INTO `δ`.  OPEN.  This is B9,
-- `StageCountedCoded` (agents/tasks/LJ-1-564/Probe564.agda:127-130),
-- and [LJ-1.533] is its NO-GO.
site2-stage : Type (ℓ-suc ℓ)
site2-stage =
    (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ)) → CodeShape Lδ δ

-- SITE 3.  THE SQUARE, `Pairs κ` INTO `κ`.  OPEN.  THIS TASK.
site3-square : Type (ℓ-suc ℓ)
site3-square = SquareResidue

-- SITE 4.  THE AMBIENT LEAST CARDINAL, `α` INTO `κL α`.  OPEN.  The
-- ambient injection is `LeastCardInjL.κ-inj` (src/L/Cardinal.lagda.md:133)
-- and the coded counterpart is what `InternalLeastCard.Selected` takes
-- as its `nonempty` parameter (src/L/Cardinal.lagda.md:238-243).
-- Nothing in `src/` supplies it.
site4-leastcard : Type (ℓ-suc ℓ)
site4-leastcard =
  (α : S) (oα : IsOrd (fst α)) → CodeShape α (LeastCardInjL.κ α oα)

-- AND SITE 1 IS THE ONLY ONE WITH A TERM.  The three below are TYPES
-- and nothing inhabits them here, in this file or in `src/`.

-- =====================================================================
-- SECTION 8.  AND SITE 3 IS NOT AN INDEPENDENT SITE.  IT IS SITE 2.
--
--   THIS IS THE RESULT OF THE TASK AND IT WAS NOT ANTICIPATED BY THE
--   BRIEF.  `[LJ-1.552]`'s review priced the coded square law as "a
--   chapter and not a task"
--   (agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-192), and
--   the brief calls it "THE LARGEST OBJECT LEFT ON THE BILL".  It is
--   neither.  **It is B9 at κ, plus terms this file builds.**
--
--   THE ROUTE, IN THREE STEPS AND NO RECURSION.
--
--     (a)  κ IS A LIMIT.  From the three hypotheses, using SITE 1 as a
--          LEMMA: if κ were `sucV d`, then `shift-coded` would code κ
--          into d, and `IsCardinalL κ` refutes that.
--     (b)  SO THE PAIRS LIE INSIDE `Lset κ`.  `Bound.prʟ∈λ`
--          (src/L/Coding/Bound.lagda.md:142-144) closes a LIMIT stage
--          under the ordered pair, and (a) is exactly its `succλ`
--          parameter (src/L/Coding/Bound.lagda.md:135).
--     (c)  SO THE CODE IS AN INCLUSION FOLLOWED BY B9.  `InclGraph`
--          (src/L/InjChain.lagda.md:575-598) codes the inclusion and
--          `Comp` (src/L/InjChain.lagda.md:314-434) composes two codes.
--          Both are `src/`'s and both were already measured paid by
--          [LJ-1.564] (`inclusion-coded`, Probe564.agda:162-164;
--          `injl-trans`, :167-178).
--
--   NOTHING HERE ASSERTS B9.  B9 is a HYPOTHESIS of every statement
--   below and of no other.  [LJ-1.533] is its NO-GO and I do not
--   contradict it.
-- =====================================================================

open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( sucʟ-fst )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; suc∈or≡ )
open import L.Constructible {ℓ} using ( Lset-mono )
open import L.InjChain {ℓ} lem using ( ω-limit; module InclGraph; module Comp )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.Data.Sigma using ( Σ≡Prop )

-- 8.0  THE TWO `src/` DEVICES, REBUILT AT THIS FILE'S BINDINGS.  Both
-- are [LJ-1.564]'s terms; they are rewritten from `src/` and not
-- imported, so this file pays no import for the 550/564 chain.
inclusion-coded :
    (a b : S) → ((z : V ℓ) → ⟨ z ∈ fst a ⟩ → ⟨ z ∈ fst b ⟩) → InjL a b
inclusion-coded a b sub = ∣ I.G , (I.sv , I.dm , I.ij , I.ran) ∣₁
  where module I = InclGraph a b sub

injl-trans : (a b c : S) → InjL a b → InjL b c → InjL a c
injl-trans a b c = PT.rec2 PT.squash₁ step
  where
  step : Σ[ F ∈ S ] InjCode F a b → Σ[ H ∈ S ] InjCode H b c → InjL a c
  step (F , svF , dmF , ijF , ranF) (H , svH , dmH , ijH , ranH) =
    ∣ K.K , (K.svK , K.dmK , K.ijK , K.ranK) ∣₁
    where
    module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH

-- 8.1  (a) AND (b), UNDER THE THREE HYPOTHESES AND NOTHING ELSE.
module Stage (κ : S) (ordκ : IsOrd (fst κ))
             (cardκ : IsCardinalL κ) (κ∉ω : ClauseTrophy κ) where

  private
    module Sq = P556.Square κ

  -- A member of kappa, as an element of L.
  memL : (d : V ℓ) → ⟨ d ∈ˢ fst κ ⟩ → S
  memL d h = d , isL-trans {x = fst κ} {y = d} h (snd κ)

  -- (a)  KAPPA IS SUCCESSOR-CLOSED.  SITE 1 IS THE LEMMA.
  succ-closed : (d : V ℓ) → ⟨ d ∈ˢ fst κ ⟩ → ⟨ sucV d ∈ˢ fst κ ⟩
  succ-closed d d∈ = go (suc∈or≡ d (fst κ) ordd ordκ d∈)
    where
    ordd : IsOrd d
    ordd = mem-ord {A = fst κ} ordκ d d∈

    dL : S
    dL = memL d d∈

    go : ⟨ sucV d ∈ˢ fst κ ⟩ ⊎ (sucV d ≡ fst κ) → ⟨ sucV d ∈ˢ fst κ ⟩
    go (inl h) = h
    go (inr e) = Empty.rec (cardκ dL d∈ codeκ)
      where
      -- d is not finite: else its successor is, and that successor IS
      -- kappa, which the third hypothesis forbids.
      d∉ω : ClauseTrophy dL
      d∉ω h = κ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (ω-limit d h))

      shift : InjL (sucʟ dL) dL
      shift = shift-coded dL ordd (trophy-is-cs∉ dL d∉ω)
                (numerals-from-trophy dL ordd d∉ω)

      sucʟ≡κ : sucʟ dL ≡ κ
      sucʟ≡κ = Σ≡Prop (λ x → snd (isL x)) (sucʟ-fst dL ∙ e)

      codeκ : InjL κ dL
      codeκ = subst (λ a → InjL a dL) sucʟ≡κ shift

  -- Every member of kappa is a member of the stage at kappa.
  memL∈stage : (d : V ℓ) → ⟨ d ∈ˢ fst κ ⟩ → ⟨ d ∈ˢ Lset (fst κ) ⟩
  memL∈stage d d∈ = Lset-mono {α = fst κ} {β = sucV d} (succ-closed d d∈)
    {x = d} (ord∈Lset-suc d (mem-ord {A = fst κ} ordκ d d∈))

  private
    ∅∈κ : ⟨ ∅ ∈ˢ fst κ ⟩
    ∅∈κ = numerals-from-trophy κ ordκ κ∉ω 0

    module B = Bound (fst κ) ordκ succ-closed ∅∈κ

  -- (b)  THE PAIRS LIE INSIDE THE STAGE AT KAPPA.
  pairs⊆stage :
    (z : V ℓ) → ⟨ z ∈ fst (Pairs κ) ⟩ → ⟨ z ∈ fst (LsetS (fst κ) ordκ) ⟩
  pairs⊆stage z h = subst (λ w → ⟨ w ∈ˢ Lset (fst κ) ⟩) (sym (c .snd)) inStage
    where
    zL : S
    zL = z , isL-trans {x = fst (Pairs κ)} {y = z} h (snd (Pairs κ))

    c : Sq.Comp zL
    c = Sq.sqL-out zL h

    inStage : ⟨ fst (Sq.pw (c .fst)) ∈ˢ Lset (fst κ) ⟩
    inStage = B.prʟ∈λ (Sq.toκ (c .fst .fst)) (Sq.toκ (c .fst .snd))
      (memL∈stage (⟪ fst κ ⟫↪ (c .fst .fst)) (member (fst κ) (c .fst .fst)))
      (memL∈stage (⟪ fst κ ⟫↪ (c .fst .snd)) (member (fst κ) (c .fst .snd)))

-- 8.2  B9, STATED AND NOT ASSERTED.
--
--   `B9` is `StageCountedCoded` as the campaign's bill carries it
--   (agents/tasks/LJ-1-564/Probe564.agda:127-130), copied letter for
--   letter.  [LJ-1.533] is its NO-GO and its finding 1 says the type is
--   FALSE for want of infinitude
--   (agents/tasks/LJ-1-533/lj-1.533-report.md:26-28).  SO I DO NOT SPEND
--   IT.  `B9Inf` is the same row NARROWED to this brief's own three
--   hypotheses, which exclude every finite δ, and `B9Inf` is all the
--   derivation below spends.
B9 : Type (ℓ-suc ℓ)
B9 = (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ

B9Inf : Type (ℓ-suc ℓ)
B9Inf =
    (δ Lδ : S) → IsOrd (fst δ) → IsCardinalL δ → ClauseTrophy δ
  → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ

-- The narrowing is a weakening, so nothing already owed becomes harder.
b9-pays-b9inf : B9 → B9Inf
b9-pays-b9inf b9 δ Lδ ordδ _ _ e = b9 δ Lδ ordδ e

-- 8.3  (c).  THE OBLIGATION, FROM B9 AT KAPPA AND NOTHING ELSE.
square-from-b9inf : B9Inf → SquareCodedAt
square-from-b9inf b9 κ ordκ cardκ κ∉ω =
  injl-trans (Pairs κ) Lκ κ
    (inclusion-coded (Pairs κ) Lκ (Stage.pairs⊆stage κ ordκ cardκ κ∉ω))
    (b9 κ Lκ ordκ cardκ κ∉ω refl)
  where
  Lκ : S
  Lκ = LsetS (fst κ) ordκ

-- AND FROM B9 AS THE BILL WRITES IT, so the row the campaign already
-- carries closes this obligation with no restatement at all.
square-from-b9 : B9 → SquareCodedAt
square-from-b9 b9 = square-from-b9inf (b9-pays-b9inf b9)

-- =====================================================================
-- SECTION 9.  AND `B9` IS THE BILL'S OWN ROW, AS A TERM.
--
--   Section 8.2 says `B9` is `StageCountedCoded` copied letter for
--   letter.  A sentence like that is worth one identity function and
--   not more, so here are two.  [LJ-1.564] is GO
--   (agents/tasks/LJ-1-564/lj-1.564-report.md:8), and its row is taken
--   as the type THAT TASK DELIVERED and not as a retyped copy, which is
--   my slot's rule.
--
--   PRICE.  Importing [LJ-1.564] carries [LJ-1.550], [LJ-1.528],
--   [LJ-1.526], [LJ-1.543], [LJ-1.540] and [LJ-1.544]
--   (agents/tasks/LJ-1-589/Probe589.agda:369-371).  [LJ-1.589] measured
--   that import at 37.28 s and 1.9 GB (Probe589.agda:372-373).  The
--   number MEASURED HERE is in this task's report and it is not that
--   one: a price does not transfer.
--
--   AND NOTHING [LJ-1.550] FAILED TO DELIVER IS USED AS A FACT.  No
--   term of [LJ-1.550] appears below in any position.
-- =====================================================================

import LJ-1-564.Probe564 {ℓ} lem as P564

b9-is-the-bill-row : P564.StageCountedCoded → B9
b9-is-the-bill-row x = x

b9-is-the-bill-row-back : B9 → P564.StageCountedCoded
b9-is-the-bill-row-back x = x

-- SO THE BILL ALREADY CARRIES EVERY INPUT THE CODED SQUARE LAW NEEDS.
-- `gch-from-five-inf` (agents/tasks/LJ-1-589/Probe589.agda:421-429)
-- takes `b9` in its fourth place.  THIS LINE SPENDS THAT SAME `b9` ON
-- THE SQUARE LAW, so the square law adds NO NEW ROW to the bill.
square-from-the-bills-own-b9 : P564.StageCountedCoded → SquareCodedAt
square-from-the-bills-own-b9 b9 = square-from-b9 (b9-is-the-bill-row b9)
