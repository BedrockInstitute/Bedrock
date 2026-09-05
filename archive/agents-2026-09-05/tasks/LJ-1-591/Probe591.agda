{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.591]  Is row 2's square the same square as row 5's?
--
-- ANSWER: NO.  THEY ARE TWO OBJECTS AND ROW 2's IS THE WIDER ONE.
-- The obligation is inhabited in the direction row 2 → row 5 and in no
-- other direction, and this file measures the whole gap.
--
--   Section 1.  W3, AND IT IS GO.  The two types sit in one file.
--   Section 2.  THE TWO SQUARES SIDE BY SIDE, with the one place they
--               DO agree: row 5's conclusion IS `InjL` at the diagonal
--               pair, by two identity functions.
--   Section 3.  THE BRIDGE.  An ambient square at kappa, read onto the
--               coded domain `sqL kappa`.
--   Section 4.  `Init` FROM ROW 5's OWN HYPOTHESES PLUS ROW 2's SQUARE.
--               This is where every side condition of row 5 is spent.
--   Section 5.  THE OBLIGATION.
--   Section 6.  WHICH IS STRONGER, in four terms.
--   Section 7.  WHAT IS NOT HERE.
--
-- Nothing is postulated.  No hole.  Nothing lands in src/.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-591.Probe591 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( ω-limit )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )

-- The five helpers of the ambient chain, TAKEN AND NOT REBUILT.  The
-- module parameters `α₀ oα₀` are dead for every name below: none of the
-- five reads them (src/L/SquareLawClosed.lagda.md:55, :51, :117, :119).
open import L.SquareLawClosed {ℓ} lem ω ω-ord
  using ( comp-inj; isL-ord; shift-at; module Shiftω )

import LJ-1-556.Probe556 {ℓ} lem as P556
import LJ-1-581.Probe581 {ℓ} lem as P581
import LJ-1-583.Probe583 {ℓ} lem as P583
import LJ-1-590.Probe590 {ℓ} lem as P590

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 1.  W3, AND IT IS GO.
--
--   The slice is agents/tasks/LJ-1-591/runs/W3.agda, run runs/w3-1.out:
--   205.69 s, exit 0, green on the FIRST run, everything cold.  There
--   is no red predecessor.  The question it settles is the brief's own:
--   whether the two types can be written in ONE file at all.  THEY CAN,
--   and the reason is that `LJ-1-583.Probe583` and `LJ-1-581.Probe581`
--   carry the SAME telescope `{ℓ} (lem : LEM (ℓ-suc ℓ))`, so one ℓ and
--   one `lem` serve both.  Both types land at `Type (ℓ-suc ℓ)`.
-- =====================================================================

-- =====================================================================
-- SECTION 2.  THE TWO SQUARES, SIDE BY SIDE.
--
--   ROW 2.  agents/tasks/LJ-1-583/Probe583.agda:195-196.
--
--     SquareCoded = (κ β : S) → ⟪ fst κ ⟫ ↪ ⟪ fst β ⟫ → InjL κ β
--
--     carrier          TWO free L-elements, κ and β.  Neither is an
--                      ordinal, neither is a cardinal.
--     pair             NONE.  No pair set occurs in the type.  The name
--                      is the CALL SITE's and not the statement's: the
--                      site is src/L/SquareLawClosed.lagda.md:109 and
--                      its middle factor happens to come from a square.
--     side conditions  NONE.  Not `IsOrd`, not `IsCardinalL`, not ω.
--                      One hypothesis and it is an AMBIENT injection.
--
--   ROW 5.  agents/tasks/LJ-1-581/Probe581.agda:427-432.
--
--     SquareStepInf = (κ : S) → IsOrd (fst κ) → ⟨ ω ∈ fst κ ⟩
--                   → IsCardinalL κ
--                   → ((β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩
--                      → ⟨ ω ∈ fst β ⟩ → Coded β)
--                   → Coded κ
--
--     carrier          ONE free L-element κ.
--     pair             `P556.Square.sqL κ`, the L-set of the ordered
--                      pairs of κ (agents/tasks/LJ-1-556/Probe556.agda
--                      :148-149), which IS the domain of the code:
--                      `Coded κ = ∥ Σ[ F ∈ S ] InjCode F (sqL κ) κ ∥₁`
--                      (Probe581.agda:127-128).
--     side conditions  FOUR: ordinal, infinite, L-cardinal, and an
--                      induction hypothesis at every infinite ordinal
--                      member.
--
--   SO THE BRIEF'S GUESS IS WRONG IN ITS DIRECTION.  The infinity clause
--   is NOT the difference: row 2's square carries no side condition at
--   all, so it cannot be row 5's minus one clause.  Section 6a says what
--   the four clauses actually buy.
-- =====================================================================

RowTwo : Type (ℓ-suc ℓ)
RowTwo = P583.SquareCoded

RowFive : Type (ℓ-suc ℓ)
RowFive = P581.SquareStepInf

-- THE ONE PLACE THEY AGREE, AND IT IS A DEFINITIONAL ONE.  Row 5's
-- conclusion is row 2's conclusion at the diagonal pair `(sqL κ , κ)`.
-- Neither function below has a proof term: both are `λ x → x`, so the
-- two types are the SAME type.  src/L/GCH.lagda.md:37-38 against
-- agents/tasks/LJ-1-581/Probe581.agda:127-128.
coded-is-injL : (κ : S) → P581.Coded κ → InjL (P556.Square.sqL κ) κ
coded-is-injL κ x = x

injL-is-coded : (κ : S) → InjL (P556.Square.sqL κ) κ → P581.Coded κ
injL-is-coded κ x = x

-- =====================================================================
-- SECTION 3.  THE BRIDGE.
--
--   Row 2's square consumes an AMBIENT injection out of `⟪ fst (sqL κ) ⟫`
--   and the tree's ambient square law delivers one out of
--   `⟪ fst κ ⟫ × ⟪ fst κ ⟫` (src/L/Ordinal/SquareLaw.lagda.md:685-687).
--   The two are not the same type and the reading between them is the
--   OPPOSITE of [LJ-1.581]'s: `Read.ix→mem` goes Ix → member
--   (Probe581.agda:165-166), and this file needs member → Ix.  That is
--   `sqL-out` (Probe556.agda:186), which is UNTRUNCATED, so nothing is
--   chosen here.
-- =====================================================================

module Bridge (κ : S) where

  module Sq = P556.Square κ

  -- A member index of `sqL κ`, as an element of L.  The spelling is
  -- `Square.toκ`'s (Probe556.agda:90-92) at the pair set instead of at κ.
  memL : ⟪ fst Sq.sqL ⟫ → S
  memL m = ⟪ fst Sq.sqL ⟫↪ m
         , isL-trans {x = fst Sq.sqL} {y = ⟪ fst Sq.sqL ⟫↪ m}
             (member (fst Sq.sqL) m) (snd Sq.sqL)

  out : (m : ⟪ fst Sq.sqL ⟫) → Sq.Comp (memL m)
  out m = Sq.sqL-out (memL m) (member (fst Sq.sqL) m)

  mem→ix : ⟪ fst Sq.sqL ⟫ → Sq.Ix
  mem→ix m = out m .fst

  mem→ix-inj : (m n : ⟪ fst Sq.sqL ⟫) → mem→ix m ≡ mem→ix n → m ≡ n
  mem→ix-inj m n e = ↪-inj {a = fst Sq.sqL}
    (out m .snd ∙ cong (λ p → fst (Sq.pw p)) e ∙ sym (out n .snd))

  sqL↪ix : ⟪ fst Sq.sqL ⟫ ↪ Sq.Ix
  sqL↪ix = mem→ix , mem→ix-inj

  -- `sq (fst κ)` IS `Sq.Ix ↪ ⟪ fst κ ⟫` and no coercion is written.
  from-square : sq (fst κ) → (⟪ fst Sq.sqL ⟫ ↪ ⟪ fst κ ⟫)
  from-square s = comp-inj sqL↪ix s

-- =====================================================================
-- SECTION 4.  `Init` FROM ROW 5's HYPOTHESES PLUS ROW 2's SQUARE.
--
--   THIS IS THE WHOLE OF THE IMPLICATION AND IT IS WHERE EVERY ONE OF
--   ROW 5's FOUR SIDE CONDITIONS IS SPENT.  `Init`
--   (src/L/Ordinal/SquareLaw.lagda.md:692-698) has four conjuncts and
--   the tree pays them for the ambient least cardinal `κL` at
--   src/L/SquareLawClosed.lagda.md:166-177.  That proof CANNOT be
--   imported: `init-at-kappa` is stated at `fst (κL a oa)` and reaches
--   `κ-min-atL` (:86-89), the AMBIENT minimality of that particular κ.
--   Row 5's κ is arbitrary and carries `IsCardinalL`, which refutes a
--   CODE and not an ambient injection (src/L/Cardinal.lagda.md:230-233).
--
--   `no-inj` below is the join, and it is the ONLY line of this file
--   that uses row 2's square.  Everything else is the tree's own
--   argument transplanted.
-- =====================================================================

module MakeInit (sc : P583.SquareCoded) (κ : S)
                (oκ : IsOrd (fst κ)) (ω∈κ : ⟨ ω ∈ fst κ ⟩)
                (cκ : IsCardinalL κ)
                (ih : (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩
                    → ⟨ ω ∈ fst β ⟩ → P581.Coded β) where

  -- ROW 2's SQUARE, USED ONCE, AND IT IS AN INTERNALIZATION AND NOT A
  -- SQUARE: it turns an ambient injection into a code, and `IsCardinalL`
  -- refutes the code.
  no-inj : (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ fst κ ⟩
         → ⟪ fst κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥
  no-inj δ oδ δ∈κ f = cκ δL δ∈κ (sc κ δL f)
    where
    δL : S
    δL = δ , isL-ord δ oδ

  -- CONJUNCT 4.  src/L/SquareLawClosed.lagda.md:96-115 with `κ-min-atL`
  -- replaced by `no-inj`, and with the ambient `sq β` of that file's
  -- `ih` replaced by row 5's CODED `ih`, read down by [LJ-1.581]'s own
  -- `Read.square-from-coded` (Probe581.agda:203-204).
  clause4 : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ fst κ ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ fst κ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  clause4 β oβ β∈κ ω∈β f finj =
    PT.rec Empty.isProp⊥ from-sq
      (P581.Read.square-from-coded βL (ih βL oβ β∈κ ω∈β))
    where
    βL : S
    βL = β , isL-ord β oβ

    from-sq : ((⟪ β ⟫ × ⟪ β ⟫) ↪ ⟪ β ⟫) → Empty.⊥
    from-sq g = no-inj β oβ β∈κ (comp-inj (f , finj) g)

  -- CONJUNCT 3.  src/L/SquareLawClosed.lagda.md:125-158, same shape,
  -- same three cases of trichotomy, same two shift injections.
  sω∈κ : ⟨ sucV ω ∈ fst κ ⟩
  sω∈κ = Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-ω e))
    (suc∈or≡ ω (fst κ) ω-ord oκ ω∈κ)
    where
    eq-ω : sucV ω ≡ fst κ → Empty.⊥
    eq-ω e = no-inj ω ω-ord ω∈κ
      (subst (λ z → ⟪ z ⟫ ↪ ⟪ ω ⟫) e Shiftω.shift↪)

  limit : (γ : V ℓ) → ⟨ γ ∈ˢ fst κ ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
  limit γ γ∈κ = γ-tri (ord-tri γ oγ ω ω-ord)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = fst κ} oκ γ γ∈κ

    γ-tri : ⟨ γ ∈ˢ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩) → ⟨ sucV γ ∈ˢ fst κ ⟩
    γ-tri (inl γ∈ω) = oκ .fst (ω-limit γ γ∈ω) ω∈κ
    γ-tri (inr (inl γ≡ω)) =
      subst (λ w → ⟨ sucV w ∈ fst κ ⟩) (sym γ≡ω) sω∈κ
    γ-tri (inr (inr ω∈γ)) =
      Sum.rec (λ s∈κ → s∈κ) (λ e → Empty.rec (eq-γ e))
        (suc∈or≡ γ (fst κ) oγ oκ γ∈κ)
      where
      eq-γ : sucV γ ≡ fst κ → Empty.⊥
      eq-γ e = no-inj γ oγ γ∈κ
        (subst (λ z → ⟪ z ⟫ ↪ ⟪ γ ⟫) e (shift-at γ oγ ω∈γ))

  init : Init (fst κ)
  init = oκ , ω∈κ , limit , clause4

-- =====================================================================
-- SECTION 5.  THE OBLIGATION.
-- =====================================================================

one-square-two-rows : P583.SquareCoded → P581.SquareStepInf
one-square-two-rows sc κ oκ ω∈κ cκ ih =
  sc (P556.Square.sqL κ) κ
     (Bridge.from-square κ (via-col-square (fst κ) MI.init))
  where
  module MI = MakeInit sc κ oκ ω∈κ cκ ih

-- =====================================================================
-- SECTION 6.  WHICH IS STRONGER.  FOUR TERMS.
-- =====================================================================

-- 6a.  ROW 2's SQUARE PAYS ROW 5's CONCLUSION WITH NO SIDE CONDITION AT
--      ALL, once an ambient square is in hand.  Read this against
--      section 5: the four side conditions of `SquareStepInf` are NOT a
--      difference between the two squares.  They are the price of the
--      ambient square, which section 4 pays through `Init`, and row 2's
--      square consumes that square as a hypothesis.
SquareStepBare : Type (ℓ-suc ℓ)
SquareStepBare = (κ : S) → ((⟪ fst κ ⟫ × ⟪ fst κ ⟫) ↪ ⟪ fst κ ⟫)
               → P581.Coded κ

square-coded→bare : P583.SquareCoded → SquareStepBare
square-coded→bare sc κ s = sc (P556.Square.sqL κ) κ (Bridge.from-square κ s)

-- 6b.  AND IT PAYS SOMETHING ROW 5 NEVER ASKS FOR: no L-cardinal is
--      ambiently collapsed.  Nothing on the bill claims this and no row
--      needs it.  One line, and it uses `IsCardinalL` positively.
NoAmbientCollapse : Type (ℓ-suc ℓ)
NoAmbientCollapse = (κ δ : S) → IsCardinalL κ → ⟨ fst δ ∈ fst κ ⟩
                  → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫ → Empty.⊥

square-coded→no-collapse : P583.SquareCoded → NoAmbientCollapse
square-coded→no-collapse sc κ δ cκ δ∈κ f = cκ δ δ∈κ (sc κ δ f)

-- 6c.  D-10, AND IT IS THE FINDING THE NEXT BRIEF MUST PRICE FIRST.
--      [LJ-1.590] delivered the DOWNWARD reading unconditionally
--      (`bare-inj-of`, agents/tasks/LJ-1-590/Probe590.agda:207-213).
--      Row 2's square is the UPWARD one.  Together the ambient and the
--      coded injection relations are the SAME relation at EVERY pair of
--      L-elements.  That is the distinction the whole route rests on,
--      and this term says row 2's square erases it.
AmbientIsCoded : Type (ℓ-suc ℓ)
AmbientIsCoded = (a b : S)
  → ((⟪ fst a ⟫ ↪ ⟪ fst b ⟫) → InjL a b)
  × (InjL a b → (⟪ fst a ⟫ ↪ ⟪ fst b ⟫))

square-coded→ambient-is-coded : P583.SquareCoded → AmbientIsCoded
square-coded→ambient-is-coded sc a b = sc a b , P590.bare-inj-of a b

-- 6d.  THE OTHER DIRECTION, AND IT IS CONDITIONAL AND NOT AN IDENTITY.
--      Row 5's square pays row 2's site src/L/SquareLawClosed.lagda.md
--      :109 AS SOON AS that site's clause-4 hypothesis `f` is stated
--      CODED instead of ambient.  No new principle appears: both steps
--      are [LJ-1.583]'s delivered `codedComp` (Probe583.agda:169-175).
--      THIS IS NOT A DISCHARGE OF ROW 2.  Restating conjunct 4 of `Init`
--      in coded form is unbuilt and is not attempted here.
CodedClause4 : Type (ℓ-suc ℓ)
CodedClause4 = (a κ β : S) → InjL a κ → InjL κ (P556.Square.sqL β)
             → P581.Coded β → InjL a β

coded-clause4 : CodedClause4
coded-clause4 a κ β aκ f cβ =
  P583.codedComp a κ β aκ (P583.codedComp κ (P556.Square.sqL β) β f cβ)

-- =====================================================================
-- SECTION 7.  WHAT IS NOT HERE.
--
--   1.  NO TERM OF `SquareStepInf → SquareCoded`, and none is claimed.
--       A non-implication is not writable in Agda and this file does not
--       pretend one.  What IS measured is 6a, 6b and 6c: row 2's square
--       has strictly more consequences in this file than row 5's, and
--       6d is the only payment that runs the other way.
--   2.  NEITHER SQUARE IS BUILT.  `SquareCoded` is a hypothesis at every
--       use, and `SquareStepInf` occurs only as a conclusion.
--   3.  NO CODED `Init`.  6d's antecedent `InjL κ (sqL β)` is a
--       hypothesis and nothing here supplies it.
--   4.  NOTHING ABOUT `[LJ-1.581]`'s refutation.  `squarestep-false`
--       (Probe581.agda:387) refutes the form WITHOUT the ω clause, and
--       row 2's square does not reach that form: `square-coded→bare`
--       needs an ambient square at κ, and at κ := 2 there is none.
-- =====================================================================
