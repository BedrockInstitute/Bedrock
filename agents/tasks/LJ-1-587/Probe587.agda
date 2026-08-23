{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.587]  Does either `InjCode` producer widen?
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and typechecked
-- ALONE.  runs/w3-1.out is that run.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-587.Probe587 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL-trans )
open import L.Absorption {ℓ} lem
  using ( shiftFo; val; module Carve )
  renaming ( shift-coded to abs-shift-coded )
open import L.CodedShift {ℓ} lem
  renaming ( shift-coded to cs-shift-coded )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.InjChain {ℓ} lem
  using ( module InclGraph; module OrdIncl; module Comp; module StageBound )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  THE ABSORPTION PRODUCER'S FORMULA, RE-ASCRIBED WITH
-- ITS PAIR ABSTRACT.  TYPE ONLY.
--
--   The brief names this the widest unmeasured term: "the Absorption
--   producer's Formula, lifted off its site".  The question it settles
--   is whether that formula can even STATE at a pair the site does not
--   fix.  `shiftFo` is `src/L/Absorption.lagda.md:224-226`.
--
--   The re-ascription below takes the pair `(D , C)` as arguments and
--   returns the site's own formula at that `D`.  If it typechecks, the
--   formula is not tied to `sucʟ γ`.
-- =====================================================================

formula-at-abstract-pair : (D C γ ω z : S) → Formula S 1
formula-at-abstract-pair D C γ ω z = shiftFo D γ ω z

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.  A PRODUCER AT AN ARBITRARY PAIR.
--
--   W3 said the formula states at an abstract pair.  This section says
--   the whole METHOD does.
--
--   `Carve` (src/L/Absorption.lagda.md:386-402) is the Absorption
--   producer's method, and its first two parameters `D C` ARE the pair
--   of `InjCode F D C`.  They are already abstract there.  What fixes
--   the shape `(sucʟ γ , γ)` is not `Carve`: it is `ShiftGraph`
--   (:539-541), the Part-4 instantiation that sets `D := sucV γ` and
--   `C := γ` and builds `sh` from the three-case ambient shift.
--
--   So the pair is free, and what has to be paid at a new pair is
--   `Carve`'s hypotheses.  The cheapest new pair pays them by
--   degenerating the three cases, and the tree ALREADY CARRIES that
--   degeneration under another name.  `InclGraph`
--   (src/L/InjChain.lagda.md:575-598), through its own `Carve`
--   (:468-473), carves the identity graph between two sets from a
--   subset witness, and exports `sv` (:518), `ij` (:525), `dm` (:532)
--   and `ran` (:544) at `γI = G ∷ D ∷ []` (:515).  Those four ARE
--   `InjCode`'s four conjuncts (src/L/Cardinal.lagda.md:223-228),
--   definitionally, and the tuple below is the whole cost.
-- =====================================================================

producer-widened : (D C : S)
                 → ((z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩)
                 → Σ[ F ∈ S ] InjCode F D C
producer-widened D C sub = IG.G , (IG.sv , IG.dm , IG.ij , IG.ran)
  where
  module IG = InclGraph D C sub

-- The pair is arbitrary.  Nothing above names `sucʟ`, an ordinal, ω or
-- a numeral.  For contrast, the site's own shape, taken at an ordinal.
producer-widened-at-ordinal :
    (C : S) → IsOrd (fst C) → (D : S) → ⟨ fst D ∈ fst C ⟩
  → Σ[ F ∈ S ] InjCode F D C
producer-widened-at-ordinal C oC D D∈C =
  OI.G , (OI.sv , OI.dm , OI.ij , OI.ran)
  where
  module OI = OrdIncl C oC D D∈C

-- =====================================================================
-- SECTION 3.  THE SAME QUESTION, ANSWERED ON THE PRODUCER'S OWN METHOD.
--
--   Section 2 delivered the obligation through `InclGraph`, which is a
--   SIBLING machine and not the Absorption producer.  A sibling is not
--   an answer to "does the METHOD leave its shape".  This section takes
--   `Carve` ITSELF (src/L/Absorption.lagda.md:386-402), the module the
--   Absorption producer is built from, and instantiates it at a pair
--   `(D , C)` that is arbitrary.
--
--   THE THREE CASES DEGENERATE, and each degeneration is one line.
--     `ω := ∅ʟ`  kills case 1: nothing is a member of ∅, so the numeral
--                clause is `Empty.rec`.
--     `γ := D`   kills case 2: no member of D is D, by `∈-irrefl`.  It
--                also makes `D-in-dec` the identity on its own second
--                argument, because the conclusion IS that argument.
--     case 3     is then everything, and it says the value is the same
--                SET, which is what a subset witness gives.
--
--   Nothing here names `sucʟ`, an ordinal, ω or a numeral.
-- =====================================================================

module WidenedCarve (D C : S)
                    (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩) where

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

  -- The shift, taken at this pair: a member of D, seen in C.
  sh : ⟪ fst D ⟫ → ⟪ fst C ⟫
  sh m = fiber (fst C) (sub (⟪ fst D ⟫↪ m) (member (fst D) m)) .fst

  sh-val : (m : ⟪ fst D ⟫) → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m
  sh-val m = fiber (fst C) (sub (⟪ fst D ⟫↪ m) (member (fst D) m)) .snd

  shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n
  shInj m n e =
    ↪-inj {a = fst D} (sym (sh-val m) ∙ cong (⟪ fst C ⟫↪) e ∙ sh-val n)

  -- CASE 1, VACUOUS.
  shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ∅ʟ ⟩)
        → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m)
  shNum m v∈ω = Empty.rec
    (∅-empty (⟪ fst D ⟫↪ m) (∈∈ₛ {a = ⟪ fst D ⟫↪ m} {b = ∅} .fst v∈ω))

  -- CASE 2, VACUOUS.
  shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst D)
        → ⟪ fst C ⟫↪ (sh m) ≡ fst ∅ʟ
  shTop m v≡γ = Empty.rec
    (∈-irrefl (fst D) (subst (λ w → ⟨ w ∈ fst D ⟩) v≡γ (member (fst D) m)))

  -- CASE 3, EVERYTHING.
  shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ∅ʟ ⟩ → Empty.⊥)
            (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst D) → Empty.⊥)
          → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m
  shOther m _ _ = sh-val m

  -- THE DECISION CLAUSE IS ITS OWN HYPOTHESIS at `γ := D`.
  D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst D) → Empty.⊥)
           → ⟨ fst x ∈ fst D ⟩
  D-in-dec x m _ = m

  private
    dg : ⟪ fst D ⟫ → S
    dg m = prʟ (toD m) (toC (sh m))

    module SB = StageBound ⟪ fst D ⟫ dg

    bel : (x : S) (m : ⟨ x ∈ˢ D ⟩)
        → ⟨ pr (fst x) (val D C sh x m) ∈ fst SB.bnd ⟩
    bel x m = subst (λ w → ⟨ w ∈ fst SB.bnd ⟩) pa
      (SB.below (fiber (fst D) m .fst))
      where
      pa : fst (dg (fiber (fst D) m .fst)) ≡ pr (fst x) (val D C sh x m)
      pa = prʟ-fst (toD (fiber (fst D) m .fst)) (toC (sh (fiber (fst D) m .fst)))
         ∙ cong₂ pr (snd (fiber (fst D) m)) refl

  open Carve D C D ∅ʟ ∅ʟ sh shInj shNum shTop shOther D-in-dec
    SB.bnd bel hasSeparationL public

-- THE PRODUCER, THROUGH THE ABSORPTION METHOD AND NOTHING ELSE.
producer-widened-by-carve :
    (D C : S) → ((z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩)
  → Σ[ F ∈ S ] InjCode F D C
producer-widened-by-carve D C sub = WC.G , (WC.sv , WC.dm , WC.ij , WC.ran)
  where
  module WC = WidenedCarve D C sub

-- =====================================================================
-- SECTION 4.  THE COUNT `[LJ-1.580]` REPORTED, RE-MEASURED.
--
--   Premise 1 of this brief is "two producers, both at one shape",
--   basis agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:105-108.
--   That line says it was found by `grep -rn "InjCode" src/`.  A grep
--   for a NAME is not a count of PRODUCERS, and this section measures
--   the two ways it is off.
--
--   FIRST: the two sites are ONE TERM.  `src/L/CodedShift.lagda.md:37-52`
--   is byte for byte `src/L/Absorption.lagda.md:611-626`; the diff is
--   empty.  `two-sites-one-term` is the elaborator's word for it, by
--   `refl`, so the count of METHODS at that shape is ONE and not two.
--
--   SECOND: `src/L/InjChain.lagda.md` carries TWO more machines that
--   deliver `InjCode`'s four conjuncts at an ARBITRARY pair and never
--   write the word `InjCode`, which is why the grep did not see them.
--   `InclGraph` is section 2.  `Comp` (:314-435) is the composition, and
--   `producers-compose` below is its `InjCode` reading.
-- =====================================================================

two-sites-one-term :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → abs-shift-coded γ oγ γ∉ω numerals ≡ cs-shift-coded γ oγ γ∉ω numerals
two-sites-one-term γ oγ γ∉ω numerals = refl

-- AND THE PAIR IS CLOSED UNDER COMPOSITION, at arbitrary pairs.
producers-compose :
    (D E C F H : S) → InjCode F D E → InjCode H E C
  → Σ[ K ∈ S ] InjCode K D C
producers-compose D E C F H (svF , dmF , ijF , ranF) (svH , dmH , ijH , ranH) =
  CP.K , (CP.svK , CP.dmK , CP.ijK , CP.ranK)
  where
  module CP = Comp D E C F H svF dmF ijF ranF svH dmH ijH ranH

-- =====================================================================
-- SECTION 5.  THE CAMPAIGN'S READING, so the next brief can take it.
--
--   `InjL` (src/L/GCH.lagda.md:38) is the truncation the trophy speaks
--   in.  The two reductions below are sections 2 and 4 at that grade,
--   and each NAMES ITS OWN HYPOTHESIS.  That is the whole content of
--   this task for the bill: reuse buys a subset pair and a composite
--   pair, and it buys nothing else.
--
--   `[LJ-1.580]`'s residue is `InjL (Lset β) α`
--   (agents/tasks/LJ-1-580/Probe580.agda:311).  Read against
--   `injL-from-subset`, that residue asks for `Lset β ⊆ α`.  A stage is
--   not a subset of an ordinal, so THIS ROUTE DOES NOT CLOSE IT, and
--   the line below is what says so: the hypothesis is visible in the
--   type and cannot be quietly assumed.
-- =====================================================================

injL-from-subset : (a b : S) → ((z : V ℓ) → ⟨ z ∈ fst a ⟩ → ⟨ z ∈ fst b ⟩)
                 → InjL a b
injL-from-subset a b sub = ∣ producer-widened a b sub ∣₁

injL-compose : (a c : S) (b : S) → InjL a b → InjL b c → InjL a c
injL-compose a c b = PT.rec2 squash₁
  (λ { (F , cF) (H , cH) → ∣ producers-compose a b c F H cF cH ∣₁ })
