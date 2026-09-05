{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.589]  THREAD THE INFINITY CLAUSE THROUGH ROW 5.
--
-- THE OBLIGATION IS INHABITED.  `row5-carries-infinity` is section 6.
-- This file carries NO hole and NO postulate, so every line of it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.556], [LJ-1.574] and [LJ-1.581]).
-- Nothing lands in src/.  `SquareStepInf` is NOT built here and the
-- square law is NOT built here: the brief forbids both.
--
-- WHY THIS TASK EXISTS.  [LJ-1.581] is a NO-GO, upheld
-- (agents/tasks/LJ-1-581/review-of-LJ-1-581-1.md:6).  It named two
-- reopeners and recommended the second: "THREAD THE INFINITY CLAUSE
-- THROUGH ROW 5 FIRST, because the consumer does not carry it today"
-- (agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md:169-171).
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  THE THREE SPELLINGS, copied from their sites and named.
--   Section 2.  THE TROPHY'S CLAUSE AND `CodedShift`'s FIRST CONJUNCT
--               ARE ONE TYPE.  Four identity functions say so.
--   Section 3.  `SquareStepInf`'s CLAUSE IS STRICTLY STRONGER, and the
--               gap is exactly omega.  The trophy quantifies over
--               omega; `SquareStepInf` does not reach it.
--   Section 4.  `CodedShift`'s SECOND CONJUNCT IS FREE.  `numerals`
--               follows from the trophy's clause and `IsOrd` alone.
--               So the trophy spelling and the `CodedShift` spelling
--               ARE interderivable, and `SquareStepInf`'s is not.
--   Section 5.  ROW 5, RESTATED WITH THE CLAUSE, three ways, and the
--               terms that move between them.
--   Section 6.  THE OBLIGATION.  `GCHStatement` from the NARROWED row
--               5, with row 4 and the hard leg unchanged.
--   Section 7.  AND THE CAMPAIGN'S OWN FIVE-ROW BILL closes with the
--               narrowed row too.  The bill is still five rows.
--
-- W3 IS `agents/tasks/LJ-1-589/runs/W3.agda`, written first and
-- typechecked alone (runs/w3-1.out:4, 1.68 s, EXIT=0).
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-589.Probe589 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; numeral-mem; numeral-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The L-carrier.  `GCHStatement` lives here (src/L/GCH.lagda.md:27).
module SL = hPropStructure 𝒮ʟ
-- The same instance src/L/GCH.lagda.md:30 names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- [LJ-1.558] is GO (agents/tasks/LJ-1-558/lj-1.558-report.md:7).  Its
-- rows are taken as the types that task DELIVERED, not as retyped
-- copies.  The import costs 1.96 s alone (runs/import-1.out:5).
import LJ-1-558.Probe558
module P558 = LJ-1-558.Probe558 {ℓ} lem

-- =====================================================================
-- SECTION 1.  THE THREE SPELLINGS, COPIED FROM THEIR SITES.
--
--   The brief names two.  There are three types on the page, because
--   `CodedShift` carries TWO conjuncts and only the first of them is a
--   clause about omega.  Naming the second separately is what lets
--   section 4 measure it.
-- =====================================================================

-- SPELLING A.  THE TROPHY'S.  `GCHStatement`'s fourth hypothesis,
-- src/L/GCH.lagda.md:64, copied letter for letter.
ClauseTrophy : SL.S → Type (ℓ-suc ℓ)
ClauseTrophy κ = ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥

-- SPELLING B.  [LJ-1.581]'s.  The clause `SquareStepInf` adds,
-- agents/tasks/LJ-1-581/Probe581.agda:429, copied letter for letter,
-- in the library `_∈_` that file uses.
ClauseSquareStepInf : SL.S → Type (ℓ-suc ℓ)
ClauseSquareStepInf κ = ⟨ ω ∈ fst κ ⟩

-- SPELLING C.  `CodedShift`'s, src/L/CodedShift.lagda.md:38-39, copied
-- letter for letter and split into its two conjuncts.  `ωʟ` is
-- src/L/Axioms/Infinity.lagda.md:69-70.
ClauseCodedShift∉ : SL.S → Type (ℓ-suc ℓ)
ClauseCodedShift∉ γ = ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥

ClauseCodedShiftNum : SL.S → Type (ℓ-suc ℓ)
ClauseCodedShiftNum γ = (k : ℕ) → ⟨ (# k) ∈ fst γ ⟩

-- =====================================================================
-- SECTION 2.  SPELLING A AND SPELLING C's FIRST CONJUNCT ARE ONE TYPE.
--
--   Not "agree", not "are equivalent".  ONE TYPE.  `𝒮ᵥ`'s `_∈ˢ_` field
--   IS the library's `_∈_` (src/V/Hierarchy.lagda.md:83), and `ωʟ` is
--   the pair `(ω , ω∈L)` (src/L/Axioms/Infinity.lagda.md:70), so
--   `fst ωʟ` is `ω` by reduction.  Four identity functions say it,
--   rather than four sentences.
-- =====================================================================

trophy-is-codedshift∉ : (κ : SL.S) → ClauseTrophy κ → ClauseCodedShift∉ κ
trophy-is-codedshift∉ κ x = x

codedshift∉-is-trophy : (κ : SL.S) → ClauseCodedShift∉ κ → ClauseTrophy κ
codedshift∉-is-trophy κ x = x

-- And the same for the two memberships underneath them, so the reading
-- above does not rest on the negation hiding a difference.
∈ˢ-is-∈ : (a b : SL.S) → ⟨ fst a ∈ˢ fst b ⟩ → ⟨ fst a ∈ fst b ⟩
∈ˢ-is-∈ a b x = x

∈-is-∈ˢ : (a b : SL.S) → ⟨ fst a ∈ fst b ⟩ → ⟨ fst a ∈ˢ fst b ⟩
∈-is-∈ˢ a b x = x

-- =====================================================================
-- SECTION 3.  SPELLING B IS STRICTLY STRONGER, AND THE GAP IS OMEGA.
--
--   ONE DIRECTION HOLDS AND IT NEEDS NOTHING.  The other FAILS, and it
--   fails at the first infinite ordinal, which is the first instance
--   the trophy asks for.  This is the whole of the choice section
--   `## THE SPELLING I CHOSE` reports.
-- =====================================================================

-- B IMPLIES A, for every κ, with no ordinality hypothesis on κ.  If ω
-- belonged to κ and κ belonged to ω, then ω would belong to ω, because
-- ω is transitive (`ω-ord`, src/L/Ordinal.lagda.md:263-264).
squarestepinf→trophy : (κ : SL.S) → ClauseSquareStepInf κ → ClauseTrophy κ
squarestepinf→trophy κ ω∈κ κ∈ω = ∈-irrefl ω (fst ω-ord ω∈κ κ∈ω)

-- A DOES NOT IMPLY B, AND OMEGA IS THE COUNTEREXAMPLE.
-- ωʟ is an L-ordinal, so the trophy's Π genuinely reaches it.
ωʟ-ord : IsOrd (fst ωʟ)
ωʟ-ord = ω-ord

-- ωʟ satisfies spelling A.
ωʟ-trophy : ClauseTrophy ωʟ
ωʟ-trophy = ∈-irrefl ω

-- ωʟ REFUTES spelling B.
ωʟ-not-squarestepinf : ClauseSquareStepInf ωʟ → Empty.⊥
ωʟ-not-squarestepinf = ∈-irrefl ω

-- THE TWO SPELLINGS ARE NOT INTERDERIVABLE.  A term, not a sentence:
-- any function that turned spelling A into spelling B at every κ would
-- produce `⟨ ω ∈ ω ⟩` from `ωʟ-trophy`.
no-trophy→squarestepinf :
    ((κ : SL.S) → ClauseTrophy κ → ClauseSquareStepInf κ) → Empty.⊥
no-trophy→squarestepinf f = ωʟ-not-squarestepinf (f ωʟ ωʟ-trophy)

-- AND THE SAME HOLDS WITH THE ORDINALITY HYPOTHESIS ADDED, which is
-- the form the square law would actually use.  ωʟ is an ordinal, so
-- the extra hypothesis buys nothing at the site where B fails.
no-trophy→squarestepinf-ord :
    ((κ : SL.S) → IsOrd (fst κ) → ClauseTrophy κ → ClauseSquareStepInf κ)
  → Empty.⊥
no-trophy→squarestepinf-ord f =
  ωʟ-not-squarestepinf (f ωʟ ωʟ-ord ωʟ-trophy)

-- =====================================================================
-- SECTION 4.  SPELLING C's SECOND CONJUNCT IS FREE.
--
--   `CodedShift` takes `numerals` as a SEPARATE hypothesis
--   (src/L/CodedShift.lagda.md:39).  It does not have to.  Under
--   `IsOrd` and spelling A, `numerals` is a THEOREM, by trichotomy
--   (`ord-tri`, src/L/Ordinal/Linear.lagda.md:136-137).
--
--   THE CONSEQUENCE, and it is this task's main measurement: spelling
--   A and spelling C are INTERDERIVABLE under `IsOrd`, and spelling B
--   is not derivable from either.
-- =====================================================================

numerals-from-trophy :
    (γ : SL.S) → IsOrd (fst γ) → ClauseTrophy γ → ClauseCodedShiftNum γ
numerals-from-trophy γ ordγ γ∉ω k =
  go (ord-tri (# k) (numeral-ord k) (fst γ) ordγ)
  where
  go : Tri (# k) (fst γ) → ⟨ (# k) ∈ fst γ ⟩
  go (inl #k∈γ)      = #k∈γ
  go (inr (inl e))   =
    Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) e (#∈ω k)))
  go (inr (inr γ∈#k)) =
    Empty.rec (γ∉ω (numeral-mem k (fst γ) γ∈#k))

-- The other direction is the first projection and needs nothing.
trophy-from-codedshift :
    (γ : SL.S) → ClauseCodedShift∉ γ × ClauseCodedShiftNum γ → ClauseTrophy γ
trophy-from-codedshift γ (γ∉ω , _) = γ∉ω

-- SPELLING C, WHOLE, FROM SPELLING A AND `IsOrd`.
codedshift-from-trophy :
    (γ : SL.S) → IsOrd (fst γ) → ClauseTrophy γ
  → ClauseCodedShift∉ γ × ClauseCodedShiftNum γ
codedshift-from-trophy γ ordγ γ∉ω =
  γ∉ω , numerals-from-trophy γ ordγ γ∉ω

-- =====================================================================
-- SECTION 5.  ROW 5, RESTATED WITH THE CLAUSE.
--
--   ROW 5 IS `SuccIntoPower` (agents/tasks/LJ-1-558/Probe558.agda:99-102)
--   and it is `GCHStatement`'s third conjunct (src/L/GCH.lagda.md:68).
--   Its spend site is `gch-route-without-stage`
--   (Probe558.agda:118-128): the application `b10 κ δ sc` of line 128.
--
--   THREE RESTATEMENTS, because the spend site has FOUR of the
--   trophy's hypotheses in scope at that line (Probe558.agda:122 binds
--   `κ`, `ordκ`, `cardLκ` and `κ∉ω`), and the square law will want
--   different ones of them.  Each restatement is WEAKER than
--   `P558.SuccIntoPower`, so each is a smaller obligation.
-- =====================================================================

-- (i) THE MINIMAL THREAD.  The clause and nothing else.  This is the
-- type W3 wrote alone (runs/W3.agda:59-63).
SuccIntoPowerInfMin : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPowerInfMin zf =
    (κ δ : SL.S) → ClauseTrophy κ
  → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- (ii) THE FULL THREAD.  Every hypothesis `GCHStatement` puts on κ
-- (src/L/GCH.lagda.md:61-64), in that order.  This is the widest form
-- the spend site can pay for, and it is the one the obligation uses.
SuccIntoPowerInf : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPowerInf zf =
    (κ δ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → ClauseTrophy κ
  → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- (iii) THE `CodedShift` SPELLING, so that a square law proved in
-- `CodedShift`'s own idiom can be plugged in without a translation.
SuccIntoPowerCS : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPowerCS zf =
    (κ δ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → ClauseCodedShift∉ κ → ClauseCodedShiftNum κ
  → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- THE NARROWING IS A WEAKENING.  [LJ-1.558]'s row 5 pays all three,
-- so nothing that was already owed becomes harder.
wider-pays-min : (zf : ModelL.isZFModel)
  → P558.SuccIntoPower zf → SuccIntoPowerInfMin zf
wider-pays-min zf b10 κ δ _ sc = b10 κ δ sc

wider-pays-full : (zf : ModelL.isZFModel)
  → P558.SuccIntoPower zf → SuccIntoPowerInf zf
wider-pays-full zf b10 κ δ _ _ _ sc = b10 κ δ sc

wider-pays-cs : (zf : ModelL.isZFModel)
  → P558.SuccIntoPower zf → SuccIntoPowerCS zf
wider-pays-cs zf b10 κ δ _ _ _ _ sc = b10 κ δ sc

-- AND THE THREE NARROWED ROWS ARE ORDERED.  The minimal one pays the
-- full one; the full one pays the `CodedShift` one; and the
-- `CodedShift` one pays the full one BACK, by section 4.  So (ii) and
-- (iii) are the same obligation and (i) is stronger than both.
min-pays-full : (zf : ModelL.isZFModel)
  → SuccIntoPowerInfMin zf → SuccIntoPowerInf zf
min-pays-full zf b10 κ δ _ _ κ∉ω sc = b10 κ δ κ∉ω sc

full-pays-cs : (zf : ModelL.isZFModel)
  → SuccIntoPowerInf zf → SuccIntoPowerCS zf
full-pays-cs zf b10 κ δ ordκ cardLκ κ∉ω _ sc = b10 κ δ ordκ cardLκ κ∉ω sc

cs-pays-full : (zf : ModelL.isZFModel)
  → SuccIntoPowerCS zf → SuccIntoPowerInf zf
cs-pays-full zf b10 κ δ ordκ cardLκ κ∉ω sc =
  b10 κ δ ordκ cardLκ κ∉ω (numerals-from-trophy κ ordκ κ∉ω) sc

-- =====================================================================
-- SECTION 6.  THE OBLIGATION.
--
--   `GCHStatement zf` from row 4 and the hard leg UNCHANGED, and row 5
--   NARROWED.  Both unchanged rows are [LJ-1.558]'s own types, taken
--   from that task's probe and not retyped here.
--
--   READ IT AGAINST `gch-route-without-stage` (Probe558.agda:118-128).
--   The derivation is that one with a single change: `κ∉ω` is no
--   longer spent on row 4 alone; it is passed to row 5 as well.  That
--   is the thread, and it costs one application.
-- =====================================================================

row5-carries-infinity :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → P558.PowerIntoSucc zf → SuccIntoPowerInf zf
  → GCHStatement zf
row5-carries-infinity zf b4 hard b10 κ ordκ cardLκ κ∉ω =
  PT.map step (b4 κ ordκ cardLκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) = δ , sc , hard κ δ sc , b10 κ δ ordκ cardLκ κ∉ω sc

-- AND THE SAME TROPHY FROM THE OTHER TWO NARROWED ROWS, so the choice
-- between (i), (ii) and (iii) is free at the consumer.
row5-carries-infinity-min :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → P558.PowerIntoSucc zf → SuccIntoPowerInfMin zf
  → GCHStatement zf
row5-carries-infinity-min zf b4 hard b10 =
  row5-carries-infinity zf b4 hard (min-pays-full zf b10)

row5-carries-infinity-cs :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → P558.PowerIntoSucc zf → SuccIntoPowerCS zf
  → GCHStatement zf
row5-carries-infinity-cs zf b4 hard b10 =
  row5-carries-infinity zf b4 hard (cs-pays-full zf b10)

-- SECTION 7 BELOW CLOSES THE CAMPAIGN'S OWN BILL, `gch-from-five`
-- (agents/tasks/LJ-1-564/Probe564.agda:456-463), with the narrowed row
-- in its fifth place and the four other rows untouched.

-- =====================================================================
-- SECTION 7.  THE LIVE BILL STILL CLOSES WITH THE NARROWED ROW.
--
--   SECTION 6 THREADS [LJ-1.558]'s ROUTE.  That route is not the
--   campaign's bill.  The bill is `gch-from-five`
--   (agents/tasks/LJ-1-564/Probe564.agda:456-463), and it takes row 5
--   as `P558.SuccIntoPower zf` (:460).  So the thread is not finished
--   until the BILL closes with the narrowed row.  This section closes
--   it, and it changes exactly one application.
--
--   THE PRECEDENT IS IN THAT SAME FILE, AND IT IS NOT MINE.
--   [LJ-1.564] ALREADY MADE THIS MOVE ONCE, on the OTHER leg:
--   `PowerIntoSuccAt` is `PowerIntoSucc` narrowed by `IsOrd (fst κ)`
--   and by the trophy's fourth hypothesis, in those words
--   (Probe564.agda:325-330), and `gch-route-with-premised-hard`
--   (:335-345) is the type check that the route still closes.  This
--   section is that move on row 5.  Its comment at :321-322 says what
--   the check is for.
--
--   WHAT IS TAKEN FROM WHOM, AND WHAT THAT COMMITS ME TO.
--   [LJ-1.564] is GO (agents/tasks/LJ-1-564/lj-1.564-report.md:8).  Its
--   terms `power-into-succ-at`, `bounded-subset-theorem`, `b4-paid`,
--   `b6-paid`, `b7-paid` and `b8-paid` are used as that task
--   DELIVERED them.  [LJ-1.550] is NO-GO
--   (agents/tasks/LJ-1-550/lj-1.550-report.md:6).  NOTHING [LJ-1.550]
--   FAILED TO DELIVER IS USED AS A FACT HERE.  Its residues
--   `AmbientCardAtSucc`, `SqAt` and `CoHyps` appear ONLY as
--   HYPOTHESES of the statements below, exactly as they appear in
--   [LJ-1.564]'s own GO type (Probe564.agda:458-460), so this section
--   asserts nothing about their truth.
--
--   PRICE.  Importing [LJ-1.564] alone costs 37.28 s and 1.9 GB
--   maximum resident (runs/import-2.out).  It carries [LJ-1.550],
--   [LJ-1.528], [LJ-1.526], [LJ-1.543], [LJ-1.540] and [LJ-1.544].
-- =====================================================================

import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-564.Probe564 {ℓ} lem as P564

-- [LJ-1.564]'s `gch-route-with-premised-hard` (Probe564.agda:335-345)
-- with row 5 narrowed.  ONE CHARACTER GROUP CHANGES: `b10 κ δ sc`
-- becomes `b10 κ δ ordκ cardLκ κ∉ω sc`.  Every argument it gains is
-- already bound on the line above it (:339).
gch-route-with-premised-hard-inf :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → P564.PowerIntoSuccAt zf → SuccIntoPowerInf zf
  → GCHStatement zf
gch-route-with-premised-hard-inf zf b4 hard b10 κ ordκ cardLκ κ∉ω =
  PT.map step (b4 κ ordκ cardLκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) =
    δ , sc , hard κ ordκ κ∉ω δ sc , b10 κ δ ordκ cardLκ κ∉ω sc

-- [LJ-1.564]'s `gch-from-here` (Probe564.agda:367-378), rebuilt on the
-- line above.  `power-into-succ-at` is taken whole.
gch-from-here-inf :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists
  → P550.BoundedSubsetTheorem → P550.SubsetIntoStage zf
  → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → SuccIntoPowerInf zf
  → GCHStatement zf
gch-from-here-inf zf b4 bst b6 b7 b8 r1 r2 r3 b9 b10 =
  gch-route-with-premised-hard-inf zf b4
    (P564.power-into-succ-at zf bst b6 b7 b8 r1 r2 r3 b9) b10

-- [LJ-1.564]'s `gch-from-here-sharp` (Probe564.agda:408-417), rebuilt.
-- `bounded-subset-theorem` is src/'s own row and is taken whole.
gch-from-here-sharp-inf :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists
  → P550.SubsetIntoStage zf → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → SuccIntoPowerInf zf
  → GCHStatement zf
gch-from-here-sharp-inf zf b4 b6 b7 b8 r1 r2 r3 b9 b10 =
  gch-from-here-inf zf b4 P564.bounded-subset-theorem b6 b7 b8 r1 r2 r3 b9 b10

-- THE BILL.  [LJ-1.564]'s `gch-from-five` (Probe564.agda:456-463) with
-- its fifth row narrowed and its four other rows untouched.  THE BILL
-- IS STILL FIVE ROWS.  Nothing was added and nothing was widened.
gch-from-five-inf :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → SuccIntoPowerInf zf
  → GCHStatement zf
gch-from-five-inf zf r1 r2 r3 b9 b10 =
  gch-from-here-sharp-inf zf P564.b4-paid (P564.b6-paid zf) P564.b7-paid
    P564.b8-paid r1 r2 r3 b9 b10

-- AND THE OLD BILL IS A SPECIAL CASE OF THE NEW ONE, so no route that
-- reads today stops reading.  `wider-pays-full` supplies the fifth row.
gch-from-five-old-still-pays :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-five-old-still-pays zf r1 r2 r3 b9 b10 =
  gch-from-five-inf zf r1 r2 r3 b9 (wider-pays-full zf b10)

-- AND THE `CodedShift` SPELLING PAYS THE BILL TOO, by section 4.  This
-- is the line the square-law brief is aimed at: a square law proved in
-- `CodedShift`'s own idiom (src/L/CodedShift.lagda.md:37-39) closes
-- the campaign's bill with NO translation step.
gch-from-five-codedshift :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → SuccIntoPowerCS zf
  → GCHStatement zf
gch-from-five-codedshift zf r1 r2 r3 b9 b10 =
  gch-from-five-inf zf r1 r2 r3 b9 (cs-pays-full zf b10)
