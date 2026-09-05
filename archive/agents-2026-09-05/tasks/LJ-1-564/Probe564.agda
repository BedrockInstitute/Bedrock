{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.564]  `PowerIntoSucc`, the direction nobody had attempted.
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and typechecked
-- ALONE.  That slice is kept at agents/tasks/LJ-1-564/runs/W3.agda and
-- its run is agents/tasks/LJ-1-564/runs/w3-1.out.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-564.Probe564 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Axioms.Basic {ℓ} using ( isL-Lset )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

-- THE TWO PREDECESSORS, BY THE TYPE EACH ONE DELIVERED.
-- [LJ-1.558] is GO (agents/tasks/LJ-1-558/lj-1.558-report.md:1) and
-- [LJ-1.550] is NO-GO on its own obligation only
-- (agents/tasks/LJ-1-550/lj-1.550-report.md:16): the module is green
-- and `bridge-without-B5` is simply absent from it, so every type and
-- every term named below typechecks in its own file.
import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-558.Probe558 {ℓ} lem as P558
-- THE FOUR ROWS OTHER TASKS HAVE ALREADY PAID.  Each is taken as the
-- TYPE ITS OWN REPORT DELIVERED, and each of the four reports is GO:
-- [LJ-1.528] (lj-1.528-report.md:17), [LJ-1.543] (:32),
-- [LJ-1.540] (:29), [LJ-1.544] (:39).
import LJ-1-528.Probe528 {ℓ} lem as P528
import LJ-1-543.Probe543 {ℓ} lem as P543
import LJ-1-540.Probe540 {ℓ} lem as P540
import LJ-1-544.Probe544 {ℓ} lem as P544

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier.  `Lset` and the ambient membership live here.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier.  `GCHStatement` lives here.
module SL = hPropStructure 𝒮ʟ
-- The same instance src/L/GCH.lagda.md:30 names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  CAN `InjCode` BE STATED WITH `𝒫 κ` AS ITS SOURCE?
--
--   The brief names this as the widest unmeasured term and orders it
--   written first and typechecked alone.  It was:
--   agents/tasks/LJ-1-564/runs/W3.agda, exit 0, 1.45 s
--   (agents/tasks/LJ-1-564/runs/w3-1.out).
--
--   THE ANSWER IS YES AND IT IS FREE.  `InjCode : S → S → S → Type`
--   (src/L/Cardinal.lagda.md:223) and `𝒫 : S → S`
--   (src/FOL/ZFModel.lagda.md:287) are at the SAME `S`, the L-carrier's
--   (src/L/GCH.lagda.md:27).  No coercion, no side condition, no
--   constructibility premise about `𝒫 κ`: it is an L-element by
--   construction, because `𝒫` is a field of `ModelL.isZFModel`.
-- =====================================================================

CodeAtPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
CodeAtPower zf = (κ δ F : SL.S) → InjCode F (𝒫 κ) δ
  where open ModelL.isZFModel zf using ( 𝒫 )

-- The obligation's own type, which is `[LJ-1.558]`'s hypothesis 2
-- (agents/tasks/LJ-1-558/Probe558.agda:93-96) copied letter for letter,
-- and `GCHStatement`'s second conjunct (src/L/GCH.lagda.md:67).
PowerIntoSucc : ModelL.isZFModel → Type (ℓ-suc ℓ)
PowerIntoSucc zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL (𝒫 κ) δ
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 2.  THE SIX RESIDUES OF `[LJ-1.550]`, COPIED LETTER FOR
-- LETTER, AND THE TWO `[LJ-1.558]` LEFT ON THE ROUTE.
--
--   [LJ-1.550] closed the bridge from nine inputs and SIX residues
--   (Probe550.agda:301-333).  [LJ-1.558] collapsed the join and left
--   `stage-is-one-middle` (Probe558.agda:229-253) standing on four:
--   `StageLanding`, `StageIsL`, `InclusionCoded`, `StageCountedCoded`,
--   plus `InjLTrans` for the composite (Probe558.agda:175-183).
--
--   THIS SECTION ONLY STATES THEM.  Section 3 pays three from src/.
-- =====================================================================

-- [LJ-1.558]'s `StageLanding` (Probe558.agda:59-64), which is
-- [LJ-1.550]'s `UseSite.member-in-stage` (Probe550.agda:257-261) as a
-- type.  This is the bounded subset theorem AT THE USE SITE.
StageLanding : ModelL.isZFModel → Type (ℓ-suc ℓ)
StageLanding zf =
    (κ δ : SL.S) → SuccCardL δ κ
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

-- R4 (Probe550.agda:317-318, Probe558.agda:212-213).
StageIsL : Type (ℓ-suc ℓ)
StageIsL = (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩

-- R5 (Probe550.agda:324-327, Probe558.agda:216-219).
InclusionCoded : Type (ℓ-suc ℓ)
InclusionCoded = (a b : SL.S)
               → ((z : SV.S) → ⟨ z ∈ˢ fst a ⟩ → ⟨ z ∈ˢ fst b ⟩)
               → InjL a b

-- R6 (Probe550.agda:332-333, Probe558.agda:161-162).
InjLTrans : Type (ℓ-suc ℓ)
InjLTrans = (a b c : SL.S) → InjL a b → InjL b c → InjL a c

-- B9 (Probe523.agda:258-261, Probe558.agda:222-225).
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- =====================================================================
-- SECTION 3.  src/ PAYS THREE OF THE FIVE, AND NONE OF THE THREE IS A
-- HYPOTHESIS ANY MORE.
--
--   [LJ-1.550] recorded R5 and R6 as residues, and its own comments say
--   why: "The only producers of `InjCode` in src/ are
--   src/L/Absorption.lagda.md:614 and src/L/CodedShift.lagda.md:40, and
--   both deliver the single shape `InjCode F (sucʟ γ) γ`"
--   (Probe550.agda:322-323), and "src/L/CantorBernstein.lagda.md is the
--   only consumer of `InjL` in src/ and it delivers
--   `mutual-inj→bijection` (:51-55), not transitivity"
--   (Probe550.agda:329-331).
--
--   BOTH SEARCHES MISSED `src/L/InjChain.lagda.md`.  That master
--   produces the FOUR CONJUNCTS, not an `InjCode` value and not an
--   `InjL` value, so neither grep reached it.  Its row 1
--   (src/L/InjChain.lagda.md:313-434) is the composite of two coded
--   injections and its row 3 (:463-598) is the inclusion of one set into
--   another, carved.  Both deliver `sv`, `dm`, `ij` and `ran` at the
--   exact frame `InjCode` names (src/L/Cardinal.lagda.md:223-228).
-- =====================================================================

-- R4 IS PAID.  src/L/Axioms/Basic.lagda.md:156.
stage-is-L : StageIsL
stage-is-L δ ordδ = isL-Lset (fst δ) ordδ

-- R5 IS PAID.  src/L/InjChain.lagda.md:575-598.  `InclGraph`'s `sub`
-- parameter (:576) is `(z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩`, and
-- `𝒮ᵥ`'s `_∈ˢ_` IS `_∈_` (src/V/Hierarchy.lagda.md:81), so the two
-- statements are the same type and no conversion is written here.
inclusion-coded : InclusionCoded
inclusion-coded a b sub = ∣ I.G , (I.sv , I.dm , I.ij , I.ran) ∣₁
  where module I = InclGraph a b sub

-- R6 IS PAID.  src/L/InjChain.lagda.md:314-434.
injl-trans : InjLTrans
injl-trans a b c = PT.rec2 PT.squash₁ step
  where
  step : Σ[ F ∈ SL.S ] InjCode F a b
       → Σ[ H ∈ SL.S ] InjCode H b c
       → InjL a c
  step (F , svF , dmF , ijF , ranF) (H , svH , dmH , ijH , ranH) =
    ∣ K.K , (K.svK , K.dmK , K.ijK , K.ranK) ∣₁
    where
    module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.
--
--   `power-into-succ`, which is `PowerIntoSucc zf` of section 1, under
--   the TWO hypotheses section 3 did not pay.  The brief permits a row
--   that lands under named hypotheses and forbids a row that stalls
--   trying to kill them: "A row that lands under two named hypotheses
--   is a result; a row that stalls trying to kill them is not."
--
--   THE TWO ARE NOT `levelIn` AND `cover`.  The brief guessed those.
--   `levelIn` and `cover` (src/L/BoundedSubset.lagda.md:1555-1558) are
--   two of the SIX inputs `StageLanding` is built from, and section 5
--   prices that reduction.  What this term carries is `StageLanding`
--   itself and `StageCountedCoded`.
--
--   READ THE SHAPE AGAINST [LJ-1.550].  `bridge-with-residues`
--   (Probe550.agda:335-362) built the same arrow from THIRTEEN inputs.
--   Six of the thirteen were residues, and three of the six are now
--   section 3's theorems rather than anyone's hypothesis.
-- =====================================================================

-- THE ENGINE, AT ONE PAIR.  The landing is asked for at THIS κ and THIS
-- δ and nowhere else, so section 6 can feed it from a producer that
-- needs premises about κ.  R4, R5 and R6 are section 3's theorems and
-- appear in no hypothesis slot.
power-into-succ-from-landing :
    (zf : ModelL.isZFModel) → StageCountedCoded
  → (κ δ : SL.S) → SuccCardL δ κ
  → ((y : SL.S) → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
                → ⟨ fst y ∈ˢ Lset (fst δ) ⟩)
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
power-into-succ-from-landing zf b9 κ δ sc land =
  injl-trans (𝒫 κ) Lδ δ (inclusion-coded (𝒫 κ) Lδ into) (b9 δ Lδ ordδ refl)
  where
  open ModelL.isZFModel zf using ( 𝒫 )

  ordδ : IsOrd (fst δ)
  ordδ = fst sc

  -- R4, paid at section 3.
  Lδ : SL.S
  Lδ = Lset (fst δ) , stage-is-L δ ordδ

  -- Every member of the model's power set is constructible, because L
  -- is transitive (src/L/Constructible.lagda.md:379).  The same step
  -- [LJ-1.550] takes at Probe550.agda:356 and [LJ-1.558] at
  -- Probe558.agda:252.
  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ = land (z , isL-trans z∈ (snd (𝒫 κ))) z∈

-- THE OBLIGATION.
power-into-succ :
    (zf : ModelL.isZFModel)
  → StageLanding zf → StageCountedCoded
  → (κ δ : SL.S) → SuccCardL δ κ
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
power-into-succ zf land b9 κ δ sc =
  power-into-succ-from-landing zf b9 κ δ sc (land κ δ sc)

-- THE OBLIGATION IS `PowerIntoSucc` AND NOT A NEIGHBOUR OF IT.  This
-- line is the type check that says so: it is section 1's type, filled by
-- the term above, with no argument of its own beyond the two carried
-- hypotheses.
power-into-succ-is-the-conjunct :
    (zf : ModelL.isZFModel)
  → StageLanding zf → StageCountedCoded → PowerIntoSucc zf
power-into-succ-is-the-conjunct = power-into-succ

-- =====================================================================
-- SECTION 5.  D-10.  DOES THIS ROW NEED THE BOUNDED SUBSET THEOREM?
--
--   THE BRIEF ORDERS THIS ANSWERED BEFORE ANY AGDA, AT `file:line`, AND
--   IT IS ANSWERED HERE MECHANICALLY RATHER THAN IN A SENTENCE.
--
--   `[LJ-1.543]` found that a sibling row, B6, does NOT need the
--   theorem: `SubsetIntoStage` costs 9 lines
--   (agents/tasks/LJ-1-543/Probe543.agda:125-130).  The brief tells this
--   row to check before it assumes.
--
--   THE CHECK IS THE TYPE AND THE ANSWER IS YES, THE THEOREM IS NEEDED.
--   B6 is not an alternative to the theorem.  **B6 IS ONE OF THE
--   THEOREM'S OWN INPUT SLOTS**, `x⊆Lα` at
--   src/L/BoundedSubset.lagda.md:1390, and `t-x-slot` below is that slot
--   copied letter for letter.  `b6-fills-the-slot` is the one line that
--   says so, and [LJ-1.550] already spends B6 exactly there
--   (Probe550.agda:265, `x⊆ = b6 κ y ordκ y∈`).
--
--   THE DIFFERENCE IS WHICH OBJECT GETS PLACED.  B6 places `z` where
--   `z ∈ y ∈ 𝒫 κ`, and such a `z` is an ORDINAL BELOW κ, which the
--   tower places with no theorem.  `StageLanding` places `y` ITSELF,
--   and `y` is a SUBSET of κ and not a member of it.  Nothing in the
--   tower places a subset; that it appears below δ = κ⁺ is the
--   condensation content of
--   `Devlin55.BoundedSubsetAt.Co.theorem : ⟨ x ∈ˢ Lset κ ⟩`
--   (src/L/BoundedSubset.lagda.md:1621).
--
--   AND THE TWO HYPOTHESES THE BRIEF NAMED ARE CARRIED, NOT DISCHARGED.
--   `levelIn` and `cover` are `Co`'s parameters
--   (src/L/BoundedSubset.lagda.md:1555-1558).  They are two of the
--   THREE slots [LJ-1.550]'s nine inputs cannot fill
--   (Probe550.agda:250-256), where they travel as `CoHyps`
--   (Probe550.agda:215-230).  Section 6 carries them by that name and
--   does not try to kill them, as the brief orders.
-- =====================================================================

-- B6's type, [LJ-1.543]'s `SubsetIntoStageAt` (Probe543.agda:119-123),
-- which is [LJ-1.523]'s (Probe523.agda:224-228), copied letter for
-- letter.  [LJ-1.543]'s report is GO, so this row is PAID.
SubsetIntoStage : ModelL.isZFModel → Type (ℓ-suc ℓ)
SubsetIntoStage zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

-- THE THEOREM'S `x⊆Lα` SLOT (src/L/BoundedSubset.lagda.md:1390),
-- copied letter for letter at (x := fst y, α := fst κ).
t-x-slot : SV.S → SV.S → Type (ℓ-suc ℓ)
t-x-slot x α = (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩

-- D-10, ANSWERED BY THE ELABORATOR.  The cheap row FILLS a slot of the
-- theorem.  It does not replace the theorem.
b6-fills-the-slot :
    (zf : ModelL.isZFModel) → SubsetIntoStage zf
  → (κ y : SL.S) → IsOrd (fst κ)
  → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
  → t-x-slot (fst y) (fst κ)
b6-fills-the-slot zf b6 κ y ordκ y∈ = b6 κ y ordκ y∈

-- =====================================================================
-- SECTION 6.  THE WHOLE REMAINING BILL, IN ONE TYPE.
--
--   Section 4 carries `StageLanding` as one opaque hypothesis.  That is
--   honest but it is not USEFUL to the next brief, because nobody can
--   read a price off it.  This section replaces it by the rows that
--   produce it, so the bill is a list of NAMED predecessor types and
--   the elaborator, not this file, decides that the list is complete.
--
--   ONE WEAKENING IS NEEDED AND IT IS FREE.  The producer of the
--   bounded subset theorem's use site needs `IsOrd (fst κ)` and
--   `κ ∉ ω` (Probe550.agda:232-237), and `SuccCardL δ κ` carries
--   neither (src/L/GCH.lagda.md:46-53).  `GCHStatement` binds both at
--   its own head (src/L/GCH.lagda.md:60-62), so a producer may ask for
--   them: `PowerIntoSuccAt` is `PowerIntoSucc` with those two premises,
--   and `gch-route-with-premised-hard` is the type check that says the
--   route still closes with the weaker row in hypothesis 2's place.
-- =====================================================================

-- `PowerIntoSucc` with the two premises `GCHStatement` already binds.
-- `IsCardinalL κ` is NOT asked for: the route does not need it here.
PowerIntoSuccAt : ModelL.isZFModel → Type (ℓ-suc ℓ)
PowerIntoSuccAt zf =
    (κ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (δ : SL.S) → SuccCardL δ κ → InjL (ModelL.isZFModel.𝒫 zf κ) δ

-- The premised row is enough for the target.  [LJ-1.558]'s
-- `gch-route-without-stage` (Probe558.agda:118-128) with hypothesis 2
-- weakened, and hypotheses 1 and 3 taken from [LJ-1.558] itself.
gch-route-with-premised-hard :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → PowerIntoSuccAt zf → P558.SuccIntoPower zf
  → GCHStatement zf
gch-route-with-premised-hard zf b4 hard b10 κ ordκ cardLκ κ∉ω =
  PT.map step (b4 κ ordκ cardLκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) = δ , sc , hard κ ordκ κ∉ω δ sc , b10 κ δ sc

-- THE ROW, FROM NAMED PREDECESSOR ROWS AND NOTHING ELSE.  Eight
-- hypotheses.  Four of the eight are [LJ-1.523]'s inputs, three are
-- [LJ-1.550]'s residues R1, R2 and R3, and one is B9.  R4, R5 and R6
-- are NOT here: section 3 pays them out of src/.
power-into-succ-at :
    (zf : ModelL.isZFModel)
  → P550.BoundedSubsetTheorem → P550.SubsetIntoStage zf
  → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → StageCountedCoded
  → PowerIntoSuccAt zf
power-into-succ-at zf bst b6 b7 b8 r1 r2 r3 b9 κ ordκ κ∉ω δ sc =
  power-into-succ-from-landing zf b9 κ δ sc
    (U.member-in-stage (r1 κ δ sc) (r2 κ ordκ) r3)
  where
  module U = P550.UseSite zf bst b6 b7 b8 κ δ ordκ κ∉ω sc

-- AND THE TARGET, FROM THE SAME LIST PLUS THE TWO ROWS THIS BRIEF DOES
-- NOT TOUCH.  READ THE HYPOTHESIS LIST: it is the campaign's remaining
-- bill for `GCHStatement`, with nothing hidden inside a `StageLanding`.
gch-from-here :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists
  → P550.BoundedSubsetTheorem → P550.SubsetIntoStage zf
  → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-here zf b4 bst b6 b7 b8 r1 r2 r3 b9 b10 =
  gch-route-with-premised-hard zf b4
    (power-into-succ-at zf bst b6 b7 b8 r1 r2 r3 b9) b10

-- =====================================================================
-- SECTION 7.  src/ PAYS A FOURTH ROW, AND IT IS THE THEOREM ITSELF.
--
--   `[LJ-1.550]` carries `BoundedSubsetTheorem` as an INPUT
--   (Probe550.agda:337) and `[LJ-1.523]` carried it before that.  But
--   the type is `Tele.At` over the telescope (Probe550.agda:130-141),
--   and `Tele.At` is DEFINED as
--   `LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩` (Probe550.agda:114-115) at
--   `Tele.BSA = Devlin55.BoundedSubsetAt` applied to the same telescope
--   (Probe550.agda:102-103).  That is exactly
--   `Devlin55.BoundedSubsetAt.Co.theorem` with `Co`'s two parameters
--   still to the left (src/L/BoundedSubset.lagda.md:1555-1621).
--
--   SO THE ROW IS A THEOREM OF src/ AND NOT A HYPOTHESIS OF ANYBODY.
--   The line below is the whole proof.
-- =====================================================================

bounded-subset-theorem : P550.BoundedSubsetTheorem
bounded-subset-theorem κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq
                       x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ =
  T.BSA.Co.theorem
  where
  module T = P550.Tele κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq
                       x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

-- THE BILL, WITH EVERY ROW src/ CAN PAY REMOVED.  Nine hypotheses in
-- section 6, EIGHT here.  Compare it with `bridge-with-residues`
-- (Probe550.agda:335-339), which needed thirteen.
gch-from-here-sharp :
    (zf : ModelL.isZFModel)
  → P558.SuccCardExists
  → P550.SubsetIntoStage zf → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-here-sharp zf b4 b6 b7 b8 r1 r2 r3 b9 b10 =
  gch-from-here zf b4 bounded-subset-theorem b6 b7 b8 r1 r2 r3 b9 b10

-- =====================================================================
-- SECTION 8.  THE ROWS ALREADY PAID, PLUGGED IN AND NOT QUOTED.
--
--   The brief orders `## HOW FAR GCHStatement NOW IS` to COUNT and not
--   to estimate.  A count read off a table of other people's reports is
--   still a reading.  These four lines make the elaborator do the
--   counting: each plugs a predecessor's delivered TERM into the slot
--   this route asks for, and a mismatch of even one implicit would be
--   exit 42.
--
--   B4 IS PAID AND THE BRIEF'S CITATION FOR IT IS OFF.  Premise 4 gives
--   `agents/tasks/LJ-1-528/Probe528.agda:638`, and that line is
--   `CardAboveL`, which is SOME cardinal above κ with no leastness
--   conjunct.  `SuccCardExists` is `Probe528.agda:696-697`,
--   `succCardExists = P526.reduction CardAboveL`.  The premise is TRUE;
--   the line is 58 lines early.
-- =====================================================================

-- B4.  [LJ-1.528] (Probe528.agda:696-697), through [LJ-1.526]'s
-- reduction (Probe526.agda:285).
b4-paid : P558.SuccCardExists
b4-paid = P528.succCardExists

-- B6.  [LJ-1.543] (Probe543.agda:125-130).
b6-paid : (zf : ModelL.isZFModel) → P550.SubsetIntoStage zf
b6-paid = P543.SubsetIntoStage

-- B7.  [LJ-1.540] (Probe540.agda:359-364).
b7-paid : P550.AbsorbsAt
b7-paid = P540.AbsorbsAt

-- B8.  [LJ-1.544] (Probe544.agda:225-228).
b8-paid : P550.LimitAbove
b8-paid = P544.limitAbove

-- THE CAMPAIGN'S REMAINING BILL FOR `GCHStatement`, AND IT IS FIVE ROWS.
-- Nothing here is quoted from a report: every row above became a term.
gch-from-five :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-five zf r1 r2 r3 b9 b10 =
  gch-from-here-sharp zf b4-paid (b6-paid zf) b7-paid b8-paid r1 r2 r3 b9 b10
