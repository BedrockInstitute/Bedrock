# [LJ-1.299] report: build `noinj²`, the last row of `Init`

tier: pi (pi-subagent-mode), model `glm-5.3`. A PROBE: nothing lands, all
work in `agents/tasks/LJ-1-299/`. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**CIRCULAR**, with a second, deeper wall behind it, and ONE cross-cutting
find outside the target.

1. **The circularity the brief anticipated is REAL.** `noinj²` at κ needs
   the square law at every infinite β ∈ˢ κ. `SqShape`-below-κ is exactly
   `[LJ-1.8]`'s undischarged hypothesis. **The tree's only delivered route
   to a square at an ordinal is `via-col-square`, which consumes `Init`,
   whose fourth row is `noinj²` at that same ordinal.** Section 3.
2. **The deeper wall: even with the square law HANDED OVER, `IsCardinalL`
   cannot close it.** My probe `NoInj2.agda` PROVES the target from the
   square law plus the AMBIENT cardinal `IsCardinal`
   (`src/L/BoundedSubset.lagda.md:1047`) outright, and reduces the
   as-stated target to ONE named hole, the ambient-to-code bridge
   `AmbientToCode`. That bridge is the REVERSE of the move `[LJ-1.294]`
   priced, and it has NO finite price: it is MEASURED absent from the
   tree, and INFERRED false as mathematics (an ambient injection's graph
   need not be constructible; `IsCardinalL` says nothing about ambient
   injections). Sections 3 and 4.
3. **THE CROSS-CUTTING FIND, MEASURED: `SqShape` as written is NOT the
   square law.** At `src/L/GCH.lagda.md:47` the body reads
   `⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫` with no parentheses around the
   product. `_↪_` (`src/L/Cardinal.lagda.md:47`) carries NO fixity
   declaration, so it binds tighter than `infixr 5 _×_`
   (`Cubical.Data.Sigma.Base:25`), and the body parses as
   `⟪α⟫ × (⟪α⟫ ↪ ⟪α⟫)`: **an element of the carrier PAIRED WITH a
   self-injection.** My probe `Mini.agda` MEASURES both facts: `.snd` of
   the hypothesis is a self-injection, and the hypothesis is inhabited
   OUTRIGHT (an element exists by trichotomy, the identity is the
   self-injection). **The trophy's ONE remaining hypothesis, as written
   today, gates NOTHING.** The fix is one pair of parentheses. Section 5.

**`Init κ` is NOT constructible at the use site from the hypotheses
`GCHStatement` gives.** Rows 1 and 2 stand ([LJ-1.294]), row 3 stands
(`κ-limit`), row 4 does not follow from `IsCardinalL κ` by any device the
tree holds, and the missing strength is exactly the ambient-against-coded
cardinal split. Section 6.

**The `InjCode`-to-`↪` move cost, priced:** the direction `[LJ-1.294]`
used (code to ambient, `Small`) is delivered and costs nothing. The
direction THIS task needs (ambient to code) costs INFINITY as a lemma:
nothing in the tree builds it and standard semantics says it is not
provable. The corrected target replaces it with the ambient cardinal
face, where the proof is three lines. Section 3.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap
never raised. **MEASURED FALSE: a wall.** Longest single invocation
3.589 s (a rejected intermediate). **MEASURED FALSE: a heap exhaustion.**
No kill, no interrupt. The machine was NOT quiet: a sibling task held an
Agda slot and the 1-minute load moved between 5.89 and 7.59 during the
kept runs. Every absolute figure below carries its load.

| run | exit | elapsed s | 1-min load |
|---|---:|---:|---:|
| Mini.agda, parse tests green | 0 | 2.392 | 6.3 |
| NoInj2.agda, all three parts green | 0 | 3.432 | 6.00 |
| NoInj2.agda cold caliber (own `.agdai` deleted) | 0 | 3.412 | 5.92 |

## 2. THE OBJECT, AND THE USE SITE (C-44 readings, verified)

1. **"`Init` is four parts, the fourth being `noinj²`."** VERIFIED,
   `src/L/Ordinal/SquareLaw.lagda.md:688-702`. The chapter's `S` is the
   V-carrier (`open hPropStructure 𝒮ᵥ`, `:64`), so at the use site α is
   `fst κ` and β ranges over `V ℓ`.
2. **"`IsCardinalL` says no smaller ordinal admits a coded injection
   back."** VERIFIED, `src/L/Cardinal.lagda.md:230-233`: for δ with
   `fst δ ∈ fst κ`, no `∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁`. `InjCode`'s F
   ranges over L-ELEMENTS only. **MEASURED: `InjCode` occurs in exactly
   ONE file in `src/`** (`src/L/Cardinal.lagda.md`; grep over all
   masters). No other master consumes it.
3. **"`InjChain` row 1 is the composition of two injections; the
   composition you need may already be there."** READ, whole file. Row 1
   (`Comp`, `src/L/InjChain.lagda.md:314-455`) composes two CODED graphs
   and reads the composite back by `Small`. **It does not apply here:**
   my f is AMBIENT, not coded, so there is no second graph to compose
   with, and the composite the target needs runs ambient-graph-ambient,
   a shape row 1 does not have. Row 3 (`OrdIncl`) codes inclusions
   between ordinal carriers; row 5 is `squareω : sq ω` (`:184-185`), the
   base of the square law.
4. **"If the square of an infinite β injects into β, the two are
   bridgeable and `IsCardinalL` should close it."** HALF VERIFIED. The
   bridge half is PROVED (`noinj²-code` in my probe): square law plus
   ONE hole closes it. The `IsCardinalL` half is REFUTED: the hole is
   the ambient-to-code bridge, and no square-law strength can fill it.
   Section 3.
5. **How `noinj²` is consumed inside the chapter**, a reading the brief
   did not ask for, load-bearing for the corrected target: at
   `src/L/Ordinal/SquareLaw.lagda.md:876`, `noinj²` is applied at
   β = `sucV (γp p)`, a SUCCESSOR member, with a SPECIFIC composite
   `comp₀` built from the column construction's own descent data
   (`:837-854`), not an arbitrary ambient function. The row's
   mathematical content at the use site is thus consumed through
   constructible-shaped data; the AMBIENT generality of the row is what
   the use site cannot supply.

## 3. THE TERM, AND THE TERM I COULD NOT WRITE (C-36)

The probe is `agents/tasks/LJ-1-299/NoInj2.agda`, green, exit 0. It
holds, in order:

- `NoInj²`, the row verbatim at α = `fst κ` (`:55-60`).
- `ω∈β→β∉ω` (`:65-66`): an infinite member of an ordinal is outside ω,
  by the ordinal's own transitivity and `∈-irrefl`.
- `SqAll` (`:75-78`): the square law handed over, `SqShape`'s INTENDED
  body at the V-carrier, with the parentheses `GCH.lagda.md:47` lacks.
- `κ→β` (`:82-95`): the composite, κ into the member's square, then the
  square into the member. **Three lines of content once the square law
  is handed over: this is the whole descent.**
- **PART 1, `amb→code` (`:103-111`):** `IsCardinal (fst κ) →
  IsCardinalL κ`, by the `Small` readback. **The two cardinal faces are
  provably related in ONE direction.** This is also the FIRST crossing
  of the two faces in the tree; the two `_↪_` definitions
  (`src/L/Cardinal.lagda.md:45-47` and
  `src/L/BoundedSubset.lagda.md:1042-1044`) are judgmentally the same
  type, MEASURED by the green check.
- **PART 2, `noinj²-amb` (`:119-123`): THE CORRECTED TARGET, PROVED.**
  `SqAll → IsCardinal (fst κ) → NoInj² κ`. The ambient face refutes the
  composite directly. No coded world is entered.
- **PART 3, `noinj²-code` (`:135-149`): THE TARGET AS STATED, REDUCED.**
  `SqAll → AmbientToCode → IsCardinalL κ → NoInj² κ`, where
  `AmbientToCode` (`:131-133`) is the named hole:
  `(a b : S) → (⟪ fst a ⟫ ↪ ⟪ fst b ⟫) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`.
  **THE TERM I COULD NOT WRITE** is any inhabitant of `AmbientToCode`
  feeding `noinj²-code` without PART 2's ambient hypothesis: it would
  have to code an arbitrary ambient function's graph as an L-element,
  and no tree device takes an ambient function as input (MEASURED by
  grep: every code in the tree is carved by separation over a FORMULA;
  `Comp`, `Carve`, `ShiftGraph` and `Small` all build or read codes from
  constructible data only).

**Why PART 3's hole has no price, INFERRED from standard semantics:**
`IsCardinalL` refutes CODED injections; `noinj²`'s f is AMBIENT. In a
model of ZF in which an L-cardinal κ is collapsed (a Levy collapse of
`ω₁^L`), `IsCardinalL κ` holds, rows 1 to 3 of `Init κ` hold, and an
internal injection κ → ω exists, which reads back along the
`Extract`-pattern to an ambient f : ⟪κ⟫ → ⟪ω⟫ × ⟪ω⟫; row 4 is FALSE
there. So the implication "rows 1 to 3 plus `IsCardinalL` give row 4"
is not a valid implication of ZF. This is a reading of the standard
forcing semantics, not a construction inside this development's term
model; it is marked INFERRED. What it prices: no proof assembled only
from the tree's internal-ZF devices (separation, stages, condensation)
can close PART 3's hole, and the fix belongs in the STATEMENT, not in
the proofs.

## 4. D-10: THE TRUTH AT THE USE SITE

**Row 4 at κ is TRUE for every AMBIENT cardinal.** PROVED in the probe:
PART 2. **Row 4 at κ is not a consequence of `IsCardinalL κ`.**
MEASURED as to the tree (PART 3's hole), INFERRED as to mathematics
(section 3's collapse argument). The corrected target is PART 2's
hypothesis set: the square law below κ, and κ ambiently initial over
its members, which `IsCardinal` states exactly and
`LeastCardInjL.κ-min-at` (`src/L/Cardinal.lagda.md:140-142`) supplies at
the canonical least cardinal. **`[LJ-1.286]`'s method, applied here: the
row is false on a domain the use site does not exclude** (collapsed
L-cardinals, INFERRED), so the use site must either carry the ambient
face or construct κ by `LeastCardInjL`, never accept a bare
`IsCardinalL` κ where an ambient refutation is owed.

## 5. THE `SqShape` MIS-PARSE (C-42 sweep included)

- **MEASURED: `Mini.agda` testA.** `sq α oα h .snd : ⟪ α ⟫ ↪ ⟪ α ⟫`
  typechecks, so the body at `src/L/GCH.lagda.md:47` parses as
  `⟪ fst α ⟫ × (⟪ fst α ⟫ ↪ ⟪ fst α ⟫)`.
- **MEASURED: `Mini.agda` trivialSq.** The parsed hypothesis is
  inhabited outright: `mem` gives `(# 0) ∈ˢ α` for every α outside ω by
  `ord-tri`, `fiber` gives the carrier element, the identity is the
  self-injection.
- **THE SWEEP (C-42), MEASURED by grep over `src/`:** the ambiguous
  shape `A × B ↪ C` occurs at exactly ONE site, `src/L/GCH.lagda.md:47`
  itself. Every other ×-↪ co-occurrence is parenthesized
  (`GCH.lagda.md:71,86`), inside an explicit Σ
  (`SquareLaw.lagda.md:686-687`, `StageCardinal.lagda.md:17-19`,
  `BoundedSubset.lagda.md:1386-1390`), or a `⟪ M ⟫↪ m` application.
  `AbsorbsShape` (`GCH.lagda.md:49-53`) carries no product and is SAFE.
- **The fix:** parentheses at one line. It touches one master, `GCH`,
  which the probe did not edit. **Until it lands, any proof of
  `GCHStatement` could discharge `sq` with `trivialSq` and bypass the
  square law entirely**; that hole is in the statement, not in any
  proof.

## 6. IS `Init κ` CONSTRUCTIBLE AT THE USE SITE?

**NO, not from the hypotheses `GCHStatement` supplies, and the debt is
now correctly located.**

| `Init κ` row | status |
|---|---|
| `IsOrd κ` | GIVEN by `GCHStatement` |
| `⟨ ω ∈ˢ κ ⟩` | derivable under the κ ≠ ω split ([LJ-1.294] section 6) |
| successor closure | PROVED, `κ-limit` ([LJ-1.294]) |
| `noinj²` | **NOT from `IsCardinalL`. PROVED from `IsCardinal (fst κ)` + `SqAll`** (PART 2) |

**The corrected plan for `[LJ-1.8]`:** prove `SqAll` (the parenthesized
square law) by `∈ˢ`-descent, then instantiate row 4 through PART 2 at
the ambient face. The descent's successor case is delivered
(`absorbs`, `src/L/Absorption.lagda.md:613-618`, plus composition), its
base is delivered (`squareω`, `src/L/InjChain.lagda.md:184-185`), and
its cardinal case is PART 2 plus `κ-min-at` at a `LeastCardInjL`
cardinal. What is NOT delivered: the descent's well-founded recursion
itself, and one decision the probe surfaced: `LeastCardInjL.κ-inj` is
TRUNCATED (`∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁`,
`src/L/Cardinal.lagda.md:121-122`) while `SqAll` is not, so the
reduction `sq α` from `sq (init α)` cannot extract the componentwise map
without a propositional target. Either `SqShape` is restated truncated
or the least-cardinal chapter exports an untruncated witness. That
decision is `[LJ-1.8]`'s to make, not this probe's.

## 7. THE HOME, AND DD4 (C-46, P-k)

**DD4: maximize the code the two proofs share, and write it generic.**
My terms are generic: `NoInj²` names no tower, no stage and no
presentation; `κ→β` quantifies over κ and β; PART 1 and PART 2 name no
L-axiom.

**MY AXIS IS AC-AGAINST-GCH (C-46), DD4's own**, fixed in code at
`scripts/measure/ledger.py`. Today's `--reuse` print: AC closure 73
masters / 17,197 lines, GCH 51 / 9,967, SHARED 44 / 7,632, share 39.1%
of 19,532.

**P-k: the home under the consumer.** The corrected lemma (PART 2's
body) consumes `IsCardinal` (local to `L.BoundedSubset`), `SqAll` (a
hypothesis, no import) and `IsOrd` (already imported). Its consumers are
the `[LJ-1.8]` descent and, through it, `L.GCH`. **`L.Cardinal` is
impossible: it does not know the square hypothesis, and the lemma's
consumers sit above `L.BoundedSubset`'s chapter anyway.** The natural
home is **`src/L/BoundedSubset.lagda.md`, beside `Devlin55` and
`IsCardinal`**, whose `sq` parameter (`:1386-1390`) already carries my
`SqAll`'s window form. PART 2's landing needs NO import widenings;
PART 1's landing adds two (`L.Cardinal`, `L.Coding.Injection`; neither
imports `L.BoundedSubset`, so no cycle, MEASURED by their import lists).
The mis-parse fix belongs in `src/L/GCH.lagda.md:47` alone.

**DD4 effect, MEASURED for the boundary, INFERRED for the figure:**
landing in `L.BoundedSubset` touches no AC-closure master; the GCH
closure grows by the landing and the share FALLS, for the structural
reason `[LJ-1.286]` section 8 and `[LJ-1.294]` section 8 recorded: the
GCH trophy owes GCH-specific mathematics and none of it is AC's. The
lemma cannot raise the shared figure in principle: `IsCardinal`'s only
consumer today is `Devlin55` (`src/L/BoundedSubset.lagda.md:1386`),
GCH-side. **The share figure will point the wrong way at this landing
too; read the SHARED row.**

**Price, one best-effort number (DD8), basis: the probe itself.** The
landing of PARTS 1 and 2 into `L.BoundedSubset` costs about 55 non-blank
lines (the probe's 125 non-blank lines minus its header, the row-verbatim
block and PART 3, which names the hole rather than landing), plus the
two import widenings. The `SqShape` parenthesis costs one line in
`L.GCH`.

## 8. TIMING AND SIZE (DD24, DD8)

`NoInj2.agda`: 142 lines, 125 non-blank. `Mini.agda`: 53 lines, 45
non-blank. Cold caliber 3.412 s at load 5.92 (section 1). No master was
touched.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-294/lj-1.294-report.md`, read FIRST, whole, as
  the brief ordered.** TAKEN: the `Init` table, the measurement that no
  fourth-conjunct term exists, and the finding that the code half of
  `ShiftGraph` dissolves the bridge in THAT direction. Line read `:25`,
  "No ambient-to-code bridge is needed and none exists in the tree
  (MEASURED by grep, section 5)." **My task is the mirror image: the
  bridge IS needed here, and this report prices why it cannot be
  built.**
- **`agents/tasks/LJ-1-286/lj-1.286-report.md`, the Init-rows reading.**
  Line read `:167`, "Two of the three missing parts are FALSE on
  `SqShape`'s own domain, not merely unproved." TAKEN: the method of
  pricing truth on a domain before pricing proof; my section 4 applies
  it to row 4 and finds the same shape of failure, at collapsed
  L-cardinals, INFERRED.
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`, sections 0 to 3.** Line
  read `:113`, "Consumer: the `noinj²` proof (the L-side composition
  `sqβ ∘ f` that refutes an injection into a member's square)". TAKEN:
  row 1 composes CODED graphs, so it cannot host an ambient first
  factor; the composition this task needs is `κ→β`, built ambiently in
  my probe instead.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`,
  read for shape.** Line read `:563`,
  `cardFo v = ordFo v ∧̇ (∀̇∈ (var v) (¬̇ eqFo zero (suc v)))`. TAKEN,
  SHAPE ONLY: the retired cardinal predicate is the AMBIENT
  equipotence form (`IsCard` at `:565-566` refutes a member HOST-equal
  to the ordinal), so the retired route never split the cardinal into
  two faces and never met this wall. **WHAT DOES NOT TRANSFER:** the
  bijection form against today's injection form (`[LJ-1.273]`'s
  measurement, confirmed here), and the ambient setting itself: the
  retired route had no coded face to bridge to.

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:140-170` (the 5.5 to 5.8
chain), `:275-296` (the ingredient list) and `:373-420` (the twelve-row
table).**

**WHICH ROW: F.** Row F (`:382`) files 5.5 under "condensation (i)(ii),
`|L_α| = |α|`, initial ordinals". `noinj²` sits in the last ingredient,
the initial-ordinal arithmetic recorded at `:281-282`: "the cardinal
fact `|γ| = |α| < κ` with κ a cardinal implies `γ < κ`
(`dev2.txt:1372-1384`)".

**DOES DEVLIN PROVE IT OR TAKE IT DEFINITIONALLY? He takes the
cardinal's initiality DEFINITIONALLY, and the square law as chapter-I
arithmetic.** "Let κ be a cardinal" (`:147`) means, in his ambient
meta-universe, that no smaller ordinal is equipotent with κ; that is
the definition, not a lemma. The positive square law `|β×β| = |β|` he
inherits from chapter-I cardinal arithmetic; II.5 never reproves it and
never states row 4's negative form at all. **So the brief's hypothesis
is CONFIRMED with one refinement: the gap IS in our DEFINITION.**
Devlin's cardinals are ambient; our `IsCardinalL`
(`src/L/Cardinal.lagda.md:230-233`) is the coded-injection face, and
PART 1 of my probe proves the faces are related in only one direction.
Devlin's chain, transported to our statement, needs κ ambiently initial
exactly where `GCHStatement` supplies the coded face. **WHY NOT the
other rows:** rows A to C6 and E are elementarity, collapse,
absoluteness, bookkeeping and hull counting; rows D and G are the
definable well-order; none touches cardinality. Row F is the only
cardinal-arithmetic row, and the digest itself files its cardinal
content as "either tower" shared background.

## 11. WHAT I DID NOT DO

- **No master was touched.** Not `GCH.lagda.md`, whose mis-parse this
  report measures; not any other master. `git status --short` over my
  writes shows exactly `agents/tasks/LJ-1-299/` (the tracked report,
  modified, and two untracked `.agda` files); the sibling's writes in
  `agents/tasks/LJ-1-298/` are not mine and were not touched.
- **No attempt to build `AmbientToCode`**, beyond pricing it: section 3.
- **`make check` not run.** Checkers run on my writes:
  `scripts/gate/lint-prose.py --check` and
  `scripts/gate/lint-agda.py --check` both exit 0, on the tree and on
  my files by name. No em dash in any file, checked by grep.
- **No `.agdai` left undeclared**: the probe's interface files are
  gitignored, MEASURED by `git check-ignore`.

## 12. FOR THE ORCHESTRATOR

1. **Fix `src/L/GCH.lagda.md:47` FIRST.** One pair of parentheses;
   until it lands, `GCHStatement`'s `sq` hypothesis is dischargeable by
   `trivialSq` (`Mini.agda`) and the square law gates nothing. This is
   a statement hole, not a proof debt.
2. **Row 4 must change its hypothesis, not gain a proof.** Either
   `GCHStatement` names the ambient face (`IsCardinal`) for κ, or κ is
   constructed by `LeastCardInjL` where `κ-min-at` gives ambient
   minimality. The ambient-to-code bridge is not a buildable debt
   (section 3).
3. **The corrected lemma is priced and ready**: PART 2, about 55
   non-blank lines into `L.BoundedSubset`, no import widenings.
4. **PART 1 is independently landable** and closes the face relation
   the trophy's assembly will need anyway, since `Devlin55` consumes
   `IsCardinal` while `GCHStatement` names `IsCardinalL`.
5. **The `[LJ-1.8]` descent still owes its well-founded recursion**,
   with the successor case from `absorbs`, the base from `squareω`, and
   the truncatedness decision of section 6.
