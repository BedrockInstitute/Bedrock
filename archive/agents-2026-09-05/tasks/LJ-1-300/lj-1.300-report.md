# LJ-1.300 report: the DD25 review of [LJ-1.299]

tier: opus (pi-subagent-mode), the ADVERSARIAL row. The target was written
by pi on `glm-5.3`. I did not write it, so DD17's invariant holds. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those
words. ASD-STE100 applies.

## 0. LEAD: three verdicts, one word each

- **CLAIM 1**, the `SqShape` mis-parse: **HOLDS.**
- **CLAIM 2**, the circularity: **WRONG.**
- **CLAIM 3**, the `AmbientToCode` wall: **HOLDS**, with one label
  corrected.

**SWEEP COUNT: 1.** One line in `src/` carries the defect, and it is
`src/L/GCH.lagda.md:47` itself. Six more lines carry the same mechanical
shape and are correct as written. Section 5.

**THE TROPHY STATEMENT MUST CHANGE, in two places.** One is the pair of
parentheses. The other is the cardinal face at κ, which claim 3 prices.
Section 6.

## 1. MACHINE DISCIPLINE

ONE agda process at a time. `GHCRTS="-A64m -I0 -M8g"` on every run. The
cap was never raised. **MEASURED FALSE: a wall.** The longest single
invocation was 3.572 s, and that run was a rejected intermediate.
**MEASURED FALSE: a heap exhaustion.** The machine was NOT quiet: a
sibling held a slot and the 1-minute load moved between 6.25 and 9.04.
Every absolute figure carries its load.

| run | exit | elapsed s | 1-min load |
|---|---:|---:|---:|
| `ParseReal.agda`, tests 1 to 3 | 0 | 2.412 | 8.38 |
| `StepProbe.agda`, level error (rejected) | 42 | 3.572 | 6.55 |
| `StepProbe.agda`, green | 0 | 2.716 | 6.25 |
| `ParseReal.agda`, tests 1 to 4 | 0 | 2.431 | 8.96 |

## 2. CLAIM 1: HOLDS, against the REAL `SqShape`

**My own term, and it is not a reconstruction.** The probe is
`agents/tasks/LJ-1-300/ParseReal.agda`. It **imports `SqShape` from
`L.GCH`** (`ParseReal.agda:19`). It does not restate the type. It does
not define its own `_↪_`; it imports the real one from `L.Cardinal`
(`ParseReal.agda:18`). Every fixity, every operator and every import is
`L.GCH`'s own.

Four tests, all green, exit 0:

1. **`realSnd` (`ParseReal.agda:36-38`).** `sq α oα h .snd` has the type
   `⟪ fst α ⟫ ↪ ⟪ fst α ⟫`: a self-injection. This typechecks only if
   `↪` binds tighter than `×` at the real site.
2. **`realFst` (`ParseReal.agda:43-45`).** `sq α oα h .fst` has the type
   `⟪ fst α ⟫`: ONE carrier element, and not the product
   `⟪ fst α ⟫ × ⟪ fst α ⟫` that a reader expects.
3. **`realTrivial` (`ParseReal.agda:60-62`).** The real `SqShape` is
   **inhabited outright**. The witness is one carrier element, from
   `fiber` after `ord-tri` gives a member, paired with the identity map.
   No square law appears in the term.
4. **`sq-same` (`ParseReal.agda:69-70`).** With the parentheses in
   place, the body is JUDGMENTALLY the tree's own delivered square law
   `L.Ordinal.SquareLaw.sq` (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).
   `refl` typechecks. Section 7 gives what this buys.

**The fixity, MEASURED.** `_↪_` is declared at
`src/L/Cardinal.lagda.md:47`. `grep -n infix src/L/Cardinal.lagda.md`
returns NOTHING, so the file carries no fixity declaration at all and
`_↪_` takes Agda's default level. `_×_` is `infixr 5` at
`Cubical/Data/Sigma/Base.agda:25`. The default level is above 5, so `↪`
binds tighter and `src/L/GCH.lagda.md:47` parses as
`⟪ fst α ⟫ × (⟪ fst α ⟫ ↪ ⟪ fst α ⟫)`.

**MEASURED: the cubical library does not rescue it.** Cubical declares
its own `_↪_` at `Cubical/Functions/Embedding.agda:71` and gives it NO
fixity either. A fixity declared for the same symbol in another module
never transfers, and here there is none to transfer.

**THE ORCHESTRATOR'S RECONSTRUCTION IS FAITHFUL.**
`agents/tasks/LJ-1-299/ParseCheckOrch.agda` defines its own `_↪_` with
the same `Σ`-of-function-and-proof body and gets the same two answers.
I looked for a divergence and found none. The real `_↪_`
(`src/L/Cardinal.lagda.md:45-47`) has that same body, and `L.GCH` opens
no module that re-fixes either operator: `grep -n infix
src/L/GCH.lagda.md` returns nothing.

### 2.1 THE DIRECTION OF THE DEFECT, which the target states loosely

The target says the hypothesis "gates NOTHING". That is right about USE.
It must not be read as "the trophy is now easy". `GCHStatement zf`
(`src/L/GCH.lagda.md:79-80`) has the shape `(sq : SqShape) → REST`. When
`SqShape` is inhabited, `(sq : SqShape) → REST` is logically EQUIVALENT
to `REST`: drop the argument for one direction, apply it to
`realTrivial` for the other. So:

- **A proof cannot USE `sq`.** It supplies no square law. Any plan that
  consumes `sq` fails at the first projection.
- **The statement as landed is STRICTLY STRONGER than intended.** It
  claims the GCH bound with NO square-law hypothesis. It is harder to
  prove, not easier.
- The fix makes the HYPOTHESIS stronger, so it makes the STATEMENT
  weaker, back to the intended staging.

**C-45 reads exactly here.** The telescope of `SqShape` looks like a
real assumption: it binds α, it demands `IsOrd (fst α)`, it excludes the
finite case. Only the instantiation shows that the conclusion is not a
square law. Audit the instantiation, never the telescope.

## 3. CLAIM 2: WRONG. The dependency descends; it is not a cycle

**Two links break the alleged circle. The first is MEASURED by a probe.**

### 3.1 LINK ONE: `Init`'s fourth row quantifies STRICTLY BELOW

`Init α`'s fourth row (`src/L/Ordinal/SquareLaw.lagda.md:696-698`)
quantifies over `β` with `⟨ β ∈ˢ α ⟩`. Every such β is strictly below α
in the membership order. So `sq α` depends on `noinj² α`, and `noinj² α`
depends on `sq β` for members β only. It never returns to `sq α`.

**MEASURED, `agents/tasks/LJ-1-300/StepProbe.agda`, exit 0, 2.716 s at
load 6.25.** `descent-step` (`StepProbe.agda:45-63`) has the type

    (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩
              → ((γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
              → IsCardinal α → SqBelow α → sq α

where `SqBelow α` (`StepProbe.agda:39-40`) is the square law at MEMBERS
of α only. The term builds `Init α`'s fourth row and calls the delivered
`via-col-square`. **Nothing in the term mentions `sq α`.** One step of
the descent closes, so the graph is a step function on a well-founded
order and not a cycle.

### 3.2 LINK TWO: `via-col-square` is NOT the only delivered route

The target's section 3 says "the tree's only delivered route to a square
at an ordinal is `via-col-square`". **MEASURED FALSE.**
`squareω : sq ω` is delivered at `src/L/InjChain.lagda.md:184-185`. It
does NOT go through `Init` or `via-col-square`. It instantiates
`InitialCore` directly at ω (`src/L/InjChain.lagda.md:171`) and supplies
the three hypotheses by hand. Its `noinj²ω`
(`src/L/InjChain.lagda.md:123-126`) is **VACUOUS**: an infinite member
of ω is impossible, by the ordinal's own transitivity and `∈-irrefl`.

**So the descent has a delivered base and it terminates.** The chapter's
own comment says why (`src/L/InjChain.lagda.md:102-105`): `Init ω` needs
`⟨ ω ∈ˢ ω ⟩`, which `∈-irrefl` refutes, so the base was rebuilt without
`Init`.

### 3.3 THE TARGET CONTRADICTS ITSELF, and its section 6 has it right

The target's section 6 states the correct picture: "its base is
delivered (`squareω`, `src/L/InjChain.lagda.md:184-185`)", and "What is
NOT delivered: the descent's well-founded recursion itself"
(`agents/tasks/LJ-1-299/lj-1.299-report.md:207-209`). That is an UNBUILT
RECURSION, and it is not a circularity. Its section 3 calls the same
structure CIRCULAR.

**The distinction is not a word.** A circularity says the route is
impossible and the statement must move. An unbuilt descent says the
route is a finite amount of work over a delivered base. The phase is in
better shape than the target's lead reports.

### 3.4 WHAT IS REALLY MISSING, and it is not the cycle

`descent-step` needs α to be an AMBIENT cardinal (`IsCardinal α`), so
the descent as built covers the cardinals. **MEASURED: `via-col-square`
cannot reach a non-cardinal**, because `Init`'s fourth row is FALSE
there ([LJ-1.286] section 5.1 records the same at successor ordinals).
The infinite non-cardinals need the transport from their own
cardinality, whose successor case is `absorbs`
(`src/L/Absorption.lagda.md:613-618`). That gap is real, it is priced in
the target's section 6, and it is a different obstruction from the one
its lead names.

## 4. CLAIM 3: HOLDS, and one label in the target is WRONG

**THE WALL IS REAL, and it is firmer than the target argued.**

### 4.1 What is MEASURED

- **MEASURED: the bridge is absent.** `InjCode` occurs in exactly ONE
  file in `src/`, `src/L/Cardinal.lagda.md` (grep over all masters). The
  only crossing device is `Small`
  (`src/L/Coding/Injection.lagda.md:123`), and it runs code to ambient.
  The reverse has no term.
- **MEASURED: the two cardinal faces relate in ONE direction only.**
  `amb→code` (`agents/tasks/LJ-1-299/NoInj2.agda:103-111`) proves
  `IsCardinal (fst κ) → IsCardinalL κ`. Nothing proves the reverse.
- **MEASURED: `IsCardinalL` (`src/L/Cardinal.lagda.md:230-233`) refutes
  CODED injections only**, because `InjCode F a b`'s F ranges over `S`,
  the L-carrier (`src/L/Cardinal.lagda.md:223-228`). `noinj²`'s f is an
  ambient function.

### 4.2 The label the target got WRONG

The target calls `AmbientToCode` "INFERRED false as mathematics". **That
is WRONG, and the correct word is INDEPENDENT.**

- **INFERRED: `AmbientToCode` is TRUE whenever the ambient universe
  satisfies V = L.** Then every set is constructible, and the graph of
  an injection is a set, so the code exists. Nothing in this development
  forbids that: it builds L INSIDE an ambient V and never assumes the
  two differ. **MEASURED: `src/` holds no term asserting that any set is
  non-constructible** (grep for a refutation of `isL` returns nothing).
- **INFERRED: `AmbientToCode` is FALSE in a Levy collapse of `ω₁^L`**,
  which is the target's own argument.
- Two models on opposite sides means INDEPENDENT. A statement true in
  some model is not false as mathematics.

**Where the FALSE verdict does belong.** The target attached it to the
bridge. It belongs to the IMPLICATION. In the collapse model,
`IsCardinalL κ` holds, the square law holds, and an ambient injection
`⟪κ⟫ → ⟪ω⟫ × ⟪ω⟫` exists, so `NoInj² κ` FAILS. So

    SqAll → IsCardinalL κ → NoInj² κ

is **INFERRED FALSE**, and not merely unprovable. That is the strongest
correct form of the target's finding, and it is a stronger result than
the target claimed for itself.

**The two are marked INFERRED, in that word.** Both readings live in the
standard set-theoretic semantics and neither can be run inside this
development's term model. **I did not build a countermodel in Agda, and
D-10 does not ask for one here:** the truth question is settled once
models exist on both sides.

### 4.3 What this changes for the project

**NOTHING in the route, and ONE word in the record.** The wall stands,
so the cure is the target's own: name the ambient face `IsCardinal` at
κ, or build κ by `LeastCardInjL` where `κ-min-at`
(`src/L/Cardinal.lagda.md:140-142`) gives ambient minimality. The label
matters because FALSE forbids a cure that in principle exists (assume
more about the ambient), and that cure is one the project must REFUSE
for its own reasons, not because it is impossible.

## 5. THE SWEEP (C-42): COUNT 1

**The tool is `agents/tasks/LJ-1-300/sweep-fixity.py`, tracked beside
this report.**

**The universe.** Every binary infix operator `_op_` declared in `src/`
that carries NO fixity declaration in `src/` or in cubical. **MEASURED:
14 such declarations, 14 distinct symbols**: `<ᵇ`, `<∙`, `~`, `↪`, `∩`,
`∪`, `≤₁`, `≺'`, `≺×`, `≺₁`, `⊆ᵇ`, `⊨c`, `⊨₀`, `⊨ₚ`. Each takes Agda's
default level and binds tighter than `×`, `⊎` and `≡`.

**The shape.** `A LOOSE B OP C`, or its mirror, with LOOSE and OP at ONE
bracket depth and no `→`, `=` or `;` between them at that depth.
Declarations are joined across continuation lines first, so a defect
split over two lines cannot hide.

**MEASURED: 7 lines in `src/` carry the shape. ONE is a defect.**

| line | shape | verdict |
|---|---|---|
| `src/L/GCH.lagda.md:47` | `× ... ↪` | **DEFECT.** The author wants `(A × A) ↪ A` |
| `src/L/Coding/EnvSupply.lagda.md:807` | `∪ ... ≡` | correct as written |
| `src/L/Coding/EnvSupply.lagda.md:821` | `∪ ... ≡` | correct as written |
| `src/L/Coding/EnvSupply.lagda.md:835` | `∪ ... ≡` | correct as written |
| `src/L/Coding/Key.lagda.md:653` | `∪ ... ≡` | correct as written |
| `src/L/Coding/Key.lagda.md:668` | `∪ ... ≡` | correct as written |
| `src/L/Coding/Key.lagda.md:683` | `∪ ... ≡` | correct as written |

**Why the six are correct.** They read `a ∪ b ≡ b ∪ a` and the same
family. `∪` builds a value and `≡` relates two values, so the author
WANTS `∪` to bind tighter, and it does. The defect needs the opposite
intent: at `GCH.lagda.md:47`, `×` builds the argument of a relation, so
the author wants `×` tighter, and it is not.

**C-42, honoured.** The refutation measured the site it named. The sweep
measures how far it extends, and the answer is: it does not.

## 6. WHAT THE FIX VOIDS (C-32)

**[LJ-1.286] loses its central conclusion.**

- `agents/tasks/LJ-1-286/lj-1.286-report.md:139`: "**MEASURED: nothing
  in `src/` inhabits `SqShape`.**" The grep behind it still stands, but
  `realTrivial` inhabits `SqShape` in four lines, so the sentence no
  longer supports what it was used for.
- `agents/tasks/LJ-1-286/lj-1.286-report.md:375-380`: "`sq : SqShape` is
  NOT dischargeable." **REFUTED.** It is dischargeable today, by
  `realTrivial`.
- The Init gap table
  (`agents/tasks/LJ-1-286/lj-1.286-report.md:160-165`) compares `Init α`
  against what `SqShape` supplies. It was computed against the wrong
  object, because `SqShape`'s conclusion is not `sq α`. Its four
  verdicts happen to survive; its BASIS does not.

**[LJ-1.294] is NOT voided.** Its result `κ-limit`
(`agents/tasks/LJ-1-294/CardinalLimit.agda:53-124`) mentions no
`SqShape` and consumes only `IsCardinalL`. **MEASURED:
`agents/tasks/LJ-1-294/CardinalLimit.agda` contains no occurrence of
`SqShape` or of `sq`.** The five mentions in its REPORT are context. Its
use-site analysis of `Init` rows 1 to 3 stands.

**[LJ-1.299] is NOT voided by its own find.** Its `SqAll`
(`agents/tasks/LJ-1-299/NoInj2.agda:75-77`) is written with the
parentheses, so its PART 1, PART 2 and PART 3 are already stated against
the FIXED statement.

**`dev/ledger.toml:204` carries a sentence that the fix falsifies.** The
`gch_root_why` says "sq alone remains an unsupplied Pi-parameter". `sq`
is not unsupplied; it is suppliable by `realTrivial`. **I did not edit
`dev/ledger.toml`, which the brief forbids.** The number it justifies
does not move; section 7 says why.

## 7. DD4, and my axis (C-46)

**MY AXIS IS AC-AGAINST-GCH, DD4's own**, fixed in code at
`scripts/measure/ledger.py` and printed by `--reuse`. Today's figure, at
HEAD: AC closure 73 masters / 17,197 lines, GCH closure 51 / 9,967,
SHARED 44 / 7,632, share 39.1% of 19,532.

**THE FIGURE DOES NOT MOVE.** The reuse report reads an IMPORT CLOSURE
from each declared root. A pair of parentheses adds no import, so the
closure is the same set of masters and the same line count.

**Nor does the sharper fix move it.** Test 4 shows the parenthesized
body IS `sq (fst α)`, so `SqShape` can be written in terms of the
delivered `L.Ordinal.SquareLaw.sq` instead of restating it. **MEASURED:
`L.Ordinal.SquareLaw` is ALREADY in the GCH closure**, reached through
`L.Cardinal` (`src/L/Cardinal.lagda.md:22`). I recomputed both closures
from the import graph and reproduced `ledger.py`'s 73 / 51 / 44 exactly,
so the method is checked. **A direct import of `L.Ordinal.SquareLaw`
into `L.GCH` adds NO master and moves NO line.**

**What DD4 does gain, at zero import cost.** Today the square law is
STATED TWICE in the tree, once as `sq`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`) and once inside `SqShape`.
Writing `SqShape` through `sq` states it once, which is DD4's "write it
generic" half. **MEASURED: `L.Ordinal.SquareLaw` is in the GCH closure
and NOT in the AC closure**, so the square law is GCH-side code today
and this change does not move it into SHARED. **The share figure will
not reward the fix; read the SHARED row and not the percentage.**

**DD4's first published figure was NOT computed over the wrong
statement.** The figure is import-based. What was computed over the
wrong statement is the PROSE in `dev/ledger.toml:204` and [LJ-1.286]'s
gap table.

## 8. THE LITERATURE (DD18), and a third finding

**`dev/literature/devlin-II5.md`, read `:140-170` (the 5.5 to 5.8
chain), `:270-300` (Steps E and F) and `:373-420` (the twelve-row
table).**

**MEASURED: Devlin II.5 never states a square law, and the digest never
mentions one.** A grep for "square" or "product" over
`dev/literature/devlin-II5.md` returns nothing outside references to our
own `SquareLaw` chapter. 5.5's cardinal content is different: the level
size equation `|L_α| = |α|` from 1.1(vii), and the initial-ordinal fact
"`|γ| = |α| < κ` with κ a cardinal implies `γ < κ`"
(`dev/literature/devlin-II5.md:281-282`). Row F of the table
(`dev/literature/devlin-II5.md:382`) files 5.5 under "condensation
(i)(ii), |L_α| = |α|, initial ordinals".

**So the literature CANNOT settle the parenthesisation, and the tree
can.** The square law `|β × β| = |β|` is chapter-I cardinal arithmetic
that II.5 inherits and never restates. The decisive comparison is
internal: the tree's own delivered `sq`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`) is
`Σ[ f ∈ (⟪α⟫ × ⟪α⟫ → ⟪α⟫) ]` with injectivity, which is exactly
`(⟪α⟫ × ⟪α⟫) ↪ ⟪α⟫`. **Test 4 measures that the parenthesized body and
`sq` are the SAME type, by `refl`.**

**THE THIRD FINDING.** The tree's intended reading differs from
Devlin's in ONE way, and it is not the parenthesisation. Devlin's
chapter-I fact is an EQUALITY of cardinals, so a bijection. The tree's
`sq` is an INJECTION of the square into the ordinal. The injection is
the weaker half and it is the half the descent consumes. **That
difference is deliberate and already recorded**, and the fix does not
touch it.

## 9. WHAT I DID NOT DO

- **No master was touched.** Not `src/L/GCH.lagda.md`, whose defect this
  report measures; not any other master. My writes are confined to
  `agents/tasks/LJ-1-300/`.
- **I did not apply the parenthesis fix.** The brief reserves it, and
  the statement change is the owner's ruling.
- **`agents/tasks/LJ-1-299/` was read and never written.**
- **`make check` not run**, as the brief orders. The two named linters
  were run on my files; section 10.
- **No countermodel was built in Agda.** Section 4.2 says why, and marks
  both readings INFERRED.

## 10. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check`: exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check`: exit 0.
- **MEASURED: no em dash in any file I wrote** (grep).

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-299/lj-1.299-report.md`, read WHOLE**, as the
  brief ordered. Line read `:207-209`, "its base is delivered
  (`squareω`, `src/L/InjChain.lagda.md:184-185`) ... What is NOT
  delivered: the descent's well-founded recursion itself". **TAKEN: the
  sentence that refutes the report's own lead.** Section 3.3.
- **`agents/tasks/LJ-1-299/NoInj2.agda`, read whole.** Line read `:103`,
  `amb→code : (κ : S) → IsCardinal (fst κ) → IsCardinalL κ`. TAKEN: the
  one-directional face relation, which is the MEASURED half of the wall.
- **`agents/tasks/LJ-1-299/Mini.agda`, read whole.** Line read `:51`,
  `trivialSq : SqShape`. TAKEN: the SHAPE of the trivial witness, which
  I rebuilt at the REAL `SqShape` in `ParseReal.agda:60-62`. Mini's
  `SqShape` is a restatement over `V ℓ`, so it is not evidence about the
  real one.
- **`agents/tasks/LJ-1-299/ParseCheckOrch.agda`, read whole, treated as
  the least trustworthy evidence.** Line read `:11`,
  `asWritten A = A × A ↪ A`. TAKEN: nothing but the question. I settled
  it against the real object instead. Section 2 records that the
  reconstruction is faithful.
- **`agents/tasks/LJ-1-286/lj-1.286-report.md`.** Line read `:139`,
  "MEASURED: nothing in `src/` inhabits `SqShape`." **TAKEN: the
  conclusion this task voids.** Section 6.
- **`agents/tasks/LJ-1-294/lj-1.294-report.md`.** Line read `:25`, "No
  ambient-to-code bridge is needed and none exists in the tree
  (MEASURED by grep, section 5)." TAKEN: the direction that IS
  delivered, which fixes what claim 3's bridge is the mirror of. Its own
  result survives; section 6.
- **`archive/dev/TASKS-archived.md`, read for SHAPE and never a claim.**
  Line read `:140`, `| L3.32-T105 | Adversarial review: context layering
  | REFUTED (diagnosis) | ...`. TAKEN, SHAPE ONLY: an adversarial review
  is recorded as one index row whose verdict cell says WHAT was refuted,
  with the detail in the report. My row should read the same way, and it
  should say WRONG on the diagnosis and HOLDS on the find.

## 12. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`**, sections 1.5, 2.5, 2.6 and 5, at
  `:140-170`, `:270-300` and `:373-420`. Section 8 gives what it says
  and what it cannot settle.
- **WHY NOT the rest of the digest.** Sections 3 and 4 are the engine
  list and the crossing map; sections 6 and 7 are the errata and the
  Jech cross-check. **None of them touches cardinal arithmetic**, which
  is the only content this task needed. Row F is the digest's single
  cardinal row and I read it.
- **WHY NOT any other file under `dev/literature/`.** The task is a
  parse and a dependency graph inside `src/`, and the digest was named
  by the brief for ONE question: what Devlin's square law states. It
  states none.

## 13. FOR THE ORCHESTRATOR

1. **Apply the parenthesis fix, and consider the sharper form.** Test 4
   proves `(⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫` IS `sq (fst α)`. Stating
   `SqShape` through `sq` costs no import and states the law once.
2. **The circularity is NOT the obstruction. Say so in the next brief.**
   The descent has a delivered base at ω and one measured step. What is
   missing is the well-founded recursion and the non-cardinal transport.
3. **Claim 3's wall stands, and its label must change** from FALSE to
   INDEPENDENT for the bridge, with FALSE moved to the implication where
   a countermodel really exists.
4. **[LJ-1.286]'s "sq is NOT dischargeable" must be marked REFUTED** in
   the record, and `dev/ledger.toml:204`'s justification sentence needs
   one correction.
5. **The sweep found nothing else.** One defect, one line, and six
   correct uses of the same shape.
