# LJ-1.569 report: row 1 is consumed at one site, and weakening the slot does not make the demand internal

## HEAD
head_slot: coder
machine: shared
task: LJ-1.569
obligation: agents/tasks/LJ-1-569/Probe569.agda::gch-without-row-1
verdict: NO-GO

No commit, no push. I wrote only inside `agents/tasks/LJ-1-569/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. Nothing is postulated, the probe
carries `--safe`, and there is no hole. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot
fire on it.

**NO HEAP EVENT.** The largest peak memory footprint of any run is 1,887,405,952
bytes, about 1.76 GiB, against an 8 GB cap
(`agents/tasks/LJ-1-569/runs/w3-1.out:48`). No run reported exit 251 and no run
printed a heap message.

## VERDICT

**NO-GO, AND THE STOP IS THE DELIVERABLE (AGENTS.md:43).**
`agents/tasks/LJ-1-569/review-of-gch-without-row-1.md` states it.
`scripts/pod/witness.py --brief` reports
`missing exit=42 3.37s agents/tasks/LJ-1-569/Probe569.agda::gch-without-row-1`
and `witness: 1 UNRESOLVED of 1, 3.37 s, probe_red=False`
(`agents/tasks/LJ-1-569/runs/witness-1.out:1-2`).

**THE PROBE IS GREEN** (`agents/tasks/LJ-1-569/runs/final-5.out`, `EXIT=0`,
3.23 s) and carries what the brief asked for instead of the term: the site,
stated as terms whose types name row 1 and nothing else.

**THE BRIEF'S OWN WORDS FOR THIS OUTCOME APPLY WITHOUT SOFTENING.** `L ⊨ GCH`
as routed here needs δ to be a real cardinal. The route proves more than the
trophy.

## WHERE ROW 1 IS USED

**D-10, BEFORE ANY AGDA, AND IT IS THE USE SITE.** No Agda was written until
this table was read off the predecessors' probes.

**ONE SITE IN `[LJ-1.564]`, AND ONE SITE INSIDE IT.**

| where | `file:line` | what it does |
|---|---|---|
| the only consumer of row 1 in `[LJ-1.564]` | `agents/tasks/LJ-1-564/Probe564.agda:351-361` | `power-into-succ-at`, whose body spends row 1 once |
| the spend, in that body | `agents/tasks/LJ-1-564/Probe564.agda:360` | `U.member-in-stage (r1 κ δ sc) (r2 κ ordκ) r3` |
| the slot it fills | `agents/tasks/LJ-1-550/Probe550.agda:257-258` | `member-in-stage`'s first argument, `IsCardinal (fst δ)` |
| what that slot is passed to | `agents/tasks/LJ-1-550/Probe550.agda:278` | `bst (fst δ) ordδ cardδ δ∉ω (fst κ) ...`, the `cardκ` slot of `BoundedSubsetTheorem` |
| the telescope that asks for it | `src/L/BoundedSubset.lagda.md:1386` | `(cardκ : IsCardinal κ)` of `Devlin55.BoundedSubsetAt` |
| where the module SPENDS it | `src/L/BoundedSubset.lagda.md:1597` and `:1601` | both times as `cardκ α α∈κ`, inside the proof of `β∈κ` |

**WHAT THE STEP NEEDS THE AMBIENT CARDINALITY FOR.** The two spend sites are the
two branches of ordinal trichotomy at `src/L/BoundedSubset.lagda.md:1594-1603`.
The collapse of the hull has ordinal β with an ambient injection `β ↪ α`; the
proof must place β strictly below κ, and it does so by refuting `κ ↪ α`. **At
the assignment `[LJ-1.550]` fixed (theorem-κ := `fst δ`, theorem-α := `fst κ`)
that refutation is "there is no ambient injection of δ into κ".** The hull and
the collapse are ambient constructions, so the size comparison they force is an
ambient one.

**AND ROW 1 IS CONSUMED, MEASURED, NOT INFERRED.** W3 below.

## W3: DOES `gch-from-five` CONSUME ROW 1 AT ALL

**IT DOES.** The brief priced W3 at about 15 lines and under 60 seconds. I wrote
three slices instead of one, because the first two only prove the Π is in the
TYPE and the third makes the elaborator name the slot.

| slice | file | what it drops | run | result |
|---|---|---|---|---|
| A | `runs/W3.agda.txt:48-55` | row 1 from the argument list of `gch-from-here-sharp` | `runs/w3-1.out` | `EXIT=42`, 31.67 s |
| B | `runs/W3b.agda.txt:49-60` | row 1 at the spend site | `runs/w3-2.out` | `EXIT=42`, 3.25 s |
| C | `runs/W3c.agda.txt:58` | row 1 replaced by a term of a known wrong type | `runs/w3-3.out` | `EXIT=42`, 3.26 s |

Slice C is the answer. `runs/w3-3.out:10-11`:

    when checking that the expression r3 has type
    L.BoundedSubset.IsCardinal lem (fst δ)

**A NOTE ON THE BRIEF'S WORDING.** The brief asked for the body "typechecked
with an unused-variable check on". Agda 2.8.0 has no unused-binder warning for a
term binder, so that check does not exist to turn on. The slices test the same
question the only way the elaborator can answer it: bind row 1, never mention
it, and see whether the term still elaborates. It does not. **This is a stronger
test than the warning would have been**, because it fails on the term and not on
a lint.

## WHAT THE PROBE DELIVERS INSTEAD OF THE OBLIGATION

The brief: "If it will not build, the deliverable is the site where row 1 is
really used, stated as a term whose type names it and nothing else."

| term | `file:line` | what its type says |
|---|---|---|
| `landing-at` | `agents/tasks/LJ-1-569/Probe569.agda:103-108` | the step with rows 2 and 3 paid and **`IsCardinal (fst δ)` as the last hypothesis**, nothing else open |
| `row-1-is-the-only-gap` | `:113-119` | `GCHStatement zf` with the other four rows passed to `[LJ-1.564]` verbatim and in order, and **row 1 moved to the far right** |
| `Row1Spent` / `row-1-spend-is-B5` | `:141-146` | the ONLY instance the module spends, and `refl` proving it is `[LJ-1.523]`'s B5 on the nose |
| `row-1-gives-the-spend` | `:152-153` | row 1 pays that instance |
| `ambient→internal` | `:169-171` | readback's direction, green |
| `InternalToAmbient` | `:175-176` | the converse, TYPE ONLY, neither proved nor refuted |
| `row-1-from-the-converse` | `:187-188` | the converse buys row 1 outright |
| `bill-after` | `:207-212` | the bill, counted by the elaborator |

## CHANGE EXACTLY ONE THING: ANSWERED

**THE OTHER FOUR ROWS ARE UNTOUCHED, AND A TERM SAYS SO AND NOT A SENTENCE.**
`row-1-is-the-only-gap` (`Probe569.agda:113-119`) passes `r2 r3 b9 b10` straight
into `P564.gch-from-five` in `[LJ-1.564]`'s own order. If any of the four had
been weakened, that application would not elaborate. `bill-after`
(`Probe569.agda:207-212`) is the same check at the type level: an identity at a
hand-written type, which does not typecheck if a row moved, changed or left.

## READBACK: WHICH DIRECTION THE CONSUMING STEP WANTS

**THE CONVERSE.** The step holds `IsCardinalL δ`, from `SuccCardL`'s second
conjunct (`src/L/GCH.lagda.md:49`), and wants `IsCardinal (fst δ)`. Readback
runs the other way: `readL` (`src/L/CantorBernstein.lagda.md:33-38`) turns a
code into an ambient injection, so an AMBIENT refutation refutes every code,
which is `ambient→internal` (`Probe569.agda:169-171`, green).

**AND `src/` HAS NO PRODUCER FOR THE CONVERSE.** It would need an `InjCode` for
an arbitrary ambient injection. The only `InjCode` producers are
`src/L/Absorption.lagda.md:614` and `src/L/CodedShift.lagda.md:40`, and both
deliver the single shape `InjCode F (sucʟ γ) γ`. I re-ran that search at this
site rather than quoting `[LJ-1.550]` (AGENTS.md:45); the two producers are the
same two.

**`[LJ-1.550]`'s `site-forced` TURNED ON EXACTLY THIS, AND IT STILL HOLDS.**
`agents/tasks/LJ-1-550/Probe550.agda:385-389`: any ambient cardinal μ above κ is
an L-cardinal by readback, so `SuccCardL`'s leastness gives δ ⊆ μ; landing the
conclusion inside `Lset (fst δ)` needs μ ⊆ δ; so μ ≡ δ. **The site cannot be
moved, and the reason is the direction readback runs in.**

## THE NEW MEASUREMENT: ROUTE A WEAKENS THE DEMAND AND DOES NOT REMOVE IT

`[LJ-1.550]`'s review named a Route A: restate
`src/L/BoundedSubset.lagda.md:1386` with the spent form in place of
`IsCardinal κ`, "then B5 fills the slot exactly and R1 leaves"
(`agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:66-69`).

**THAT IS TRUE OF THE ROW AND FALSE OF THE DEMAND, AND THIS TASK MEASURED THE
DIFFERENCE.** `Row1Spent` (`Probe569.agda:141-142`) is written out with the
ambient function type visible:

    Row1Spent = (κ δ : SL.S) → SuccCardL δ κ → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫ → Empty.⊥

and `row-1-spend-is-B5` (`:145-146`) is `refl`, so the spent form IS B5. **B5
names `⟪ ⟫` and `↪`. It is ambient.** So Route A trades an ambient Π for an
ambient instance: it makes row 1 cheaper and it does not make the route
internal. **A task funded as "Route A removes the ambient fact" would be funded
against a false premise.**

**AND THE INSTANCE DOES NOT GIVE THE Π BACK**, re-measured at this site and not
carried over: `runs/Neg569.agda.txt:25` with `runs/neg-1.out` (`EXIT=42`,
`[UnequalTerms]`).

## WHERE THE AMBIENT DEMAND COMES FROM, NAMED

**IT IS THE PORT.** `Devlin55.BoundedSubsetAt` is Devlin II 5.5, and 5.5 opens
`Assume V = L` (`dev/literature/devlin-II5.md:147`). Under that assumption an
ambient cardinal and an L-cardinal are the same object, so the printed
hypothesis "Let κ be a cardinal" does not choose between the two readings.
**Bedrock does not assume V = L**: `GCHStatement` is relativized and names no
ambient type (`src/L/GCH.lagda.md:59-69`). The port kept the ambient reading of a
hypothesis whose source did not have to pick one, and row 1 is the residue.

`row-1-from-the-converse` (`Probe569.agda:187-188`) names the whole demand as
one principle: **an L-cardinal is a cardinal.** `gch-from-four-plus-writeback`
(`:190-196`) is the bill with row 1 replaced by it. **THAT IS NOT AN IMPROVEMENT
AND THE PROBE SAYS SO AT `:181-184`**: `InternalToAmbient` is STRICTLY MORE than
row 1, because it gives row 1 at every L-cardinal and row 1 only at a successor
pair. What it buys is a name, not a smaller price.

## THE BILL AFTER THIS TASK

**FIVE ROWS. COUNTED, NOT ESTIMATED.** The count is `bill-after`
(`agents/tasks/LJ-1-569/Probe569.agda:207-212`), an identity at a hand-written
type: it does not typecheck if a row moved, changed or left. The five, in order:

| # | row | type | `file:line` |
|---|---|---|---|
| 1 | `AmbientCardAtSucc` | `(κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)` | `agents/tasks/LJ-1-550/Probe550.agda:301-302` |
| 2 | `SqAt` | `(κ : SL.S) → IsOrd (fst κ) → SqLaw (fst κ)` | `agents/tasks/LJ-1-550/Probe550.agda:309-310` |
| 3 | `CoHyps` | `levelIn` and `cover` over the whole telescope | `agents/tasks/LJ-1-550/Probe550.agda:215-230` |
| 4 | `StageCountedCoded` | `(δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ` | `agents/tasks/LJ-1-564/Probe564.agda:127-130` |
| 5 | `SuccIntoPower` | `(κ δ : SL.S) → SuccCardL δ κ → InjL δ (𝒫 κ)` | `agents/tasks/LJ-1-558/Probe558.agda:100-103` |

**THIS TASK REMOVED NO ROW AND ADDED NO ROW.** The bill is the same five
`[LJ-1.564]` left at `agents/tasks/LJ-1-564/Probe564.agda:456-463`.

**ONE OF THE FIVE ASKS FOR SOMETHING OUTSIDE L, AND IT IS STILL ROW 1.** Rows 2
to 5 were not attempted here (AD12, and the brief forbids it).

## THE PRICE

All numbers at caliber `-A64m -I0 -M8g`, one Agda process at a time.

| run | what the file was | result | real | peak footprint |
|---|---|---|---|---|
| `runs/w3-1.out` | W3 slice A, cold on the predecessor chain | `EXIT=42` | 31.67 s | 1,887,405,952 |
| `runs/w3-2.out` | W3 slice B | `EXIT=42` | 3.25 s | 720,520,248 |
| `runs/w3-3.out` | W3 slice C, the answer | `EXIT=42` | 3.26 s | 719,520,848 |
| `runs/final-1.out` | the probe, first write | `EXIT=0` | 4.25 s | 818,365,592 |
| `runs/neg-1.out` | the negative, expected red | `EXIT=42` | 4.22 s | 661,816,376 |
| `runs/final-2.out` | after the comment repair | `EXIT=0` | 4.27 s | 818,381,976 |
| `runs/final-3.out` | after the width repair | `EXIT=0` | 4.24 s | 818,381,976 |
| `runs/final-4.out` | after the citation repair | `EXIT=0` | 3.69 s | 818,365,592 |
| `runs/final-5.out` | the probe, final state of the tree | `EXIT=0` | 3.23 s | 713,213,008 |
| `runs/witness-1.out` | `witness.py --brief` | 1 UNRESOLVED of 1 | 3.37 s | not measured |

**`make check` PASSES.** Every gate is clean: `typecheck`, `markers`, `lint`,
`lint-agda`, `glossary`, `ledger`, `probes`, `closure`, `fences`, `reuse`,
`ruleids`, `specsurface`. **One operational note the next worker needs:** this
worktree has no `.venv`, so the Makefile's `$(PY)` and its hard-coded
`.venv/bin/reuse` do not resolve here. I ran the gate as
`make check PY=/Users/alsg/Agentic/Bedrock/.venv/bin/python` and then ran
`reuse lint`, `check-rule-ids.py` and `check-spec-surface.py --check` from the
same interpreter. `reuse lint` reports 6561 / 6561 files with copyright and
license information and declares the project compliant.

**THE ESTIMATE AND WHAT IT COST.** The brief estimated about 130 lines in the
probe, of which the obligation is about 25. The probe is 212 lines
(`agents/tasks/LJ-1-569/Probe569.agda`), of which about 75 are the terms and the
rest are the comment blocks the site needs. The obligation costs 0 lines because
it is not there. W3 was estimated at about 15 lines and under 60 seconds; the
three slices are 69, 60 and 61 lines and the three runs are 31.67 s, 3.25 s and
3.26 s, so the estimate held on time and not on lines: the slices carry the
import block of the predecessor chain, which the estimate did not price.

## W2 AND W4, ANSWERED

**W2 (from DD4), the generic carrier.** This task wrote no mathematics at a
carrier. Every type it names is already stated once, at `SL.S` and `SV.S`, by
`[LJ-1.550]`, `[LJ-1.558]` and `[LJ-1.564]`, and this probe imports them rather
than restating them. The one type it declares fresh, `Row1Spent`
(`Probe569.agda:141-142`), is proved `refl`-equal to the existing
`P550.AmbientSpentAtSucc` (`:145-146`), so it is not a second statement of the
same thing: it is the same statement with the ambient function type made
visible, and the `refl` is what stops it from drifting. **No conflict with W2
and no deadline pressure to report.**

**W4 (from DD13), retirement.** Nothing retired. No module moved, no fragment
was deleted, and `dev/ARCHIVE.md` needs no row from this task. The three RED W3
slices and the RED negative are kept as `.agda.txt` under
`agents/tasks/LJ-1-569/runs/`, tracked and not deleted, because
`agents/tasks` is on the library's include path (`bedrock.agda-lib:2`) and a
`.agda` extension there would break `make check`.

## WHAT THE NEXT BRIEF SHOULD KNOW

1. **DO NOT FUND "ROUTE A REMOVES THE AMBIENT FACT".** It does not. Measured
   above. Route A is worth funding as a cheapening of row 1 and as nothing else.
2. **THE QUESTION THAT IS ACTUALLY OPEN IS `InternalToAmbient`, AND THIS TASK
   DID NOT TOUCH IT.** The brief forbade proving or refuting it, so it stands
   stated as a type at `Probe569.agda:175-176` and nowhere else. It is not
   plausible as a theorem of this development: it says the ambient V collapses
   no L-cardinal.
3. **THE ONE ROUTE THIS TASK CANNOT PRICE IS AN INTERNAL 5.5.** The demand comes
   from a hull and a collapse built in V (`src/L/BoundedSubset.lagda.md:1594-1603`).
   A version whose size comparison is internal would not ask for row 1. That is
   a mathematician's call and a new price, and this report does not estimate it.
4. **`[LJ-1.94]` IS NOT A PRECEDENT HERE.** It supplied `cardκ` at its own site
   from the ambient Hartogs cardinal (`archive/dev/LJ-dispatch-index.md:170`).
   `SuccCardL` fixes δ, Hartogs does not produce δ, and `site-forced`
   (`agents/tasks/LJ-1-550/Probe550.agda:385-389`) proves no other choice
   serves.

## C-22, C-42 AND THE OTHER LAWS THE BUNDLE NAMES

**C-22 (write the deliverable incrementally).** Partly kept and I say so
plainly. The probe was written and typechecked in pieces, each run recorded in
`runs/` as it landed, so no measurement was held to the end. **The report and
the review were written after the last measurement and not as a skeleton
first.** The task was short enough that nothing was at risk, but that is the
reason and not an excuse.

**C-42 (a refutation measures the site it names).** This task did not refute a
statement, so C-42's sweep is not owed by its own terms. **The nearest thing to
a refutation here is the finding that Route A does not remove the ambient
demand, and I swept for that shape. THE COUNT COMES FIRST.**

**THE NAME.** `IsCardinal` occurs in `src/` at SIX lines and no more:
`src/L/BoundedSubset.lagda.md:1046`, `:1047` and `:1386`, and
`src/L/StageBound.lagda.md:16`, `:65` and `:94`.

**THE TELESCOPE SLOTS.** THREE: `src/L/BoundedSubset.lagda.md:1386`,
`src/L/StageBound.lagda.md:65` and `:94`.

**THE SPEND SITES.** TWO, and both are inside `BoundedSubsetAt`:
`src/L/BoundedSubset.lagda.md:1597` and `:1601`, both as `cardκ α α∈κ`. Grepping
`cardκ` over `src/` returns seven lines and no more, and the other five are the
three telescope slots plus two PASS-THROUGHS at
`src/L/StageBound.lagda.md:74` and `:114`, which hand `cardκ` straight on.

**SO THE SHAPE IS ONE SITE AND NOT MANY.** `src/L/StageBound.lagda.md`'s two
slots are wrappers over the same `Devlin55.BoundedSubsetAt`. Anyone pricing an
internal 5.5 pays one proof and three telescopes, not three proofs.

**D-10 (price the truth of a recorded residue before pricing its proof).** Kept
and it is the whole first half of this report: the use site was read before any
Agda was written, and the target's truth was NOT priced because the brief
forbade it in those words.

**P-l and D-26.** Neither applies. `P-l` is about a statement's type naming a
transparent presentation of a stage; every type here names `Lset (fst δ)` behind
`[LJ-1.550]`'s existing definitions and nothing unfolds. `D-26` is about
well-founded keys on a tower and this task builds no key.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.** `:170` reads:
  `| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |`
  This is the one earlier task that SUPPLIED the ambient cardinality slot, and
  it is why point 4 above exists. `:167` reads:
  `| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |`
  The campaign recorded "IsCardinal is ambient" as a finding at `[LJ-1.91]`, and
  this task's NO-GO is that finding reaching `GCHStatement`.
- **`archive/dev/JOURNAL.md`: not used.** Grepped for `cardinal` and
  `GCHStatement`; the four hits are about `src/L/StageCardinal.lagda.md`'s size
  and timing, not about the ambient reading of `IsCardinal`. Declined.
- **`archive/dev/JOURNAL-archived.md`: not used.** Grepped the same way; its
  hits are route pricing from before the cardinal chapter was built. Declined.
- **`archive/dev/DD-archived.md`: not read.** 38 lines, zero hits for
  `cardinal`, `IsCardinal` or `GCHStatement`. Declined.
- **`dev/ARCHIVE.md`: read, and it takes no row from this task.** `:1` reads
  `# ARCHIVE.md: the archive registry`. Nothing was retired here, so W4 owes it
  nothing. Declined as evidence.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`: READ AND USED, and it is the source of the
  finding.** `:147` reads:
  `> 5.5 Lemma. Assume V = L. Let κ be a cardinal. If x is a bounded subset of`
  and `:164` reads:
  `The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every`
  The first line is why row 1 exists: the source lemma assumes `V = L`, so its
  "cardinal" is ambient and internal at once. The second confirms that the
  assignment `[LJ-1.550]` fixed (theorem-κ := the successor, theorem-α := κ) is
  Devlin's own.
- **`dev/literature/digest.md`: READ, and it confirms a gap rather than filling
  one.** `:345` reads:
  `8. **GCH via Skolem hull and collapse; |J_α| = |α|.** The argument shape is`
  and the item goes on to flag the GCH-in-L derivation as an open item to
  source. So the corpus carries no alternative to Devlin 5.5 for this step, and
  point 3 above cannot be priced from the literature that is here.
- **`dev/literature/truncation-and-selection.md`: not read.** Grepped for
  `ambient cardinal`, `cardinal of L`, `cardinal-preserv` and `collaps`: zero
  hits. This task eliminated no truncation and made no choice. Declined.
- **`dev/literature/geology.md`: not used.** One hit for `collaps`, at `:566`,
  and it is Usuba on the mantle and the generic mantle, which is set-forcing
  geology and not the ambient reading of a cardinal. Declined.
- **`dev/literature/terms-2026-08.md`: not used.** Its two `collaps` hits,
  `:87` and `:230`, are the transitive collapse as a naming question for the
  glossary. This task proposed no term. Declined.
