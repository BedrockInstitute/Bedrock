# LJ-1.545 report: the three families join at 12.5 percent of the cap, and the wall is not the field count

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-545/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. **No heap event.**

TARGET: one term `three-families-inhabited` in
`agents/tasks/LJ-1-545/Probe545.agda`, the extra hypotheses of
`[LJ-1.538]`'s nine env forms, `[LJ-1.539]`'s seven `subK` forms and
`[LJ-1.542]`'s twelve `numK` forms collected as ONE telescope, with a
witness at `KValue`'s frame, 28 fields in one value. Nothing lands in
`src/`. I did not build a `TFacts` value. I did not collect a fourth
family. I did not edit `src/`. I did not rebuild `[LJ-1.495]`'s shift.
I postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## VERDICT

**GO. THE 28 JOIN, AND THEY COST 12.5 PERCENT OF THE CAP.**

`three-families-inhabited` typechecks
(`agents/tasks/LJ-1-545/Probe545.agda:440-540`, top-level alias at
`:544`), exit 0, every run warning-free.

It PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-545
--brief agents/tasks/LJ-1-545/LJ-1.545.md`, exit 0, 9.19 s,
**0 UNRESOLVED of 1**, `probe_red=False`, `runs/witness-0.out`).
`.venv/bin/python` is absent in this worktree, as it was for
`[LJ-1.538]` (`agents/tasks/LJ-1-538/lj-1.538-report.md:34-36`),
`[LJ-1.539]` and `[LJ-1.542]`. I added no dependency.

I did not write `review-of-three-families.md`. The obligation is
inhabited, so the verdict on the obligation is GO.

**TWO FIGURES, AND THE REPORT USES THE FIRST ONE FOR THE CURVE.**

| file | contents | seconds | peak RSS (median) | of the 8 GiB cap |
|---|---|---|---|---|
| obligation only | record + packaging + frame | 5.01 to 5.69 | **1,069,932,544 B** | **12.46 %** |
| delivered | the above plus W3 and `statement-matches` | 8.54 to 9.74 | 1,684,815,872 B | 19.61 % |

The obligation-only figure is the like-for-like row, and the section
`THE CURVE` says why. Runs: `runs/obl-0.time` to `runs/obl-7.time` and
`runs/full-0.time` to `runs/full-6.time` plus `runs/final.time`.

## D-10, BEFORE ANY AGDA

**THE THREE TELESCOPES SHARE SEVEN ITEMS, CONFLICT ON NOTHING, AND THE
UNION IS 7 + 1 + 5 + 1.**

Read off the three probes, not off the briefs:

| task | telescope | evidence |
|---|---|---|
| `[LJ-1.538]` | `KValue`'s seven, then `ω∈σ : ⟨ ω ∈ sucV gam ⟩`, then FIVE free cells; cell 0 is PINNED to `SupplyEnv.B₀` | `agents/tasks/LJ-1-538/Probe538.agda:159-164` and `:177-178` |
| `[LJ-1.539]` | `KValue`'s seven, then SIX free cells, then a slot-one `valSub` | `agents/tasks/LJ-1-539/Probe539.agda:357-361` and `:368-373` |
| `[LJ-1.542]` | `KValue`'s seven, then SIX free cells, and nothing else | `agents/tasks/LJ-1-542/Probe542.agda:139-143` and `:150-151` |

**THEY SHARE.** All three carry `KValue`'s seven parameters word for
word (`src/L/Condensation.lagda.md:7380-7383`), so the union carries
them ONCE and not three times. That is the whole of the sharing, and it
is why the union telescope is 14 items and not 28.

**THEY DO NOT CONFLICT, AND THE ANSWER IS NOT "THEY DO NOT MENTION EACH
OTHER".** The one place they could have collided is the environment.
`[LJ-1.538]` PINS cell 0 to `SupplyEnv.B₀` because the nine env forms
read the carrier out of it (`Probe538.agda:177-178`, and `B₀` is
`LsetS gam ordγ` at `src/L/Coding/EnvSupply.lagda.md:124-125`).
`[LJ-1.539]` and `[LJ-1.542]` leave all six cells free. So the union
must take `[LJ-1.538]`'s environment, and the live question is whether
`valSub` is still a sane hypothesis where cell 0 is no longer free.
It is: `valSub` speaks about cell 1 (`Probe539.agda:370`, `lookup (suc
zero)`) and never about cell 0, and neither `[LJ-1.539]` nor
`[LJ-1.542]` reads cell 0 at all. **Pinning cell 0 costs the other two
families nothing.**

**`ω∈σ` IS NOT USED BY THE OTHER TWO FAMILIES, AND IT IS STILL
REQUIRED.** It is `SupplyEnv`'s eighth parameter
(`src/L/Coding/EnvSupply.lagda.md:111`); opening `SupplyEnv` is what
gives `B₀`, and `B₀` is what cell 0 is pinned to. So the union carries
it for the nine env forms and the other nineteen fields never consume
it. That is the same trim `[LJ-1.538]` reported at its own site for
`ordλ`.

**THE ANSWER TO THE BRIEF'S QUESTION IS: THE UNION IS ONE VALUE.**

## W3

**GO. `ω∈σ` AND `valSub` HOLD AT ONE FRAME, AND `valSub` IS INHABITED
THERE.**

The brief asks only whether the two can be stated together. The term
`valSub-at-carrier` (`Probe545.agda:121-122`, top-level alias `:124`)
answers the stronger question. At `[LJ-1.538]`'s pinned environment,
take cell 1 to be `B₀` as well. Then `valSub` says a member of the
CARRIER is a member of the BOUND, and that is `KFacts.carrierK`
(`src/L/Condensation.lagda.md:6112-6113`) at `KValue`'s own indices with
**no `subst` and no transport**: `Kenv`'s slot `iA` IS `LsetS gam ordγ`
(`src/L/Condensation.lagda.md:7389-7390`) and `B₀` IS `LsetS gam ordγ`
(`src/L/Coding/EnvSupply.lagda.md:125`), so the two are the SAME type.
The term is one identifier long.

So the union telescope is not vacuous, and the refutation the brief
allowed for did not happen.

W3 alone: exit 0, three forced rechecks, **2.46 to 2.54 s, median
552,583,168 B** (`runs/w3-0.time` to `runs/w3-2.time`; the file at that
run is `runs/Probe545.w3-only.agda.txt`). That is 6.4 percent of the
cap, which is the import cost and almost nothing else.

## THE OBLIGATION

`ThreeFamilies` (`Probe545.agda:144-258`) states the 28 fields ONCE at a
generic `K` and `γ'`, at `TFacts`'s own indices, and is instantiated at
`n = 9` against `KValue`'s `Fin 14` (`:443`). The nine come from
`Probe538.agda:72-129`, the seven from `Probe539.agda:163-204` and the
twelve from `Probe542.agda:94-105`, copied verbatim; the masters are
`src/L/Condensation/TwelveAgree.lagda.md:186-243`, `:265-331` and
`:145-156`.

`statement-matches` (`Probe545.agda:268-295`) is Agda's word that all 28
types ARE `TFacts`'s own: every field is read off a `TFacts` value by
projection, with no coercion, no `subst` and no re-association. It is
`[LJ-1.539]`'s device (`Probe539.agda:213-225`) at 28 fields instead of
seven. **It is not part of the obligation and the obligation never calls
it**, which is why the two figures in the verdict are separate.

Every one of the 28 is ONE application and nothing else:
the nine are `SE.envK-gen` / `SE.envInK-gen` as `[LJ-1.538]` applies
them, the seven are `SK.subK-from-sub` / `SK.subKSucc-from-sub` as
`[LJ-1.539]` applies them, and the twelve are `KV.facts .numK*` read at
the SHIFTED index with no conversion, as `[LJ-1.542]` reads them. No
`subst` was added at the field level for the join.

**`[LJ-1.539]`'s PACKAGING IS RE-MEASURED HERE AND NOT IMPORTED.**
`AGENTS.md:45` forbids carrying a measured cure by analogy, so
`SubKPack` (`Probe545.agda:313-395`) re-writes `[LJ-1.539]`'s `W3` block
at this site. It holds. So does the definitional shift the twelve rest
on, and so does `[LJ-1.509]`'s `arityK` bridge (`Probe545.agda:432-438`),
which reads `KV.facts .arityK` at the shifted index with no conversion.
If any of those three reductions ever stops being definitional, this
file stops checking.

**WHAT RESISTED: NOTHING IN THE MATHEMATICS.** The obligation
typechecked on its first run (`runs/full-0.time`). No weakening was
needed, no hypothesis was added beyond the union D-10 predicted, and no
field needed a bridge that its own predecessor had not already built.

**WHAT RESISTED: THE MEASUREMENT.** Two things, both in `THE CURVE`.

## THE CURVE

**FOUR ROWS, ALL FOUR MEASURED BY ME, ON THIS PANE, AT ONE CALIBER.**
The brief asked me to re-run the two imported figures if it fitted the
estimate. It did, so I re-ran all THREE predecessor probes here rather
than importing any of them.

| fields | task | seconds | peak RSS (median) | of the cap | run |
|---|---|---|---|---|---|
| 7 | `[LJ-1.539]` | 3.74 to 3.76 | 749,109,248 B | 8.72 % | `runs/rerun-539-*.time` |
| 9 | `[LJ-1.538]` | 3.97 to 3.98 | 722,698,240 B | 8.41 % | `runs/rerun-538-*.time` |
| 12 | `[LJ-1.542]` | 2.94 to 2.95 | 679,690,240 B | 7.91 % | `runs/rerun-542-*.time` |
| **28** | **`[LJ-1.545]`** | **5.01 to 5.69** | **1,069,932,544 B** | **12.46 %** | `runs/obl-*.time` |

**THE GROWTH IS LINEAR IN THE FIELD COUNT, AND THE PER-FIELD CONSTANT IS
A PROPERTY OF THE FAMILY.** That is the one sentence, and it is about
the numbers I measured myself.

The four totals above each contain an import baseline that is NOT the
family. So I measured the four baselines too, by running each probe's
header alone with the module line renamed
(`runs/Probe545.base538.agda.txt`, `.base539.`, `.base542.`, `.base.`):

| task | baseline | whole file | the family alone | per field |
|---|---|---|---|---|
| `[LJ-1.539]`, 7 | 589,496,320 B | 749,109,248 B | 159,612,928 B | 22,801,846 B |
| `[LJ-1.538]`, 9 | 564,346,880 B | 722,698,240 B | 158,351,360 B | 17,594,595 B |
| `[LJ-1.542]`, 12 | 564,166,656 B | 679,690,240 B | 115,523,584 B | 9,626,965 B |
| `[LJ-1.545]`, 28 | 546,078,720 B | 1,069,932,544 B | 523,853,824 B | 18,709,065 B |

**SO THE 7-9-12 BAND WAS NEVER FLAT: IT WAS THREE DIFFERENT PER-FIELD
RATES UNDER ONE BASELINE THAT DOMINATED ALL THREE.** `subK` costs
22.8 MB a field, the env forms 17.6 MB, `numK` 9.6 MB. `[LJ-1.542]`'s
"twelve fields cost less than seven" is confirmed as a fact about the
files and explained: twelve of the cheapest family cost less than seven
of the dearest, on top of a baseline of about 560 MB that both files
pay.

**THE JOIN IS ADDITIVE TO WITHIN 20.8 PERCENT.** The three families cost
159,612,928 + 158,351,360 + 115,523,584 = **433,487,872 B** separately.
Joined in one file they cost **523,853,824 B**. The excess is
**90,365,952 B, 20.8 percent**, and it is the price of the join itself.
**Nothing here is superlinear.**

**AT THE MEASURED RATE THE HEAP TURNS AT ABOUT 430 FIELDS.** With a
baseline of 546,078,720 B and the union's own rate of 18,709,065 B a
field, the 8 GiB cap is reached at (8,589,934,592 - 546,078,720) /
18,709,065 = **429 fields**. `TFacts` has 59 fields in total
(`src/L/Condensation/TwelveAgree.lagda.md:129`), which at that rate is
about 1,650,000,000 B, **19 percent of the cap**. THIS IS AN
EXTRAPOLATION FROM 28 AND NOT A MEASUREMENT, and `AGENTS.md:45` says it
must be re-measured at its own site before anything is funded against
it. It is offered as the order of magnitude, which is what nobody had.

**TWO THINGS RESISTED THE MEASUREMENT, AND BOTH ARE RESULTS.**

**FIRST: PEAK RSS STOPS BEING REPRODUCIBLE ABOVE ABOUT 1 GB.**
`[LJ-1.542]` reported that "the seconds carry a tenth of a second of
load noise and the peak RSS does not"
(`agents/tasks/LJ-1-542/lj-1.542-report.md:40-41`). **That holds at its
own size and it fails at mine.** My nine predecessor re-runs vary by
16,384 B inside each task, which is the measurement's own granularity.
Eight runs of my byte-identical delivered file span **1,452,261,376 B to
1,709,637,632 B, a spread of 257,376,256 B, 17.7 percent of the
minimum** (`runs/full-0.time` to `runs/full-6.time`, `runs/final.time`;
`diff` confirmed the file was byte-for-byte the same for all eight). The
obligation-only file is bimodal in the same way: runs 0 to 2 sit at
about 1,010,000,000 B and 5.5 to 5.7 s, runs 3 to 7 at 1,069,940,736 B
and 5.0 to 5.1 s. **The faster runs use MORE memory**, which is what a
run with fewer major collections looks like. **So at this scale a single
peak-RSS figure is not evidence. Plan against the maximum.**

**SECOND: A SECOND HEAVY TERM IN THE SAME FILE COSTS 7.1 TIMES WHAT IT
COSTS ALONE.** `statement-matches` added to a light file (the record and
nothing else) costs **98,598,912 B** (`runs/smonly-*.time` against
`runs/stated-*.time` and `runs/base-tf-*.time`). The SAME term added to
the file that already carries the obligation costs **701,710,336 B**
(`runs/full-*.time` against `runs/nosm-*.time`). **7.1 times.** Under
`-I0` the runtime does not return memory between terms, so a file's peak
RSS is a high-water mark over everything it has elaborated, and two
heavy terms do not cost the maximum of the two. `[LJ-1.74]` measured the
same shape from the other side: "PEAK PER PROCESS ... 3 and 6 rows
green, 9 and 12 wall. A one-file split walls too. Separate invocations
are green" (`archive/dev/LJ-dispatch-index.md:137`, the row above at
`:133`).

**WHAT THIS BUYS THE NEXT BRIEF.** A collection brief should be priced
in FIELDS times the family's own per-field rate, plus one baseline, plus
20 percent for the join, and it should name **how many heavy terms share
the file**, because that is the axis that is not linear. A brief that
asks for the obligation AND its certification in one file is asking for
two heavy terms and should expect the 7.1.

## WHAT THIS SAYS ABOUT LJ-1.534

**I HAVE NO REPORT AND NO PROBE FROM `[LJ-1.534]`, AND NO BRIEF EITHER.**
`agents/tasks/LJ-1-534/` does not exist in this worktree, `git log --all`
returns nothing for it, and `dev/pod/transitions/2026-08.jsonl` carries
zero `LJ-1-534` records. What the tree does hold is the rule table's
admitted rows (`dev/pod/table.toml:14714-14815`) and my own brief's
record that the heap-wall row "matched a heap wall FOUR times, exit 251
each, to attempt_max" (`agents/tasks/LJ-1-545/LJ-1.545.md:185-186`), and
that `[LJ-1.534]` was collecting sixteen hypotheses at once
(`agents/tasks/LJ-1-545/LJ-1.545.md:30`). **So I reason from its brief
and from my own numbers, and that is what I did.**

**MY NUMBERS MAKE THE FIELD COUNT AN UNLIKELY CAUSE.** 28 fields in one
value reach 12.5 percent of the same 8 GiB cap and the growth is linear,
so a wall would need about 430 fields on this axis; `[LJ-1.534]` was
nowhere near that, and it was counting hypotheses rather than fields in
any case.

**THE SOMETHING ELSE I CAN SEE HAS TWO NAMES, AND I MEASURED THE
SECOND.** The first is the axis my task never pushed: my union carries
TWO extra hypotheses above `KValue`'s seven, and `[LJ-1.534]` carried
sixteen, so telescope width is untested here and stays the prime
suspect; `[LJ-1.542]` had already read its table that way
(`agents/tasks/LJ-1-542/lj-1.542-report.md:218-221`). The second is the
file-level compounding I did measure: a second heavy term in one file
cost 7.1 times what it cost alone, `[LJ-1.74]` measured that the peak is
PER PROCESS and that a one-file split walls where separate invocations
are green (`archive/dev/LJ-dispatch-index.md:137`), and R-35's appendix
records a 12 GB wall caused by STORAGE POSITION and not expression size,
whose only measured cure was inlining at each use site
(`dev/LESSONS.md:827-832`). A sixteen-hypothesis collection is very
likely several heavy terms in one file, and on this evidence that is
where the cap goes, not into the field count.

## W2, ANSWERED

The brief states it and this is the answer. `ThreeFamilies`
(`Probe545.agda:144-258`) states the 28 ONCE at a generic `K` and `γ'`
and is instantiated at `n = 9` (`:443`). `SubKPack`
(`Probe545.agda:313-395`) states the `subK` packaging ONCE, generic in
the environment length, the environment and all four indices, and is
applied seven times. No block in this file is written twice, and nothing
is stated in a fixed form that could have been stated generically. No
deadline forced a fixed form, so there is no conflict to report.

## W3, THE WIDEST UNMEASURED TERM, FOR THE NEXT TASK

**It is the telescope width, and the probe is a telescope of sixteen
hypotheses over the SAME 28 fields.**

    -- the union telescope, widened to sixteen extra hypotheses,
    -- with the SAME 28-field witness, at KValue's frame

If 28 fields at 2 extra hypotheses cost 12.5 percent of the cap and 28
fields at 16 extra hypotheses wall, the wall is telescope width and
`[LJ-1.534]` is explained. If it does not wall, the remaining suspect is
the number of heavy terms in one file, and that is settled by adding
terms rather than hypotheses. ESTIMATE: about 40 lines on top of the
delivered probe, under 20 seconds of Agda if it does not wall.

## SCOPE, AND WHAT I TOUCHED

I wrote only inside `agents/tasks/LJ-1-545/`:
`Probe545.agda`, `lj-1.545-report.md`, and `runs/`. `git status` shows
that directory and nothing else. I ran Agda over the three predecessor
probes, which WROTE their interface files under `_build/2.8.0/agda/` and
changed no source; that path is declared `class = "toolchain"` in
`dev/build-manifest.toml:117-120`, so no new lifecycle declaration is
owed.

The ratio bar cannot fire on this task: my write scope carries no
` ```agda ` fence, so the in-fence line count is 0 and the divisor is
absent by construction, as the brief's role section states.

## THE RUN RECORD

Every file variant I measured is kept beside its runs, so a critic can
re-run any row of any table above:

| file | what it is |
|---|---|
| `runs/Probe545.w3-only.agda.txt` | the file at the W3 run |
| `runs/Probe545.base.agda.txt` | my imports alone |
| `runs/Probe545.base-tf.agda.txt` | my imports plus `TwelveAgree` |
| `runs/Probe545.stated-only.agda.txt` | imports plus the 28 field TYPES |
| `runs/Probe545.smonly.agda.txt` | imports plus the types plus `statement-matches` |
| `runs/Probe545.obligation-only.agda.txt` | the obligation, the curve's row |
| `runs/Probe545.nosm.agda.txt` | the obligation plus W3 |
| `runs/Probe545.delivered.agda.txt` | the delivered file |
| `runs/Probe545.base538.agda.txt` | `[LJ-1.538]`'s header alone, module renamed |
| `runs/Probe545.base539.agda.txt` | `[LJ-1.539]`'s header alone, module renamed |
| `runs/Probe545.base542.agda.txt` | `[LJ-1.542]`'s header alone, module renamed |

**ONE CORRECTION TO THE BRIEF'S TABLE, AND IT IS ABOUT LIKE FOR LIKE.**
The brief's three-family table (`agents/tasks/LJ-1-545/LJ-1.545.md:22-26`)
gives `[LJ-1.542]` as 649,183,232 B. My re-run of `[LJ-1.542]`'s
DELIVERED file gives **679,690,240 B**, and it reproduces the other two
rows to the byte (722,698,240 and 749,125,632). The 649,183,232 figure
is `[LJ-1.542]`'s OBLIGATION-ONLY file, not its delivered one: its own
report says the delivered file sits "at about 7.9 percent"
(`agents/tasks/LJ-1-542/lj-1.542-report.md:208-209`), which is 679,690,240 B,
and its `runs/delivered-*.time` carry exactly that number. **So the
brief's table put one obligation-only row beside two delivered rows.**
The ordering it draws survives the correction (679.7 < 722.7 < 749.1),
and the table in `THE CURVE` above is uniform.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ AND USED. `:137` reads
  "| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |".
  It is the precedent for the whole task: the telescope was green and the
  APPLICATION walled. `:133` reads
  "| LJ-1.70 | The generic frame and the discharge | 24 DISCHARGED, 14.7 s | TwelveAgree takes 47 facts once and instantiates the twelve rows. The record shape heap-walled; the telescope is green |".
  Both are cited in `WHAT THIS SAYS ABOUT LJ-1.534`.
- `archive/dev/JOURNAL-archived.md`: READ AND USED. `:760` reads
  "small-index heap wall, the only cure is inlining), C-14 appended (third".
  It is the appending record for R-35, which sent me to
  `dev/LESSONS.md:827-832` and its "Storage position, not expression
  size, was the trigger" at `:831`.
- `archive/dev/JOURNAL.md`: searched for `1.534`, `1-534` and
  `heap wall`; zero hits. NOT USED.
- `dev/ARCHIVE.md`: searched for the same three; zero hits. NOT USED.
  This task retires no module, so W4 has nothing to record here.
- `archive/dev/DECISIONS-archived.md`: 61 lines, zero hits for the same
  three. DECLINED: it resolves bare `D<n>` codes and this task cites
  none.

## LITERATURE USED

**NO HIT, AND ALL FIVE ARE DECLINED IN WRITING.** This task chooses no
mathematics: it collects three families that three predecessors already
built and it measures a heap. No primary source bears on that.

- `dev/literature/digest.md`: NOT USED. It pins the orthodox form of
  the rud route; this task touches no rud construction.
- `dev/literature/truncation-and-selection.md`: NOT USED. It is about
  how the two literatures pick a witness; the witness here is fixed by
  the three predecessor probes.
- `dev/literature/devlin-II5.md`: NOT USED. It is the Condensation
  Lemma and the GCH in L, the mathematics BEHIND `KFacts`; this task
  changes no statement and re-derives none.
- `dev/literature/geology.md`: NOT USED. Set-theoretic geology is not
  on the `[LJ-1]` path at all.
- `dev/literature/glossary-review-2026-08.md`: NOT USED. I added no
  glossary entry and named no new term.
