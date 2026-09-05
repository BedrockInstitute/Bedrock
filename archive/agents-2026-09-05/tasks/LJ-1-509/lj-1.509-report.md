# LJ-1.509 report: the subK family, and the one membership that pays all seven

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-509/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `subK-and` in `agents/tasks/LJ-1-509/Probe509.agda`, the
type of `TFacts`'s `subK₁-and` at `KValue`'s frame, plus a written answer
on whether the same argument serves the other five `subK` fields the brief
names. Nothing lands in `src/`. I did not build any of the other six, and
the sixth is a field the brief did not name. I did not touch `valK`,
`valV`, `valW` or `wKfact`. I did not build a `TFacts` value.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection and it does not start phase 3. No Boundary clause is
in conflict.

## PREDECESSORS, READ FIRST

A predecessor taken as a hypothesis is its REPORT, never the brief. Audit
F1 is the measurement behind that rule: its heading at
`dev/pod/audit-2026-08-20.md:34` reads `### F1 / F2. LJ-1.398 GO is hollow`,
and `:36-42` is the case, a brief's obligation type taken as a hypothesis
after the predecessor's report had refuted it. I opened each report below.

`[LJ-1.495]` is **GO** (`agents/tasks/LJ-1-495/lj-1.495-report.md:71`),
quoted at `:71`:

> **GO.** `twice` typechecks

and its full-file term at `:74`:

> `tfacts-shared-from-kfacts` typechecks

Its measured frame is `agents/tasks/LJ-1-495/lj-1.495-report.md:56-60`:
`KValue` is `KFacts` at `n = 14` over `Kenv : S ^ 14`, six cons cells give
`S ^ 20` and `Fin 14`, and `TFacts` at `n = 9` is `S ^ (11 + 9)` over
`Fin (5 + 9)`. I took that frame. I did not import its probe.

`[LJ-1.500]` is **GO** (`agents/tasks/LJ-1-500/lj-1.500-report.md:145`).
I took its method, not its result: state the field type ONCE at `TFacts`'s
generic shape, then instantiate at `KValue`'s frame.

`[LJ-1.506]` is **GO** (`agents/tasks/LJ-1-506/lj-1.506-report.md:5`).
I took its refutation idiom: `sucʟ`, `self∈sucV` and `∈-irrefl`, at
`agents/tasks/LJ-1-506/Probe506.agda:128-130`.

`[LJ-1.113]` is the row this task tests
(`agents/tasks/LJ-1-113/lj-1.113-report.md:48`). Its verdict for row 18 was
NEEDS NEW CONTENT, not FALSE, so nothing in it required a stop.

## VERDICT

**GO.** `subK-and` typechecks
(`agents/tasks/LJ-1-509/Probe509.agda:199-207`, top-level alias at `:267`,
exit 0, median **3.74 s** on three forced rechecks of the full file) and
PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-509
--brief agents/tasks/LJ-1-509/LJ-1.509.md`, exit 0, 3.44 s, 0 UNRESOLVED
of 1, `probe_red=False`, `runs/witness-2.out`, which is the run AFTER the
last comment correction; `runs/witness-1.out` is the earlier one at
3.26 s). `.venv/bin/python` is absent in this worktree. I added no
dependency.

W3 is **GO** and it is the load-bearing half of this return: `T` IS a named
slot of the frame, so `[LJ-1.113]`'s route is usable and the family does
not need a different argument.

I did not write `review-of-subK-and.md`. The verdict is GO.

**A GO PAYS SEVEN POSITIONS FROM ONE MEMBERSHIP, not the six the brief
counted, and the argument was already in `src/`.** It does not land
anything in `src/`. It does not build the other six fields. It does not
inhabit any other `TFacts` field. It does not build a `TFacts` value. It
does not fill `someEnv`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not claim
a trophy.

## 1. W3, THE WIDEST UNMEASURED TERM: WHAT IS `T`

Done first, before any obligation term, as the brief required.

**`T` IS `lookup (suc zero) γ'`: THE SECOND CELL OF THE FRAME'S OWN
ENVIRONMENT. It is not a bound variable of the adequacy, so the task does
NOT stop here.**

`TFacts.subK₁-and` (`src/L/Condensation/TwelveAgree.lagda.md:265-270`)
states its hypothesis over `(x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')` at the four
indices 8, 5, 4, 1. Seven cells sit in front of `γ'`, so index 8 is
`γ'` position 1. `subValAt-adequate`
(`src/L/Coding/Model.lagda.md:821-824`) then pins
`pr (pr (fst ar) (fst a)) (fst y)` into that cell.

`what-T-is` (`Probe509.agda:65-79`) is that instance with the right-hand
side WRITTEN OUT, so Agda and not this report is what names the cell. Exit
0, median **1.33 s** on three forced rechecks of the W3-only file, which is
kept verbatim at `runs/Probe509.w3-only.agda.txt`.

**AND THE FRAME DOES NOT ALREADY GIVE `T ∈ K`.** The cell
`lookup (suc zero) γ'` occurs in exactly two `TFacts` field types, `valK`
(`src/L/Condensation/TwelveAgree.lagda.md:175`) and `valK-un` (`:179`), and
in both it is the CONTAINER of a membership, never a member of `K`. COUNT
of `TFacts` fields that state `T ∈ K`: **0**. So `[LJ-1.113]`'s
"NEEDS NEW CONTENT" was right about the record and still is.

**A CORRECTION TO THE BRIEF, AND IT CHANGES NO MATHEMATICS.** The brief
calls this hint three months old, in its title and at its reasoning section
("a three month old hint"). **The tree does not give that date.**
`agents/tasks/LJ-1-113/` entered git in commit `1b6b0444`, dated
`2026-08-13` (`git log --diff-filter=A -- agents/tasks/LJ-1-113/`), which
is NINE days before this dispatch. The report itself says
`agents/tasks/LJ-1-113/lj-1.113-report.md:4`:

> ASD-STE100. This report is `_build/lj-1.113-report.md`.

so it was authored before the `agents/` move of 2026-08-13 and its exact
authoring date is not recorded anywhere I could find. The evidence supports
"at or before 2026-08-13" and nothing longer. The row's CONTENT is
confirmed; only the age is wrong.

## 2. D-10: THE TARGET IS TRUE, AND IT IS TRUE FOR THE STATED REASON

D-10 asks whether the recorded residue's TARGET is true before its proof is
priced. Three things were checked at their own lines.

1. **The statement is what the brief says it is.** `statement-matches`
   (`Probe509.agda:107-113`) reads `TFacts.subK₁-and` off a `TFacts` value
   at the type `SubKAnd K γ'`, with no coercion, no `subst` and no
   re-association. Agda accepts it, so `SubKAnd` IS the field's type. The
   obligation never calls that term, so no `TFacts` field proves a `TFacts`
   field.

2. **`arityK` is delivered at these indices, and it needs NO `KFactsCons`.**
   `[LJ-1.495]` shifts the record with six `KFactsCons` steps. For THIS
   field the shift is free: `lookup (suc i) (c ∷ γ)` is `lookup i γ` by
   definition, and both the index and the environment are literal chains,
   so `KValue.facts .arityK` (`src/L/Condensation.lagda.md:6114-6115`, value
   at `:7411`) already has the shifted type. `Probe509.agda:206-207` passes
   it with no conversion. **That is a cheaper route than the brief assumed
   and the next brief should not pay for six conses to reach a field.**

3. **The bare form is FALSE, so `TK` is not optional.**
   `no-TK-is-not-a-theorem` (`Probe509.agda:254-265`, top-level alias at
   `:268`) refutes the `TK`-free statement AT THIS FRAME, not at a generic
   one (C-42 measures the site it names). `γ'` position 1 at
   `KValue`'s frame is `c5`, one of the six cells
   the shift conses on, so a counterexample only has to put one Kuratowski
   pair into `c5` whose right component escapes `Lset lam`; `Lset lam`
   itself escapes it by `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`). Exit 0.

**SO THE WEAKEST REPAIRING HYPOTHESIS IS `TK` ITSELF**, which is the one the
obligation takes. It pins no slot: `c5` stays a free variable of the frame,
and `[LJ-1.505]` is not pre-empted.

## 3. THE OBLIGATION

**THE DERIVATION IS ALREADY IN `src/`, AND `[LJ-1.113]` DID NOT KNOW IT.**
`Fact.subK-gen` (`src/L/Coding/EnvSupply.lagda.md:481-487`) carries the
whole argument, tower-neutral over `(K, Ktr)` and generic in the
environment and the four indices. `EnvSupply`'s own comment calls the block
"the seven subK-* fields" (`src/L/Coding/EnvSupply.lagda.md:480`). So this
task supplied INPUTS to a delivered term; it wrote no set theory.

`SubK` (`Probe509.agda:140-169`) takes two hypotheses and nothing else:

| hypothesis | shape | where it comes from |
|---|---|---|
| `arity` | `(N v : S) → v ∈ N → N ∈ Kset → v ∈ Kset` | `KFacts.arityK`, `src/L/Condensation.lagda.md:6114-6115` |
| `TK` | `lookup (suc zero) γ' ∈ Kset` | nowhere in the record; supplied by the frame |

**THE ONE NEW STEP IS A PACKAGING, AND IT IS THREE LINES.** `Fact` wants
`isTransV (fst Kset)` (`src/L/Constructible.lagda.md:83-84`), which
quantifies over the RAW carrier `V ℓ`; `arityK` quantifies over `S`. `Ktr`
(`Probe509.agda:154-158`) closes that gap with `isL-trans`
(`src/L/Constructible.lagda.md:379`): a member of `fst Kset` is `isL`
because `Kset` is, and a member of that member is `isL` again, so each raw
set packages back into `S`. **At any `K` that is itself an `S` the two are
INTERDERIVABLE: `isTransV` gives `arityK` by applying it at `fst N` and
`fst v`, and `arityK` gives `isTransV` by the packaging above. The S-level
form is the one the frame delivers, so ask for that.** That is the finding
a later brief should reuse: do not ask a frame for `isTransV`; ask for
`arityK` and package.

`subK-and` (`Probe509.agda:162-169`) is then `subK-gen` at the four indices
8, 5, 4, 1, and `Frame.subK-and-at-KValue` (`:199-207`) instantiates it at
`n = 9` against `KValue`'s `Fin 14`.

## THE SIX subK FIELDS

`subK-gen` (`src/L/Coding/EnvSupply.lagda.md:481-487`) is generic in the
environment LENGTH, the environment itself and all four `Fin` indices. So a
field is served unchanged whenever its hypothesis is `γ ⊨ subValAt T ar a y`
and its conclusion is `lookup y γ ∈ K`, whatever the prefix. The prefix
length only changes the four numerals passed. `subValSuccAt` fields need the
SIBLING generic `subKSucc-gen` (`:489-495`), which is a different term.

| # | field | line | index quadruple | `T` resolves to | verdict |
|---|---|---|---|---|---|
| 1 | `subK₁-and` | `:265` | 8, 5, 4, 1 over a 7-cell prefix | `γ'` position 1 | **BUILT** here |
| 2 | `subK₀-and` | `:271` | 8, 5, 3, 0 over a 7-cell prefix | `γ'` position 1 | serves UNCHANGED, same generic, four different numerals |
| 3 | `subK₁-imp` | `:277` | 9, 6, 5, 2 over an 8-cell prefix | `γ'` position 1 | serves after a PREFIX CHANGE, same generic |
| 4 | `subK₀-imp` | `:283` | 9, 6, 4, 1 over an 8-cell prefix | `γ'` position 1 | serves after a PREFIX CHANGE, same generic |
| 5 | `subK-neg` | `:290` | 7, 4, 3, 1 over a 6-cell prefix | `γ'` position 1 | serves after a PREFIX CHANGE, same generic |
| 6 | `subK-un` | `:311` | 7, 4, 3, 1 over a 6-cell prefix, `subValSuccAt` | `γ'` position 1 | does NOT serve: needs `subKSucc-gen`, `src/L/Coding/EnvSupply.lagda.md:489-495` |

**ALL SIX READ `T` OUT OF THE SAME CELL, `γ'` POSITION 1.** So ONE `TK` pays
all six, and the six do not need six memberships. That is the number the
brief asked for.

**THERE IS A SEVENTH `subK` FIELD AND THE BRIEF NAMED SIX.** `subK-allin`
(`src/L/Condensation/TwelveAgree.lagda.md:326-331`) is `subValSuccAt` at
8, 5, 3, 1 over a 7-cell prefix, with `T` again at `γ'` position 1. It is in
the same family, it is served by `subKSucc-gen`, and the same one `TK` pays
it. `EnvSupply`'s own comment counts seven (`:480`). **So the count is SEVEN
POSITIONS FROM ONE MEMBERSHIP, not six.** I did not build it.

## transK

**`transK` (`src/L/Condensation/TwelveAgree.lagda.md:262-264`) IS `arityK`
with its two arguments swapped, and the tree says so twice.**
`src/L/Coding/EnvSupply.lagda.md:436` reads
`arityK₀ N v hv hNK = transK v N hv hNK`, and
`src/L/Condensation/TwelveAgree.lagda.md:353` reads
`arityK N v hv hNK = transK v N hv hNK` inside `AbstractFrame`, which is the
frame that consumes `TFacts`. **So `transK` is paid for nothing at any frame
that carries `KFacts`.** This is the cheap confirmation the brief asked for.
It is NOT the obligation and I have not counted it as one.

## 4. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

| piece | written once at | instantiated at |
|---|---|---|
| `subK-gen` | `src/L/Coding/EnvSupply.lagda.md:481-487`, generic in `n`, `γ` and four `Fin`s | `Probe509.agda:163-169` |
| `SubKAnd` | `Probe509.agda:90-99`, at `TFacts`'s own `Fin (5 + n)` over `S ^ (11 + n)` | `n = 9`, `Probe509.agda:204` |
| `SubK` | `Probe509.agda:140-169`, generic frame | `Probe509.agda:205-207` |
| `what-T-is` | `Probe509.agda:65-79`, generic frame | reused by the refutation, `Probe509.agda:261-264` |

**I RE-DERIVED NOTHING THAT `src/` ALREADY HAS.** The Kuratowski split is
`Fact.prK` (`src/L/Coding/EnvSupply.lagda.md:452-459`), reached through
`subK-gen`; this probe writes no `pairing-ax` and no `∈∈ₛ`. The statement is
written once and instantiated once. No site is named as a fixed form. There
is no conflict with W2.

W4 does not fire: no module was retired.

P-l did not fire. `SubKAnd`'s type (`Probe509.agda:90-99`) names `Fin`,
`lookup`, `subValAt` and numerals, and NO transparent stage presentation.
`sucV` occurs twice in a stated type in this file, at `Probe509.agda:193`
and `:231`, and both are `KValue`'s OWN telescope entry copied verbatim
from `src/L/Condensation.lagda.md:7381`; there `sucV` is applied to a bound
variable, which is not the shape P-l names. The refutation's successor is
`sucʟ`, which is `opaque` (`src/L/Axioms/Numerals.lagda.md:97-105`), the
same guard `[LJ-1.506]` used.

D-26 did not fire: this is a closure over a record, not a well-founded key.

C-42 fired and is answered above in section 2 item 3 and in the six-field
table: the refutation names ONE site and the table is the sweep of the shape
across the record, seven positions counted, not the cure priced.

## 5. MEASUREMENTS

One Agda process at a time. `GHCRTS="-A64m -I0 -M8g"`, set by the program on
this pane, untouched. A recheck is forced by deleting
`_build/2.8.0/agda/agents/tasks/LJ-1-509/Probe509.agdai` before each run,
so the probe re-elaborates while the `src/` interfaces stay warm.

| file | runs | median wall | peak RSS | evidence |
|---|---|---|---|---|
| W3 only, `what-T-is` alone | 3 forced | **1.33 s** | 302,596,096 B (288.6 MiB) | `runs/w3-r0..2.{out,time}` |
| full file, all four terms | 3 forced | **3.74 s** | 668,221,440 B (637.3 MiB) | `runs/full-r0..2.{out,time}` |
| witness meter | 2 | 3.26 s, 3.44 s | 653,656,064 B (run 1) | `runs/witness-1.out`, `runs/witness-2.out` |
| final forced recheck | 1 | 3.79 s | 668,205,056 B | `runs/final.{out,time}` |

Individual wall times: W3 1.34, 1.33, 1.31; full 3.79, 3.73, 3.74. Exit 0
everywhere. No heap event, no WALL, no rerun after a failure. Every term in
the file typechecked on its FIRST submission; the later runs are the forced
rechecks and two comment corrections, not repairs.

**THE W3 NUMBER IS MEASURED AT ITS OWN SITE AND NOT FUNDED AGAINST
`[LJ-1.506]`'s W3**, as the brief required: that one opened a code set and
this one opens an adequacy.

**THE BRIEF'S SHAPE ESTIMATE WAS 170 LINES, OF WHICH 45 THE OBLIGATION.**
Measured: the file is 268 lines, of which 135 are comment or blank and 133
are code. The obligation's own chain, `SubKAnd` (`:90-99`) plus `SubK`
(`:140-169`) plus `Frame` (`:191-207`), is **48 code lines**; `what-T-is`
(`:65-79`) is 15; `statement-matches` (`:107-113`) is 7; the refutation
(`:229-265`) is 30. **THE OBLIGATION'S 48 LINES SIT ON THE BRIEF'S 45-LINE
SHAPE, AND ALMOST ALL OF THEM ARE THE STATEMENT.** `subK-and`'s BODY is
seven lines (`:163-169`) and `Frame`'s instantiation is two (`:206-207`);
the rest is the field type written out and two module telescopes. The file
is longer than the 170-line shape because `statement-matches` and the
refutation are extra, and the brief required neither. Comparables are of
SHAPE and nothing is funded against them.

**THE RATIO BAR DOES NOT FIRE.** This task wrote a raw `.agda` probe, this
report and the `runs/` evidence, and nothing else. A raw `.agda` file
carries no ` ```agda ` fence, so the divisor is 0 and the bar cannot fire.
In-fence `agda` lines under `src/` written by this task: **0**. Nothing
landed in `src/`.

## 6. WHAT THE NEXT BRIEF SHOULD KNOW

1. **One membership pays seven positions, not six.** `TK` at `γ'` position 1
   discharges `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`,
   `subK-neg`, `subK-un` and `subK-allin`. The last two go through
   `subKSucc-gen`, not `subK-gen`.
2. **Ask a frame for `arityK`, never for `isTransV`.** The S-level form is
   what `KFacts` delivers and it is no weaker; `isL-trans` is the whole
   bridge and it is three lines (`Probe509.agda:154-158`).
3. **The six-fold shift is definitional for a FIELD.** MEASURED for
   `arityK` only (`Probe509.agda:206-207`): `KValue.facts .arityK` is
   accepted at `TFacts`'s shifted index with no `KFactsCons` and no
   conversion, because `lookup` reduces through the literal cons chain.
   The same reduction is available to any single field, but I measured one.
   `[LJ-1.495]` needed the conses to build a whole RECORD, which is a
   different job.
4. **`TK` itself is now the open question for this family, and it is one
   question, not seven.** It asks whether the frame's value-set slot lies in
   the bound. That is a `KValue`-frame question and it belongs with whatever
   task fixes what occupies `γ'` position 1. This task deliberately did not
   pin it.
5. **`valV`, `valW` and `wKfact` are a DIFFERENT closure and this result does
   not reach them.** `Fact.tmValK` (`src/L/Coding/EnvSupply.lagda.md:575-592`)
   needs TWO memberships, the environment's and the term's, not one. I did
   not touch them; `[LJ-1.508]` holds that ground.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:146` reads:
  `| LJ-1.77 | Machine-check whether KFacts is uninhabitable | CONFIRMED, one step | arityK gives X in X through the singleton; ∈-irrefl refutes it. 6 masters take KFacts, 20 take a field |`
  That is the same refutation shape this task used at
  `Probe509.agda:254-265`, and it is why the refutation was cheap rather
  than novel. `:149` reads:
  `| LJ-1.79 | Guard the closure facts across the band | WHOLE BAND REPAIRED, GREEN | KFacts and every row guarded; arityK bound by transitivity. The LJ-1.77 refutation no longer typechecks |`
  which records that `arityK` was already bound by transitivity across the
  band, and `:175` reads:
  `| LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |`
  which is the precedent that transitivity of `K` closes this class of field.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` reads: `# ARCHIVED 2026-08-20`.
  It is a retired per-episode journal and holds no `subK`, `arityK`, `transK`
  or `subVal` occurrence (grep count 0). Not used.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** The retired-route journal,
  grep count 0 for `subK`, `arityK`, `transK` and `subVal`. Not read beyond
  that search.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` reads:
  `# ARCHIVE.md: the archive registry`. It registers RETIRED MODULES, and W4
  did not fire on this task because nothing was retired. Grep count 0 for
  this family. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** The archived `D<n>`
  series, which is not a rule in force. Grep count 0 for this family. Not
  used.

## LITERATURE USED

- `dev/literature/devlin-errata.md`: **READ AND USED as background only.**
  `:135` reads:
  `  "Let u be an infinite transitive set containing only finitely many sets of`
  which is the `K(u)` setting `KValue`'s own comment names
  (`src/L/Condensation.lagda.md:7369-7370` calls the bound "Devlin's `K(u)`
  on this coding"). It confirms that the transitivity this task packages is
  the bound's own property in the source, not an artefact of the coding. **No
  step of the Agda rests on it.**
- `dev/literature/devlin-II5.md`: **DECLINED.** It is the condensation
  lemma's dossier; `:75` reads:
  `> (ii) if Y ⊆ X is transitive, then π ↾ Y = id ↾ Y;`
  which is transitivity of a COLLAPSE argument, a different use of the word.
  Nothing in this task touches condensation or collapse. Not used.
- `dev/literature/truncation-and-selection.md`: **DECLINED.** `:1` reads:
  `# Truncation and selection: how the two literatures pick a witness`.
  This task selects no witness out of a truncation: the one `PT` step it
  might have needed was avoided by `self∈sucV`. Not used.
- `dev/literature/digest.md`: **DECLINED.** It digests the S-hierarchy and
  Mathias-Bowler material, which belongs to the route question at
  `[LJ-2.5]`, not to a field of the delivered record. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` reads:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  It is a translation dossier and this task added no term and wrote no
  prose. Not used.
