# LJ-1.708 report: below-direct, the route that does not pass through the door

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.708
obligation: agents/tasks/LJ-1-708/Probe708.agda::below-direct
verdict: **NO-GO on the closed term from the licensed triple; GO on
the delivered record (probe, floor, measured residual).** The stated
NO-GO is `review-of-below-direct.md`.

The obligation term is not written and is deliberately absent from
the probe, as at `Probe679.agda:97-99` and `Probe697.agda`. The
witness meter reads `missing`, exit 42,
`1 UNRESOLVED of 1, 3.27 s, probe_red=False`
(`runs/meter-obligation.out`). The probe is green with no hole:
`runs/p-2.out`, `EXIT=0`, first green 3.59 s; median 3.14 s over the
three forced rechecks (`runs/recheck-1.out` to `runs/recheck-3.out`).

**THIS IS NOT A REFUTATION OF `Below`.** I did not build a negation.
The type closes through the door on its two keystone hypotheses, by
`[LJ-1.707]`'s GO (`agents/tasks/LJ-1-707/lj-1.707-report.md:9-11`).
What is measured here is that `ord∈Lset→∈`, `Lset-mono` and `succλ`
place no table.

Written as a skeleton before any Agda ran and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-708/`. Agda ran ONE process at a time under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the
WIDE tier. I did not set `GHCRTS`. Nothing is postulated, every
delivered `.agda` file carries `--safe` and no hole, nothing lands in
`src/`. Every file that cannot typecheck sits as `.agda.txt`, never
`.agda` (`agents/tasks/LJ-1-708/LJ-1.708.md`, conjunct 1 runs every
`.agda` under this task home).

**NO HEAP WALL WAS MET ON ANY DELIVERED SHAPE, AND NO RE-RUN OF A
FAILING SCOPE HAPPENED UNCHANGED.** Each failing shape produced one
new shape that was then tested: `floor-1` to `floor-2`, `cand-1` to
`cand-2`, `p-1` to `p-2`. The highest peak of any finished run is
969,228,288 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), 45 percent of it; on the meaningful rows the
highest peak is 729,366,528 bytes (`runs/floor-2.out`), 34 percent.
No run prints a heap event.

The standing direction (`dev/pod/direction.md`) says one SRC
collection after LJ-1, not gated on `[LJ-2.5]`, and nothing in phase
3 before `[LJ-2.5]`. This task starts neither. No Boundary clause is
in conflict.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.697]` closed **NO-GO on the closed term `hier-in-stage`**, **GO
on W3**, and **GO on the assembly `Below → HierInStage`**
(`agents/tasks/LJ-1-697/lj-1.697-report.md:9-10`): `from-below`
(`Probe697.agda:81-86`) consumes `Below` and is green; `Below`
(`Probe697.agda:72-74`) is unpaid. That report's guidance names what
this brief funds: do not re-dispatch `from-below`, `from-below-at`,
`ordinal-in`, `climb`, `lset-in-stage` or `Lset∈suc`; fund `Below`.
This task takes that guidance literally and tests the uncorrected
third member of the critic's triple against it.

The critic of `[LJ-1.679]` recorded that its attempt ingredients
(`Lset-out`, `Lset-mono`) do not assemble stage placement alone
(`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:154-157`) and named
the corrected attempt for the coder
(`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:231-234`). C-42 says
that refutation measures one site; `[LJ-1.697]` re-measured at this
frame with the corrected out-lemma and won the ASSEMBLY, which is why
a fresh attack on `Below` itself was worth a dispatch rather than a
transfer of either older verdict.

`[LJ-1.707]` closed **GO as an assembly** on `through-door-closed`,
composing the two keystone hypotheses through `[LJ-1.693]`'s door
type (`agents/tasks/LJ-1-707/lj-1.707-report.md:9-11`). This task is
the OTHER route at the SAME target: the brief fixes the toolkit to
three door-free rows
(`agents/tasks/LJ-1-708/LJ-1.708.md`, THE OBLIGATION).

## 2. D-10, BEFORE ANY AGDA

The target's truth was priced before its proof. `Below δ oδ` states
that the internal hierarchy table lands in `Lset (step 3 δ)`.
Mathematically the fact is classical and true, and in THIS tree it is
reachable only through definability data: the producer census below
(section 4) shows every stage-membership producer either fires
`𝒟ₒ-intro` or needs collection data the frame does not carry. So the
risk was never the statement; it was the LICENSED TOOLKIT, exactly
what W3 asks to be measured. The corrected target beside the
original: nothing of the obligation survives restriction to the
triple; the residue named for the next brief is unchanged from
`[LJ-1.697]` (fund identification plus bound), now with the added
fact that the door-free shortcut cannot undercut those keystones.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing clause orders a floor before a heavy object. I ran it.
`runs/FLOOR.agda.txt` is the obligation's whole type inside the
`[LJ-1.697]` frame, hole where the term goes, `.agda.txt` because
conjunct 1 verifies every `.agda` under this task home.

**THE FRAME COSTS 3.46 S AND 0.73 GB, AND IT DOES NOT WALL.**
`runs/floor-2.out`: exit 42 at 3.46 s, peak 729,366,528 bytes, one
error and it is the designed hole
(`FLOOR.agda:52.23-59`, `[UnsolvedInteractionMetas]`, rows :4). **The
obligation TYPE is well-formed at this frame.** The import set is the
delivered probe's own trim: `src/` warm interfaces plus
`LJ-1-652.Probe652` (for `Frame652.A.Elementary`, the frame's last
parameter) plus `LJ-1-697.runs.W3` (for `climb` and `ordinal-in`,
taken not rebuilt). `Probe679` and everything above it are not
imported: nothing in the licensed toolkit or the target type reaches
them. This is far inside the wide cap, so the object proved light and
no narrowing was needed.

## 4. W3, THE WIDEST UNMEASURED TERM

Estimate 90 to 220 lines, basis
`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:154`.

**NO-GO ON THE CLOSED TERM FROM THE TRIPLE. THE GAP IS IN NEITHER
LEMMA INDIVIDUALLY: IT IS THE ABSENCE OF A BASE-CASE PRODUCER FOR
STAGE MEMBERSHIP AMONG ALL THREE.**

`below-direct` targets `[LJ-1.697]`'s `Below`
(`Probe708.agda:68-71`, verbatim `Probe697.agda:72-74`). I attempted
the honest maximal assembly: fire the only rule in the triple whose
conclusion is a stage membership, `Lset-mono`
(`src/L/Constructible.lagda.md:365-366`), aimed at the goal
(`runs/cand-1.agda.txt:69-71`). Three unsolved metas remain, one per
unproducible slot (`runs/cand-2.out:4-8`):

1. the index slot `β : S`,
2. `⟨ β ∈ˢ step 3 (fst δ) ⟩`, already unproduced among the three,
3. `⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset β ⟩`: `Below` shifted
   down one step. Descent recurses with no floor.

Producer census over `src/` (full rows in the review file, section
3): `𝒟ₒ-intro` fires the door
(`src/L/Constructible.lagda.md:301-304`); `Lset-in` needs a `𝒟ₒ`
premise (`src/L/Constructible.lagda.md:329`);
`stage-mem` places a set only at its OWN earliest stage
(`src/L/Stage.lagda.md:188`) and out of license besides;
`Lset∈suc` is green but fired ON the door
(`agents/tasks/LJ-1-697/runs/W3.agda:42-44`); StageBound lemmas are
out of license (`src/L/StageBound.lagda.md:122`). The probe's
using-list opens only door-free rows (`Probe708.agda:65-66`); taking
`Lset∈suc` would smuggle the door in through a preproven lemma.

So the two answers W3 offered are BOTH wrong: `ord∈Lset→∈` does close
a DOWNWARD gap, measurably, and did close it in `[LJ-1.697]`'s
assembly; `succλ` climbs only plain carrier memberships inside `lam`;
neither belongs to the class of rules that could start the recursion
above. The critic's refutation measured `Lset-out` at the old site;
C-42 forbade transferring that verdict here, and correctly, because
the corrected out-lemma changed the assembly outcome. What it could
not change is the census.

Final shape of the deliverable: `below-direct` named absent
(`Probe708.agda:73-83` documents why and where the residual lives),
probe green (`p-2`), meter unresolved as designed.

## 5. W2

**Nothing is proved twice.** The frame parameters are
`[LJ-1.679]`'s, verbatim (`Probe679.agda:63-67`, carried at
`Probe708.agda:56-62`): premise 5 fixes `climb` and `ordinal-in` as
known good AT this frame, and they come from `W3.At` by an explicit
using-list, not rebuilt (`W3.agda:55-61`). `Below` is the
predecessor's type verbatim. `ord∈Lset→∈`, `Lset-mono`, `hierL`,
`𝒮ʟ`, `IsOrd` come straight from `src/`. `X`, `X⊆Lλ`, `∅∈λ` and
`elem` ride the telescope inert, exactly because the frame must be
indistinguishable from the one the predecessors metered; no row of
this file spends them. No deadline forced a fixed form. No conflict.

## 6. W4, AND P-l

**W4: not applicable.** Nothing retired, nothing left `src/`,
`dev/ARCHIVE.md` takes no row from this task. The ideal form today is
the form delivered: frame taken, target stated verbatim, attempt and
residual in `runs/`, NO-GO stated for the critic.

**P-l: obeyed.** The obligation type names `step 3`, inside the
predecessor's own lemma-level `Below`, not a transparent presentation
of a concrete stage dragged into a statement. No conversion is asked
of the elaborator anywhere: nothing unfolds opaque `Lset`, `hierAt`
or `𝒟ₒ`, and the metas that stopped the attempt were measured at
types, not at spellings.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Section 2: the target is true,
  the toolkit is what fails, corrected target = `[LJ-1.697]`'s
  residue now shielded from undercut.
- **C-22** (`dev/LESSONS.md:2307`). Report skeleton written before
  any Agda ran; review skeleton likewise; both filled as runs closed.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind: no well-founded key
  was built and none is proposed.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed, so no sweep
  is owed. The reviewer of this return should still note the census
  result generalizes the OLD boundary: the door-dependence the critic
  found at `[LJ-1.679]`'s site and `[LJ-1.536]`'s door-stop now has a
  counted producer list covering every `⟨ t ∈ˢ Lset w ⟩` shape in
  `src/`.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, wide, set on the pane by the program and
untouched here. One Agda process at a time, strictly sequential. All
runs from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | floor, plumbing: `[NoSuchModule]` qualified path | 6.33 | 969,228,288 | 42 |
| `runs/floor-2.out` | DESIGNED FLOOR: type + one hole | 3.46 | 729,366,528 | 42 |
| `runs/cand-1.out` | attempt plumbing: module name mismatch | 0.08 | 114,409,472 | 42 |
| `runs/cand-2.out` | THE ATTEMPT: 3 unsolved metas | 4.72 | 636,928,000 | 42 |
| `runs/p-1.out` | probe plumbing: signature without body | 3.68 | 682,786,816 | 42 |
| `runs/p-2.out` | first green probe | 3.59 | 691,798,016 | 0 |
| `runs/recheck-1.out` | forced recheck | 2.98 | 716,652,544 | 0 |
| `runs/recheck-2.out` | forced recheck | 3.14 | 716,652,544 | 0 |
| `runs/recheck-3.out` | forced recheck | 3.23 | 628,768,768 | 0 |
| `runs/final-1.out` | final file-state check, comment-only edits after recheck-3 | 3.68 | 691,765,248 | 0 |
| `runs/meter-obligation.out` | the obligation metered | 3.27 | not taken | 1 |

Median of the three forced rechecks **3.14 s**. Highest peak of any
finished run 969,228,288 bytes (45 percent of cap, `floor-1`),
highest on a meaningful row 729,366,528 (34 percent, `floor-2`),
highest on a green row 716,652,544 (33 percent). No heap event. No
restructuring needed on the delivered shapes.

Meter: `missing   exit=42   3.27s ... Probe708.agda::below-direct
([NotInScope])`, then `witness: 1 UNRESOLVED of 1, 3.27 s,
probe_red=False` (`runs/meter-obligation.out`). Ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`;
this worktree holds no `.venv` of its own and none was created. No
dependency added.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds
no `.lagda.md` master and no fenced Agda block in either `.md`
file, so the in-fence divisor is 0; every code-bearing artifact is a
raw `.agda` or `.agda.txt` file. Nothing landed in `src/`.

Plumbing rows, each fixed once and never re-run unchanged:
`floor-1` (aliased module reached by full path), `cand-1` (module
name not matching dashed filename), `p-1` (`MissingDefinitions`:
Agda carries no signature-only form, so the obligation name is
absent outright, matching house pattern).

## 9. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 84 | 28 | `Probe708.agda` |
| the target `Below` slice | 3 | 3 | `Probe708.agda:69-71` |
| the using-list, door-free rows | 2 | 2 | `Probe708.agda:65-66` |
| the frame, whole | 7 | 7 | `Probe708.agda:56-62` |
| floor slice | 52 | 30 | `runs/FLOOR.agda.txt` |
| candidate attempt, whole | 71 | 31 | `runs/cand-1.agda.txt` |
| the attempt body | 3 | 3 | `runs/cand-1.agda.txt:69-71` |

Whole scope: 207 raw lines, 89 code lines, against an estimate of 90
to 220 lines. The shortfall against the low end IS the result: no
term exists to grow.

## 10. WHAT THE SHAPE RESISTED

- **What it cost.** 89 code lines across three artifacts, median
  3.14 s per green check, highest peak 0.97 GB against the 2 GB cap,
  no heap wall anywhere.
- **What the shape resisted.** The goal itself: after the single
  available move fires, three independent slots stand empty and no
  fourth rule exists to try. Three plumbing rows cost minutes, not
  structure.
- **What I had to weaken.** Nothing. I did not inhabit `below-direct`
  from `lset-in-stage` or `Lset∈suc` and call it door-free. I did not
  open door-built W3 rows. I did not restage the claim as something
  weaker about `lam` and call it paid.
- **What I could not close.** `below-direct` from `ord∈Lset→∈`,
  `Lset-mono` and `succλ`, at `[LJ-1.697]`'s frame, at any budget:
  the toolkit lacks a base-case producer, which is a structural
  count, not a price.

## 11. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT FUND `below-direct` AGAIN** from these three rows or from
   any bundle that excludes door-fired lemmas. The absence of a base
   producer is counted, not timed (`review-of-below-direct.md`,
   sections 1 to 3).
2. **THE BELOW CHAIN'S BILLS ARE UNCHANGED AND NOW SHIELDED:**
   fund `[LJ-1.704]`'s identification (carved ≡ hierL) and the bound
   hypothesis `[LJ-1.707]` names (`agents/tasks/LJ-1-707/
   Probe707.agda:60-63`); `through-door-closed` pays `HierInK` end to
   end from them. This task removes the hope of undercutting either
   keystone door-free.
3. **IF A DOOR-FREE PLACEMENT IS EVER WANTED,** fund a NEW producer
   first: a bounded form of `stage-mem` (a set at its earliest stage,
   plus the bound clause that would compare that stage down to
   `step 3 δ`), as its own task, priced against the census. Do not
   reuse this frame's triple.
4. **DO NOT RE-DISPATCH:** `from-below`, `from-below-at`, `climb`,
   `ordinal-in`, `lset-in-stage`, `Lset∈suc` (all GO, take them via
   imports), nor `through-door-closed` ([LJ-1.707], GO).

## 12. SURVEY DUTY, ADDED BY THE REVIEW DISPATCH (LJ-1.708#2)

Attempt 1 failed acceptance conjunct 6: this return carried no survey
sections. The adversarial review of attempt 1
(`agents/tasks/LJ-1-708/review-of-LJ-1-708-1.md`, verdict upheld)
appends the two missing sections here and re-ran the checks clean.
Each candidate below was opened at header level to decline it honestly;
none is quoted as evidence.

## ARCHIVE USED

- `archive/dev/DD-archived.md` declined as a corpus: read only at :35
  for the reviewer lens; its rows are retired decisions and none bears
  on this probe NO-GO.
- `archive/dev/ORCHESTRATION.md` not read: the retired orchestrator's
  operating rules; routing facts for this return come from
  `runs/accept-1.out` and scripts, not from it.
- `archive/dev/PLAN-archived.md` not used: retired planning record,
  replaced by the live screen; bears nothing on the probe or census.
- `archive/dev/STATUS-archived.md` not surveyed: retired goal table of
  the old route; no claim of this return rests on it.
- `archive/dev/TASKS-archived.md` not used: archived L3.32-T series
  index; no bearing on this task home.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md` not surveyed: author
  statements of levelhood matter to prose planning, not to a
  tree-side lemma-supply measurement.
- `dev/literature/devlin-errata.md` not used: book error classes; the
  measured gap here is which lemmas the licensed triple carries.
- `dev/literature/glossary-review-2026-08.md` not used: glossary
  protocol deliverable; no translation term is in play.
- `dev/literature/primary-sources.md` not read: second fetch round of
  the retired route; no bearing on the producer census.
- `dev/literature/BIBLIOGRAPHY.md` not surveyed: the rud route's
  source list; this return cites only live proofs and probes.
