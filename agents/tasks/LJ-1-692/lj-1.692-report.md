# LJ-1.692 report: spend the hull transport at the matrix

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.692
obligation: agents/tasks/LJ-1-692/Probe692.agda::hull-convert-at-matrix
verdict: **GO.** `hull-convert-at-matrix` is `[LJ-1.689]`'s
`hull-convert` instantiated at `{φ = matrix₃}` with
`Δ₀-matrix₃`, `Probe673.slide` and `Probe673.val`, the leftover
equation discharged by `Probe686.slide-embed-eq`. The result
inhabits `At.Convert` (`Probe673.agda:115-119`). The witness
meter reads `0 UNRESOLVED of 1, 6.06 s, probe_red=False`
(`runs/meter-obligation.out:4`). The probe is green and carries no
hole (`runs/p-final.out`, `EXIT=0` at `:22`). Two delivered names
meter `0 UNRESOLVED of 2, 5.44 s, probe_red=False`
(`runs/meter-names.out:5`).

**THIS IS THE INSTANTIATION, NOT A REWRITE.** The body is one
application (`Probe692.agda:64-66`). `convert-generic`, `pin₃`,
`pin₃-map`, `convert-at-matrix` and `slide-embed-eq` are not
re-dispatched. `val` is the name `Probe673.At` opens at
`Probe673.agda:69` and does not re-export. This file opens that
same name (`Probe692.agda:57`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-692/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON ANY SHAPE.** The highest peak of a finished
run is 1,784,627,200 bytes against the 2,147,483,648-byte wide cap
(`runs/p-2.out:5`, `runs/recheck-2.out:5`), which is 83 percent of
it. No run prints a heap event.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** The cold floor checked `Probe652`,
`Probe641`, `Probe667`, `W3`, `Probe520`, `Probe673`, `Probe686`,
`Probe689` and `Probe680` (`runs/floor-1.out:4-12`). Later green
runs are warm on those interfaces. A warm floor of the same hole
is 9.31 s (`runs/floor-warm.out`). The green body is not that
frame: a forced recheck of the delivered probe is a median 135.43 s.

**I DID NOT write `review-of-hull-convert-at-matrix.md`.** The
obligation is inhabited. A `review-of-*.md` is how a coder states a
NO-GO. This return is GO.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.689]` closed **GO on `hull-convert`**
(`agents/tasks/LJ-1-689/lj-1.689-report.md:8-16`). The report does
not name `hull-convert` FALSE. It says to spend the term by
instantiation, not rewrite
(`lj-1.689-report.md:345-351`). The type I take is the type that
probe delivered (`Probe689.agda:52-67`).

`[LJ-1.686]` closed **GO on `slide-embed-eq`**
(`agents/tasks/LJ-1-686/lj-1.686-report.md:9-17`). The report does
not name that equation FALSE. The type I take is
`Probe686.agda:52-53`. I do not re-inhabit it. I apply it.

`[LJ-1.673]` closed **NO-GO on `lset-grounded`**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:8-10`). That is not a
stop here. The NO-GO is on inhabiting `LsetGrounded` at `matrix₃`
as a closed term. `Convert` is a TYPE (`Probe673.agda:115-119`).
The report does not name `Convert` FALSE. `slide` and `val` are
written (`Probe673.agda:69-73`). `inBound` is written
(`Probe673.agda:83-87`).

`[LJ-1.682]` closed **GO on `convert-at-matrix`**. Premise 4 of
this brief forbids a re-dispatch. I do not rewrite it.

`[LJ-1.680]` closed **GO on `convert-generic`**, `pin₃` and
`pin₃-map`. Premise 4 of this brief forbids a re-dispatch. I do
not rewrite them.

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**. That is not a
stop here. `matrix₃` and `Δ₀-matrix₃` are green
(`Probe667.agda:72-76`). The report does not name those FALSE.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `hull-convert` | generic hull form, equation as hypothesis | `Probe689.agda:52-67` | GO; instantiate, do not rewrite |
| leftover equation | `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` | `Probe686.agda:52-53` | GO; applied, not re-inhabited |
| `Convert` (hull form) | AbsL of `inBound` to ambient 3-slot | `Probe673.agda:115-119` | TYPE, green; inhabited here |
| `slide` | `Empty.rec*` into `Code` | `Probe673.agda:72-73` | GO; named instantiation argument |
| `val` | code evaluation | `Probe673.agda:69` | GO, from `src/`; named instantiation argument |
| `inBound` | two `∃̇` and two `≐ con` at `matrix₃-Code` | `Probe673.agda:83-87` | GO; `hull-convert`'s generic `inBound` at `matrix₃` |
| `matrix₃`, `Δ₀-matrix₃` | 3-slot Δ₀ | `Probe667.agda:72-76` | GO syntax |
| `convert-generic`, `pin₃`, `pin₃-map` | generic unpack | `Probe680.agda:53-60,119-137` | GO; not re-dispatched |
| `convert-at-matrix` | unpack at `pin₃ (embed matrix₃)` | `Probe682.agda:45-49` | GO; not re-dispatched |

## 2. D-10, BEFORE ANY AGDA

The target: `[LJ-1.689]`'s `hull-convert` instantiated at
`{φ = matrix₃}` with `Δ₀-matrix₃`, `Probe673.slide` and
`Probe673.val`, the leftover equation discharged by
`Probe686.slide-embed-eq`. No cardinality or Tarskian obstruction
at that instantiation. Completeness of the matrix is not this
lemma. Soundness is not this lemma. `LsetGrounded` is not this
lemma.

The HYPOTHESIS at risk is the SHAPE of the instance: whether
`Probe673.val : Code → SL` unifies with `hull-convert`'s
`val : K → Ab.SM` when the carrier is `Lset lam`, and whether the
resulting type is `At.Convert` (`Probe673.agda:115-119`).
`[LJ-1.689]` named that composite unmeasured
(`lj-1.689-report.md:345-351`) and warned that the `Probe667`
frame is 19.51 s and 1.51 GB cold. `[LJ-1.686]` warned the same
at 17.68 s and 1.76 GB. Measure the floor before composing.

The corrected target beside the original, as D-10 asks: the
instance of the generic transport at the delivered matrix and the
hull maps, inside `Probe673.At`'s telescope. W2. The generic
transport is not rewritten.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is `At.Convert` at the hull
telescope, with a HOLE where the term goes. It is `.agda.txt`
and not `.agda`, because conjunct 1 runs every `.agda` under this
task home (`agents/tasks/LJ-1-692/LJ-1.692.md:16-17`).

**THE COLD FRAME COSTS 146.69 s AND 1.68 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 146.69 s, peak 1,684,914,176 bytes,
one error and it is the designed hole (`[UnsolvedInteractionMetas]`
at `FLOOR.agda:50`, `runs/floor-1.out:13`). **The obligation TYPE
is well-formed.** The frame checked `Probe652`, `Probe641`,
`Probe667`, `W3`, `Probe520`, `Probe673`, `Probe686`, `Probe689`
and `Probe680` (`runs/floor-1.out:4-12`). Highest peak of that
run is 78 percent of the 2,147,483,648-byte wide cap. No heap
event.

**THE WARM FRAME COSTS 9.31 s AND 1.62 GB.** `runs/floor-warm.out`:
exit 42 at 9.31 s, peak 1,624,457,216 bytes, the same designed
hole. The 146.69 s cold number is the dependency composite
`[LJ-1.682]` and `[LJ-1.686]` warned about. The type itself is
the 9.31 s.

The import trim after the floor: `Probe689` is the delivered
transport. `Probe686` discharges the leftover equation.
`Probe673` supplies `slide`, `val` and `Convert`. `Probe667`
supplies `matrix₃` and `Δ₀-matrix₃`. `Probe652` supplies
`Elementary` in the telescope and `Ltr` at `Lset lam`. Those
are the names the instance uses. The module telescope carries
`lem` because `Probe667` and `Probe673` take it. The term does
not use LEM.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the instantiation elaborates at
`matrix₃`'s own slide and val. Estimate 60 to 140 lines, basis
`agents/tasks/LJ-1-689/lj-1.689-report.md:1`.

**GO.** `hull-convert-at-matrix` (`Probe692.agda:68`, body at
`:64-66`) is inhabited. The carrier is `Lset lam` with
`F.HS.ASt.Ltr` (`Probe692.agda:58`). `val : Code → SL` unifies
with `hull-convert`'s `val : K → Ab.SM`. The result is
`A.Convert`. All three instantiation arguments fit.

The first body that named `A.val` failed: `val` is opened inside
`At` and is not re-exported (`runs/p-1.out:4`, `[NotInScope]` at
`Probe692.agda:61`). That is plumbing. The delivered shape opens
`A.F.HS.H.T.val`, the same name `Probe673.agda:69` opens, and
compiled on the next attempt (`runs/p-2.out`, `EXIT=0`).

The estimate was 60 to 140 lines. The delivered probe is 68
lines, 33 code. W3 is the application, which is three lines.

**THE APPLICATION IS THE PRICE, NOT THE FRAME.** Warm floor 9.31 s.
Median forced recheck of the inhabited term 135.43 s. The
instantiation elaborates. It does not wall.

## 5. TWO LAYERS, AND WHAT STILL SITS BETWEEN THIS TERM AND `LsetGrounded`

**Layer 1. The transport, already green.** `hull-convert` is not
rewritten.

**Layer 2. The instance at the hull, now green.** `At.Convert`
(`Probe673.agda:115-119`) is inhabited. A consumer of
`hull-closed` at `inBound` can now convert AbsL satisfaction of
`mapFo val (inBound ca cp)` into the ambient 3-slot reading of
`matrix₃`.

**The remaining gap to `LsetGrounded`.** `Completeness` /
`BoundInStage` (`Probe673.agda:90-95,126-130`) is still a TYPE.
`hull-closed` at `inBound` is already the consumer
(`Probe673.agda:100-104`). This file does not inhabit either.
The critic of `[LJ-1.673]` (`review-of-LJ-1-673-1.md:157-165`)
says `LsetGrounded` itself must carry `IsOrd δ`. That repair is
not this task.

## 6. W2

**Nothing is proved twice.** `hull-convert` is the generic
transport at a generic carrier, a generic alphabet and a generic
3-slot Δ₀ formula. This task instantiates it at the delivered
`matrix₃` and the hull maps. `slide-embed-eq` is applied and is
not re-inhabited. `convert-generic`, `pin₃`, `pin₃-map` and
`convert-at-matrix` are not rewritten. No deadline forced a
fixed form. There is no conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The
ideal form written fresh today is the form delivered: one
application of the delivered transport at the delivered matrix
and the hull maps.

**P-l: obeyed.** The public type of `hull-convert-at-matrix` is
`Convert` (`Probe673.agda:115-119`). That type quantifies over
`Code` and `ASt.SL`. It does not name a stage presentation.
`⟪ Lset lam ⟫` appears nowhere. `Lset lam` is the VALUE argument
that selects the carrier of `hull-convert`. It is not in the
public type.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is the hull `Convert` at `matrix₃`. The instance is
  written. Completeness is not. `Matrix₂` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled
  as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded
  key was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop
  at `[LJ-1.673]` was that two green types do not compose without
  extra hypotheses. This task inhabits one of those types at the
  hull. It is not a measurement that a named statement is false,
  so no sweep is owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs
from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | Convert type, one hole, deps cold | 146.69 | 1,684,914,176 | 42 |
| `runs/p-1.out` | first body, `A.val` not in scope | 3.33 | 750,977,024 | 42 |
| `runs/p-2.out` | first green of the delivered shape | 136.90 | 1,784,627,200 | 0 |
| `runs/recheck-1.out` | forced recheck | 136.75 | 1,592,197,120 | 0 |
| `runs/recheck-2.out` | forced recheck | 131.62 | 1,784,627,200 | 0 |
| `runs/recheck-3.out` | forced recheck | 135.43 | 1,784,594,432 | 0 |
| `runs/p-final.out` | last green of the delivered shape | 139.79 | 1,591,099,392 | 0 |
| `runs/floor-warm.out` | same hole, deps warm | 9.31 | 1,624,457,216 | 42 |
| `runs/meter-obligation.out` | the obligation | 6.06 | not taken | 0 |
| `runs/meter-names.out` | 2 names, grouped | 5.44 | not taken | 0 |

Median of the three forced rechecks **135.43 s**. Median peak of
those three **1,784,594,432 bytes**. Highest peak of any finished
run **1,784,627,200 bytes** (`runs/p-2.out:5`,
`runs/recheck-2.out:5`), 83 percent of the 2 GiB cap. Highest
green peak is that same figure. No heap event on any shape. No
restructuring for a heap wall was needed.

`p-1` is `[NotInScope]` on `A.val`. The fix is to open
`A.F.HS.H.T.val`, the name `At` itself opens. The delivered
shape compiled on the first attempt that did that (`p-2`).

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, two names
(`hull-convert-at-matrix`, `Spend.hull-convert-at-matrix`):
`runs/meter-names.out`, `0 UNRESOLVED of 2`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds
no `.lagda.md` and no ` ```agda ` fence, so the in-fence divisor
is 0. Nothing landed in `src/`.

The probe interface was deleted after the last run, so the working
tree carries no generated file.

## 10. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 68 | 33 | `Probe692.agda` |
| `Spend.hull-convert-at-matrix` | 4 | 4 | `Probe692.agda:63-66` |
| top-level lift | 1 | 1 | `Probe692.agda:68` |
| floor slice | 52 | 29 | `runs/FLOOR.agda.txt` |

The brief estimated 60 to 140 lines. The probe is 33 code lines.
The transport is `[LJ-1.689]`. The new term is one application.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 33 code lines, median 135.43 s on a forced
  recheck, highest peak 1,784,627,200 bytes against a 2 GB cap,
  no heap wall. The cold floor is 146.69 s and 1.68 GB. The warm
  floor is 9.31 s and 1.62 GB. The body, not the frame, is the
  135 s.
- **What the shape resisted.** One plumbing error: `A.val` is not
  in scope, because `At` opens `val` and does not re-export it.
  The three instantiation arguments all fit. `val : Code → SL`
  unifies with `Ab.SM` at carrier `Lset lam`. The result is
  `Convert` with no extra `subst`. The leftover equation was not
  re-inhabited. Completeness was not attempted.
- **What I had to weaken.** Nothing of the obligation. The public
  type is `Convert`, not a restated form. `slide` and `val` are
  the hull maps, not generic parameters.
- **What I could not close.** `Completeness` (`Probe673.agda:126-130`)
  and `LsetGrounded`. Those are not this obligation.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH THIS INSTANCE.** `hull-convert-at-matrix`
   inhabits `At.Convert` at `{φ = matrix₃}` with `Δ₀-matrix₃`,
   `Probe673.slide` and `Probe673.val`. `hull-convert`,
   `slide-embed-eq`, `convert-generic`, `pin₃`, `pin₃-map` and
   `convert-at-matrix` remain green.
2. **FUND `Completeness` / `BoundInStage` AT `matrix₃` STILL.**
   That is Devlin 5.2 (b), not this unpack. Carry `IsOrd` on the
   parameter. The critic of `[LJ-1.673]`
   (`review-of-LJ-1-673-1.md:157-165`) says `LsetGrounded` itself
   must carry `IsOrd δ`. That repair is not this task.
3. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
4. **THIS FRAME RUNS WIDE AND THE BODY IS THE 135 s.** Cold
   composite 146.69 s and 1.68 GB. Warm type 9.31 s and 1.62 GB.
   Warm inhabited term median 135.43 s and 1.78 GB against a
   2 GB cap, 83 percent. Do not import `Probe667` or `Probe673`
   into a further consumer without measuring the composite
   frame. A further term in this same telescope will pay the
   135 s of this instance if it forces a recheck of this probe.
5. The module telescope carries `lem` because `Probe667` and
   `Probe673` take it. `hull-convert-at-matrix` does not use LEM.
6. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires.
This worktree has no `.venv`; the gates ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10666
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task instantiates a live
  probe and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `hull-convert-at-matrix`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this instance.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the three-slot shape.** The instance is at `matrix₃`,
  which is that formula. Convert unpacks the two pins and leaves
  the witness free, the same order as `pin₃`
  (`Probe680.agda:53-55`) and `Witnessed` (`Probe652.agda:87-91`).
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md`. A second
  round of source notes does not change a type.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  No Devlin error class is at issue in this instance.
- **`dev/literature/formalizations.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Formalization landscape: Paulson, Flypitch, and what else the fetched material shows`.
  No formalization is a consumer of this instance.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not rewrite `hull-convert`, `slide-embed-eq`,
  `convert-generic`, `pin₃`, `pin₃-map` or `convert-at-matrix`.
- I did not inhabit `Completeness` or `LsetGrounded`.
- I did not postulate. I left no hole in `Probe692.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not write `review-of-hull-convert-at-matrix.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-692/`:

- `Probe692.agda`, the instance of `hull-convert` at `matrix₃` and
  the hull maps, green
- `lj-1.692-report.md`, this report
- `runs/`, the Agda transcripts and `FLOOR.agda.txt`
