# LJ-1.686 report: the leftover equation, measured as its own floor

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.686
obligation: agents/tasks/LJ-1-686/Probe686.agda::slide-embed-eq
verdict: **GO.** `slide-embed-eq` inhabits
`mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` at generic
`val` and `slide`, by applying a generic lemma that is
`mapFo-comp` plus uniqueness of maps out of `⊥*`. The witness
meter reads `0 UNRESOLVED of 1, 3.21 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-final.out`, `EXIT=0`). Three delivered names meter
`0 UNRESOLVED of 3, 3.14 s, probe_red=False`
(`runs/meter-names.out`).

**THIS IS THE LEFTOVER EQUATION AT `matrix₃`, NOT THE HULL
`Convert`.** `val` and `slide` are parameters. Nothing in the
probe names `Code`, `Frame652` or `inBound`. The hull maps of
`Probe673.agda:69-73` are one instance of those parameters.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-686/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON ANY SHAPE.** The highest peak of a finished
run is 1,760,133,120 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-matrix-1.out`), which is 82 percent of it. No run prints
a heap event. The highest green peak is 670,973,952 bytes
(`runs/recheck-1.out`), 31 percent of the cap.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** The matrix floor checked `Probe667`,
`Probe652`, `Probe641`, `W3` and `Probe520` cold
(`runs/floor-matrix-1.out:3-8`). Later green runs are warm on those
interfaces. This report does not bound a cold-cache number for the
instance itself.

**I DID NOT write `review-of-slide-embed-eq.md`.** The obligation
is inhabited. A `review-of-*.md` is how a coder states a NO-GO. This
return is GO.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.680]` closed **GO on `convert-generic`**
(`agents/tasks/LJ-1-680/lj-1.680-report.md:9-15`). The leftover
equation is named there and is not formed
(`lj-1.680-report.md:146-153`). The report does not name that
equation FALSE. It says the equation is `mapFo-comp` plus
uniqueness of maps out of `⊥*` and that it inducts on the
formula (`lj-1.680-report.md:147-148`).

`[LJ-1.682]` closed **GO on `convert-at-matrix`**
(`agents/tasks/LJ-1-682/lj-1.682-report.md:9-18`). That spend
restates `Convert` at `pin₃ (embed matrix₃)` and never forms the
leftover equation (`lj-1.682-report.md:12-13,181-185`). The report
does not name the leftover equation FALSE. It says to measure it
as its own floor (`lj-1.682-report.md:309-316`).

`[LJ-1.673]` closed **NO-GO on `lset-grounded`**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:8-10`). That is not a
stop here. The NO-GO is on inhabiting `LsetGrounded` at `matrix₃`
as a closed term. `Convert` is a TYPE (`Probe673.agda:115-119`).
The report does not name `Convert` FALSE. `slide` and `val` are
written (`Probe673.agda:69-73`). `inBound` is written
(`Probe673.agda:83-87`).

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**. That is not a
stop here. `matrix₃` and `Δ₀-matrix₃` are green
(`Probe667.agda:72-76`). The report does not name those FALSE.

`[LJ-1.652]` closed **NO-GO on `picommute-D-from-elem`** and **GO**
on `AtTrans.read` and on `embed-map` (`Probe652.agda:56-61`).
`embed-map` is the same uniqueness at `embed`, not at an
intermediate `slide`. The report does not name `embed-map` FALSE.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| leftover equation | `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` | named, not formed, `lj-1.680-report.md:146-147` | NAMED |
| `convert-generic` | generic unpack at 3-slot Δ₀ | `Probe680.agda:119-137` | GO |
| `convert-at-matrix` | restated Convert at `pin₃ (embed matrix₃)` | `Probe682.agda:45-49` | GO |
| `Convert` (hull form) | AbsL of `inBound` to ambient 3-slot | `Probe673.agda:115-119` | TYPE, green; not inhabited |
| `slide` | `Empty.rec*` into `Code` | `Probe673.agda:72-73` | GO |
| `val` | code evaluation | `Probe673.agda:69` | GO, from `src/` |
| `inBound` | two `∃̇` and two `≐ con` | `Probe673.agda:83-87` | GO |
| `matrix₃` | 3-slot Δ₀ | `Probe667.agda:72-76` | GO syntax |
| `embed-map` | `mapFo f (embed φ) ≡ embed φ` | `Probe652.agda:56-61` | GO |
| `mapFo-comp` | functoriality | `src/FOL/Manipulation/Relabelling.lagda.md:87-101` | GO, in `src/` |
| `embed` | `mapFo Empty.rec*` | `src/FOL/Manipulation/Relabelling.lagda.md:117-118` | GO, in `src/` |

## 2. D-10, BEFORE ANY AGDA

The target: `mapFo val (mapFo slide φ) ≡ embed φ` at a parameter-free
formula, by `mapFo-comp` and uniqueness of maps out of `⊥*`. No
cardinality or Tarskian obstruction. `embed-map`
(`Probe652.agda:56-61`) is the same uniqueness at `f` after `embed`.
The leftover equation is that uniqueness with an intermediate
`slide`. Completeness of the matrix is not this lemma. Soundness
is not this lemma. The hull `Convert` is not this lemma.

The HYPOTHESIS at risk is the SHAPE: whether forming the equation
at `matrix₃` unfolds the formula. `[LJ-1.673]` did not finish a
substitution into the ambient reading
(`agents/tasks/LJ-1-673/runs/p-4.out`). This task forms a syntactic
equation and does not substitute into satisfaction.

The corrected target beside the original, as D-10 asks: the
equation at a generic carrier and a generic parameter-free
formula, then the instance at `matrix₃`. W2.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I
ran two.

**GENERIC FLOOR, `src/` ONLY.** `runs/FLOOR.agda.txt` is the
equation at a variable `φ` and variable `val`, `slide`, with a
HOLE where the term goes. It is `.agda.txt` and not `.agda`,
because conjunct 1 runs every `.agda` under this task home
(`agents/tasks/LJ-1-686/LJ-1.686.md:16-17`).

**THE GENERIC FRAME COSTS 0.93 s AND 242 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 0.93 s, peak 242,417,664 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:30`). **The generic obligation TYPE is well-formed.**
Importing `Probe667`, `Probe673` or `Probe652` is not part of this
frame.

**MATRIX FLOOR, THE NAMED EQUATION.** `runs/FLOOR-matrix.agda.txt`
is the same type at `matrix₃`, with a HOLE. It imports `Probe667`
for the delivered name.

**THE MATRIX FRAME COSTS 17.68 s AND 1.76 GB, AND IT DOES NOT WALL.**
`runs/floor-matrix-1.out`: exit 42 at 17.68 s, peak 1,760,133,120
bytes, one error and it is the designed hole
(`[UnsolvedInteractionMetas]` at `FLOOR-matrix.agda:31`). **The
obligation TYPE at `matrix₃` is well-formed.** The frame checked
`Probe667`, `Probe652`, `Probe641`, `W3` and `Probe520`
(`runs/floor-matrix-1.out:3-8`). That is the composite `[LJ-1.680]`
and `[LJ-1.682]` warned about (`lj-1.680-report.md:299-302`,
`lj-1.682-report.md:324-329`). Highest peak is 82 percent of the
2,147,483,648-byte wide cap. No heap event.

The import trim after the two floors: the generic lemma uses
`src/` only. The instance at `matrix₃` uses `Probe667` for the
delivered name. `Probe652` and `Probe641` ride in because
`Probe667` imports them; they are not names this file uses. I did
not import `Probe673`: `val` and `slide` stay parameters, so the
hull telescope does not leak into this type. The module telescope
carries `lem` because `Probe667` takes it. The lemma does not use
LEM.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: the induction itself. Estimate 90 to 200
lines, basis `agents/tasks/LJ-1-680/lj-1.680-report.md:1`.

**GO. THE INDUCTION IS ALREADY IN `src/`.** `mapFo-comp`
(`src/FOL/Manipulation/Relabelling.lagda.md:87-101`) is the
structural induction on the formula. `lemma`
(`Probe686.agda:34-41`) is that composite plus `funExt` of
`Empty.rec*`. `slide-embed-eq` (`Probe686.agda:52-53`) is
`lemma matrix₃ slide val`. The proof term is an application. It
does not unfold `mapFo-comp` at `matrix₃` to typecheck.

The estimate was 90 to 200 lines. The delivered probe is 55
lines, 23 code. W3 is the induction at `matrix₃`, which is one
application of a twelve-clause lemma that already lives in `src/`.

## 5. TWO LAYERS, AND WHAT STILL SITS BETWEEN THIS TERM AND THE HULL `Convert`

**Layer 1. The generic uniqueness, already green.** `lemma` takes
a variable formula and two variable maps. It does not name
`matrix₃`. `embed-map` (`Probe652.agda:56-61`) is the same
uniqueness with `slide` definitionally `Empty.rec*`. This file
does not import `Probe652`.

**Layer 2. The instance at `matrix₃`.** `slide-embed-eq` is
`lemma` at the delivered `matrix₃`. `val` and `slide` stay
parameters. Forming the type at `matrix₃` is the matrix floor
above. Applying the lemma is the green spend below.

**The remaining gap to `At.Convert` (`Probe673.agda:115-119`).**
The hull form takes `mapFo val (inBound ca cp)` and concludes
`⊨ₚ matrix₃`. `pin₃-map` (`Probe680.agda:57-60`) closes the pin
under `mapFo val`. This equation rewrites
`mapFo val (mapFo slide matrix₃)` to `embed matrix₃`. A consumer
then applies `convert-generic {φ = matrix₃} Δ₀-matrix₃`. **This
file does not take that composition.** The transport is a `subst`
along this equation at `pin₃`, not a substitution into the
ambient reading of `matrix₃`. `[LJ-1.673]` did not finish the
latter (`agents/tasks/LJ-1-673/runs/p-4.out`). The former is
unmeasured. Measure it as its own floor before composing.

## 6. W2

**Nothing is proved twice.** `lemma` is the uniqueness at a
generic carrier and a generic parameter-free formula.
`slide-embed-eq` instantiates it at the delivered `matrix₃`.
`embed-map` (`Probe652.agda:56-61`) is the same uniqueness at
`embed`. I did not import that module: it takes LEM and pulls the
hull telescope. The two-liner in this file is the generic form,
not a second proof. No deadline forced a fixed form. There is no
conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The
ideal form written fresh today is the form delivered: a generic
uniqueness and one instance at the delivered matrix.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over variable carriers `K` and `K'`.
`⟪ Lset lam ⟫` appears nowhere. `matrix₃` is a `Formula`, not a
stage. `val` and `slide` are parameters, so `Code` does not enter
the type.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is the leftover equation. The generic form is written.
  The instance at `matrix₃` is written. Completeness is not.
  `Matrix₂` is not funded. The hull `Convert` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled
  as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded
  key was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop
  at `[LJ-1.673]` was that two green types do not compose without
  extra hypotheses. This task inhabits the leftover equation those
  reports named. It is not a measurement that a named statement is
  false, so no sweep is owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs
from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | generic type, one hole, `src/` only | 0.93 | 242,417,664 | 42 |
| `runs/floor-matrix-1.out` | type at `matrix₃`, one hole, deps cold | 17.68 | 1,760,133,120 | 42 |
| `runs/p-1.out` | generic lemma only, no `Probe667` | 0.67 | 242,597,888 | 0 |
| `runs/p-2.out` | first green of the delivered shape | 3.09 | 669,908,992 | 0 |
| `runs/recheck-1.out` | forced recheck | 3.10 | 670,973,952 | 0 |
| `runs/recheck-2.out` | forced recheck | 3.09 | 669,908,992 | 0 |
| `runs/recheck-3.out` | forced recheck | 3.34 | 669,941,760 | 0 |
| `runs/p-final.out` | last green of the delivered shape | 3.40 | 669,941,760 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.21 | not taken | 0 |
| `runs/meter-names.out` | 3 names, grouped | 3.14 | not taken | 0 |

Median of the three forced rechecks **3.10 s**. Median peak of
those three **669,941,760 bytes**. Highest peak of any finished
run **1,760,133,120 bytes** (`runs/floor-matrix-1.out`), 82 percent
of the 2 GiB cap. Highest green peak **670,973,952 bytes**
(`runs/recheck-1.out`). No heap event on any shape. No
restructuring for a heap wall was needed.

`p-1` is the generic lemma at `src/` only, before `lem` and
`Probe667` entered the file. The delivered shape compiled on the
first attempt that added the instance (`p-2`). There is no
plumbing red run on the delivered shape.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, three names:
`runs/meter-names.out`, `0 UNRESOLVED of 3`. This worktree has no
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
| the probe, whole | 55 | 23 | `Probe686.agda` |
| `lemma` | 8 | 8 | `Probe686.agda:34-41` |
| `At.slide-embed-eq` | 6 | 5 | `Probe686.agda:48-53` |
| top-level lift | 1 | 1 | `Probe686.agda:55` |
| generic floor slice | 32 | 12 | `runs/FLOOR.agda.txt` |
| matrix floor slice | 33 | 14 | `runs/FLOOR-matrix.agda.txt` |

The brief estimated 90 to 200 lines. The probe is 23 code lines.
The induction is the twelve clauses of `mapFo-comp` in `src/`.
The new term is two lines plus one application.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 23 code lines, median 3.10 s on a forced
  recheck, highest green peak 671 MB against a 2 GB cap, no heap
  wall. The generic floor is 0.93 s and 242 MB. The cold matrix
  frame is 17.68 s and 1.76 GB.
- **What the shape resisted.** Nothing of the mathematics. The
  generic lemma compiled on the first attempt. The instance at
  `matrix₃` compiled on the first attempt that imported
  `Probe667`. Forming the type at `matrix₃` did not unfold the
  formula. The induction estimate of 90 to 200 lines was the
  wrong object: the induction already lives in `src/`.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit the hull `Convert`. I did not import `Probe673`. `val`
  and `slide` are parameters, which is the generic form, not a
  weaker equation.
- **What I could not close.** `At.Convert` at
  `mapFo val (inBound ca cp)` (`Probe673.agda:115-119`),
  `Completeness` (`Probe673.agda:126-130`), and `LsetGrounded`.
  Those are not this obligation. The `subst` along this equation
  at `pin₃` is unmeasured.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH THIS EQUATION.** `slide-embed-eq` is green
   at `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`. `lemma`
   remains green at a generic formula. `convert-generic`, `pin₃`,
   `pin₃-map` and `convert-at-matrix` remain green.
2. **THE HULL `Convert` IS NOW ONE COMPOSITION, AND THAT
   COMPOSITION IS UNMEASURED.** A consumer that starts from
   `hull-closed` still has `mapFo val (inBound ca cp)` in its
   hypothesis. Closing that form is `pin₃-map`, then this
   equation, then `convert-generic {φ = matrix₃} Δ₀-matrix₃`. The
   transport is a `subst` along this equation at `pin₃`. It is
   not the substitution into the ambient reading of `matrix₃`
   that `[LJ-1.673]` did not finish. Measure that `subst` as its
   own floor before composing. Apply this file at
   `Probe673.slide` and `Probe673.val` (`Probe673.agda:69-73`).
   Do not re-dispatch the equation.
3. **FUND `Completeness` / `BoundInStage` AT `matrix₃` STILL.**
   That is Devlin 5.2 (b), not this equation. Carry `IsOrd` on the
   parameter. The critic of `[LJ-1.673]`
   (`review-of-LJ-1-673-1.md:157-165`) says `LsetGrounded` itself
   must carry `IsOrd δ`. That repair is not this task.
4. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
5. **THIS FRAME RUNS WIDE.** Generic lemma at `src/` is 0.93 s and
   242 MB. Cold matrix composite 17.68 s and 1.76 GB against a
   2 GB cap, 82 percent. Warm instance median 3.10 s and 670 MB.
   `Probe667` pulls `Probe652` and `Probe641`, which this file
   does not use. `W3` / `Probe520` are the 1.76 GB. Do not import
   `Probe667` into a further consumer without measuring the
   composite frame.
6. The module telescope carries `lem` because `Probe667` takes it.
   `lemma` does not use LEM.
7. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires.
This worktree has no `.venv`; the gates ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10592
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task writes a syntactic
  equation from live probes and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `slide-embed-eq`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this equation.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the three-slot shape.** The leftover equation is at
  `matrix₃`, which is that three-slot formula. The equation does
  not depend on slot roles. It is why a three-slot consumer can
  move from `mapFo val (inBound ca cp)` to `pin₃ (embed matrix₃)`.
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
- **`dev/literature/formalizations.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Formalization landscape: Paulson, Flypitch, and what else the fetched material shows`.
  No formalization is a consumer of this equation.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit the hull `Convert` at `mapFo val (inBound ca cp)`.
- I did not take the `subst` along this equation at `pin₃`.
- I did not inhabit `Completeness` or `LsetGrounded`.
- I did not import `Probe652` or `Probe673`. `Probe652` is pulled
  by `Probe667`.
- I did not postulate. I left no hole in `Probe686.agda`.
- I did not leave a red `.agda` under this task home: the two files
  that cannot typecheck are `runs/FLOOR.agda.txt` and
  `runs/FLOOR-matrix.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not write `review-of-slide-embed-eq.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-686/`:

- `Probe686.agda`, the leftover equation at `matrix₃`, green
- `lj-1.686-report.md`, this report
- `runs/`, the Agda transcripts and the two `.agda.txt` floor slices
