# LJ-1.689 report: the hull Convert, from hull-closed's own hypothesis form

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.689
obligation: agents/tasks/LJ-1-689/Probe689.agda::hull-convert
verdict: **GO.** `hull-convert` inhabits `Convert` starting from
`hull-closed`'s hypothesis form `mapFo val (inBound ca cp)`, with
`[LJ-1.686]`'s leftover equation as a HYPOTHESIS. The body is
`pin₃-map`, then `subst` along that equation at `pin₃`, then
`convert-generic`. The witness meter reads
`0 UNRESOLVED of 1, 1.07 s, probe_red=False`
(`runs/meter-obligation.out:4`). The probe is green and carries no
hole (`runs/p-final.out`, `EXIT=0` at `:22`). Two delivered names
meter `0 UNRESOLVED of 2, 0.70 s, probe_red=False`
(`runs/meter-names.out:5`).

**THIS IS THE HULL HYPOTHESIS FORM, NOT THE HULL TELESCOPE.**
`val` and `slide` are parameters. Nothing in the probe names
`Code`, `Frame652` or `Probe673`. The hull maps of
`Probe673.agda:69-73` are one instance of those parameters.
`inBound` (`Probe689.agda:43-46`) is `pin₃ (mapFo slide φ)`, which
is `Probe673.agda:83-87` at a generic alphabet and a generic
formula. The leftover equation is not formed and is not
re-inhabited.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-689/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON ANY SHAPE.** The highest peak of a finished
run is 262,848,512 bytes against the 2,147,483,648-byte wide cap
(`runs/recheck-3.out:5`), which is 12 percent of it. No run prints a
heap event.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** The floor checked `Probe680` as
part of its own frame (`runs/floor-1.out:4`). Later green runs are
warm on that interface. This report does not bound a cold-cache
number for the composition itself.

**I DID NOT write `review-of-hull-convert.md`.** The obligation
is inhabited. A `review-of-*.md` is how a coder states a NO-GO. This
return is GO.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.682]` closed **GO on `convert-at-matrix`**
(`agents/tasks/LJ-1-682/lj-1.682-report.md:9-18`). The report names
that spend **NOT the hull `Convert`** (`lj-1.682-report.md:20-24`).
It does not name `convert-generic` or `convert-at-matrix` FALSE. It
names what a hull consumer still carries: `mapFo val (inBound ca cp)`
in the hypothesis, and the leftover equation
`mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`
(`lj-1.682-report.md:309-316`).

`[LJ-1.680]` closed **GO on `convert-generic`**
(`agents/tasks/LJ-1-680/lj-1.680-report.md:9-15`). The leftover
equation is named there and is not formed
(`lj-1.680-report.md:146-153`). The report does not name that
equation FALSE. The brief cites `:1` for "take it and do not form
it"; the named leftover is at `:146-153`.

`[LJ-1.686]` closed **GO on `slide-embed-eq`**
(`agents/tasks/LJ-1-686/lj-1.686-report.md:9-17`). The report does
not name that equation FALSE. This brief takes the equation as a
HYPOTHESIS and does not form it. I take the type from the probe
that typechecked (`Probe686.agda:52-53`) and I do not inhabit it
again. The next-brief item at `lj-1.686-report.md:343-353` names
the unmeasured composition: `pin₃-map`, then the equation, then
`convert-generic {φ = matrix₃} Δ₀-matrix₃`, as a `subst` along the
equation at `pin₃`. That composition is this obligation.

`[LJ-1.673]` closed **NO-GO on `lset-grounded`**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:8-10`). That is not a
stop here. The NO-GO is on inhabiting `LsetGrounded` at `matrix₃`
as a closed term. `Convert` is a TYPE (`Probe673.agda:115-119`).
The report does not name `Convert` FALSE. `inBound` is written
(`Probe673.agda:83-87`). `slide` and `val` are written
(`Probe673.agda:69-73`). `hull-closed` is the hull's only closure
rule and takes a `Formula Code 1` (`src/L/Hull.lagda.md:415`).

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**. That is not a
stop here. `matrix₃` and `Δ₀-matrix₃` are green
(`Probe667.agda:72-76`). The report does not name those FALSE.

`[LJ-1.652]` closed **NO-GO on `picommute-D-from-elem`** and **GO**
on `AtTrans.read`. That is not a stop here. This task does not
inhabit `PiCommuteD`.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `convert-generic` | generic unpack at 3-slot Δ₀ | `Probe680.agda:119-137` | GO |
| `pin₃` | two `∃̇` and two `≐ con` | `Probe680.agda:53-55` | GO |
| `pin₃-map` | `refl` | `Probe680.agda:57-60` | GO |
| `convert-at-matrix` | restated Convert at `pin₃ (embed matrix₃)` | `Probe682.agda:45-49` | GO; not the hull form |
| leftover equation | `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` | `Probe686.agda:52-53` | GO; taken as HYPOTHESIS, not re-inhabited |
| `Convert` (hull form) | AbsL of `inBound` to ambient 3-slot | `Probe673.agda:115-119` | TYPE, green; inhabited here at the generic form |
| `inBound` | two `∃̇` and two `≐ con` at `matrix₃-Code` | `Probe673.agda:83-87` | GO; restated at a generic formula |
| `slide` | `Empty.rec*` into `Code` | `Probe673.agda:72-73` | GO; a parameter here |
| `val` | code evaluation | `Probe673.agda:69` | GO, from `src/`; a parameter here |
| `hull-closed` | `Formula Code 1` to a hull member | `src/L/Hull.lagda.md:415` | GO, in `src/` |
| `matrix₃`, `Δ₀-matrix₃` | 3-slot Δ₀ | `Probe667.agda:72-76` | GO syntax; not imported |

## 2. D-10, BEFORE ANY AGDA

The target: `Convert` starting from `hull-closed`'s hypothesis form
`mapFo val (inBound ca cp)`, with `[LJ-1.686]`'s equation as a
hypothesis. No cardinality or Tarskian obstruction. The generic
unpack is already green. The leftover equation is already green and
is not re-formed. Completeness of the matrix is not this lemma.
Soundness is not this lemma. `LsetGrounded` is not this lemma.

The HYPOTHESIS at risk is the SHAPE of the composition: a `subst`
along the equation at `pin₃`, then `convert-generic`. That is the
unmeasured term `[LJ-1.686]` named (`lj-1.686-report.md:343-353`).
It is not the substitution into the ambient reading of `matrix₃`
that `[LJ-1.673]` did not finish (`agents/tasks/LJ-1-673/runs/p-4.out`).

The corrected target beside the original, as D-10 asks: the hull
hypothesis form at a generic transitive carrier, a generic alphabet
`K`, a generic 3-slot Δ₀ formula, and a generic pair of maps
`slide` and `val`, with the leftover equation as a hypothesis. W2.
Instantiation at `Probe673.slide` and `Probe673.val` is a consumer.
Importing `Probe673` would put the hull telescope into this type,
which `[LJ-1.680]` refused (`lj-1.680-report.md:158-161`).

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the hull `Convert` at
`mapFo val (inBound φ slide ca cp)`, with `[LJ-1.686]`'s equation
as a hypothesis and a HOLE where the term goes. It is `.agda.txt`
and not `.agda`, because conjunct 1 runs every `.agda` under this
task home (`agents/tasks/LJ-1-689/LJ-1.689.md:16-17`).

**THE FRAME COSTS 1.64 s AND 238 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 1.64 s, peak 237,912,064 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:58`, `runs/floor-1.out:5`). **The obligation TYPE is
well-formed.** The frame checked `Probe680` (`runs/floor-1.out:4`).
Importing `Probe667`, `Probe673` or `Probe686` is not part of this
frame.

The import trim after the floor: `Probe680` is the delivered unpack
and `pin₃` / `pin₃-map`. Relabelling supplies `mapFo` and `embed`.
Nothing else is added. The equation is a hypothesis, so `Probe686`
is not imported. `φ` is a variable, so `Probe667` is not imported.
`val` and `slide` are parameters, so `Probe673` is not imported.
The module telescope does not carry LEM.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the hull hypothesis form unpacks once
the equation is given. Estimate 80 to 180 lines, basis
`agents/tasks/LJ-1-682/lj-1.682-report.md:1`.

**GO.** `hull-convert` (`Probe689.agda:71`, body at `:62-67`) is
inhabited. `inBound` (`:43-46`) is `pin₃ (mapFo slide φ)`.
`pin₃-map` rewrites `mapFo val (inBound φ slide ca cp)` to
`pin₃ (mapFo val (mapFo slide φ)) (val ca) (val cp)` and is `refl`
(`Probe680.agda:57-60`). `subst` along the hypothesized equation
rewrites the inner formula to `embed φ`. `convert-generic`
(`Probe680.agda:119-137`) unpacks at `pin₃ (embed φ)`. The
delivered body compiled on the first attempt (`runs/p-1.out`,
`EXIT=0` at `:22`).

The estimate was 80 to 180 lines. The delivered probe is 71 lines,
37 code. W3 is the composition, which is the whole probe. The unpack
is `[LJ-1.680]` and is not rewritten.

## 5. TWO LAYERS, AND WHAT STILL SITS BETWEEN THIS TERM AND `LsetGrounded`

**Layer 1. The transport, now green.** `pin₃-map` is definitional.
The leftover equation is a hypothesis of the type `[LJ-1.686]`
already inhabited at `matrix₃`. The `subst` along that equation at
`pin₃` elaborates. It does not substitute into the ambient reading
of `matrix₃`.

**Layer 2. The unpack, already green.** `convert-generic` unpacks
two `∃̇` and two `≐`, then `read` at `Δ₀ φ`. This file does not
re-dispatch it. `convert-at-matrix` remains the spend at
`pin₃ (embed matrix₃)` and is not this term.

**The remaining gap to `At.Convert` as `Probe673` wrote it
(`Probe673.agda:115-119`).** That type fixes `K = Code`,
`φ = matrix₃`, `slide` and `val` from the hull, and does not
mention the leftover equation. Closing it is this term applied at
`Δ₀-matrix₃`, `Probe673.slide`, `Probe673.val`, and
`Probe686.slide-embed-eq`. That application imports `Probe667` and
`Probe673`. It is unmeasured as a composite. Measure it as its own
floor before composing. Do not re-dispatch this transport. Do not
re-dispatch the equation.

**The remaining gap to `LsetGrounded`.** `Completeness` /
`BoundInStage` (`Probe673.agda:90-95,126-130`) is still a TYPE.
`hull-closed` at `inBound` is already the consumer
(`Probe673.agda:100-104`). This file does not inhabit either.

## 6. W2

**Nothing is proved twice.** `convert-generic` is the generic unpack
at a generic transitive carrier. `slide-embed-eq` is the leftover
equation, taken as a hypothesis and not re-inhabited. `inBound` is
`pin₃` at `mapFo slide φ`, the same pin `[LJ-1.680]` wrote, not a
second formula. This task writes the composition once at a generic
carrier, a generic alphabet and a generic 3-slot Δ₀ formula.
`convert-at-matrix` (`Probe682.agda:45-49`) is the unpack at
`matrix₃` without this transport. No deadline forced a fixed form.
There is no conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The
ideal form written fresh today is the form delivered: one
composition of a delivered unpack with a hypothesized equation, at
a generic carrier.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over a variable `U` with `isTrans U` and a
variable alphabet `K`. `⟪ Lset lam ⟫` appears nowhere. `φ` is a
`Formula`, not a stage. `val` and `slide` are parameters, so `Code`
does not enter the type.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is the hull `Convert`. The generic composition is written.
  Completeness is not. `Matrix₂` is not funded. Instantiation at
  `Probe673`'s hull telescope is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled
  as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded
  key was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop
  at `[LJ-1.673]` was that two green types do not compose without
  extra hypotheses. This task inhabits the hull form of one of
  those types, with the missing equation as a hypothesis. It is not
  a measurement that a named statement is false, so no sweep is
  owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs
from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | hull form, one hole, `Probe680` in frame | 1.64 | 237,912,064 | 42 |
| `runs/p-1.out` | first green of the delivered shape | 0.99 | 262,815,744 | 0 |
| `runs/recheck-1.out` | forced recheck | 1.24 | 262,799,360 | 0 |
| `runs/recheck-2.out` | forced recheck | 0.88 | 262,815,744 | 0 |
| `runs/recheck-3.out` | forced recheck | 0.88 | 262,848,512 | 0 |
| `runs/p-final.out` | last green of the delivered shape | 0.87 | 262,832,128 | 0 |
| `runs/meter-obligation.out` | the obligation | 1.07 | not taken | 0 |
| `runs/meter-names.out` | 2 names, grouped | 0.70 | not taken | 0 |

Median of the three forced rechecks **0.88 s**. Median peak of
those three **262,815,744 bytes**. Highest peak of any finished
run **262,848,512 bytes** (`runs/recheck-3.out:5`), 12 percent of
the 2 GiB cap. Highest green peak is that same figure. No heap
event on any shape. No restructuring for a heap wall was needed.
The delivered shape compiled on the first attempt (`p-1`). There
is no plumbing red run.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, two names
(`hull-convert`, `Convert.inBound`): `runs/meter-names.out`,
`0 UNRESOLVED of 2`. This worktree has no `.venv`; the meter ran as
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
| the probe, whole | 71 | 37 | `Probe689.agda` |
| `Convert.inBound` | 4 | 4 | `Probe689.agda:43-46` |
| `Convert.hull-convert` | 16 | 16 | `Probe689.agda:52-67` |
| top-level lift | 1 | 1 | `Probe689.agda:71` |
| floor slice | 60 | 32 | `runs/FLOOR.agda.txt` |

The brief estimated 80 to 180 lines. The probe is 37 code lines.
The unpack is `[LJ-1.680]`. The new term is `inBound` plus a
six-line body.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 37 code lines, median 0.88 s on a forced
  recheck, highest peak 263 MB against a 2 GB cap, no heap wall.
  The floor is 1.64 s and 238 MB.
- **What the shape resisted.** Nothing of the mathematics. The
  obligation type was well-formed at the floor. The body compiled
  on the first attempt. The leftover equation was not formed, so
  its induction was not re-measured. Instantiation at `matrix₃`
  and at `Probe673`'s hull telescope was not attempted.
- **What I had to weaken.** Nothing of the obligation. The equation
  is a hypothesis, as the brief ordered, even though `[LJ-1.686]`
  already inhabited it. `val` and `slide` are parameters, which is
  the generic form, not a weaker Convert. I did not inhabit
  `Probe673.At.Convert` inside the hull telescope.
- **What I could not close.** `At.Convert` at the hull telescope
  (`Probe673.agda:115-119`) as a closed instance,
  `Completeness` (`Probe673.agda:126-130`), and `LsetGrounded`.
  Those are not this obligation. The instance at `Δ₀-matrix₃`,
  `Probe673.slide`, `Probe673.val` and `Probe686.slide-embed-eq`
  is unmeasured as a composite.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH THIS TRANSPORT.** `hull-convert` is green
   at `mapFo val (inBound φ slide ca cp)`, with the leftover
   equation as a hypothesis. `convert-generic`, `pin₃`,
   `pin₃-map`, `convert-at-matrix` and `slide-embed-eq` remain
   green.
2. **TO SPEND THIS TERM AT THE HULL, INSTANTIATE, DO NOT REWRITE.**
   Apply `hull-convert` at `{φ = matrix₃}` with `Δ₀-matrix₃`,
   `Probe673.slide`, `Probe673.val` (`Probe673.agda:69-73`), and
   discharge the hypothesis with `Probe686.slide-embed-eq`. That
   application is `At.Convert` (`Probe673.agda:115-119`). It
   imports `Probe667` and `Probe673`. Measure that composite as
   its own floor before composing. `[LJ-1.682]` warned that the
   `Probe667` frame is 19.51 s and 1.51 GB cold
   (`lj-1.682-report.md:324-329`). `[LJ-1.686]` warned the same
   at 17.68 s and 1.76 GB (`lj-1.686-report.md:361-367`). This
   file's own frame is 1.64 s and 238 MB and does not pay that.
3. **FUND `Completeness` / `BoundInStage` AT `matrix₃` STILL.**
   That is Devlin 5.2 (b), not this unpack. Carry `IsOrd` on the
   parameter. The critic of `[LJ-1.673]`
   (`review-of-LJ-1-673-1.md:157-165`) says `LsetGrounded` itself
   must carry `IsOrd δ`. That repair is not this task.
4. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
5. **THIS FRAME RUNS WIDE AND IS CHEAP.** Floor 1.64 s and 238 MB
   against a 2 GB cap, 12 percent at the highest green peak. Do
   not import `Probe667` or `Probe673` into a further consumer
   without measuring the composite frame.
6. The module telescope does not carry LEM. A consumer that
   imports `Probe667` will take LEM because that module takes it.
   `hull-convert` does not use LEM.
7. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires.
This worktree has no `.venv`; the gates ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10621
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task writes a hull Convert
  from live probes and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `hull-convert`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this composition.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the three-slot shape.** `inBound` binds the value and the
  parameter by `≐ con` and leaves the witness free, the same order
  as `pin₃` (`Probe680.agda:53-55`) and `Witnessed`
  (`Probe652.agda:87-91`). The hull `Convert` is this row, not
  Jech's two-slot Δ₁ function at `:28`.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  No Devlin error class is at issue in this composition.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md`. A second
  round of source notes does not change a type.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `Probe673.At.Convert` inside the hull telescope.
- I did not form, and I did not re-inhabit, the leftover equation
  `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`.
- I did not inhabit `Completeness` or `LsetGrounded`.
- I did not import `Probe667`, `Probe673` or `Probe686`.
- I did not postulate. I left no hole in `Probe689.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not write `review-of-hull-convert.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-689/`:

- `Probe689.agda`, the hull Convert at the hull hypothesis form, green
- `lj-1.689-report.md`, this report
- `runs/`, the Agda transcripts and `FLOOR.agda.txt`
