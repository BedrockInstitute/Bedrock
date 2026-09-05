# LJ-1.682 report: spend the generic unpack at the matrix, without the substitution

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.682
obligation: agents/tasks/LJ-1-682/Probe682.agda::convert-at-matrix
verdict: **GO.** `convert-at-matrix` inhabits the restated `Convert`
at `pin₃ (embed matrix₃)` by applying `[LJ-1.680]`'s
`convert-generic` at `{φ = matrix₃}` with `Δ₀-matrix₃`. The
leftover equation `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`
is never formed. The witness meter reads
`0 UNRESOLVED of 1, 3.25 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-final.out`, `EXIT=0`). Two delivered names meter
`0 UNRESOLVED of 2, 3.14 s, probe_red=False`
(`runs/meter-names.out`).

**THIS IS NOT THE HULL `Convert`.** Nothing in the probe names
`mapFo val`, `inBound`, `Code` or `Frame652`. The term is
`convert-generic` at the delivered `matrix₃`, at a generic
transitive carrier. The hull form (`Probe673.agda:115-119`) still
asks for the leftover equation this file was ordered not to take.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-682/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON ANY SHAPE.** The highest peak of a finished
run is 1,509,605,376 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), which is 70 percent of it. No run prints a
heap event. The highest green peak is 748,535,808 bytes
(`runs/recheck-3.out`), 35 percent of the cap.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** The floor checked `Probe667`,
`Probe652`, `Probe641`, `W3` and `Probe520` cold
(`runs/floor-1.out:3-9`). Later green runs are warm on those
interfaces. This report does not bound a cold-cache number for the
spend itself.

**I DID NOT write `review-of-convert-at-matrix.md`.** The obligation
is inhabited. A `review-of-*.md` is how a coder states a NO-GO. This
return is GO.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.680]` closed **GO on `convert-generic`**
(`agents/tasks/LJ-1-680/lj-1.680-report.md:9-15`). The types I take
are the types that probe delivered: `convert-generic`, `pin₃`,
`pin₃-map`, `unpack-pin`, `read` (`Probe680.agda:53-60,75-81,87-117,119-137`).
The report does not name those FALSE. It names the spend:
apply `convert-generic` at `{φ = matrix₃}` with `Δ₀-matrix₃`, and
restate `Convert` at `pin₃ (embed φ)` so the leftover equation is
never formed (`lj-1.680-report.md:285-291`).

`[LJ-1.673]` closed **NO-GO on the closed term**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:9-10`). That is not a
stop here. The NO-GO is on inhabiting `LsetGrounded` at `matrix₃`
as a closed term. `Convert` is a TYPE (`Probe673.agda:115-119`).
The report does not name `Convert` FALSE. This task restates that
type at `pin₃ (embed φ)` and does not inhabit the hull form.

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**
(`agents/tasks/LJ-1-667/lj-1.667-report.md:9-11`). That is not a
stop here. The NO-GO is on soundness and hull membership. `matrix₃`
and `Δ₀-matrix₃` are written and green (`Probe667.agda:72-76`).
The report does not name those FALSE.

`[LJ-1.652]` closed **NO-GO on `picommute-D-from-elem`** and **GO**
on `AtTrans.read` (`agents/tasks/LJ-1-652/lj-1.652-report.md:27-40`).
That is not a stop here. This task does not inhabit `PiCommuteD`.
Δ₀ is what crosses into the collapse (`lj-1.652-report.md:111-112`).

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `convert-generic` | generic unpack at 3-slot Δ₀ | `Probe680.agda:119-137` | GO |
| `pin₃` | two `∃̇` and two `≐ con` | `Probe680.agda:53-55` | GO |
| `pin₃-map` | `refl` | `Probe680.agda:57-60` | GO |
| `Convert` (hull form) | AbsL of `inBound` to ambient 3-slot | `Probe673.agda:115-119` | TYPE, green; not inhabited |
| `matrix₃`, `Δ₀-matrix₃` | 3-slot Δ₀ | `Probe667.agda:72-76` | GO syntax; soundness not this task |
| `AtTrans.read` | inner Δ₀ reading is ambient | `Probe652.agda:118-124` | GO |

## 2. D-10, BEFORE ANY AGDA

The target: `[LJ-1.680]`'s `convert-generic` applied at
`{φ = matrix₃}` with `Δ₀-matrix₃`, by restating `Convert` at
`pin₃ (embed φ)`. No cardinality or Tarskian obstruction. The
generic unpack is already green. Completeness of the matrix is
not this lemma. Soundness of the matrix is not this lemma.

The HYPOTHESIS at risk is the SHAPE of the spend, not the
mathematics. The leftover equation
`mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` inducts on the
formula (`lj-1.680-report.md:146-153`). That is the substitution
`[LJ-1.673]` did not finish (`agents/tasks/LJ-1-673/runs/p-4.out`).
Restating `Convert` at `pin₃ (embed φ)` never forms that equation.
The brief forbids the other road unless I measure that equation
as its own floor. I did not take that road.

The corrected target beside the original, as D-10 asks: the
restated `Convert` at a generic transitive carrier, at the
delivered `matrix₃`, not at `Frame652`'s hull telescope and not
by substituting into the matrix. That is the term this file
inhabits.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the restated `Convert` at
`pin₃ (embed matrix₃)`, with a HOLE where the term goes. It is
`.agda.txt` and not `.agda`, because conjunct 1 runs every `.agda`
under this task home (`agents/tasks/LJ-1-682/LJ-1.682.md:16-17`).

**THE FRAME COSTS 19.51 s AND 1.51 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 19.51 s, peak 1,509,605,376 bytes,
one error and it is the designed hole (`[UnsolvedInteractionMetas]`
at `FLOOR.agda:43`). **The obligation TYPE is well-formed.** The
frame checked `Probe680`, `Probe667`, `Probe652`, `Probe641`, `W3`
and `Probe520` (`runs/floor-1.out:3-9`). That is the composite
`[LJ-1.680]` warned about (`lj-1.680-report.md:299-302`). Highest
peak is 70 percent of the 2,147,483,648-byte wide cap. No heap
event.

The import trim after the floor: `Probe667` is the delivered
`matrix₃` / `Δ₀-matrix₃`. `Probe680` is the delivered unpack.
Nothing else is added. `Probe652` and `Probe641` ride in because
`Probe667` imports them; they are not names this file uses. A
reconstruction of `matrix₃` from `W3.erased` plus a copied
`isOrd-at-p` would drop those two, and would not drop `W3` /
`Probe520`, which are the 1.5 GB of the floor. I kept the
delivered names. The module telescope carries `lem` because
`Probe667` takes it. The restated `Convert` does not use LEM.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether `pin₃ (embed φ)` elaborates at
`matrix₃`. Estimate 70 to 160 lines, basis
`agents/tasks/LJ-1-680/lj-1.680-report.md:1`.

**GO.** `convert-at-matrix` (`Probe682.agda:53`, body at `:45-49`)
is inhabited by `convert-generic {φ = matrix₃} Δ₀-matrix₃`.
`pin₃ (embed matrix₃)` is well-formed at the floor
(`runs/FLOOR.agda.txt:41`, `runs/floor-1.out:10-12`). The body
elaborates: first green at 4.28 s and 547,569,664 bytes
(`runs/p-2.out`). Median of three forced rechecks **3.48 s**,
median peak **748,470,272 bytes**.

The estimate was 70 to 160 lines. The delivered probe is 53 lines,
23 code. W3 is the spend at `matrix₃`, which is the whole probe.

## 5. TWO LAYERS, AND WHAT STILL SITS BETWEEN THIS TERM AND THE HULL `Convert`

**Layer 1. The pin, already green.** `pin₃` is `inBound` at a
generic formula (`Probe680.agda:53-55`). `pin₃-map` is `refl`
(`Probe680.agda:57-60`). This file does not re-dispatch either.

**Layer 2. The unpack at `matrix₃`.** `convert-generic` unpacks
two `∃̇` and two `≐`, then `read` at `Δ₀-matrix₃`. `φ` is no
longer a variable: it is the delivered `matrix₃`. The restated
`Convert` takes `pin₃ (embed matrix₃)` and concludes `⊨ₚ matrix₃`.

**The remaining gap to `At.Convert` (`Probe673.agda:115-119`).**
The hull form takes `mapFo val (inBound ca cp)` and concludes
`⊨ₚ matrix₃` at `fst (val ca)` and `fst (val cp)`. `pin₃-map`
closes the pin under `mapFo val`. The leftover equation is
`mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`. **This file
does not take that induction at `matrix₃`.** That is the
substitution `[LJ-1.673]` could not finish. A consumer that
starts from `hull-closed` still has that equation, or it uses
this restated form and never forms it.

## 6. W2

**Nothing is proved twice.** `convert-generic` is the generic
unpack at a generic transitive carrier. This task instantiates it
at the delivered `matrix₃`. `convert-at-true` (`Probe680.agda:141`)
is the same term at `⊤̇`. No deadline forced a fixed form. There
is no conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The
ideal form written fresh today is the form delivered: one
application of the generic unpack at the delivered matrix.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over a variable `U` with `isTrans U`.
`⟪ Lset lam ⟫` appears nowhere. `matrix₃` is a `Formula`, not a
stage.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is `Convert`. The restated form is written. Completeness
  is not. `Matrix₂` is not funded. The hull form at
  `mapFo val (inBound ca cp)` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled
  as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded
  key was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop
  at `[LJ-1.673]` was that two green types do not compose without
  extra hypotheses. This task inhabits the restated form of one of
  those types at `matrix₃`. It is not a measurement that a named
  statement is false, so no sweep is owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs
from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | restated type, one hole, deps cold | 19.51 | 1,509,605,376 | 42 |
| `runs/p-1.out` | `AmbiguousName` on `convert-generic` | 3.52 | 746,946,560 | 42 |
| `runs/p-2.out` | first green of the delivered shape | 4.28 | 547,569,664 | 0 |
| `runs/recheck-1.out` | forced recheck | 3.76 | 748,470,272 | 0 |
| `runs/recheck-2.out` | forced recheck | 3.48 | 748,470,272 | 0 |
| `runs/recheck-3.out` | forced recheck | 3.40 | 748,535,808 | 0 |
| `runs/p-final.out` | last green of the delivered shape | 3.47 | 748,486,656 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.25 | not taken | 0 |
| `runs/meter-names.out` | 2 names, grouped | 3.14 | not taken | 0 |

Median of the three forced rechecks **3.48 s**. Median peak of
those three **748,470,272 bytes**. Highest peak of any finished
run **1,509,605,376 bytes** (`runs/floor-1.out`), 70 percent of
the 2 GiB cap. Highest green peak **748,535,808 bytes**
(`runs/recheck-3.out`). No heap event on any shape. No
restructuring for a heap wall was needed.

`p-1` is `[AmbiguousName]` for `convert-generic`
(`runs/p-1.out:4-19`). `open import ... as P680` brought the
lifted name into scope beside `Unpack.convert-generic`. The cure
is `import` rather than `open import` (`Probe682.agda:30-31`).
That is plumbing. The body compiled on the first attempt that
got the name right.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, two names:
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
| the probe, whole | 53 | 23 | `Probe682.agda` |
| `Spend.convert-at-matrix` | 5 | 5 | `Probe682.agda:45-49` |
| top-level lift | 1 | 1 | `Probe682.agda:53` |
| floor slice | 45 | 23 | `runs/FLOOR.agda.txt` |

The brief estimated 70 to 160 lines. The probe is 23 code lines.
The term is one application of a delivered unpack.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 23 code lines, median 3.48 s on a forced
  recheck, highest green peak 749 MB against a 2 GB cap, no heap
  wall. The cold composite frame is 19.51 s and 1.51 GB.
- **What the shape resisted.** One plumbing error: an unqualified
  `convert-generic` was ambiguous between `Unpack.convert-generic`
  and the lifted `P680.convert-generic`. The spend compiled on
  the first attempt that qualified the import. The leftover
  equation was not formed, so its induction was not measured.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit the hull `Convert`. I did not induct on `matrix₃`. I
  did not import `Probe673`.
- **What I could not close.** `At.Convert` at
  `mapFo val (inBound ca cp)` (`Probe673.agda:115-119`),
  `Completeness` (`Probe673.agda:126-130`), and `LsetGrounded`.
  Those are not this obligation.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH THIS SPEND.** `convert-at-matrix` is green
   at `pin₃ (embed matrix₃)`. `convert-generic`, `pin₃`,
   `pin₃-map`, `unpack-pin` and `read` remain green.
2. **THIS IS NOT THE HULL `Convert`.** A consumer that starts from
   `hull-closed` still has `mapFo val (inBound ca cp)` in its
   hypothesis. Closing that form still asks for the leftover
   equation `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`,
   which inducts on the formula. This file did not form that
   equation and did not measure it. Measure it as its own floor
   before composing, exactly as `[LJ-1.680]` said
   (`lj-1.680-report.md:285-291`).
3. **FUND `Completeness` / `BoundInStage` AT `matrix₃` STILL.**
   That is Devlin 5.2 (b), not this unpack. Carry `IsOrd` on the
   parameter. The critic of `[LJ-1.673]`
   (`review-of-LJ-1-673-1.md:157-165`) says `LsetGrounded` itself
   must carry `IsOrd δ`. That repair is not this task.
4. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
5. **THIS FRAME RUNS WIDE.** Cold composite 19.51 s and 1.51 GB
   against a 2 GB cap, 70 percent. Warm spend median 3.48 s and
   748 MB. `Probe667` pulls `Probe652` and `Probe641`, which this
   file does not use. `W3` / `Probe520` are the 1.5 GB. Do not
   import `Probe667` into a further consumer without measuring
   the composite frame.
6. The module telescope carries `lem` because `Probe667` takes it.
   The restated `Convert` does not use LEM.
7. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires.
This worktree has no `.venv`; the gates ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10555
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task spends a delivered
  unpack from live probes and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `convert-at-matrix`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this spend.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the three-slot shape.** `pin₃` binds the value and the
  parameter by `≐ con` and leaves the witness free, the same order
  as `inBound` (`Probe673.agda:83-87`) and `Witnessed`
  (`Probe652.agda:87-91`). The spend at `matrix₃` is this row, not
  Jech's two-slot Δ₁ function at `:28`.
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
  No Devlin error class is at issue in this spend.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit the hull `Convert` at `mapFo val (inBound ca cp)`.
- I did not form, and I did not measure, the leftover equation
  `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`.
- I did not inhabit `Completeness` or `LsetGrounded`.
- I did not import `Probe652` or `Probe673` directly. `Probe652`
  is pulled by `Probe667`.
- I did not postulate. I left no hole in `Probe682.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not write `review-of-convert-at-matrix.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-682/`:

- `Probe682.agda`, the spend at `matrix₃`, green
- `lj-1.682-report.md`, this report
- `runs/`, the Agda transcripts and `FLOOR.agda.txt`
