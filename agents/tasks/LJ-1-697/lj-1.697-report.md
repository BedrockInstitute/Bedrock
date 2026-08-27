# LJ-1.697 report: an adequate K that stays inside the stage

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.697
obligation: agents/tasks/LJ-1-697/Probe697.agda::hier-in-stage
verdict: **NO-GO on the closed term. GO on W3: `Lset δ` is a member
of the stage, and on the assembly `Below → HierInStage`.**

The obligation term is not written. The witness meter reads
`1 UNRESOLVED of 1, 3.04 s, probe_red=False`
(`runs/meter-obligation.out:4`). The probe is green and carries no
hole (`runs/recheck-3.out`, `EXIT=0`). Ten other delivered names
meter `0 UNRESOLVED of 10, 3.05 s, probe_red=False`
(`runs/meter-names.out`). W3 meters `0 UNRESOLVED of 4, 1.00 s,
probe_red=False` (`runs/meter-w3.out`). The stated NO-GO is
`agents/tasks/LJ-1-697/review-of-hier-in-stage.md`. That file is the
critic's input and it does not close the task.

**THIS IS NOT A REFUTATION OF `HierInStage`.** I did not build a
term of its negation. Devlin 2.6(ii) still has the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit
(`dev/literature/devlin-II5.md:221-222`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-697/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON THE DELIVERED SHAPE.** The highest peak of
a finished run is 1,754,939,392 bytes against the 2,147,483,648-byte
wide cap (`runs/floor-1.out`), which is 82 percent of it. No run
prints a heap event. The designed-hole floor is `runs/floor-1.out`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** `floor-1` rechecked `Probe679` and
its predecessors and is the one cold-probe row. This report does not
bound a cold-cache number for `src/`.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.679]` closed **NO-GO on the closed term `bound-in-stage`** and
**GO on W3** (`agents/tasks/LJ-1-679/lj-1.679-report.md:8-10`). The
standing coder clause says a NO-GO predecessor is a stop. **It is not
a stop here.** The NO-GO is on inhabiting `bound-in-stage` from
`SameAsGraph` alone. `HierInStage` is a TYPE
(`agents/tasks/LJ-1-679/Probe679.agda:84-88`). The report does not
name it FALSE. The critic upheld the NO-GO and named this type as the
next fund (`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:226-234`).

`[LJ-1.678]` closed **GO on `k-value`**
(`agents/tasks/LJ-1-678/lj-1.678-report.md:8-11`). That value is
`KValue.facts` at `K = Lset λ`. W3 of `[LJ-1.679]` is GO on the
opposite: `kvalue-escapes` (`agents/tasks/LJ-1-679/runs/W3.agda:36-37`).
This task does not inhabit that `K`. Two consumers, two different `K`s.

`[LJ-1.494]` closed **NO-GO on `hier-in-stage` as a term**
(`agents/tasks/LJ-1-494/lj-1.494-report.md:125-130`). The type is not
named FALSE. That frame has no `succλ` (`Probe494.agda:35`). This
frame does (`Probe679.agda:64`). I re-measure at this site. I do not
transfer that NO-GO by analogy.

`[LJ-1.536]` closed **NO-GO on `StageHigh` at the door of `𝒟ₒ-intro`**
(`agents/tasks/LJ-1-536/review-of-StageHigh.md:3-6`). `HierBelow` is a
TYPE (`Probe536.agda:186-187`). The report does not name it FALSE.
`Lset∈suc` and `pr-at` are GO there (`:159-164`). I take those facts
from `src/`, not by importing that probe.

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `HierInStage` | `hierL δ` in `Lset lam` | `Probe679.agda:84-88` | TYPE, green; not inhabited |
| `CompletenessFrom` | `SameHyp → HierInStage → Completeness` | `Probe679.agda:94-95` | TYPE, green; consumer, not this obligation |
| `kvalue-escapes` | `Lset lam ∈ Lset lam → ⊥` | `LJ-1-679/runs/W3.agda:36-37` | GO. Do not use `K = Lset λ` |
| `k-value` | `KValue.facts` at `Lset λ` | `Probe678.agda:32` | GO; serves the reverse, not this consumer |
| `hier-in-stage` | `hierL δ` in `Lset α` | `Probe494.agda:49-53` | TYPE, green; NO-GO as a term. No `succλ` |
| `HierBelow` | `hierL γ` in `Lset (γ+3)` | `Probe536.agda:186-187` | TYPE, green; not inhabited |
| `Lset∈suc` | `Lset β ∈ Lset (sucV β)` | `src/` via `𝒟ₒ-intro`, `Lset-suc` | GO, restated at generic `β` |
| `ord∈Lset→∈` | ordinal in `Lset α` is in `α` | `src/L/Ordinal/Stages.lagda.md:265-268` | GO, in `src/` |

## 2. D-10, BEFORE ANY AGDA

The target is `HierInStage` at `[LJ-1.679]`'s limit frame. Devlin 2.6(ii)
(`dev/literature/devlin-II5.md:221-222`) is the sequence
`(L_δ | δ ≤ γ) ∈ L_α` for `γ < α` at a limit. I did not find a
cardinality or Tarskian obstruction at that generality, once the
parameter is an ordinal in a limit stage.

What is at risk is the HYPOTHESIS that `Lset-out`, `Lset-mono` and
`succλ` assemble the membership of `hierL`. The critic of `[LJ-1.679]`
named those three as the attempt
(`review-of-LJ-1-679-1.md:231-234`) and already recorded that
`Lset-out` and `Lset-mono` do not assemble it alone (`:154-157`).
`[LJ-1.536]` reduced the classical fact to `HierBelow` and stopped at
the door of `𝒟ₒ-intro` (`review-of-StageHigh.md:23-32`).

For an ordinal, `Lset-out` (`src/L/Constructible.lagda.md:346-348`)
is weaker than `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265-268`).
The specialised lemma is the out-lemma this frame spends.

The corrected target beside the original, as D-10 asks:
`At.from-below` (`Probe697.agda:81-86`), `Below → HierInStage`, with
`Below` (`:72-74`) still unpaid.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the obligation's whole type, `Probe679`
and `Probe652` imported, and a HOLE where the term goes. It is
`.agda.txt` and not `.agda`, because conjunct 1 runs every `.agda`
under this task home (`agents/tasks/LJ-1-697/LJ-1.697.md:16-17`).

**THE FRAME COSTS 144.56 s AND 1.75 GB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 144.56 s, peak 1,754,939,392 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:49.19-23`, `:12-14`). **The obligation TYPE is well-formed.**
Importing `Probe679` (and through it `Probe673`, `Probe667`, `Probe652`,
`Probe520`) is not a wall. That run rechecked those predecessors.

The import trim is: `src/` plus `Probe652` plus `Probe679` plus W3.
That is the trim the floor and the probe measured. The delivered
probe does not import `Probe536`.

## 4. W3, WHETHER AN ADEQUATE K CAN SIT INSIDE `Lset lam`

The brief names it. Estimate 120 to 260 lines, basis
`agents/tasks/LJ-1-679/lj-1.679-report.md:1`.

**GO ON THREE MEMBERSHIP FACTS. NO-GO ON PUTTING `hierL` IN THE STAGE
FROM `Lset-out`, `Lset-mono` AND `succλ` ALONE.**

`runs/W3.agda` proves three facts.

1. **`Lset∈suc`** (`:42-44`). `⟨ Lset β ∈ˢ Lset (sucV β) ⟩`, by
   `𝒟ₒ-intro` at `⊤̇` and `Lset-suc`
   (`src/L/Constructible.lagda.md:301-304`,
   `src/L/Axioms/Basic.lagda.md:196-197`). W2: the same two lines as
   `Probe536.agda:159-161`, written at a generic carrier from `src/`,
   not a second import of that probe.
2. **`ordinal-in`** (`:60-62`). An ordinal in `Lset lam` is a member
   of `lam`. W2: `ord∈Lset→∈`.
3. **`lset-in-stage`** (`:67-73`). `⟨ Lset δ ∈ˢ Lset lam ⟩` when
   `δ` is an ordinal in `Lset lam`, by `ordinal-in`, one `succλ`,
   `Lset∈suc` and `Lset-mono`. This is a `K` that is a member of the
   stage. It is not `hierL`. It does not contain the approximation
   table. `kvalue-escapes` already forbids `K = Lset lam`.

`climb` (`:55-57`) is `succλ` iterated. `[LJ-1.494]` had no `succλ`.
This frame does. First green run of W3: exit 0 at 1.67 s, peak
286,048,256 bytes (`runs/w3-2.out`). Final green run: 1.07 s, peak
284,590,080 bytes (`runs/w3-final.out`).

The estimate was 120 to 260 lines. W3 is 73 lines, 39 code. The
delivered probe is 99 lines, 46 code. Together 85 code lines. The new
mathematics is `from-below` and `lset-in-stage`. Completeness as a
term is not in that count because it is not written.

`from-below` (`Probe697.agda:81-86`) takes `Below` at every ordinal
and returns `HierInStage`. `from-below-at` (`:88-95`) is the
pointwise form. Both are green. They CONSUME `Below`. They do not
pay it. That is why `SameHyp` plus this frame still does not inhabit
`CompletenessFrom`.

## 5. W2

**Nothing is proved twice.** `[LJ-1.679]`'s `HierInStage` is imported,
not copied. `ord∈Lset→∈` is `src/`. `Lset-mono` is `src/`. `Lset∈suc`
is `𝒟ₒ-intro` and `Lset-suc` from `src/`, instantiated once at a
generic carrier in `runs/W3.agda`. I did not import `Probe536`: that
probe is the `StageHigh` NO-GO and its conversion wall
(`Probe536.agda:366-375`). `climb` is `succλ` iterated, not a second
limit hypothesis. `from-below` instantiates `Lset-mono` at `step 3`.
No deadline forced a fixed form. There is no conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: `HierInStage` taken
from `[LJ-1.679]`, `Below → HierInStage` inhabited, `Lset δ` a member
of the stage, and `hier-in-stage` not written.

**P-l: obeyed.** The obligation type names `Lset lam`, which is opaque
(`src/L/Constructible.lagda.md:221-223`). It does not name
`sucV (sucV (sucV _))`. `Below` names `step 3`. That is a lemma type,
not the obligation type. `[LJ-1.536]` walled on a successor
presentation in a conversion (`Probe536.agda:366-375`). This file
does not ask Agda to convert `step 4 α ≡ step 3 (sucV α)`.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is `HierInStage` at the limit frame. The type is well-formed.
  `from-below` is inhabited. `Below` is not. `Matrix₂` is not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled as
  each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation of `HierInStage`
  landed. `from-below` is a reduction, not a measurement that the
  type is false. The stop is that `Lset-out`, `Lset-mono` and `succλ`
  do not compose with `hierL` without `Below`. No sweep is owed.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | obligation type, one hole | 144.56 | 1,754,939,392 | 42 |
| `runs/w3-1.out` | W3, `V` not in scope | 1.21 | 283,049,984 | 42 |
| `runs/w3-2.out` | W3 first green | 1.67 | 286,048,256 | 0 |
| `runs/p-1.out` | probe, `CS` shadowed | 3.41 | 796,098,560 | 42 |
| `runs/p-2.out` | first green probe | 4.44 | 907,952,128 | 0 |
| `runs/recheck-1.out` | forced recheck | 3.44 | 677,871,616 | 0 |
| `runs/recheck-2.out` | forced recheck | 3.26 | 677,871,616 | 0 |
| `runs/recheck-3.out` | forced recheck | 3.32 | 677,871,616 | 0 |
| `runs/w3-final.out` | forced recheck of W3 | 1.07 | 284,590,080 | 0 |
| `runs/meter-obligation.out` | the obligation | 3.04 | not taken | 1 |
| `runs/meter-names.out` | 10 names | 3.05 | not taken | 0 |
| `runs/meter-w3.out` | 4 names | 1.00 | not taken | 0 |

Median of the three forced rechecks of the delivered probe **3.32 s**.
Highest peak of any finished run **1,754,939,392 bytes**
(`runs/floor-1.out`), 82 percent of the 2 GiB cap. Highest peak of a
green run **907,952,128 bytes** (`runs/p-2.out`), 42 percent of the
cap. No heap event. No restructuring was needed on the delivered
shape.

`w3-1` is `[NotInScope]` on `V`. The fix is to quantify over `S`.
`p-1` is `[ShadowedModule]` on `CS` with `Probe679.agda:38`. The fix
is `import` not `open import`. Both are plumbing.

Witness meter, one obligation: `runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`. Witness meter, ten names:
`runs/meter-names.out`, `0 UNRESOLVED of 10`. Witness meter, W3:
`runs/meter-w3.out`, `0 UNRESOLVED of 4`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 9. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 99 | 46 | `Probe697.agda` |
| W3, whole | 73 | 39 | `runs/W3.agda` |
| `Lset∈suc` | 3 | 3 | `runs/W3.agda:42-44` |
| `climb` | 3 | 3 | `runs/W3.agda:55-57` |
| `ordinal-in` | 3 | 3 | `runs/W3.agda:60-62` |
| `lset-in-stage` | 7 | 7 | `runs/W3.agda:67-73` |
| `Below` | 3 | 3 | `Probe697.agda:72-74` |
| `from-below` | 6 | 6 | `Probe697.agda:81-86` |
| `from-below-at` | 8 | 8 | `Probe697.agda:88-95` |
| floor slice | 49 | 23 | `runs/FLOOR.agda.txt` |

The brief estimated 120 to 260 lines. W3 plus the probe is 85 code
lines. Completeness as a term is not in that count.

## 10. WHAT THE SHAPE RESISTED

- **What it cost.** 85 code lines, median 3.32 s on a forced
  recheck, highest peak 1.75 GB against a 2 GB cap, no heap wall on
  the delivered shape.
- **What the shape resisted.** Two plumbing errors: `V` not in
  scope, `CS` shadowed by `Probe679`. The membership of `Lset δ`
  compiled on the first attempt that used `S`. Completeness did not
  compile as a term because it was not written: `Lset-out`,
  `Lset-mono` and `succλ` do not put `hierL` in `SL`.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit `HierInStage` from `lset-in-stage` and call it
  `hier-in-stage`. I named `Below`. I did not inhabit `Matrix₂`.
- **What I could not close.** `hier-in-stage`, the membership of
  `hierL δ` in `Lset lam`, given only `Lset-out`, `Lset-mono`,
  `succλ` and `IsOrd`.

## 11. WHAT THE NEXT BRIEF NEEDS

1. **FUND `Below` / `HierBelow`**, `hierL δ ∈ Lset (δ+3)`, at this
   `isL` witness or `[LJ-1.536]`'s. `from-below` then pays
   `HierInStage` (`Probe697.agda:81-86`). Do not re-dispatch
   `from-below`, `from-below-at`, `ordinal-in`, `climb`,
   `lset-in-stage`, or `Lset∈suc`.
2. **THEN FUND `CompletenessFrom`.** `SameHyp → HierInStage →
   Completeness` (`Probe679.agda:94-95`). Do not fund
   `hier-in-stage` from `Lset-out`, `Lset-mono` and `succλ` alone.
   Those three assemble the reduction, not the table.
3. **DO NOT USE `KValue`'s `K = Lset λ`.** `kvalue-escapes` is
   green (`agents/tasks/LJ-1-679/runs/W3.agda:36-37`).
4. **DO NOT TAKE `lset-in-stage` AS `HierInStage`.** `Lset δ` is a
   member of the stage (`runs/W3.agda:67-73`). `hierL δ` is not that
   member.
5. **DO NOT RE-DISPATCH `inBound`, `count-matrix₃`, OR
   `bound-from-stage`.** Green in `[LJ-1.673]`.
6. **DO NOT RE-DISPATCH THE SYNTAX OF THE 3-SLOT MATRIX.** `matrix₃`
   and `Δ₀-matrix₃` are green (`Probe667.agda:72-76`).
7. **DO NOT RE-DISPATCH PINS AT THE NUMERALS.** Green in
   `[LJ-1.672]`. `tags-in-stage` is `num∈λ`.
8. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
9. **THIS FRAME RUNS WIDE.** Highest peak 1.75 GB against a 2 GB cap,
   on a floor that rechecked predecessors. The designed hole and
   every green run sat under 0.91 GB. The heavy tier is not needed.
10. This task changed nothing in `src/`.

## 12. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10722
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

**I DID write `review-of-hier-in-stage.md`, and that is a decision.**
The standing clause says a `review-of-*.md` is how a coder states a
NO-GO, and a NO-GO means the brief's type was not inhabited. The name
`hier-in-stage` is not inhabited. The three membership facts of W3
and the assembly `Below → HierInStage` are inhabited, green and
metered.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task measures a stage
  membership and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this matrix.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `HierInStage`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:60` reads
  `Devlin's \`∃w\` carries the conjunct \`K(w,u)\`, "which says \`w = K(u)\`"`.
  An adequate `K` is the determined bound, not a bare existential, and
  not `K = Lset λ`. `lset-in-stage` places a smaller stage as a member.
  That member is not the internal table `HierInStage` names.
  `dev/literature/level-formula-slot-roles.md:24` reads
  `| 2 | Devlin 2.6 | \`G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]\`; \`G\` says \`f = (L_γ ∣ γ ≤ α)\` | 2 | \`w\`, ONE bound, determined | \`f\`, \`α\` | SEQUENCE, ORDINAL | \`_build/literature/dev2.txt:655-659\` |`.
  **This is `HierInStage`.** The sequence is `hierL`. The bound that
  contains it must sit inside `L_α`.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added and no source was missing.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  The slot arithmetic is in `level-formula-slot-roles.md` and the 2.6
  shape is in `devlin-II5.md` (standing). A second round of source notes
  does not change a type.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  This task certifies no leaf as bounded and quotes no Δ₀ certificate
  from a scanned page, so the errata have nothing to bite.
