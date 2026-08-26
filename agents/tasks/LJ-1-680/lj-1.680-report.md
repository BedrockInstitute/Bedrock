# LJ-1.680 report: a generic unpack at a three-slot Delta-zero formula

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.680
obligation: agents/tasks/LJ-1-680/Probe680.agda::convert-generic
verdict: **GO.** `convert-generic` inhabits `Convert` as a generic unpack
at a 3-slot Δ₀ formula. The witness meter reads
`0 UNRESOLVED of 1, 0.73 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-final.out`, `EXIT=0`). Seven delivered names meter
`0 UNRESOLVED of 7, 0.67 s, probe_red=False`
(`runs/meter-names.out`).

**THIS IS NOT AN INSTANCE AT `matrix₃`.** Nothing in the probe names
`matrix₃`. The term is at a generic transitive carrier and a generic
3-slot Δ₀ formula. `convert-at-true` (`Probe680.agda:141`) forces the
unpack at `⊤̇`. The substitution into one matrix's ambient reading is
the checker `[LJ-1.673]` did not finish
(`agents/tasks/LJ-1-673/runs/p-4.out`) and is not this term.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-680/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ON ANY SHAPE.** The highest peak of a finished
run is 273,743,872 bytes against the 2,147,483,648-byte wide cap
(`runs/p-final.out`), which is 13 percent of it. No run prints a
heap event.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE
UNLESS THE ROW SAYS OTHERWISE.** This report does not bound a
cold-cache number.

**I DID NOT write `review-of-convert-generic.md`.** The obligation
is inhabited. A `review-of-*.md` is how a coder states a NO-GO. This
return is GO.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.673]` closed **NO-GO on `lset-grounded`**
(`agents/tasks/LJ-1-673/lj-1.673-report.md:8-10`). The standing coder
clause says a NO-GO predecessor is a stop. **It is not a stop here.**
The NO-GO is on inhabiting `LsetGrounded` at `matrix₃` as a closed
term. `Convert` is a TYPE (`Probe673.agda:115-119`). The report does
not name `Convert` FALSE. This task takes that type as the generic
unpack `[LJ-1.673]` asked for (`lj-1.673-report.md:299-303`).

`[LJ-1.652]` closed **NO-GO** on `picommute-D-from-elem` and **GO**
on `AtTrans.read` (`Probe652.agda:114-124`). The report does not name
`AtTrans.read` FALSE. Δ₀ is what crosses into the collapse
(`lj-1.652-report.md:111-112`).

The types I took are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `Convert` | AbsL of `inBound` to ambient 3-slot | `Probe673.agda:115-119` | TYPE, green; not inhabited |
| `inBound` | two `∃̇` and two `≐ con` | `Probe673.agda:83-87` | GO |
| `AtTrans.read` | inner Δ₀ reading is ambient | `Probe652.agda:118-124` | GO |
| `matrix₃`, `Δ₀-matrix₃` | 3-slot Δ₀ | `Probe667.agda:72-76` | GO; not imported |
| `Witnessed` | 3-slot Δ₀, soundness | `Probe652.agda:87-91` | TYPE, green |

## 2. D-10, BEFORE ANY AGDA

The target: a 3-slot Δ₀ formula, pinned at two slots by `≐ con` and
wrapped in two `∃̇`, converts AbsL satisfaction at the remaining
free slot into the ambient 3-slot reading. No cardinality or
Tarskian obstruction. Unbounded inner `∃̇` unpacks over the
restricted carrier. `≐` is path equality at `𝒮ᵥ`. `abs₀` moves the
Δ₀ body. Completeness of any one matrix is not this lemma.

The HYPOTHESIS at risk is the SHAPE: a substitution into
`matrix₃`'s ambient reading is the checker `[LJ-1.673]` did not
finish (`agents/tasks/LJ-1-673/runs/p-4.out`). The generic form
never looks inside `φ`. `pin₃-map` is `refl` (`Probe680.agda:60`)
and does not induct on `φ`.

The corrected target beside the original, as D-10 asks: `Convert`
at a generic transitive carrier and a generic 3-slot Δ₀ formula,
not at `matrix₃` and not at `Frame652`'s hull telescope. That is
the term this file inhabits.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the obligation's whole type, `src/`
only, and a HOLE where the term goes. It is `.agda.txt` and not
`.agda`, because conjunct 1 runs every `.agda` under this task home
(`agents/tasks/LJ-1-680/LJ-1.680.md:16-17`).

**THE FRAME COSTS 0.68 s AND 260 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 0.68 s, peak 260,538,368 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:57`). **The obligation TYPE is well-formed.** Importing
`Probe652`, `Probe667` or `Probe673` is not part of this frame.

The import trim is: `src/` only. That is the trim the floor
measured. The delivered probe uses the same imports.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether a generic unpack elaborates where the
substitution did not. Estimate 90 to 190 lines, basis
`agents/tasks/LJ-1-673/lj-1.673-report.md:1`.

**GO.** `convert-generic` (`Probe680.agda:145`, body at `:125-137`)
is inhabited. `pin₃` (`:53-55`) is `inBound` at a generic formula.
`pin₃-map` (`:57-60`) is `refl`. `unpack-pin` (`:87-117`) unpacks
two `∃̇` and two `≐` and does not use Δ₀. `read` (`:75-81`) is
`AtTrans.read` at the carrier it needs and does not use `elem`.
`convert-at-true` (`:141`) is the same term at `⊤̇`.

The estimate was 90 to 190 lines. The delivered probe is 146 lines,
93 code. W3 is the generic unpack, which is the whole probe.

## 5. TWO LAYERS, AND WHAT STILL SITS BETWEEN THIS TERM AND `Convert`

**Layer 1. The pin.** `pin₃` is `inBound` (`Probe673.agda:83-87`) at
a generic `Formula K 3`. `mapFo f (pin₃ φ ca cp)` is
`pin₃ (mapFo f φ) (f ca) (f cp)` by `refl`. A consumer that maps
`inBound` from `Code` to `SM` does not induct on the matrix.

**Layer 2. The unpack.** Two inner `∃̇` yield two restricted-carrier
witnesses. Two `≐` conjuncts are `fst y ≡ fst ca` and
`fst x ≡ fst cp`. `read` fires at those witnesses. `subst` adjusts
the ambient environment along the two paths. Δ₀ is used only by
`read`. `φ` is a variable.

**The remaining gap to `At.Convert` (`Probe673.agda:115-119`).**
`convert-generic` takes `pin₃ (embed φ)` and concludes `⊨ₚ φ`.
`Convert` takes `mapFo val (inBound ca cp)` and concludes `⊨ₚ matrix₃`.
`pin₃-map` closes the pin under `mapFo val`. The leftover equation
is `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃`. That equation
is `mapFo-comp` plus uniqueness of maps out of `⊥*`, and it inducts
on the formula. **This file does not take that induction at
`matrix₃`.** That is the substitution `[LJ-1.673]` could not
finish. A consumer should keep `φ` a variable until the use site,
or restate `Convert` at `pin₃ (embed φ)` so the leftover equation
is never formed.

## 6. W2

**Nothing is proved twice.** `pin₃` is `inBound` at a generic
carrier. `read` is `AtTrans.read` (`Probe652.agda:118-124`) at the
carrier that lemma already quantified over. `AtTrans` lives inside
`Frame652`, so instantiating it would put a hull telescope into
this type. Restating the four-line body at `(U, Utr)` is the
generic form, not a second proof. `convert-at-true` is one
instantiation, at `⊤̇`. No deadline forced a fixed form. There is
no conflict to report.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: a generic pin, a
generic unpack, and `read` at a generic transitive carrier.

**P-l: obeyed.** No type in the probe names a stage presentation.
The statements quantify over a variable `U` with `isTrans U`.
`⟪ Lset lam ⟫` appears nowhere.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2. The recorded
  residue is `Convert`. The generic unpack is written. Completeness
  is not. `Matrix₂` is not funded. Instantiation at `matrix₃` is
  not funded.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before any Agda beyond the predecessor read and filled as
  each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The stop
  at `[LJ-1.673]` was that two green types do not compose without
  extra hypotheses. This task inhabits one of those types at the
  generic form. It is not a measurement that a named statement is
  false, so no sweep is owed.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | obligation type, one hole | 0.68 | 260,538,368 | 42 |
| `runs/p-1.out` | `⊤̇` not in scope | 0.66 | 259,014,656 | 42 |
| `runs/p-2.out` | `⊤̇_` is not `⊤̇` | 0.67 | 259,194,880 | 42 |
| `runs/p-3.out` | unsolved metas, implicit `φ` and SM-paths | 0.75 | 262,422,528 | 42 |
| `runs/p-4.out` | `↾-reflects` unsolved metas | 0.71 | 260,915,200 | 42 |
| `runs/p-5.out` | `∥_∥₁` not in scope, parse | 0.63 | 264,470,528 | 42 |
| `runs/p-6.out` | first green of the delivered shape | 0.75 | 273,727,488 | 0 |
| `runs/recheck-1.out` | forced recheck | 0.73 | 273,711,104 | 0 |
| `runs/recheck-2.out` | forced recheck | 0.72 | 273,694,720 | 0 |
| `runs/recheck-3.out` | forced recheck | 0.73 | 273,711,104 | 0 |
| `runs/p-final.out` | last green of the delivered shape | 0.78 | 273,743,872 | 0 |
| `runs/meter-obligation.out` | the obligation | 0.73 | not taken | 0 |
| `runs/meter-names.out` | 7 names, grouped | 0.67 | not taken | 0 |

Median of the three forced rechecks **0.73 s**. Highest peak of any
finished run **273,743,872 bytes** (`runs/p-final.out`), 13 percent
of the 2 GiB cap. No heap event on any shape. No restructuring for
a heap wall was needed. The first import shape that compiled is
the delivered shape, after the plumbing in `p-1` through `p-5`.

`p-1` is `[NotInScope]` for `⊤̇`. `p-2` is the same after `⊤̇_` in
the `using` list, which `FOL.Syntax` does not export
(`runs/p-2.out:4-8`). `p-3` is unsolved metas on an implicit `φ`
and on SM-equality paths. `p-4` is `[UnsolvedMetaVariables]` at
`↾-reflects` (`runs/p-4.out:5-7`). The cure is not SM-equality:
`read` fires at the unpacked witnesses and `subst` uses the two
`fst` paths from `≐`. `p-5` is `[NoParseForApplication]` because
`∥_∥₁` was not opened. All five are plumbing.

Witness meter, one obligation: `runs/meter-obligation.out`,
`0 UNRESOLVED of 1`, `probe_red=False`. Witness meter, seven names:
`runs/meter-names.out`, `0 UNRESOLVED of 7`. This worktree has no
`.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

The probe interface was deleted after the last run, so the working
tree carries no generated file.

## 10. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 146 | 93 | `Probe680.agda` |
| `pin₃` | 3 | 3 | `Probe680.agda:53-55` |
| `pin₃-map` | 4 | 4 | `Probe680.agda:57-60` |
| `read` | 7 | 7 | `Probe680.agda:75-81` |
| `unpack-pin` | 31 | 31 | `Probe680.agda:87-117` |
| `Unpack.convert-generic` | 19 | 19 | `Probe680.agda:119-137` |
| `convert-at-true` | 3 | 1 | `Probe680.agda:141` |
| top-level lift | 2 | 2 | `Probe680.agda:145-146` |
| floor slice | 59 | 35 | `runs/FLOOR.agda.txt` |

The brief estimated 90 to 190 lines. The probe is 93 code lines.

## 11. WHAT THE SHAPE RESISTED

- **What it cost.** 93 code lines, median 0.73 s on a forced
  recheck, highest peak 274 MB against a 2 GB cap, no heap wall.
- **What the shape resisted.** Five plumbing errors: `⊤̇` not
  imported, `⊤̇_` is not `⊤̇`, an implicit `φ` plus SM-paths,
  `↾-reflects` unsolved, and `∥_∥₁` not in scope. The generic
  unpack compiled on the first attempt that got those five right.
  Instantiation at `matrix₃` was not attempted.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit `Convert` at `matrix₃`. I did not import `Probe673`. I
  did not induct on any concrete formula.
- **What I could not close.** `At.Convert` at `matrix₃`
  (`Probe673.agda:115-119`), and `Completeness`
  (`Probe673.agda:126-130`). Those are not this obligation.

## 12. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH THE GENERIC UNPACK.** `convert-generic`,
   `pin₃`, `pin₃-map`, `unpack-pin` and `read` are green.
2. **TO SPEND THIS TERM AT `matrix₃`, DO NOT SUBSTITUTE INTO THE
   MATRIX.** Apply `convert-generic` at `{φ = matrix₃}` with
   `Δ₀-matrix₃`, after transporting the hypothesis along
   `pin₃-map`. The leftover equation
   `mapFo val (mapFo slide matrix₃) ≡ embed matrix₃` inducts on
   the formula. Measure that equation as its own floor before
   composing. Restating `Convert` at `pin₃ (embed φ)` avoids it.
3. **FUND `Completeness` / `BoundInStage` AT `matrix₃` STILL.**
   That is Devlin 5.2 (b), not this unpack. Carry `IsOrd` on the
   parameter. The critic of `[LJ-1.673]`
   (`review-of-LJ-1-673-1.md:157-165`) says `LsetGrounded` itself
   must carry `IsOrd δ`. That repair is not this task.
4. **DO NOT FUND `Matrix₂`.** D-10 in `[LJ-1.665]`
   (`lj-1.665-report.md:35-39`) still stands.
5. **THIS FRAME RUNS WIDE AND IS CHEAP.** Highest peak 274 MB
   against a 2 GB cap. Do not import `Probe652` or `Probe667`
   into a consumer of this file without measuring the composite
   frame. The floor of this file alone is 0.68 s and 260 MB.
6. This task changed nothing in `src/`.

## 13. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10492
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  It is the archived process document. This task writes a generic unpack
  from live probes and does not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  W2 is live in the slot file. The archived DD row is not a type.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. That
  series is not a predecessor of `Convert`.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this unpack.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  **This is the three-slot shape.** `pin₃` binds the value and the
  parameter by `≐ con` and leaves the witness free, the same order
  as `inBound` (`Probe673.agda:83-87`) and `Witnessed`
  (`Probe652.agda:87-91`).
  `dev/literature/level-formula-slot-roles.md:28` reads
  `| 6 | Jech 13.14 | "The function \`α → L_α\` is Δ₁", from a Σ₁ step \`∃W[...]\` | 2 | \`W\`, the approximating function | value, ordinal | **VALUE, ORDINAL** | \`_build/literature/jech13.txt:561-572\` |`.
  The brief names `:28`. That row is Jech's two-slot Δ₁ function.
  The three-slot unpack this task inhabits is row 4 at `:26`.
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
- **`dev/literature/formalizations-landscape.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Formalization landscape sweep: L, V=L, condensation, AC-in-L, GCH-in-L, rud (OPEN item 7)`.
  No formalization is a consumer of this unpack.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `Convert` at `matrix₃`.
- I did not inhabit `Completeness` or `LsetGrounded`.
- I did not import `Probe652`, `Probe667` or `Probe673`.
- I did not postulate. I left no hole in `Probe680.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not write `review-of-convert-generic.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-680/`:

- `Probe680.agda`, the generic unpack, green
- `lj-1.680-report.md`, this report
- `runs/`, the Agda transcripts and `FLOOR.agda.txt`
