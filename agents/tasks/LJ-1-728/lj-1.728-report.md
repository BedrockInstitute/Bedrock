# LJ-1.728 report: grounded-from-complete against the constructed Convert

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.728
obligation: agents/tasks/LJ-1-728/Probe728.agda::grounded-from-complete
verdict: **HEAP WALL, PARKED. The obligation is not inhabited and the
probe is delivered as `Probe728.agda.txt`** (brief naming rule: a file
that cannot typecheck is never `.agda`). The W3 question the brief
asked is answered, and the answer corrects 718's attribution: **the
wall is NOT Convert's body at any application, constructed or
hypothesised.** In all seven walling runs the conversion was
hole-shielded and never elaborated. The wall sits in the frame's own
assembly region: the `hull-closed` application against its ascribed
result, and the ambient-slot assembly beside it, at the repaired
telescope. The green floors are measured: the frame with a hole body
peaks 1,622,016,000 bytes (`runs/sd-1.out:8`), the membership region
adds 0.06 GB (`runs/sh-1.out:8`), and every full shape dies at the
2,147,483,648-byte cap (`runs/floor-4.out:4-5`, `runs/full-1.out:4-5`).
The ratio bar cannot fire: the write scope holds no `.lagda.md` and no
fence.

## 0. THE RUN

Written as a skeleton before any Agda beyond the predecessor read and
filled as each answer landed (C-22). No commit, no push. I wrote only
inside `agents/tasks/LJ-1-728/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier
(`runs/full-1.out:1`), ONE Agda process at a time, sequentially. I did
not set `GHCRTS`. Nothing is postulated; no delivered file carries a
hole except the floor shapes, whose holes are their design. Nothing
lands in `src/`.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.692]` is GO and its term is constructed, not hypothesised:
`hull-convert-at-matrix : Convert` is one application of `[LJ-1.689]`'s
`hull-convert` at `{φ = matrix₃}`
(`agents/tasks/LJ-1-692/Probe692.agda:63-65`), metered
`0 UNRESOLVED of 1` (`agents/tasks/LJ-1-692/runs/meter-obligation.out:4`),
green `EXIT=0` (`agents/tasks/LJ-1-692/runs/p-final.out:22`), verdict GO
(`agents/tasks/LJ-1-692/lj-1.692-report.md:7`). Per the coder clause on
module hypotheses I took the type that probe delivered and this
verdict; no NO-GO stands against 692.

`[LJ-1.718]` is NO-GO on ITS shape and the critic upheld it
(`agents/tasks/LJ-1-718/review-of-LJ-1-718-1.md:7`). Its wall was
attributed to the APPLICATION of a hypothesised `conv : A.Convert`.
Its repaired telescope and its green half are the base this task
reuses; its report and its `review-of-grounded-from-complete.md` are
not in this checkout (only `Probe718.agda` and the review were
committed, `git show 81b45343 --stat`), so every 718 fact here is
cited to the two files that exist.

## 2. THE TERM

The delivered shape (shape 4, `Probe728.agda.txt`) states the
obligation's type verbatim at the repaired telescope
(`Probe718.agda:93-101` with its Convert line dropped), takes
`Completeness` with the IsOrd repair as a HYPOTHESIS
(`Probe718.agda:81-86`), opens 692's constructed term as a module
alias over this frame, and assembles the composition from five
strongly ascribed Build-level pieces:

- `AmbientAt v p w`, the ambient matrix₃ reading, named once;
- `SatIn a ca cp`, the hull's reading of `inBound`, named once;
- `HullM a`, hull membership at a witness, named once;
- `codeOf`, hull membership read as the code search
  (`src/L/Hull.lagda.md:337-339`);
- `conv`, the constructed conversion applied
  (`agents/tasks/LJ-1-692/Probe692.agda:63-65`);
- `amb`, the two code equations as two single-coordinate substs over
  `AmbientAt`;
- `hullClosed`, Completeness to hull-closed, the half 718 measured
  green;
- `mkWit`, the witness triple.

The term body is neutral applications only. The soundness argument is
clause (iii)'s own; the composition does not need it and does not use
it. The name is exported at the file's top level
(`agents/tasks/LJ-1-692/Probe692.agda:66`'s pattern). W2: nothing is
written twice. `hull-convert`, `Frame652`, `At`, and 718's statements
are imported, not restated; the only new statement is the telescope
718 already stated, reused verbatim minus one line.

## 3. W3, ANSWERED

**The wall is not Convert's body at any application.** The brief asked
whether composing against the constructed `hull-convert-at-matrix`
avoids 718's Convert-application wall. It cannot be avoided OR
confirmed at this tier, because the application is never reached: in
every walling run the application was a hole and the file still died.
The ladder:

| run | shape | wall s | peak RSS B | exit |
|---|---|---|---|---|
| `runs/sd-1.out` | frame + statement, hole body | 13.52 | 1,622,016,000 | 42 (designed) |
| `runs/sh-1.out` | + AmbientAt, codeOf, membership nest, hole innermost | 13.76 | 1,683,079,168 | 42 (designed) |
| `runs/si-2.out` | + conv/amb/hullClosed/mkWit, hullClosed APPLIED, mkWit hole | 499.25 | 2,561,998,848 | 251 heap |
| `runs/full-1.out` | shape 4, everything live | 382.82 | 2,505,392,128 | 251 heap |
| `runs/floor-4.out` | shape 1 (inline cast), hole in application | 367.84 | 2,505,441,280 | 251 heap |
| `runs/floor-5.out` | shape 2 (AmbientAt + amb), hole in application | 382.01 | 2,539,012,096 | 251 heap |
| `runs/sa-1.out` | shape 2 minus the P692 import | 347.79 | 2,505,408,512 | 251 heap |
| `runs/se-1.out` | shape 2b (where-tail), hole in ambient slot | 530.25 | 2,325,331,968 | 251 heap |
| `runs/floor-6.out` | shape 3 (assembled pieces), hole in conv | 386.97 | 2,363,801,600 | 251 heap |

Every heap row reads `agda: Heap exhausted; Current maximum heap size
is 2147483648 bytes (2048 MB)` (`runs/floor-4.out:4-5`) under the pane
caliber (`runs/full-1.out:1`). Three defects were met and fixed on the
way, each measured: a missing `mapFo` import (`runs/floor-1.out:14`),
a reversed `cong` in the parameter-code equation
(`runs/floor-2.out:4`), and an AmbiguousName between the Spend-opened
`hull-convert-at-matrix` and 692's top-level alias of the same
spelling (`runs/si-1.out:4`), cured by a plain qualified import of 692.

So the measured attribution is: the frame with a hole body sits at
75.5 percent of the cap (`runs/sd-1.out:8`, 1,622,016,000 over
2,147,483,648); the membership region is 0.06 GB more
(`runs/sh-1.out:8`, 1,683,079,168, 78.4 percent); any shape that also
applies `hull-closed` and assembles the ambient slot exceeds the cap.
This region is where 673's `grounded-from-complete` substitution term
stalled (`agents/tasks/LJ-1-673/lj-1.673-report.md:225`, `p-4`, no
`ended` line) and where 718's six shapes walled
(`agents/tasks/LJ-1-718/review-of-LJ-1-718-1.md:32-34`). What is NEW
here is that the application is exonerated: the wall precedes it.

## 4. THE RESTRUCTURING DUTY, DISCHARGED

Six shapes were built and tested under the same cap, each a different
shape, never the same code twice: inline cast, AmbientAt with a
where-block tail, assembled Build-level pieces, named-type pieces
(SatIn/HullM), the same minus the P692 import, and the bisect ladder
sd/sh/si between them. A wall still stands. Per the coder clause this
is now reportable as a finding, and per the brief's naming rule the
probe is `Probe728.agda.txt`, never a red `.agda`. The obligation's
witness meter was not run: with no `.agda` at the obligation path
there is no probe file for it to read, and a crashed meter is not a
measurement.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **The heavy-tier falsifier, funded explicitly.** The 718 review
   already named it for the hypothesis-based composition
   (`agents/tasks/LJ-1-718/review-of-LJ-1-718-1.md:97-100`); this task
   re-names it for the CONSTRUCTED composition: one HEAVY-tier run of
   the `full-1` shape. The tier is program-set (`dev/pod/heads.toml`),
   so this coder could not run it and did not. It is a cheap
   falsifier, not a promised cure: `si-2` peaked 2.56 GB RSS, and RSS
   is not the RTS heap figure, so 4 GB may pass where 2 GB walls.
2. **If heavy passes, the meter reads the obligation and the term is
   already written** (`Probe728.agda.txt`, shape 4). The rename back
   to `.agda` is one `mv`.
3. **If heavy walls too, the frame is the defect**, in the 2026-08-23
   ruling's sense: a term whose floor is 1.62 GB before its first
   row. The cure is a narrower re-dispatch at the SAME obligation
   name, splitting the frame per the ruling's `[LJ-1.559]`/`[LJ-1.566]`
   pattern, not another shape at this tier.
4. **No `review-of-grounded-from-complete.md` was written, and that is
   a decision.** A `review-of-*.md` states a NO-GO about the
   statement. What is measured here is a resource wall in the
   elaboration frame, not the statement's truth; Devlin 5.2 (b)'s
   slot roles, the literature ground of the repaired telescope
   (`dev/literature/level-formula-slot-roles.md:27`), are untouched by
   it. The obligation stays open, supply stays 0.

## SURVEY QUOTES CHECK

Pasted in the return, per the brief.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not run a second Agda process.
- I did not write in `src/`.
- I did not rewrite `hull-convert`, `hull-convert-at-matrix`,
  `slide-embed-eq` or any predecessor term.
- I did not inhabit `Completeness`, and I did not hypothesise
  `Convert`.
- I did not postulate. The delivered `.agda.txt` carries no hole in
  its delivered (full) shape; the hole-bearing files are the floors
  and bisect shapes, `.agda.txt` all.
- I did not run the witness meter, for the reason in section 4.
- I did not add a dependency and I did not create a local `.venv`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-728/`:

- `Probe728.agda.txt`, the term at shape 4, wall-measured
- `lj-1.728-report.md`, this report
- `runs/run.sh`, the runner copied from 692's
- `runs/FLOOR728.agda.txt`, `SA728.agda.txt`, `SD728.agda.txt`,
  `SE728.agda.txt`, `SH728.agda.txt`, `SI728.agda.txt`, the shapes
- `runs/*.out`, the thirteen transcripts

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read, declined. This task needed
  no dispatch mechanics; the loop's operation lives in the live pod
  files and the brief.
- `archive/dev/DD-archived.md`: not read, declined. The DD25 lens the
  718 critic used is quoted inside
  `agents/tasks/LJ-1-718/review-of-LJ-1-718-1.md`, which I read
  directly; the archived source was not opened.
- `archive/dev/PLAN-archived.md`: not read, declined. The live
  direction is `dev/pod/direction.md`; no plan phase bears on a
  single-probe heap measurement.
- `archive/dev/STATUS-archived.md`: not read, declined. The standing
  status is `dev/pod/screen.toml`; no archived status was consulted.
- `archive/dev/TASKS-archived.md`: not read, declined. The
  predecessors that matter (673, 692, 718) were read at their live
  sites under `agents/tasks/`.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read and used.
  `dev/literature/level-formula-slot-roles.md:27` reads "| 5 | Devlin 5.2 (b) | `(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]` | same | `z` | `v`, `γ` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1193-1198` |",
  the row that grounds Completeness's IsOrd-on-the-parameter repair
  this task carries as its hypothesis; the wall measured here is a
  resource wall and does not touch it.
- `dev/literature/devlin-errata.md`: not read, declined. No Devlin
  erratum is at issue; the probe coins no reading of 5.2.
- `dev/literature/glossary-review-2026-08.md`: not read, declined. No
  translation term was coined and no glossary entry was proposed.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined. No source
  beyond the tree's own extracts was consulted.
- `dev/literature/formalizations-landscape.md`: not read, declined.
  No external formalization is a consumer of this probe.
