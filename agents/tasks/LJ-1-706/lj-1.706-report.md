# LJ-1.706 report: Below, from the identification, as a hypothesis

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.706
obligation: agents/tasks/LJ-1-706/Probe706.agda::below-from-carved
verdict: **NO-GO. `below-from-carved` is not inhabited.** The statement is
not false and the identification is not the gap. The gap is ONE row,
`Bound-in-tower`, the placement of `mkBoundedFo`'s bounding stage under
the tower. That row is not in the tree, and it is FALSE in the direction
the door needs unless the carve is re-bounded: the bound climbs one
successor per relativized binder, and the base formula has at least
three nested ones. The corrected target is the carve re-bounded at
`step 2 γ`, where the door lands exactly at `Below`'s stage. The
reduction `below-from-place` (Bound-in-tower + Identified → Below) is
green, so the distance from `[LJ-1.704]`'s identification to `Below` is
measured: exactly the placement row. The stop is stated at
`agents/tasks/LJ-1-706/review-of-below-from-carved.md`. That file is
the critic's input and it does not close the task.

Written as a skeleton before any Agda beyond the predecessor read and
filled as each answer landed (C-22). No commit, no push. I wrote only
inside `agents/tasks/LJ-1-706/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda
process at a time. I did not set `GHCRTS`. Nothing is postulated, the
delivered probe carries `--safe` and no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 857,243,648 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), which is 40 percent of it. No restructuring was
needed.

**EVERY NUMBER BELOW IS MEASURED IN THIS WORKTREE.** `floor-1` is the
one row that rechecked the predecessor cone (`Probe698`, `Probe693`,
`Probe520` and `src/`, `runs/floor-1.out`); every later row ran on the
interfaces it left. This report does not bound a cold-cache number for
`src/` outside this worktree.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

**`[LJ-1.704]` HAS NOT DELIVERED.** Its worktree holds only the
brief (`ls` of
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-704/agents/tasks/LJ-1-704/`,
at dispatch time and again at report time). No report exists, so no
NO-GO and no FALSE verdict blocks this task. The hypothesis type is therefore the type its
brief names: `carved ≡ fst (hierL γ hγ oγ)` at `[LJ-1.698]`'s frame.
This is the beside-task reading the brief orders, and the identification
is a hypothesis, never an inhabited claim, in this probe.

| piece | type | site | verdict |
|---|---|---|---|
| `Below` | `hierL δ` in `Lset (step 3 δ)` at `δ .snd` | `Probe697.agda:72-74` | TYPE, green; not inhabited. Taken as the codomain. |
| `from-below` | `Below`-all → `HierInStage` | `Probe697.agda:81-86` | GO. Not rebuilt. The consumer this probe feeds. |
| `carved-door` | `Door (Lset σ) carved` | `Probe698.agda:128-129` | GO. Taken. |
| `bound-of` | `Σ[σ] (IsOrd σ × BoundedFo ...)` | `Probe698.agda:97-101` | GO. Taken. Its `.fst` is the unplaced stage. |
| `carved∈𝒟ₒ` | `⟨ carved ∈ 𝒟ₒ (Lset σ) ⟩` | `Probe698.agda:125-126` | GO. Taken. |
| `through-door` | the `[LJ-1.698]` obligation | type at `Probe693.agda:135-139`; name absent in `Probe698.agda` | NO-GO (`lj-1.698-report.md:9-12`). Not the type here. The report names the identification and the stage membership as the two unpaid rows (`:37-40`). |
| `door-next` | `Door (Lset σ) x → x ∈ Lset (sucV σ)` | `Probe693.agda:109-111` | GO. Imported, not rebuilt. |
| `step` | `ℕ → V → V`, `sucV` iterated | `Probe693.agda:82-84` | GO. Imported, not rebuilt. |
| `HierBelow` | `hierL γ ∈ Lset (step 3 γ)` at `isL-ord` | `Probe536.agda:186-187` | TYPE, green; not inhabited. The same codomain at another witness. |
| `ApproxInK` | every `ApproxAt` witness in `K` | `Probe532.agda:206-209` | FALSE. Not touched. |

The `[LJ-1.697]` report is NO-GO on the closed term `hier-in-stage`,
not on `Below` (`agents/tasks/LJ-1-697/lj-1.697-report.md:9-10`), and
its section 11 funds exactly this task: "FUND `Below` / `HierBelow`"
(`:303`, item 1). I do not re-dispatch `from-below`,
`from-below-at`, `ordinal-in`, `climb`, `lset-in-stage` or `Lset∈suc`.

## 2. D-10, BEFORE ANY AGDA

**THE TARGET IS NOT FALSE.** `Below` is Devlin 2.6(ii)'s sequence
membership at the tree's carrier (`dev/literature/devlin-II5.md:221-222`,
standing; slot row `dev/literature/level-formula-slot-roles.md:24`).
`[LJ-1.536]` reduced the classical fact to it
(`review-of-StageHigh.md:83-88`) and built no term of its negation.
Neither does this task.

**THE GAP ROW WAS PRICED FOR TRUTH, AND IT FAILS.** The brief's W3
guessed a missing stage comparison. The tree not only lacks it; the
comparison is false in the direction the door needs, unless the stage
of `L_γ` sits at least three successors below `sucV γ`. The chain:
`stage γ = sucV γ` exactly (`src/L/Ordinal/Stages.lagda.md:265-268`,
`:434`, `src/L/Stage.lagda.md:191-193`); `bound2` is the union of the
successor family, one successor above each input
(`src/L/Ordinal.lagda.md:166-192`); `relativize` binds every unbounded
quantifier at the constant (`src/FOL/Manipulation/Relativize.lagda.md:56-57`)
and each binder is a `bound2` merge (`src/L/Axioms/Separation.lagda.md:461`);
the base formula has at least three nested unbounded quantifiers
(`src/L/Coding/Sequence.lagda.md:328-329`, `:291-292`, `:286-289`,
`src/L/Coding/Model.lagda.md:278-280`). So `σ ≥ step 2 γ` solidly, and
`σ ∈ step 3 γ` forces the whole merge chain at or below `sucV γ`.

The corrected target beside the original, as D-10 asks: the carve
re-bounded at `τ := step 2 γ`. The constants fit there (`γ` and `Lset γ`
are members of `Lset (sucV γ)`, and `Lset-mono` carries both up), and
the door at `Lset τ` lands the `τ`-carve in `Lset (sucV τ) =
Lset (step 3 γ)`, exactly `Below`'s stage. What that costs: either
`[LJ-1.704]`'s obligation restated at the `τ`-carve, or a
carve-agreement between the two bounds. The lift uses the bound's
fiber data (`src/L/Axioms/Separation.lagda.md:131-135`), so the two
carves are not the same term by conversion. That is the
separation-uniqueness shape `[LJ-1.704]`'s own W3 names. This is the
mathematician's call: it re-aims a live task.

C-42 does not fire. No refutation of `Below` landed and no false shape
was counted; the falsity argued here is of the PLACEMENT ROW, and the
sweep question for it is the two corrected shapes in the review, priced
there, not counted here. D-26 did not bind: no well-founded key was
built.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The
floor is the obligation's types, formed, in the trimmed frame: `Below`,
`Identified`, `Bound-in-tower`, and the imports that carry them
(`runs/floor-1.out`, the types-only `Probe706.agda`).

**THE FRAME COSTS 28.47 s AND 857 MB, AND IT DOES NOT WALL.** Exit 0.
That run rechecked `Probe698`, `Probe693`, `Probe520` and the `src/`
cone, so it is this worktree's cold-probe row. The import trim: `src/`
plus `Probe693` plus `Probe698`. The `Probe652`/`Probe679` chain that
frames `[LJ-1.697]`'s `At` is NOT imported: `Below` does not depend on
`At`'s parameters, so the type is restated at top level from `src/`
names, exactly as `[LJ-1.697]` itself restated `Lset∈suc` from `src/`
rather than importing `Probe536` (W2, `lj-1.697-report.md` section 5).
That trim saved the 144.56 s floor its frame costs
(`lj-1.697-report.md:126`).

## 4. THE DELIVERED PROBE

`below-from-carved` is the section 2 type without the `Bound-in-tower`
argument. It is NOT defined: no postulate stands in for it, and the
witness meter reads `missing`, `1 UNRESOLVED of 1, probe_red=False`
(`runs/meter-obligation.out`, `[NotInScope]` at the generated witness).

What IS delivered, all green (`runs/p-2.out`, exit 0):

1. **`Below`** (`Probe706.agda:53-54`). `[LJ-1.697]`'s type at
   `[LJ-1.697]`'s carrier, restated from `src/` names.
2. **`Identified`** (`:59-61`). `[LJ-1.704]`'s obligation type, verbatim
   at `[LJ-1.698]`'s frame, as a hypothesis.
3. **`Bound-in-tower`** (`:65-67`). The placement row, named.
4. **`below-from-place`** (`:78-83`). The reduction. `Lset-in`
   (`src/L/Constructible.lagda.md:329-330`) reads the carved set's
   `𝒟ₒ`-membership at the tower's stage, `subst` moves it to the table
   along the identification. THE DISTANCE IS EXACTLY THIS ROW.
5. **`door-lands`** (`:94-99`). `[LJ-1.693]`'s `door-next` applied to
   the delivered door: the carved set lands one successor above
   `mkBoundedFo`'s stage. Not rebuilt (W2).

One plumbing error on the way: `p-1` is `[UnequalTerms]` because the
`subst` went the wrong way along the identification
(`runs/p-1.out:5`). The fix is `idδ`, not `sym idδ`. No mathematical
content in the error.

The first meter attempt read `probe-red exit=-9` at 5.37 s
(`runs/meter-1.out`): the meter's Agda process was killed, not an Agda
error. The rerun under the same caliber is the honest row above.

## 5. W2 ANSWER

Nothing is proved twice. `Below` is restated, not re-proved: it is a
TYPE, and the restatement is at the same carrier `[LJ-1.697]` used,
from `src/` names, because the alternative imports the whole
`Probe652`/`Probe679` `At` frame for parameters `Below` does not read.
`step` and `door-next` are imported from the probe that typechecked
them (`Probe693.agda:82-84`, `:109-111`). The door, the bound and the
`𝒟ₒ`-membership are `[LJ-1.698]`'s, imported. `Lset-in`, `Lset-mono`
(if the corrected target is funded), `hierL` are `src/`. No deadline
forced a fixed form. There is no conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: the codomain type, the
hypothesis type, the named gap, and the reduction that ties them.

**P-l: obeyed.** Every type names `Lset` stages, which are opaque
(`src/L/Constructible.lagda.md:221-223`). `Bound-in-tower` names
`step 3 (fst δ)`, a lemma type, not the obligation type; the
obligation's own type names only `Lset (step 3 (fst δ))` through
`Below`. No conversion between successor presentations is asked
anywhere; `[LJ-1.536]`'s wall shape (`Probe536.agda:366-375`) is not
present.

## 7. WHAT THE SHAPE RESISTED

- **What it cost.** 107 lines, 40 code. Floor 28.47 s cold-cone. First
  green 8.46 s. Median forced recheck 2.38 s. Highest peak 857 MB
  against the 2 GiB cap. No heap wall.
- **What the shape resisted.** One `subst` direction. Then nothing: the
  reduction compiled on the first correct attempt. The resistance is
  not in the term, it is in the ROW the term names, and the review
  prices it.
- **What I had to weaken.** Nothing of the obligation type. I did not
  define `below-from-carved` with the placement row hidden inside
  `Identified`, and I did not take `HierBelowAll` as a hypothesis and
  name the consumer `below-from-carved`.
- **What I could not close.** The placement row. And, below it, the
  in-tree lower bound on the stage of `L_γ` (`L_γ` does not appear by
  stage `γ`), which would turn this stop into a refutation of the
  `mkBoundedFo` door at `Below`'s stage.

## 8. WHAT THE NEXT BRIEF NEEDS

1. **DECIDE THE CARVE'S BOUND BEFORE `[LJ-1.704]` CLOSES.** Its
   identification is being written against `mkBoundedFo`'s carve, whose
   stage overshoots `Below`'s ceiling by the relativized binder depth.
   Two corrected shapes are priced in
   `agents/tasks/LJ-1-706/review-of-below-from-carved.md`: re-bound at
   `step 2 γ` (changes the obligation's left side), or pay a
   carve-agreement between the two bounds. Landing the identification
   on the un-re-bounded carve buys a true equation that cannot feed
   `Below` through `[LJ-1.698]`'s door.
2. **DO NOT RE-DISPATCH** `below-from-place`, `door-lands`, `Below`,
   `Identified`, `Bound-in-tower`, or any of `[LJ-1.698]`'s and
   `[LJ-1.693]`'s pieces this probe imports.
3. **IF THE PLACEMENT ROUTE IS TAKEN ANYWAY**, the missing lemma is an
   upper placement for `bound2` under a fixed ceiling, which the tree
   does not have anywhere (the reflection machinery only goes up,
   `src/L/ReflectFo.lagda.md:202-204`), and it is false at general `γ`
   for this formula. Price the stage-of-`L_γ` lower bound first: it is
   the row that makes the falsity a theorem.
4. **THE CONSUMER STANDS.** `from-below` (`Probe697.agda:81-86`) still
   converts `Below`-all into `HierInStage`. Funding `Below` by either
   corrected shape pays `[LJ-1.697]`'s residue without touching that
   assembly.

## 9. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 107 | 40 | `Probe706.agda` |
| `Below` | 2 | 2 | `Probe706.agda:53-54` |
| `Identified` | 3 | 3 | `Probe706.agda:59-61` |
| `Bound-in-tower` | 3 | 3 | `Probe706.agda:65-67` |
| `below-from-place` | 6 | 6 | `Probe706.agda:78-83` |
| `door-lands` | 6 | 6 | `Probe706.agda:94-99` |

The brief estimated 70 to 180 lines for W3. The delivered term is 12
code lines, because the distance turned out to be one hypothesis, not a
construction. The finding that cost the estimate's worth is in the
review, not in the file: the placement row's falsity argument and the
two corrected shapes.

## 10. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | types only, cone rechecked | 28.47 | 857,243,648 | 0 |
| `runs/p-1.out` | `subst` reversed | 3.63 | 399,261,696 | 42 |
| `runs/p-2.out` | first green full probe | 8.46 | 785,235,968 | 0 |
| `runs/recheck-1.out` | forced recheck | 2.38 | 585,220,096 | 0 |
| `runs/recheck-2.out` | forced recheck | 2.38 | 602,341,376 | 0 |
| `runs/recheck-3.out` | forced recheck | 2.40 | 551,059,456 | 0 |
| `runs/meter-1.out` | witness meter, process killed | 5.37 | not taken | 1 |
| `runs/meter-obligation.out` | witness meter, rerun | 2.54 | not taken | 1 |

Median of the three forced rechecks of the delivered probe **2.38 s**.
Highest peak of any run **857,243,648 bytes** (`runs/floor-1.out`),
40 percent of the 2 GiB cap. No heap event.

Witness meter, one obligation: `runs/meter-obligation.out`, `missing`,
`1 UNRESOLVED of 1`, `probe_red=False`, `[NotInScope]` at the generated
witness for `below-from-carved`. That is the designed absence. This
worktree has no `.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`,
as `[LJ-1.697]` ran it (`lj-1.697-report.md` section 8). I did not add a
dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live membership row against a live door, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live homes of W2 and the coder clauses are the slot file and `AGENTS.md`, not this archive.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used. The only standing status is `dev/pod/screen.toml`.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |`. Read. `Below` is that sequence's membership, and the door's bound is the `w`-slot's stage; the row grounded the D-10 check that the target is the classical fact and the gap is the bound.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not read beyond this line. The 2.6 shape is carried by the slot-roles row and the standing `devlin-II5.md`; a second round of source notes does not change a placement row.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used. No glossary term was added or needed.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used. This task certifies no leaf against a scanned source.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. No Δ₀ certificate and no scanned-page quote is carried by this probe; the falsity argument in section 2 cites only tree files.
