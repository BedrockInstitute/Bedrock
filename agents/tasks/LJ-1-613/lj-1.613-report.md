# LJ-1.613 report: ingredients (i) and (ii), the two "already internal", instantiated

Status: COMPLETE. GO. No commit, no push. ASD-STE100. Written as a
skeleton before any Agda beyond W3 and filled as each run landed (C-22).

## THE VERDICT

**GO.** The obligation
`agents/tasks/LJ-1-613/Probe613.agda::first-two-internal` IS in the
probe, at `agents/tasks/LJ-1-613/Probe613.agda:283-290`, and the probe
is GREEN, EXIT 0, three runs at the delivered shape
(`runs/final-2.out` cold at 28.35 s, `runs/final-3.out` and
`runs/final-4.out` warm at 1.93 s and 1.71 s), plus `runs/final-5.out`
at 22.25 s, the run that postdates the last edit to the probe (a
comment-only citation fix; no code changed). Peak memory 1.115 to
1.244 GB cold and 412 MB warm, caliber `-A64m -I0 -M2g` set by the
program on this pane. I did not set `GHCRTS` at any point. One Agda
process at a time throughout. Every typecheck ran under a wall-clock
cap I set and report below. No hole, no postulate, `--safe` is on,
nothing landed in `src/` (`git status`: only `agents/tasks/LJ-1-613/`
is new), and `review-of-first-two-internal.md` is NOT written because
there is no stop to state.

**BOTH CLAIMS ARE TRUE, AND NEITHER WAS A TERM UNTIL THIS TASK.** Each
ingredient is a substitution instance of a green generic chapter, so
both instantiate cheaply and cleanly. What the campaign had was a
judgement recorded while its own obligation was failing; what it has
now is a typechecked term for each half of that judgement.

## D-10, THE TWO CLAIMS, BEFORE ANY AGDA

The table is `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-41`
and its two INTERNAL rows read, verbatim, one line each in the file:

> | (i) | `D`, the definable power set | INTERNAL. `D-at-the-site`, `Probe594.agda:227-234`: at the real site `limit-step` supplies `DefOf.defSet (Lset ·)` and `𝒟ₒ-inv` (`src/L/StageCardinal.lagda.md:400-401`) |

> | (ii) | the least-element selection | INTERNAL. `h-is-leastOf`, `Probe594.agda:305-317`: `leastOf` over `OrdSWO.ordSWO` (`src/L/StageCardinal.lagda.md:349-351`, `:258-264`) |

So "already internal" MEANT: no new construction is needed, because the
terms exist in the live tree, `DefOf.defSet`
(`src/L/Definability.lagda.md:111-112`), `𝒟ₒ-inv`
(`src/L/Constructible.lagda.md:306-308`), `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-161`) over the site's own
`OrdSWO.ordSWO` (`src/L/StageCardinal.lagda.md:258-264`). And what it
did NOT mean, which is the gap this task closes: both were measured
only THROUGH the site's own call. `D-at-the-site` and `h-is-leastOf`
are equations about `limit-step`'s body at the real site; neither
ingredient had ever been written standalone at the carrier
`[LJ-1.600]` fixed, and `[LJ-1.594]`'s own route line ordered (v)
before them (`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:141-142`:
"`keyS` at `A := LsetS δ oδ`. Then (i) and (ii), which are already
internal."). (v) is paid, so the order permits this task.

**THE TARGET'S TRUTH, PRICED BEFORE THE PROOF.** Both ingredients are
substitution instances of chapters that are green at a generic carrier,
so no Tarskian or cardinality obstruction can reach either. The
literature agrees on (ii) independently: the least-element selection is
a theorem in its own right in the sources (Devlin II.5.9, stated at
`dev/literature/devlin-II5.md:422`: "5.9 (the least element of a
non-empty Σ₀ predicate is Σ₁-definable from its"). The floor runs below
confirm the price is the frame and not the terms.

## W3, THE WIDEST UNMEASURED TERM

Ingredient (i) at this carrier, TYPE ONLY, as the brief ordered:
`agents/tasks/LJ-1-613/runs/W3.agda`, written FIRST and typechecked
ALONE, both halves, `D-at-carrier` at `runs/W3.agda:58-59` and
`inv-at-carrier` at `runs/W3.agda:64-66`. GREEN, EXIT 0, THREE RUNS
(`runs/w3-1.out` to `w3-3.out`): 1.29 s, 0.93 s, 0.90 s, peak 265 to
271 MB, under the cap this task set at TWO MINUTES, which no run
approached. ONE NEGATIVE CONTROL (`runs/w3-neg-1.out`): one planted
arity error, EXIT 42 at `W3neg.agda:59` and nowhere else, 0.94 s. The
checker is live. W3 is IMPORTED by the probe and tied to it by refl
(`Probe613.agda:143-144`, `:157-158`), so the alone-typechecked
statement and the delivered one cannot drift.

## THE FLOOR, MEASURED BEFORE THE PROOF

The floor ran BEFORE any final attempt (`runs/floor-1.out`): the probe
with the three load-bearing bodies as holes in the full import frame,
2.85 s cold, peak 412 MB, EXIT 42 at the holes and nowhere else, cap
300 s never approached. After the restructure below, the floor was
re-measured from the DELIVERED shape (`runs/floor-2.out`): 1.73 s warm,
EXIT 42 at the holes only. So the frame costs about 2 to 3 s and the
statement is cheap; the price story of this task is entirely in one
conversion row, next.

## THE WALL, AND THE RESTRUCTURE THAT CURED IT, IN THIS DISPATCH

The first final run (`runs/final-1.out`) was killed at 56.43 s, peak
1.2385 GB, "command terminated abnormally", the 300 s cap never reached.
Per the owner's ruling of 2026-08-23 I did not report a wall; I bisected
the three bodies and tested new shapes, all under the same cap:

| run | shape | result |
|---|---|---|
| `runs/floor2-1.out` | obligation delivered, site rows holed | 2.45 s, EXIT 42 at the holes |
| `runs/floor3-1.out` | site rows delivered, obligation holed | killed at 23.69 s, 977 MB |
| `runs/floor4-1.out` | 3.1 delivered, 3.2 holed | 2.82 s, EXIT 42 at the hole |

So the wall was ONE row: 3.2 as first written, `site-accepts-first-two
... ≡ SC.limit-step ...` at the FULL `_↪_` pair. THE CURE was
`[LJ-1.594]`'s own green shape, the PROJECTION equation
(`agents/tasks/LJ-1-594/Probe594.agda:227-234`): 3.2 now reads
`fst (site-accepts-first-two ...) ≡ SC.LimitStep.h ... (site's own
lambdas) ...` (`Probe613.agda:239-247`), by refl. The restructured
probe is green at 28.35 s cold. Same content, different shape, and the
shape that fits under the caliber. The row that walls is preserved in
the tree (`runs/Floor3.agda`) with its `.out`, so the price of the pair
form stays measurable.

## THE TWO CLAIMS, TESTED

| claim | what it is, at file:line | verdict |
|---|---|---|
| (i) `D`, the definable power set, with its inversion | `DefOf.defSet` at the stage (`src/L/Definability.lagda.md:111-112`) plus `𝒟ₒ-inv` (`src/L/Constructible.lagda.md:306-308`), in `LimitStep`'s own parameter shape (`src/L/StageCardinal.lagda.md:278-280`) | **INSTANTIATED.** `D-carrier` (`Probe613.agda:137-138`) and `inv-carrier` (`Probe613.agda:152-154`), standalone at every stage, in the alone-typechecked W3 rows (`runs/W3.agda:58-59`, `:64-66`), and running inside the site's own assembly at `Probe613.agda:217-224`, tied to the site's supply by refl at `:239-247` |
| (ii) the least-element selection | `leastOf` (`src/L/WellOrder/Base.lagda.md:158-161`) over `OrdSWO.ordSWO` (`src/L/StageCardinal.lagda.md:258-264`), the term inside `h` (`:349-351`) | **INSTANTIATED.** `least-at-carrier` (`Probe613.agda:180-183`), standalone at every stage with the leastness certified by `IsLeast` in the result type, and the order it selects in re-measured as the ordinal order by refl at `Probe613.agda:190-192` |

The obligation binds the two into one term
(`Probe613.agda:283-290`): (i) as the pair of terms the site supplies,
in `LimitStep`'s own parameter shape, (ii) as the selection. Neither
claim failed, so the "big one" the brief priced for did not happen: the
campaign's week-old judgement was correct, and now it is a term.

## WHAT THE FORMULA NOW WANTS

Of the five ingredients of `class-pred`
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-44`):

| ingredient | state after this task | basis |
|---|---|---|
| (i) | **PAID, by this task**, as a term at this carrier | `Probe613.agda:137-154`, in the obligation at `:283-290` |
| (ii) | **PAID, by this task**, as a term at this carrier | `Probe613.agda:180-192`, in the obligation at `:283-290` |
| (iii) the pairing | **UNPAID ON THIS TREE'S EVIDENCE.** It is inside the circle and this task did not touch it. `[LJ-1.607]`'s confirmation is NOT in this tree: the task expired and its files never landed (see premise defects) | no file |
| (iv) | PAID by `[LJ-1.601]` (base) and `[LJ-1.608]` (limit), both GO with files in the tree; I did not re-inhabit them | `agents/tasks/LJ-1-601/lj-1.601-report.md`, `agents/tasks/LJ-1-608/lj-1.608-report.md` |
| (v) | PAID by `[LJ-1.600]`, GO; imported here as `P600` and applied at (i)'s alphabet (`Probe613.agda:266-268`), not restated | `agents/tasks/LJ-1-600/Probe600.agda:129-130` |

**COUNT: FOUR OF FIVE PAID, ONE WANTING.** What the formula wants is
(iii) alone, plus the tying chapter itself: the one `Formula S 2` with
its `defines` and its `only`, which no task has written. I inhabited
(i) and (ii) only; the (iv) and (v) rows above are read off their GO
reports, not re-proved here.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

The statement cost 0.90 to 1.29 s alone (W3), 2.85 s of cold floor, and
28.35 s cold delivered, of which nearly all is interface building: warm,
the whole probe is 1.71 to 1.93 s. What resisted was exactly one row and
only its first shape: the full-pair refl against `SC.limit-step`, which
walls under the `-M2g` caliber and which the projection shape cures.
Nothing inside either ingredient resisted: every row is a substitution
of a green generic chapter, and the one bridge anywhere in the file,
`fst (LsetS δ oδ)` reducing to `Lset δ`, is the projection
`[LJ-1.600]` already measured at zero
(`agents/tasks/LJ-1-600/runs/W3.agda:56-57`). I weakened nothing: the
obligation's type is `LimitStep`'s own parameter block plus the
selection, and the site row says the site's assembly at my terms IS the
site's own call. The brief estimated about 150 probe lines with about 40
for the obligation and added "if both are genuinely internal, far
less"; the probe is 290 file lines of which 74 are code, and the
obligation is 8 of those. Estimates of shape held; the size came in far
under, in the direction the brief preferred.

## W2, ANSWERED

The mathematics was already written ONCE at generic carriers and this
task adds ZERO generic code: `DefOf.defSet` lives in `module DefOf (A :
S)` (`src/L/Definability.lagda.md:78`), `leastOf` in a module over an
arbitrary `SWO` (`src/L/WellOrder/Base.lagda.md:127`), `OrdSWO` over an
arbitrary ordinal (`src/L/StageCardinal.lagda.md:228`), and every row of
the probe is one of those applied at this carrier. Both trophies share
these pieces exactly as the chapters do. No deadline pressure occurred.

## PREMISE DEFECTS, TWO, BOTH REPORTED AND NEITHER LOAD-BEARING

1. **Premise 6 names files that are not in this tree.**
   `agents/tasks/LJ-1-607/` does not exist: `ls` returns nothing, and
   git shows the task was admitted (`840b8f06`) and expired
   (`2560b303`) with no files ever committed. So
   `agents/tasks/LJ-1-607/lj-1.607-report.md:173` cannot be checked
   here, and the table row "(iii) INSIDE the circle `[LJ-1.607]`
   confirmed as a term" rests on evidence this tree does not hold. Not
   load-bearing for this task: (iii) is explicitly not mine. It IS
   load-bearing for the next brief, which should not cite `[LJ-1.607]`
   as a term until it is re-landed.
2. **Premise 11 names a rule that does not exist.** There is no R-42 in
   `dev/LESSONS.md`: the R series ends at R-41, and
   `dev/LESSONS.md:4404` is C-52's Related line, which lists R-41 among
   others. The respelling rule the premise means is R-41, "state an
   index in the spelling its proof produces" (`dev/LESSONS.md:4762`),
   the same defect `[LJ-1.600]` reported in its premise 11
   (`agents/tasks/LJ-1-600/lj-1.600-report.md:192`). The premise's
   figures "1.74 s against 155.02 s" appear in neither `dev/LESSONS.md`
   nor `dev/ledger.toml` (grep, 0 hits each), so nothing funds them. I
   worked under R-41's substance: ONE spelling, `Formula ⟪ Lset δ ⟫ 1`,
   the site's own, in every row.

Minor, not a defect: premise 13's basis is `AGENTS.md:75`, not `:74`
(`:74` is the one-off-instruction bullet); the clause itself is real.

## THE GATES

`lint-agda`, `check-probes` (7753 tracked files, clean), `lint-prose`
and `check-fences` (102 masters) were run individually and are clean.
`check-rule-ids` over this task's directory flags `R-42` at
`LJ-1.613.md:60` and `:79`, the program's own brief, and this report's
premise-defect row joins it in that class, exactly as `[LJ-1.600]`'s
accepted report does at `:192`; `make check`'s `ruleids` target scans no
paths, so the commit gate itself is unaffected. Nothing under `src/` was
touched, so the whole-tree typecheck state is unchanged, and `make
check` remains the program's gate at commit time. The probe is a raw
`.agda` file, carries no ` ```agda ` fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` READ at `:212`: "| LJ-1.136 | Gate
  the remaining A-prime blocks | GO, BOTH PROBES | pick-canonical
  elaborates, so LJ-1.114's wall falls. A5's risk is seconds, not
  lines: 2.594 s per line |". This is premise 7's basis and the brief's
  own warning that a recorded claim is not a term: the row records
  `pick-canonical` as delivered and the code survives nowhere, which is
  the reason this task inhabited both claims instead of quoting them.
- `archive/dev/JOURNAL.md` declined: not surveyed; the history this task
  needed of its two ingredients is in the live tree
  (`src/L/Definability.lagda.md`, `src/L/Constructible.lagda.md`,
  `src/L/WellOrder/Base.lagda.md`) and in `[LJ-1.594]`'s green probe,
  not in the journal.
- `archive/dev/JOURNAL-archived.md` declined: not read; same reason, and
  `[LJ-1.600]` already showed the AllCodes history there is about (v),
  which this task imports rather than re-derives.
- `archive/dev/DD-archived.md` declined: the archived decision log; the
  rules that bind this task are in `dev/LESSONS.md` and the Boundary.
- `archive/dev/ORCHESTRATION.md` declined: orchestration history; no row
  of this task rests on it.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` READ at `:35`: "Lemma
  II.5.9 states the selection as a theorem in its own right: the least".
  Used for D-10's truth check on (ii): the least-element selection is a
  theorem in the sources, not a choice principle smuggled in, so a
  substitution instance of the tree's `leastOf` has no obstruction to
  fear. Section 1.4's agreement of all three sources ("The selection
  device is a definable well-order plus a universal guard", `:68-69`)
  is the shape `leastOf` + `IsLeast` already carries.
- `dev/literature/devlin-II5.md` READ at `:422`: "5.9 (the least
  element of a non-empty Σ₀ predicate is Σ₁-definable from its". The
  statement itself, quoted by the selection dossier above; confirms the
  selection is definable from parameters, which is what ingredient (ii)
  being "internal" must mean for the eventual formula chapter.
- `dev/literature/digest.md` declined: it pins the rudimentary-functions
  architecture; nothing in a carrier instantiation of `defSet` or
  `leastOf` rests on it.
- `dev/literature/level-formula-slot-roles.md` declined: slot-role
  analysis for the formula chapter that ties the ingredients, which this
  task does not write; the next brief on that chapter may need it.
- `dev/literature/primary-sources.md` declined: a sources index; the two
  passages this task used were reached through the selection dossier and
  checked at their cited lines.
