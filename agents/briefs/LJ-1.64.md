# LJ-1.64: the last 2.33 seconds, in three named row proofs

tier: codex (default)

## GOAL

The wing is **2.33 seconds** over DD24. `[LJ-1.63]` named three hot
definitions worth **5.845 s** and never measured a cure for any of them.
**Measure them.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `f2c8643`.
**The working tree carries two uncommitted edits and both are green:**

- `src/L/Condensation.lagda.md` at 6,390 in-fence lines: `[LJ-1.62]`'s
  `KFacts` bundle and the whole placed leaf chain.
- `src/L/StageCardinal.lagda.md` at 475 lines: `[LJ-1.63]`'s removal of the
  un-consumed `Successor` cluster.

**Do not discard either.** Backups exist outside the repository.

## WHERE THE WING STANDS, and I measured this myself

```text
       0.0029     335 lines      0.96 s  src/V/Collapse.lagda.md
       0.0062     431 lines      2.67 s  src/L/Hull.lagda.md
  OVER 0.0357      18 lines      0.64 s  src/V/Presentation.lagda.md
       0.0027     620 lines      1.65 s  src/FOL/Count.lagda.md
       0.0044     475 lines      2.09 s  src/L/StageCardinal.lagda.md
  OVER 0.0156   6,390 lines     99.45 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0130 s/line over 8,269 lines and 107.48 s,
             OVER THE BAR (1.18x)
```

**Ceiling 105.15 s. Residual 2.33 s.** `[LJ-1.63]`'s own two runs read
108.27 and 108.90 s, so **take the residual as 2.33 to 3.75 s** and measure
your own baseline before you compare anything.

## THE TARGET, and it is the one thing nobody has measured

`[LJ-1.63]` section 4 profiled `L.Condensation` and named three hot
definitions **that sit BEFORE the leaf chain**, which no dispatch has tried
to cure:

| definition | ms |
|---|---:|
| `PropAgree.subB2T-back` | 2,949 |
| `ImpLeaf.yaOut` | 1,579 |
| `BinFormAgree._.go` | 1,317 |
| **total** | **5,845** |

**That is 2.5x the residual.** `[LJ-1.63]` classed them "curable: INFERRED"
(its negative 6) and measured nothing.

**These are a DIFFERENT SITE from the three moves that regressed.** Those
were tree-level: sealing a built tree, sharing instantiation frames,
aliasing a duplicate. **These are individual row proofs.** Do not assume the
tree-level result transfers (P-l).

## WHAT `[LJ-1.63]` MEASURED FALSE, so you do not repeat it

Three moves regressed at the tree level and were reverted. **Do not re-run
them:**

| move | measured |
|---|---:|
| birth-site sealing of `SatGraphB.twelveB` | **+1.61 s** |
| shared instantiation frames in the wrappers | **+17.23 s** |
| `TwelveAgree.twelveB` as an alias | **+3.29 s** |

The sealed run had the CLEANER load, so the direction is not noise.
`[LJ-1.47]` measured the same shape: **sealing buys the repeats, never the
once.**

**If your cure for a row proof is a seal, say why this site differs before
you spend the run.**

## THE ABORT CRITERION, fixed in advance per D-1

`python3 scripts/check-ratio.py --check` is the gate; its **AGGREGATE** is
the verdict.

- **Under the bar**: **STOP and report.** Do not go on to the post-leaf five
  or to `levelIn`/`cover`. A green wing with the whole leaf chain placed is
  the deliverable and I will commit it.
- **Still over after measuring all three**: **STOP and report the price**,
  with each attempt's measured before and after, and say for each whether
  the floor claim is now MEASURED at that definition.

**Either way this dispatch ends at the gate.**

**Measure one definition at a time and gate after each.** If the first cure
closes the residual, stop there and say so; do not spend the other two.

## A SMALL DEFECT TO FIX WHILE YOU ARE IN THE TREE

`src/L/BoundedSubset.lagda.md:1053` is a comment that names
`L.StageCardinal.Successor`, which `[LJ-1.63]` removed. **The comment now
points at nothing.** Fix the comment to say what actually picks the canonical
code. **This is a comment, so DD23 permits it. Do not touch the theorem.**

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap, and you may not narrow a
  direction.** Both directions are needed; that is settled.
- **Do not delete content to buy the ratio.** P-q measured that removing
  duplicated content removes lines and almost no seconds, so a deletion
  shrinks the denominator faster than the numerator and makes the ratio
  WORSE. **`[LJ-1.63]`'s removal was admissible only because the cluster was
  un-consumed AND expensive, at 0.103 s per line.** If you find another
  un-consumed block, apply the same two tests and report the consumer audit
  at `file:line` before removing anything.
- **Archive, never delete**, for a whole module; a dead section inside a live
  master is a removal with a backup, per the owner's 2026-08-10 ruling.
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** `[LJ-1.63]` is the model: it turned three inferred claims into
three measured negatives, and that is why the floor claim is now credible.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Nothing placed so far mentions a concrete carrier and the bundle packages
the sharing rather than reducing it. **Keep that.** If a row-proof cure
reduces what the J tower inherits, name the trade before you take it.

## ARCHIVE (DD18)

- **`_build/lj-1.63-report.md`**, read WHOLE. Section 4 is the profile that
  names your three targets; section 5 is what regressed and by how much;
  section 2 is the consumer-audit shape that found the dead cluster.
- `_build/lj-1.62-report.md` sections 2 and 3, the bundle and its profile.
- `_build/lj-1.47-report.md`, the D-30 consumer audit and the
  "sealing buys the repeats, never the once" result.
- `dev/LESSONS.md` P-m, P-n, P-q, P-t, P-c, R-36, R-38, I-5, D-30, read
  WHOLE. **P-n is at `dev/LESSONS.md:2483` and is the claim under test.**
- **`src/ProbeLJ161A.agda`** and the four earlier probes. They must survive.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`_build/lj-1.63-report.md` sections 4 and 5 FIRST, then the three named
definitions in `src/L/Condensation.lagda.md`, then `dev/LESSONS.md:2483`
for P-n.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ164*.agda`. Your report is `_build/lj-1.64-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-i.** The conversion-explosion playbook: select the cure by its decision
  tree, not by trial.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** Inner-world truncation branches carry written types. **`[LJ-1.63]`
  reports the hot rows already carry them, so I-5 is discharged there; check
  it yourself before you rely on that.**
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-13, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries two uncommitted
  edits that are not in HEAD; do not discard them.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- **The gate's guard may refuse in your sandbox** (`pgrep` cannot read the
  process list). Say so, bypass it as the last three dispatches did, and keep
  every Agda invocation sequential. **I re-run the gate myself with a working
  guard, and my runs have agreed with yours three times.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.64-report.md` incrementally, skeleton first.

**Lead with the gate's aggregate verdict, quoted, and the seconds you removed
and from where.** Then each of the three definitions: what you tried, the
measured before and after in one caliber, and whether P-n's floor is now
MEASURED at that site. Then the comment fix. **Mark every negative MEASURED
or INFERRED.** Then the DD4 answer and **the convergence answer.**
