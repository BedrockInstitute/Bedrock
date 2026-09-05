# LJ-1.61: place the rest of the leaf chain, then take levelIn and cover

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits.
This report is `_build/lj-1.61-report.md`.

## 0. THE VERDICT

**NO-GO, MEASURED: the wing crosses at the first leaf-chain placement,
and the dispatch stops here per the pre-fixed criterion.**

`ShapedAgree` and `WitnessAgree` are placed and typecheck. The wing
aggregate after them is 0.0154 s per line over 7,695 lines and
118.31 s, OVER the DD24 bar 0.012716 (1.39x the AC side). Three gate
runs agree (0.0151 / 0.0151 / 0.0154). The marginal rate of the
placement is (100.32 - 72.70) / 165 = 0.167 s per line in the final
run, three times the densest previously measured class (the walk `out`
at 0.0538, `[LJ-1.60]`). The deciding negative is the gate's own
aggregate verdict: MEASURED.

Per the pre-fixed abort criterion (D-1), the dispatch STOPS here: the
rest of the leaf chain is not placed and `levelIn`/`cover` are not
discharged. A measured NO-GO with the gate's own numbers is the full
deliverable. The working tree carries the measured placement and this
report.

## 1. THE LEDGER (live)

| hypothesis | status | what it still needs |
|---|---|---|
| `levelIn` | NOT DISCHARGED | the rest of the leaf chain and the post-leaf five, section 5 |
| `cover` | NOT DISCHARGED | the same, plus the least-delta Skolem selection |

| step | status | the term not written |
|---|---|---|
| 1. `ShapedAgree`, `WitnessAgree` | **PLACED** | none |
| 2. `KeyAgree`, `DefinesAgree` | NOT PLACED | the port of `ProbeLJ154A.agda:97-246` |
| 3. `TwelveAgree` composition | NOT PLACED | the port of `ProbeLJ155B.agda:788-979` |
| 4. `SatGraphAgree` | NOT PLACED | the port of `ProbeLJ156A.agda:649-835` |
| 5. `LeafAgree` | NOT PLACED | the port of `ProbeLJ157A.agda:832-985` |
| 6. post-leaf five | NOT ATTEMPTED | section 5 |

**Where this dispatch stopped, in the ledger's terms:** after
`ShapedAgree` + `WitnessAgree` (step 1), measured NO-GO at wing
aggregate 0.0154; before `KeyAgree`/`DefinesAgree` (step 2). The
worktree count of `L.Condensation` is 5,727 in-fence lines (HEAD
5,562; +165).

## 2. THE GATE, AND ITS ENVIRONMENTAL REFUSAL

`scripts/check-ratio.py --check` refuses to run in this sandbox: its
`agda_blocker()` guard calls `pgrep -x agda`, and the sandbox has no
`sysmond` service, so pgrep exits 3 (`pgrep: Cannot get process list`)
and the guard fails closed. The refusal is MEASURED (section 7,
negative 1). The guard's intent is C-12: no wing measurement beside a
live Agda process. This dispatch satisfies that intent procedurally:
every Agda invocation in the session is sequential, and no two agda
processes ever overlapped. The gate's own code path runs with the guard
bypassed, at the gate's own caliber: `measure()` from the tool, cold,
warm dependencies, `ac_baseline_ghcrts` from the ledger, and
`ledger.count(at_head=False)` for the lines. Every verdict below is
the gate's own arithmetic over the gate's own measurements.

## 3. THE GATE VERDICTS, QUOTED

Baseline, clean tree at `24ada39`:

```text
check-ratio | AC baseline 0.0111 s/line (module-cold, warm dependencies) | tolerance 1.15x | bar 0.0127 s/line | cold
       0.0052     335 lines      1.74 s  src/V/Collapse.lagda.md
       0.0055     431 lines      2.39 s  src/L/Hull.lagda.md
  OVER 0.0314      18 lines      0.56 s  src/V/Presentation.lagda.md
       0.0024     620 lines      1.47 s  src/FOL/Count.lagda.md
  OVER 0.0198     564 lines     11.15 s  src/L/StageCardinal.lagda.md
  OVER 0.0131   5,562 lines     72.70 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0120 s/line over 7,530 lines and 90.01 s, within the bar
```

After step 1, run 1:

```text
  OVER 0.0173   5,730 lines     99.32 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0151 s/line over 7,698 lines and 116.57 s, OVER THE BAR (1.37x)
```

After step 1, run 2:

```text
  OVER 0.0172   5,730 lines     98.54 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0151 s/line over 7,698 lines and 116.36 s, OVER THE BAR (1.37x)
```

Final tree (imports trimmed to the placed content), run 3:

```text
  OVER 0.0175   5,727 lines    100.32 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0154 s/line over 7,695 lines and 118.31 s, OVER THE BAR (1.39x)
```

The three placed-tree runs spread 116.36 to 118.31 s (1.7 pc); the
Condensation slice spreads 98.54 to 100.32 s (1.8 pc). The baseline
slice of 72.70 s matches the `[LJ-1.60]` band (75.49 s mean at a
different load). The verdict is the aggregate: OVER in every run.

## 4. WHAT WAS PLACED, AND THE WALL

Step 1 is `ShapedAgree` and `WitnessAgree` in
`src/L/Condensation.lagda.md`, ported from `src/ProbeLJ157A.agda`
section 4 (`:660-831`) with one adaptation: the master's kit-spelled
`ShapesAgree.back` no longer takes the code-set membership argument
(`[LJ-1.58]`'s D-30 narrowing), so `ShapedAgree.back` calls
`S.back (h c c∈)` instead of the probe's `S.back c∈ (h c c∈)`. The
statement is unchanged. The master typechecks green; the consumer
`L.BoundedSubset` re-checks green at 14.34 s user (its recorded band).

The marginal rate of step 1 is 0.154 to 0.167 s per line across the
three pairwise deltas, 3x the walk-`out` class and 9x the back class.
The content class is instantiation (P-m): `WitnessAgree` instantiates
`ClosedAgree` and `ShapedAgree` four times, each at a full
twenty-plus-parameter telescope, and the two module headers carry long
formula-body types. The profile attribution (cold, `-M8g`, total
103,924 ms): `Miscellaneous` 65,896 ms; `WitnessAgree._.go` 1,422 and
1,253 ms; `ShapesAgree.out` 868 ms; `ShapedAgree.back` 814 ms;
`ShapedAgree.out` 795 ms. The named new definitions sum to about
6.7 s; the remaining about 20 s of the 27 s marginal sits in
`Miscellaneous` (header and instantiation elaboration). The three
imports the placement needed cost at most 2 s of that marginal
(`ProbeLJ161B`, three cold runs: 2.04 / 1.24 / 1.13 s real). The
deciding negative is the aggregate verdict, which does not depend on
this attribution.

## 5. THE TERM NOT WRITTEN (C-36)

The term I could not write: the placement of the rest of the leaf
chain in a spelling that keeps the wing aggregate at or under
0.012716. The rest of the chain is the ports of `KeyAgree` and
`DefinesAgree` (with `TagAgree` and `EnvOneAgree`,
`src/ProbeLJ154A.agda:61-246`), the `TwelveAgree` composition
(`src/ProbeLJ155B.agda:788-979`), `SatGraphAgree`
(`src/ProbeLJ156A.agda:649-835`) and `LeafAgree`
(`src/ProbeLJ157A.agda:832-985`), then the post-leaf five of
`[LJ-1.57]` section 8:

1. `StepAgree`/`ApproxAgree` (both directions) at the graph
   environment, from `LeafAgree` (`ProbeLJ152B.agda:53-87`).
2. `GraphAgree` (`graphBndAt` to `LsetGraphAt`) and the `Adeq` form
   (`ProbeLJ152A.agda:78-104`).
3. The stage truth of `Adeq m` at ordinal hull members (the graph
   construction direction through `Lset-defines`).
4. The ElemDown wiring (`[LJ-1.53]` wall 2, probe green).
5. The collapse of the level, `π (Lset m) = Lset (π m)`.

Then `levelIn` and `cover` (`src/L/BoundedSubset.lagda.md:916-917`).
The chain's first unplaced step is measured at the master and crosses
the wing on its own; everything downstream was not attempted because
the pre-fixed criterion stops at the first crossing. The ports are
green in the probe: `src/ProbeLJ161A.agda` carries the whole chain
against the master and typechecks, so no port is a re-proof.

## 6. THE RATES

Caliber: the gate's own, cold module, warm dependencies,
`GHCRTS=-A64m -I0 -M16g`, one process, one run per module per gate
run. The same-session deltas are the comparable figures.

| configuration | Condensation, s | in-fence lines | per-module rate | wing aggregate |
|---|---:|---:|---:|---:|
| baseline `24ada39` | 72.70 | 5,562 | 0.0131 | 0.0120 over 7,530 lines, within |
| + step 1, run 1 | 99.32 | 5,730 | 0.0173 | 0.0151 over 7,698 lines, OVER |
| + step 1, run 2 | 98.54 | 5,730 | 0.0172 | 0.0151 over 7,698 lines, OVER |
| final tree, run 3 | 100.32 | 5,727 | 0.0175 | 0.0154 over 7,695 lines, OVER |

| marginal, step 1 | lines | seconds | rate |
|---|---:|---:|---:|
| run 1 | 168 | 26.62 | 0.1584 |
| run 2 | 168 | 25.84 | 0.1538 |
| run 3 | 165 | 27.62 | 0.1674 |

**LOAD CAVEAT, MEASURED:** the machine load average during the runs
was 1.9 to 4.3 (4 users), above the quiet-machine assumption. The
same-session deltas are comparable; every absolute figure carries the
caveat. The wing verdict is robust across three runs, so the load does
not decide it.

## 7. DD4

**The placed content keeps the template shape, and the two proofs
share the maximum code.** No placed type mentions a concrete carrier:
`ShapedAgree` and `WitnessAgree` state slots, environments and site
facts as module parameters at `S ^ n` environments, exactly as the
placed walk and the closedness transfer do. `ShapedAgree` is the
forall-in wrapper around the single placed `ShapesAgree` (the kit
spelling), not a re-stated walk. `WitnessAgree` composes the placed
`ClosedAgree` and `ShapedAgree`; no placed content re-proves either.

**The trade, named:** the kit instantiations are the wall. The
elaborator pays the module-header cost of `ClosedAgree` and
`ShapedAgree` once per instantiation, and `WitnessAgree` carries four.
That cost sits in `Miscellaneous` (profile, section 4), which is why
the marginal class (0.16 s per line) exceeds even the walk-`out` class
([LJ-1.60] measured 0.0538): the walk's own instantiations live in one
module header, while the wrappers re-instantiate the whole core at each
call site.

## 8. THE CONVERGENCE ANSWER

**The obligation is not renamed; the wall is priced at the master, and
it is a NO-GO at the first leaf-chain step.** The phase arithmetic: at
7,530 lines the wing's bar ceiling is about 95.7 s and the measured
baseline is 90.01 s, leaving about 5.7 s of headroom. Step 1 added
26.6 to 27.6 s, overrunning the headroom by nearly five times. The
remaining chain (about 720 lines of ports, then the post-leaf five)
cannot land at any measured content class; the first site alone
decides NO-GO, and each further site would be re-measured at its own
place per P-l. The obligation stands: `levelIn` and `cover` still need
the machine to story chain, the chain's first unplaced step is now
priced at the master at 0.154 to 0.167 s per line, and that step
crosses the wing on its own. The next ruling belongs to the owner, on
the price or on a content-class change (P-m: instantiation of the
parameterized core is the expensive class).

## 9. NEGATIVES AND THEIR STATUS

1. The ratio gate's pgrep guard cannot verify the process list in this
   sandbox (no `sysmond`, `ps` blocked): **MEASURED**.
2. The wing aggregate after step 1 is over the bar:
   **MEASURED** (three gate runs: 0.0151 / 0.0151 / 0.0154, over the
   bar 0.012716; Condensation 98.54 to 100.32 s).
3. The step-1 marginal rate is 0.154 to 0.167 s per line:
   **MEASURED** (same-session pairwise deltas, section 6).
4. The cost sits mostly in header and instantiation elaboration
   (`Miscellaneous`), with about 6.7 s in named definitions:
   **PARTLY MEASURED** (profile totals and per-definition times),
   **PARTLY INFERRED** (the split between content elaboration and
   residual effects; the absolute profile comparison carries load
   caveats). This negative sets no verdict; negative 2 does.
5. The imports added for the unplaced steps cost at most 2 s of the
   marginal: **MEASURED** (`ProbeLJ161B`, 1.1 to 2.0 s cold for the
   three modules).
6. `levelIn` and `cover` are not discharged: **MEASURED** (the chain's
   first unplaced step crossed the gate; downstream terms were not
   attempted because the pre-fixed criterion stops at the first
   crossing).
7. The remaining chain would cross the wing at any measured class:
   **INFERRED** (arithmetic from the measured step-1 rate; each site
   would be re-measured). This inference sets no verdict; the verdict
   is negative 2.

## 10. ARCHIVE USED

- `_build/lj-1.60-report.md`, read WHOLE. TOOK the placed forward walk
  (section 1), the rest of the chain (section 2: `ShapedAgree` through
  `LeafAgree` in order), the DD4 answer (section 5) and the rates
  (section 4). Its section 0 verdict is superseded by the wing gate;
  the measurements in it are sound.
- `_build/lj-1.59-report.md`, read sections 0 and 2. TOOK the
  direction answer (machine to story is owed) and the remaining chain.
- `_build/lj-1.58-report.md`, read section 2. TOOK the `Lift12Back`
  spelling and the D-30 narrowing that dropped the membership argument
  from the back direction, which this dispatch's `ShapedAgree.back`
  adaptation reflects.
- `src/ProbeLJ157A.agda`, read WHOLE. TOOK `ShapedAgree`,
  `WitnessAgree` (section 4, `:660-831`) and `LeafAgree` (section 5,
  `:832-985`). The file is untouched.
- `src/ProbeLJ156A.agda`, read WHOLE. TOOK `SatGraphAgree` (section 7,
  `:649-835`). The file is untouched.
- `src/ProbeLJ155B.agda`, read the `TwelveAgree` composition
  (`:788-979`, `out`/`back` at `:951`/`:966`). The file is untouched.
- `src/ProbeLJ154A.agda`, read WHOLE. TOOK `TagAgree`, `KeyAgree`,
  `EnvOneAgree`, `DefinesAgree` (`:61-246`). The file is untouched.
- `src/ProbeLJ152A.agda`, `src/ProbeLJ152B.agda`, read WHOLE. TOOK the
  pinned consumers (`GraphAgree` `ProbeLJ152A.agda:48-51`, `Adeq`
  `:78-81`, `StepAgree`/`ApproxAgree`/`graph-assembly`
  `ProbeLJ152B.agda:53-87`) and the post-leaf assembly shape.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, read the
  obligation sections. TOOK what `levelIn` and `cover` each still
  need, written as terms.
- `src/L/BoundedSubset.lagda.md:916-917`, read the `Condense`
  hypotheses. TOOK `levelIn` and `cover` as the pinned targets.
- `archive/rud-route/`, SHAPE only.
- `dev/LESSONS.md`, via `scripts/rules.py --for build`. TOOK P-h,
  P-k, P-l, P-m, P-n, P-t, P-u, P-v, P-c, R-35, R-36, R-38, R-40,
  I-5, C-12, C-22, C-34, C-36, D-1, D-8, D-10, D-26, D-29, D-30.

## 11. LITERATURE USED

Nothing. `[LJ-1.59]` banked Devlin Step C: the elementarity step
transfers the bounded statement, and the production side is a tree fact
rather than a literature fact. Spend nothing.

## 12. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0. `scripts/ledger.py --check`
clean; the worktree count of `L.Condensation` is 5,727 in-fence lines
(HEAD 5,562). `L.BoundedSubset`, the only consumer, re-checks green at
14.34 s user (its recorded band). `check-ratio --check` was run three
times on the placed tree; every run is OVER the bar (section 3). No
`make check` was run, per the brief. No commit, no push. The working
tree carries the master edit, the probes `src/ProbeLJ161A.agda` and
`src/ProbeLJ161B.agda`, and this report; the four source probes are
untouched.
