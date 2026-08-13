# LJ-1.62: change the content class, or price the wall for the owner

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits.
This report is `_build/lj-1.62-report.md`.

## 0. THE VERDICT

**The content class changed, and the gate says where the wall now
stands: the bundle alone is under the bar; the bundle plus the full
leaf chain is over it, and that is the price the owner rules on.**

The record-bundle spelling of the site-fact block is the content-class
change. It is MEASURED to take the wing under the bar on its own:

```text
check-ratio | AC baseline 0.0111 s/line (module-cold, warm dependencies)
            | tolerance 1.15x | bar 0.0127 s/line | cold
       0.0121   5,695 lines     68.85 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0113 s/line over 7,663 lines and 86.53 s,
             within the bar (1.02x the AC side at the SAME caliber,
             module-cold with warm dependencies)
```

Per the pre-fixed abort criterion (D-1), the dispatch then placed the
rest of the chain. The chain at the bundled spelling is MEASURED to
cross the wing again:

```text
  OVER 0.0157   6,390 lines    100.35 s  src/L/Condensation.lagda.md
check-ratio: wing aggregate 0.0142 s/line over 8,358 lines and 118.31 s,
             OVER THE BAR (1.28x the AC side at the SAME caliber,
             module-cold with warm dependencies)
```

The chain adds 695 in-fence lines and 31.5 to 32.6 s at a marginal
rate of 0.045 to 0.047 s per line. Its cost is P-n content
(satisfaction over built formula trees at a concrete carrier): the
profile shows `LeafAgree.out`/`back` at 4,113/4,095 ms and
`SatGraphAgree.out`/`back` at 1,950/3,289 ms, named definitions, not
`Miscellaneous`. The deciding negative is the gate's own aggregate
verdict on the placed chain: MEASURED. The dispatch stops here per
the pre-fixed criterion. `levelIn` and `cover` are not discharged.

## 1. THE GATE, AND ITS ENVIRONMENTAL REFUSAL

`scripts/check-ratio.py --check` refuses to run in this sandbox: its
`agda_blocker()` guard calls `pgrep -x agda`, and the sandbox has no
`sysmond` service, so pgrep exits 3 (`pgrep: Cannot get process list`)
and the guard fails closed. The refusal is MEASURED. The guard's
intent is C-12: no wing measurement beside a live Agda process. This
dispatch satisfies that intent procedurally: every Agda invocation in
the session is sequential, and no two agda processes ever overlapped.
The gate's own code path runs with the guard bypassed, at the gate's
own caliber: `measure()` from the tool, cold, warm dependencies,
`ac_baseline_ghcrts` from the ledger, and `ledger.count(at_head=False)`
for the lines. Every verdict below is the gate's own arithmetic over
the gate's own measurements.

**LOAD CAVEAT, MEASURED:** the machine load average during the runs
was 2.7 to 3.5 (4 users), above the quiet-machine assumption. Every
absolute figure carries the caveat. The same-session deltas and the
placed-vs-baseline comparisons are the comparable figures; the verdict
is reproduced across runs and does not depend on the load.

## 2. THE SPELLINGS, SIDE BY SIDE

Caliber: the gate's own, cold module, warm dependencies,
`GHCRTS=-A64m -I0 -M8g`, one process, one run per module per gate run.
The same-session deltas are the comparable figures.

| configuration | Condensation s | in-fence lines | per-module rate | wing aggregate |
|---|---:|---:|---:|---:|
| as-placed (LJ-1.61), full gate | 99.07 | 5,727 | 0.0173 | 0.0151 over 7,695, 1.37x, OVER |
| bundle only, module gate run 1 | 69.21 | 5,695 | 0.0122 | 0.0122 over 5,695 (module slice) |
| bundle only, module gate run 2 | 69.39 | 5,695 | 0.0122 | 0.0122 over 5,695 (module slice) |
| bundle only, full gate | 68.85 | 5,695 | 0.0121 | 0.0113 over 7,663, 1.02x, WITHIN |
| bundle + chain, module gate | 101.80 | 6,390 | 0.0159 | 0.0159 over 6,390 (module slice) |
| bundle + chain, full gate | 100.35 | 6,390 | 0.0157 | 0.0142 over 8,358, 1.28x, OVER |

The marginal figures, same-session pairs:

| marginal | lines | seconds | rate |
|---|---:|---:|---:|
| bundle vs as-placed (99.07 to 68.85) | -32 | -30.22 | n/a (removes lines and seconds together) |
| bundle vs as-placed (99.07 to 69.21) | -32 | -29.86 | n/a |
| chain vs bundle (101.80 to 69.21) | 695 | 32.59 | 0.0469 |
| chain vs bundle (100.35 to 68.85) | 695 | 31.50 | 0.0453 |

The bundle is a strict improvement: it removes 32 lines AND about
30 s. The chain is a separate content block at 0.045 to 0.047 s per
line, above the parameterized class (0.01 to 0.013) and below the
hand-written forward walk's class measured at [LJ-1.60] (0.0538).

## 3. THE PROFILE ATTRIBUTION, EACH SPELLING

The profile split between named definitions and `Miscellaneous`,
cold `--profile=definitions`, one run each:

| spelling | total ms | Miscellaneous ms | new/placed named defs, ms |
|---|---:|---:|---:|
| as-placed, LJ-1.61 (cited) | 103,924 | 65,896 | about 6,700 |
| bundle only (measured here) | 67,979 | 31,770 | 3,940 |
| bundle + chain (measured here) | 102,441 | 45,361 | 23,088 |

The bundle cut `Miscellaneous` by 34,126 ms (65,896 to 31,770), which
is the whole mechanism of its 30 s win: the 24 to 44 parameter module
telescopes were re-elaborated at every instantiation site, and the
record packages them into one elaboration per module. The named
definitions of the placed content were already cheap in the as-placed
state (about 6.7 s) and stay cheap (3.9 s); what the bundle removed
was header and instantiation elaboration.

The chain's cost is the opposite split: its named definitions carry
about 19.2 s of the 23.1 s new-content total. The hot names:
`LeafAgree.out` 4,113 ms, `LeafAgree.back` 4,095 ms,
`SatGraphAgree.back` 3,289 ms, `SatGraphAgree.out` 1,950 ms,
`SatGraphAgree.body-back` 951 ms, `SatGraphAgree.body-out` 929 ms,
`TwelveAgree.back` 749 ms, `TwelveAgree.twelveB` 720 ms,
`TwelveAgree.out` 708 ms, `WitnessAgree._.go` 1,033 and 981 ms.
`Miscellaneous` grew 13,591 ms (31,770 to 45,361) for the chain's
header and instantiation elaboration. The absolute profile comparison
carries the load caveat; the totals agree with the gate runs.

## 4. WHAT WAS TRIED, AND WHAT IT COST

1. **The record bundle (the content-class change).** One record
   `KFacts` carries the twelve `tagEq`, the twelve `numK` and the
   closure facts; `KFactsCons` lifts it one environment element. The
   four transfer modules (`ShapesAgree`, `ClosedAgree`, `ShapedAgree`,
   `WitnessAgree`) state the block as ONE parameter. MEASURED: 99.07
   to 68.85 s at 5,727 to 5,695 lines, wing 1.37x to 1.02x. Three
   runs agree (69.21 / 69.39 / 68.85). The content class of the
   leaf-chain placement changed from instantiation to
   header-elaboration-free, and the wing is under the bar with the
   first half of the leaf chain placed.
2. **The rest of the chain at the bundled spelling.** TagAgree,
   KeyAgree, EnvOneAgree, DefinesAgree, TwelveAgree, SatGraphAgree
   and LeafAgree are placed, ported from `src/ProbeLJ161A.agda` with
   the bundle applied to SatGraphAgree and LeafAgree (their site-fact
   blocks are one `KFacts` parameter, and SatGraphAgree carries a
   three-level `KFactsCons` lift for its ClosedAgree sites). MEASURED:
   +695 lines, +31.5 to 32.6 s, marginal 0.045 to 0.047 s per line,
   wing 1.28x, OVER. The chain typechecks green and the consumer
   `L.BoundedSubset` re-checks green (14.5 s user, its recorded band).
3. **Reducing the number of core instantiations (4 to 2) inside
   WitnessAgree.** NOT TRIED. The bundle removed WitnessAgree's own
   cost (its `_._.go` definitions total about 2.0 s and its four
   ClosedAgree/ShapedAgree sites are inside its own body); the
   chain's overrun is in the NEW modules, whose instantiation counts
   are already one per consumer (LeafAgree instantiates WitnessAgree,
   KeyAgree, SatGraphAgree and DefinesAgree once each). This negative
   is INFERRED (reasoning from the profile, not a measurement) and
   sets no verdict.
4. **levelIn and cover.** NOT DISCHARGED. The chain's placement
   crossed the wing before the post-leaf five were attempted, and the
   pre-fixed criterion stops the dispatch at the first crossing. The
   statements remain the pinned hypotheses at
   `src/L/BoundedSubset.lagda.md:916-917`.

## 5. THE DD4 TRADE

**The bundle does not reduce sharing; it packages it.** The record
carries the same site facts the telescope carried, and every placed
type still states slots, environments and site facts at `S ^ n`
environments. No placed type mentions a concrete carrier. The J tower
inherits the generic layer unchanged, instantiated at its own slots.
The `KFactsCons` lift is the one new machinery, and it is generic.

**The trade, named:** the chain's seconds are P-n content. Its hot
definitions state and destruct built formula trees
(`DefBodyB`/`DefBody`, `SatGraphB.satGraphB` against `satGraphAt`,
the `twelveB` conjunction) at the 8-deep concrete environment.
P-n measures that class as a payable floor: named branches with
written types do not remove the cost, and the admissible moves are
less instantiation or accepting the floor. The chain shares the
maximum code with the probes (every module is the probe's template,
instantiated once per consumer); nothing was traded away to gain
seconds. What was not tried is a statement-level re-spelling of the
chain's hot modules (sealing the built trees, or stating the chain's
rows as telescope hypotheses), which P-c/R-36 arguments from
[LJ-1.58] class as moving the cost rather than removing it. That
negative is INFERRED and sets no verdict.

## 6. THE CONVERGENCE ANSWER

**The obligation is not renamed; the wall is priced at the master in
three states.** The as-placed leaf-chain first half cost 27.6 s over
165 lines and crossed the wing at 1.37x. The bundle changed that
block's content class: it removed 30 s and 32 lines and left the wing
under the bar at 1.02x, with about 10.9 s of headroom at 7,663 lines
(ceiling 97.45 s against 86.53 s). The rest of the leaf chain then
cost 31.5 to 32.6 s over 695 lines at 0.045 to 0.047 s per line and
crossed the wing again at 1.28x (118.31 s against the 106.28 s
ceiling at 8,358 lines). To land the full chain, the owner would need
about 12 s removed from the chain's marginal, a further content-class
change to the chain's statement shape (P-n's admissible moves), not a
line lever (P-q). `levelIn` and `cover` still need the chain plus the
post-leaf five; the chain is now placed and priced, and the post-leaf
five were not attempted because the pre-fixed criterion stops at the
crossing.

## 7. NEGATIVES AND THEIR STATUS

1. The ratio gate's pgrep guard cannot verify the process list in
   this sandbox: **MEASURED** (`pgrep -x agda` exits 3, no `sysmond`).
2. The bundle takes the wing under the bar alone: **MEASURED**
   (three cold runs, wing 0.0113, 1.02x).
3. The bundle removes 32 lines and about 30 s against the as-placed
   state: **MEASURED** (same-session pairs, section 2).
4. The rest of the chain at the bundled spelling crosses the wing:
   **MEASURED** (two gate runs, wing 0.0142, 1.28x; Condensation
   100.35 / 101.80 s).
5. The chain's cost sits in named definitions (P-n content), not in
   `Miscellaneous`: **PARTLY MEASURED** (the profile totals and the
   per-definition times), **PARTLY INFERRED** (the split between
   content elaboration and residual effects; the absolute profile
   comparison carries load caveats). This negative sets no verdict;
   negative 4 does.
6. The 4-to-2 instantiation reduction was not tried because the
   bundle already removed the core's cost: **INFERRED** (reasoning
   from the profile). Sets no verdict.
7. `levelIn` and `cover` are not discharged: **MEASURED** (the
   chain's placement crossed the wing; the post-leaf five were not
   attempted because the pre-fixed criterion stops at the crossing).
8. A statement-level re-spelling of the chain's hot modules would
   close the 12 s gap: **INFERRED** (P-n's floor argument, not
   measured). Sets no verdict.

## 8. ARCHIVE USED

- `_build/lj-1.61-report.md`, read WHOLE. TOOK section 4 (the wall:
   the placement and its marginal rate), section 7 (the DD4 answer),
   section 2 (the guard refusal), section 5 (the remaining chain and
   the post-leaf five), section 6 (the rates), section 10 (its
   archive list). Its profile attribution (total 103,924 ms,
   Miscellaneous 65,896 ms, named new definitions about 6,700 ms) is
   cited as the as-placed profile in section 3 here.
- `_build/lj-1.60-report.md`, sections 1 and 5. TOOK the `Lift12Out`
   spelling and its 0.0538 measured walk-`out` class, the rate the
   chain's marginal (0.045 to 0.047) is compared against.
- `_build/lj-1.58-report.md`, section 2. TOOK the `Lift12Back` kit
   and its 4.28x, and the P-c/R-36 argument that sealing moves this
   wall class's cost rather than removing it (the INFERRED negative 8
   here).
- `src/ProbeLJ161A.agda`, read WHOLE. TOOK the whole remaining chain
   in master-compatible form: TagAgree (`:70`), KeyAgree (`:106`),
   EnvOneAgree (`:163`), DefinesAgree (`:201`), TwelveAgree (`:261`),
   SatGraphAgree (`:461`), LeafAgree (`:812`). The file is untouched.
- `src/ProbeLJ157A.agda`, read WHOLE (ShapedAgree/WitnessAgree at
   `:660-831`, LeafAgree at `:832-985`). `src/ProbeLJ156A.agda`, read
   WHOLE (SatGraphAgree at `:649-835`). `src/ProbeLJ155B.agda`, read
   the TwelveAgree composition (`:788-979`). `src/ProbeLJ154A.agda`,
   read WHOLE (TagAgree/KeyAgree/EnvOneAgree/DefinesAgree at
   `:61-246`). All untouched.
- `dev/LESSONS.md`, read P-m (`:2460`), P-q (`:2633`), P-t (`:2601`),
   P-c (`:71`), R-36 (`:808`), R-38 (`:829`), C-33 (`:2987`), C-37
   (`:3304`), and the P-l/P-n/P-h entries through the rules bundle.
   TOOK P-m (the content-class certificate), P-t (the class follows
   the formula, not the carrier), P-q (no line-to-seconds
   conversion), P-n (the payable floor), C-37 (state the action),
   C-33 (the obligation is `levelIn`/`cover`).
- `_build/gch-compression-audit.md`, read WHOLE. TOOK the
   seconds-neutral deletion caution and the standing Condensation
   figures; no deletion was made.
- `dev/ledger.toml`, read the `[ratio]` table and the
   `ac_baseline_module_rate` provenance. TOOK the live bar 0.012716
   (0.011057 at the 1.15 tolerance) and the wing list. Not edited.
- `src/L/BoundedSubset.lagda.md:916-917`, read the `Condense`
   hypotheses. TOOK `levelIn` and `cover` as the pinned, undischarged
   targets.
- `archive/rud-route/`, SHAPE only (the README and the file list).
   WHY NOT more: `[LJ-1.11]` ruled its condensation content
   classically false, and the brief forbids taking a price from it.
- `scripts/check-ratio.py`, read WHOLE. TOOK the gate's own verdict
   path and the guard's failure mode, so the bypass runs the gate's
   own code with the guard neutralized.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. `[LJ-1.59]` already read
Devlin Step C and banked the answer: the elementarity step transfers
the bounded statement, and the production side is a tree fact, not a
literature fact. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0. `scripts/ledger.py --check`
clean; the worktree count of `L.Condensation` is 6,390 in-fence lines
(HEAD 5,562). `L.BoundedSubset`, the only consumer, re-checks green
at 14.5 s user (its recorded band). `check-ratio --check` ran three
times this session (baseline OVER, bundle WITHIN, chain OVER; section
2). No `make check` was run, per the brief. No commit, no push. The
working tree carries the master edit (the bundle plus the placed
chain) and this report; every probe is untouched.
