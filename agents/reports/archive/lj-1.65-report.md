# LJ-1.65: the band bundle, one family, probe-gated

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.65-report.md`.

## 0. THE VERDICT

**NO-GO, at the pre-fixed abort criterion.** The one family (`PropAgree` +
`AndAgree` + `OrAgree`) saves about 0.06 to 0.34 s at the gate's caliber,
under the 0.5 s GO line. The measured means, three cold runs each side, same
session, gate caliber:

| state | run 1 s | run 2 s | run 3 s | mean | spread | load |
|---|---:|---:|---:|---:|---:|---:|
| before (as-placed working tree) | 98.43 | 98.84 | 100.15 | 99.14 | 1.72 | 2.6 to 4.0 |
| after (record bundle, one family) | 99.87 | 98.98 | 98.38 | 99.08 | 1.49 | 4.2 to 6.6 |

The after side ran at higher load than the before side, so three further
after runs were added for a load-matched comparison:

| after, runs 4 to 6 | mean | load |
|---|---:|---:|
| 98.93 / 98.42 / 98.20 s | 98.52 | 3.3 to 6.5 |

All six after runs average 98.80 s, 0.34 s under the before mean; the three
paired runs give 0.06 s. Neither figure reaches 0.5 s, and the spread of
each side (1.5 to 1.7 s) is an order of magnitude larger than the delta.
The deciding claim is MEASURED: the gate-caliber pairs are the fixed
instrument, and the family does not reach the pre-fixed GO line.

The record itself does NOT hang: the P-o hazard did not fire. The record
with all three subK-class fields (`subK1`, `subK0`, `someEnv`) checks green
in place, exit 0, 101.44 s at load 9.2 in the record-only state, and the
full family edit checks green in every after run. No heap wall; the cap was
never raised.

Per the pre-fixed criterion, the dispatch ends here: the env family, the
chain, `levelIn` and `cover` were not attempted. The working tree keeps the
converted family in place (the probe's own edit), and everything else is
untouched.

## 1. THE PROBE, AND THE P-o RISK

The eleven-entry core (tagEq, numK, innerK, pairK, codesK, valK, keyK,
transK, subK1, subK0, someEnv) is restated at
`src/L/Condensation.lagda.md:3090-3145` (PropAgree), `:3336-3368`
(AndAgree) and `:3386-3418` (OrAgree) in the pre-dispatch tree. The probe
bundles it into ONE record parameter. The record carries the three
subK-class fields, so the P-o hazard is measured at this probe. If the
record hangs or walls, the right-nested Sigma is the prescribed cure and is
measured instead.

The record `AgreeCore` is declared at
`src/L/Condensation.lagda.md:3084-3117` in the working tree, opened at
`:3118-3119`, parameterized by `{m} (C T B N K : Fin m) (γ : S ^ m)
(k : ℕ)` with the eleven field types verbatim from the old telescope.
`PropAgree` now takes `(core : AgreeCore C T B N K γ k)` as its eleventh
parameter (`:3134-3135`); `AndAgree` and `OrAgree` take
`(core : AgreeCore C T B N K γ 2)` and `(core : AgreeCore C T B N K γ 3)`
(`:3351-3352`, `:3371-3372`), and each application passes the one value to
`PropAgree`. The only proof-body edits
are projections out of the bundle: `core .keyK`, `core .tagEq`,
`core .numK`, `core .codesK`, `core .valK`, `core .subK1`, `core .subK0`,
`core .someEnv`, `core .transK`, and the two fields hidden from the global
open to avoid clashing with `KFacts` (`innerK`, `pairK`) projected as
`AgreeCore.innerK core` / `AgreeCore.pairK core`. No statement changed; no
module application layer was added; nothing was deleted.

The net line change is minus 46 in-fence lines (6,390 to 6,344, ledger
count).

## 2. THE MEASUREMENTS

Caliber: the gate's own, cold module, warm dependencies,
GHCRTS="-A64m -I0 -M16g" (dev/ledger.toml ac_baseline_ghcrts), one process,
one run per row. The pgrep guard cannot verify the process list (exit 3, no
sysmond), so C-12's intent is held procedurally: every Agda invocation in
this session is sequential.

**LOAD CAVEAT, MEASURED:** the machine load average at the before runs was
2.6 to 4.0 (4 users), and ranged to 9.2 during the record-only run. The
first three after runs ran at 4.2 to 6.6 load. Every absolute figure
carries the caveat. Same-session deltas are the comparable figures, and the
load bias works against the GO direction: the after side measured faster at
higher load, and the delta still does not reach 0.5 s.

| state | run 1 s | run 2 s | run 3 s | load | in-fence lines |
|---|---:|---:|---:|---:|---:|
| before (as-placed working tree) | 98.43 | 98.84 | 100.15 | 2.6 to 4.0 | 6,390 |
| after (record bundle, one family) | 99.87 | 98.98 | 98.38 | 4.2 to 6.6 | 6,344 |

The profile on the after tree (cold `--profile=definitions`, one run, load
3.6 to 4.2): Total 96,600 ms, Miscellaneous 40,946 ms, against the
pre-dispatch profile's Total 99,055 ms and Miscellaneous 42,379 ms
(`_build/lj-1.63-report.md:109-119`). The Miscellaneous delta of about
1.4 s in this single profile run does NOT reproduce at the gate caliber and
is reported as orientation only; the verdict is the three-run pairs above.

The before state was verified green before measurement (the working tree at
dispatch: 6,390 in-fence lines, ledger count), and every after run exited
0. The consumer `L.BoundedSubset` re-checks green against the edited master
(exit 0, warm, 113.23 s; it re-elaborated against the changed interface).

## 3. THE P-o RESULT

P-o did NOT fire. The record with all three subK-class fields was checked in
place in two states: the record-only edit (exit 0, 101.44 s at load 9.2) and
the full family edit (every after run, exit 0). No hang, no heap wall, no
timeout. The nested Sigma fallback was not needed and was not measured; the
law's prescribed action is contingent on the record hanging, which it did
not at this site. MEASURED.

One structural note for the roll-out decision: the record's field types are
the same types the three headers restated, so the bundle removes the two
header restatements and pays the record declaration once. The measured
price of those two restatements is what the probe priced: under 0.5 s.

## 4. THE INSTANTIATION-SITE ANSWER

Structurally, the bundle is worth one record value per row at the
instantiation site: a future instantiation of PropAgree passes `core` once
instead of an eleven-entry telescope, and a future AndAgree/OrAgree
instantiation passes one `AgreeCore` value instead of eleven arguments. That
is the same packaging KFacts measured as the instantiation-site mechanism
(`_build/lj-1.62-report.md:106-112`).

The SECONDS value at the instantiation site is INFERRED, not measured: the
pending wiring does not exist (C-35: the band's consumer is the work that
remains), so no instantiation of this family outside the master can be
timed. The dispatch cannot tell what the wiring would save in seconds, and
says so per the brief.

The measured price of the bundle AT THIS SITE is the verdict: the family's
own restatements were not the band's elaboration mass, so the roll-out of
the remaining families is not funded by this probe.

## 5. THE DD4 ANSWER

YES for the structure, with the measured price named. The bundle keeps the
shared, generic structure: `AgreeCore` is stated once, parameterized by
`{m} (C T B N K : Fin m) (γ : S ^ m) (k : ℕ)`, with no concrete carrier
mentioned anywhere in its fields. The J tower inherits it as it inherits
`KFacts`: any consumer states one record parameter and passes one value.
The statements and proofs of the three rows are unchanged (only projections
were edited), so nothing was traded away to gain seconds. The bundle does
not reduce sharing; it packages it, exactly as the KFacts bundle did. The
measured price is the probe's answer: packaging these three headers is
worth under 0.5 s here.

The two `KFacts`-clashing field names (`innerK`, `pairK`) are hidden from
the global open of `AgreeCore` and projected qualified where the rows use
them, so the two records coexist without ambiguity.

## 6. THE CONVERGENCE ANSWER

The obligation is not renamed; the wall is priced at this family. The
band-bundle hypothesis predicted the band's elaboration mass sits in the
restated telescopes, and this family's telescopes are the three restatements
the diagnosis named. The probe measured that packaging those three
restatements is worth about 0.06 to 0.34 s at the gate caliber, under the
pre-fixed 0.5 s GO line. The band-wide target of 2.33 s is not reachable
from this family, and the roll-out of the remaining families was not funded
by this probe (the fixed criterion stops the dispatch after one family).
`levelIn` and `cover` are not discharged; the probe did not attempt them.

## 7. NEGATIVES AND THEIR STATUS

1. The one family saves 0.5 s or more: **MEASURED FALSE** at this site (the
   gate-caliber pairs: before mean 99.14 s, after mean 99.08 s, three paired
   runs; six after runs mean 98.80 s; the delta is 0.06 to 0.34 s, under the
   line, inside a spread of 1.5 to 1.7 s).
2. The record bundle hangs or walls at the subK-class fields (P-o):
   **MEASURED FALSE** (record-only edit exit 0 in 101.44 s at load 9.2;
   full family edit green in every after run; no timeout, no heap wall).
3. The band's elaboration mass sits in this family's three header
   restatements: **MEASURED FALSE as the probe's lever** (the price of the
   two removed restatements is under 0.5 s). What the mass is instead is
   NOT measured by this dispatch and sets no verdict here.
4. The nested Sigma is the needed spelling: **INFERRED FALSE as needed**
   (the record did not hang, so the fallback was never triggered; the claim
   that the Sigma would differ at this site was not measured).
5. The bundle's seconds value at the future instantiation site: **INFERRED**
   (no consumer exists; cannot be timed).
6. The gate's pgrep guard can verify the process list: **MEASURED FALSE**
   (pgrep exits 3, no sysmond; C-12's intent held procedurally, one Agda
   process at a time).
7. The after runs were measured at loads comparable to the before runs:
   **MEASURED FALSE** (after load 4.2 to 6.6 vs before 2.6 to 4.0; three
   further after runs at 3.3 to 6.5 were added, and the verdict does not
   change).

## 8. ARCHIVE USED

- `_build/diag-dd24-residual.md`, read WHOLE. TOOK the residual arithmetic
  (section 1), the band profile, the KFacts-shape code claims, the P-o risk
  and the one-family dispatch (section 4).
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the KFacts bundle spelling
  and its profile arithmetic (`:85-112`).
- `_build/lj-1.63-report.md`, section 5. TOOK the three measured regressions
  to not repeat, and the pre-dispatch profile totals (Total 99,055 ms,
  Miscellaneous 42,379 ms, `:109-119`) used as the after-profile baseline.
- `_build/lj-1.64-report.md`, sections 2-3. TOOK the band boundary and the
  band profile (44.31 s over 2,196 lines).
- `_build/lj-1.58-report.md`, section 2. TOOK the Lift12Back kit.
- `dev/LESSONS.md`: P-o (`:2509`), P-t (`:2601`), P-m (`:2460`), P-n
  (`:2483`), P-q (`:2633`), D-30 (`:3255`), read WHOLE. Also P-h, P-i,
  P-k, P-l, P-u, P-v, P-c, R-35, R-36, R-38, R-40, I-5, C-31 through C-37,
  D-8, D-10, D-13, D-26, D-29 via `python3 scripts/rules.py --for build`
  and `--for probe`.
- `archive/rud-route/`, SHAPE only (per the brief).

## 9. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean; `L.Condensation` counts 6,344 in-fence
lines in the working tree (pre-dispatch 6,390; HEAD 5,562).
`L.BoundedSubset` re-checks green (exit 0, warm, 113.23 s).
No `make check` was run, per the brief. No `check-ratio --check` was run,
per the brief. No commit, no push. The working tree carries the probe edit
(the converted family) and this report; a session backup of the edited
master is at `/tmp/lj165-condensation-after.backup`. The pre-dispatch tree
(the as-placed 6,390-line master) is recoverable from the orchestrator's
external backup patch named in the brief, plus HEAD; this dispatch made no
separate backup of the pre-dispatch master.

Untouched: `src/L/Coding/` (nothing under it), `src/Everything.lagda.md`,
all other masters, and every probe. The historical probe
`src/ProbeLJ155B.agda` instantiates the master's `AndAgree`/`OrAgree` with
the old eleven-argument shape and would need the bundle shape if re-run; it
is untracked scratch, outside this dispatch's write scope, and was not
edited.
