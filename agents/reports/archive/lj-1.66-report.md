# LJ-1.66: price one module application, then hoist eighteen to three

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.66-report.md`.

## 0. THE VERDICT

**The unit cost of one `EnvSet` application is 1.016 s, MEASURED.** That
prices the family at 18.29 s, far above the 2.33 s residual. The hoist
was therefore attempted, per the pre-fixed D-1 criterion, and it
**REGRESSED by +10.88 s, MEASURED**. The hoist was reverted; the working
tree is byte-identical to the dispatch start. The last named lever is
measured: the applications are individually expensive, and hoisting them
to three module-level frames does not recover the cost at this site.

Module-application hoisting is now **MEASURED FALSE at two sites**: the
chain wrappers with abstract arguments (+17.23 s, `_build/lj-1.63-report.md`
section 5) and the `EnvSet` frames with concrete slot numerals (+10.88 s,
this dispatch).

## 1. THE PROBE

The instrument, per the brief: add N = 6 extra `EnvSet` applications in a
harmless place at the same depths as the real ones, changing nothing else,
measure `L.Condensation` cold, three runs, gate caliber, before and after,
and divide the delta by N.

The six extra applications were added to three existing proof bodies, two
per depth, each a verbatim copy of the real application beside it:
`TopAgree.out` (depth `{5 + m}`), `NegAgree.out` (depth `{6 + m}`) and
`AllInAgree.out` (depth `{7 + m}`). The bindings were unused let-bound
module applications; no statement and no proof body changed. The edited
tree measured 6,420 in-fence lines (6,390 + 30).

## 2. THE MEASUREMENTS

Caliber: the gate's own, cold module, warm dependencies,
GHCRTS="-A64m -I0 -M16g" (dev/ledger.toml `[ratio] ac_baseline_ghcrts`),
one process, strictly sequential runs. Wall seconds come from
scripts/check-timing.py `time_module`, the gate's own timer. Load comes
from `uptime` before each run. The machine carried 4 users through the
session; every absolute figure carries the caveat.

| state | run 1 s | run 2 s | run 3 s | mean | spread | load |
|---|---:|---:|---:|---:|---:|---:|
| before (as-placed working tree) | 100.386 | 100.302 | 99.611 | 100.100 | 0.775 | 3.1 to 5.7 |
| after (+6 EnvSet applications) | 106.662 | 105.714 | 106.211 | 106.196 | 0.948 | 2.8 to 6.5 |
| hoist (3 module-level frames) | 111.086 | 110.763 | 111.093 | 110.981 | 0.330 | 3.6 to 4.7 |

Probe delta: 6.096 s for N = 6. **Unit cost: 1.016 s per application.**
The two sides' loads overlap and the direction is the same on every run.
The deciding claim is MEASURED.

**The family price:** 18 applications x 1.016 s = 18.29 s against the
2.33 s residual. The abort criterion's 0.05 s line is crossed by a factor
of about 20.

## 3. THE ABORT DECISION

Unit cost 1.016 s is at or above 0.05 s. GO for the hoist, per the brief.

## 4. THE HOIST, AND ITS MEASURED REGRESSION

The hoist was built as three module-level frames, one per depth, placed
right after `EnvSet` in `src/L/Condensation.lagda.md`. Each frame fixes
the depth and the four slot numerals (`zero`, the arity slot, the `B`
slot and the `K` slot) and takes the environment and the three site facts
as parameters:

```agda
module EnvSet5 {m : ℕ} (B K : Fin m) (γ : S ^ (5 + m))
  (entryK : ...) (arSubK : ...) (envInK : ...) where
  open module Env = EnvSet {5 + m} zero (suc (suc (suc zero)))
                     (suc (suc (suc (suc (suc B)))))
                     (suc (suc (suc (suc (suc K)))))
                     γ entryK arSubK envInK public
```

and analogously `EnvSet6` and `EnvSet7`. All eighteen sites then applied
the frame: `module E' = EnvSet5 B K (stack) entryK (arSubK ...) (envInK
...)`. The rows' statements and proofs were unchanged; the only proof-body
edit was the module-binding spelling. This is the only hoist shape that
keeps the statements unchanged, because the eighteen applications are NOT
textually identical within a depth: the slot numerals are identical, but
the environment stacks and the site-fact partial applications differ per
row (for example `E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ` at the six `{6 + m}`
sites of NegAgree, ForallAgree and ExistAgree against
`E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ` at the four sites of MemAgree and EqAgree),
and the stack variables are lambda-bound inside `out`/`back`, so they
cannot move to module level without a statement change.

**MEASURED REGRESSION:** the hoisted tree checked green, and the three
cold runs read 111.086 / 110.763 / 111.093 s, mean 110.981 s, against the
baseline mean 100.100 s. Delta: **+10.88 s**, with a 0.33 s spread after
against 0.78 s before, at overlapping loads. The regression is not noise.

The mechanism, read from the numbers: each site still instantiates a
parameterized module, and the frame's body still contains the `EnvSet`
application at the site's concrete arguments, so the `EnvSet` body is
still elaborated once per site; the frame adds its own layer on top. This
is the same failure shape as `[LJ-1.63]` attempt 3, now measured at a
second site with concrete slot numerals.

Per the pre-fixed criterion ("Any measured regression: revert it and
stop"), the hoist was reverted and the dispatch stops here. `AtomLeaf`,
`BndLeaf`, `PropAgree`, `ImpLeaf`, `ExistAgree`, the chain, `levelIn` and
`cover` were not attempted.

## 5. THE DD4 ANSWER

The attempted hoist kept the rows' statements and proofs unchanged, and
it is more sharing on the page: three spellings of the application
instead of eighteen. But it is NOT more sharing in the elaborator's
sense. The eighteen applications carry eighteen different argument lists
(environment and site facts), so they cannot collapse to three concrete
instances; the only statement-preserving collapse is the frame, and the
frame re-elaborates per site. The DD4 convergence is therefore right and
the price is wrong, exactly the `[LJ-1.63]` attempt-4 shape at a new
site: +10.88 s measured, reverted. A hoist that genuinely reduced the
application count to three would need the rows' stack variables at module
level, which is a statement change; per the brief, that stops the report
instead of being attempted.

## 6. THE CONVERGENCE ANSWER

The obligation is not renamed and the last named lever is now priced.
Each `EnvSet` application costs 1.016 s (MEASURED), so the eighteen are
worth about 18.3 s if they could be paid once each. The hoist that would
pay them once, three module-level frames, measured +10.88 s (MEASURED
FALSE) and was reverted. The residual of 2.33 s is not reachable through
this lever, and the ~38.5 s of band elaboration remains elsewhere: the
applications are individually expensive but not hoistable at this site
without a statement change. `levelIn` and `cover` remain not discharged.

## 7. NEGATIVES AND THEIR STATUS

1. The unit cost of one `EnvSet` application is under 0.05 s:
   **MEASURED FALSE** (1.016 s; delta 6.096 s over six applications,
   three cold runs each side, same session, gate caliber).
2. Hoisting the eighteen applications to three module-level frames helps:
   **MEASURED FALSE** (+10.88 s; three cold runs each side, mean 110.981 s
   against 100.100 s, spread 0.33 s after, loads overlapping; reverted).
3. The eighteen applications are identical within each depth, so a
   concrete three-instance hoist is possible: **MEASURED FALSE as a
   structural claim** (the slot numerals are identical, the environments
   and site facts are not; verified by reading all eighteen sites).
4. The working tree is back to the dispatch start:
   **MEASURED** (6,390 in-fence lines; `git diff --stat` 956 insertions
   and 79 deletions, identical to dispatch start; all eighteen sites back
   to the original spelling; no frame or probe remnants; fences and both
   linters clean; consumer re-checks green).
5. A statement-level restructuring (moving the rows' stack variables into
   module telescopes) would recover the 18.3 s: **INFERRED, NOT MEASURED**.
   It was not attempted, because the brief stops the dispatch on a
   statement change. An inference sets no verdict.

## 8. ARCHIVE USED

- `_build/lj-1.65-report.md`, read WHOLE. TOOK the gate-caliber protocol
  (three cold runs per side, load caveat beside every figure), the
  negative-status classification and the abort discipline.
- `_build/diag-dd24-residual.md`, read WHOLE. TOOK section 1's count of
  the 33 inner module applications (the reason this dispatch exists), the
  residual arithmetic (2.33 s) and the band attribution (44.31 s over
  2,196 lines, ~38.5 s un-attributed).
- `_build/lj-1.63-report.md`, section 5. TOOK attempt 3's measured
  +17.23 s (the chain hoist with abstract arguments) and the
  revert-on-regression discipline; its attempt 4 (+3.29 s) set the
  convergence-right/price-wrong shape this dispatch repeats.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the KFacts bundle
  mechanism (parameter telescopes re-elaborated at every instantiation
  site) and the profile attribution (instantiation is the expensive
  content class).
- `dev/LESSONS.md`: P-l (`:2305`), P-m (`:2460`), P-o (`:2509`), P-t
  (`:2601`), P-q (`:2633`), D-30 (`:3255`), read WHOLE each. TOOK P-l
  (re-measure at this site; a measured cure does not transfer), P-m
  (instantiation content is the expensive class), P-t (built formula
  trees unfold), P-q (a line lever is not a seconds lever) and D-30 (the
  consumer audit never decides a cost).
- `archive/rud-route/`, SHAPE only (README and file list), per the brief.
- `src/L/Condensation.lagda.md`: `EnvSet` (`:2761-2860`), all eighteen
  application sites (`:3488`, `:3507`, `:3563`, `:3590`, `:3670`,
  `:3703`, `:3843`, `:3872`, `:4171`, `:4193`, `:4734`, `:4765`,
  `:4854`, `:4885`, `:4956`, `:4983`, `:5052`, `:5074`), the nine row
  modules that contain them, and the three site-fact shapes per depth.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean; `L.Condensation` counts 6,390 in-fence
lines in the working tree, the dispatch-start figure.
`L.BoundedSubset` re-checks green (exit 0, cold, 15.55 s wall at load
7.9 / 4.5 / 4.2).
No `make check` was run, per the brief. No `check-ratio --check` was run,
per the brief. No commit, no push. The working tree carries the
dispatch-start placement in `src/L/Condensation.lagda.md` and this
report; no probe file was left behind. Untouched: `src/L/Coding/`,
`src/Everything.lagda.md`, all other masters, all probes. The final
`L.Condensation` source is byte-identical to the dispatch start (verified
by line count, diff stat and spot checks at all eighteen sites).
