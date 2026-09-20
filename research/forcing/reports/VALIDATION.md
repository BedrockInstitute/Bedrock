# Verification record, 2026-09-20

## Completed

* `python3 research/forcing/archive.py verify`: exit 0, 12,461 manifest entries
  and 1,090 distinct SHA-256 objects verified.
* Restore round trip for origin `soft-pause-tar`: exit 0, all 1,539 restored
  files match their recorded hashes.
* `python3 research/forcing/archive.py prepare`: exit 0, 124 historical
  production dependency files verified/restored.
* `GHCRTS='-A64m -I0 -M8g' agda K11/CountableCohen.agda`: exit 0.
* `GHCRTS='-A64m -I0 -M8g' agda K11/Corollary.agda`: exit 0, including the
  changed `CohenGeneric` compatibility wrapper.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanPowerTop.agda`: exit 0 after
  narrowing module aliases to the actual suppliers. The first broader-alias
  attempt was stopped after more than eight minutes near the heap limit;
  no mathematical assumption, theorem statement or memory limit changed.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanInjKPairFwd.agda`: exit 0
  after correcting the inherited transport direction described below.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanCHBot.agda`: exit 0,
  including the new `omega-part-top` supplier. The accepted check uses narrow
  aliases and an explicit `Σ≡Prop` path between the two presentations of the
  checked omega name. No proof-bearing name components need to be unfolded
  to establish that path. Both `omega-top` and `power-top` are now proved.
* `GHCRTS='-A64m -I0 -M8g' agda src/Milestones.lagda.md`: exit 0.
* `make lint`: exit 0 after generating the historical dependency source in an
  ignored directory, separately from the current textbook.
* `make test`: exit 0.
* Complete `make check` using the installed Agda frontend: exit 0, including
  the full Milestones closure, all lint/framework gates and 175 passing tests:

```
make check -o typecheck-stage -o /opt/homebrew/bin/agda \
  BEDROCK_AGDA=/opt/homebrew/bin/agda AGDA=/opt/homebrew/bin/agda \
  TYPECHECK_ROOT=. AGDA_DIR=/Users/alsg/.agda
```

The two `-o` options avoid rebuilding the installed compiler and copying `src`
to the private staging directory. The actual typecheck runs against current
`src/Milestones.lagda.md`; none of the proof, lint or test gates is omitted.

## Environment and interrupted checks

Plain `make check` returned exit 2 while building the custom frontend:
`FileNotFoundError: [Errno 2] No such file or directory: 'cabal'`. This is an
environment failure before typechecking. The installed-Agda run above provides
the proof and gate validation, not validation of the custom frontend build.

The first serial endpoint run was cold. Completed module logs are preserved
under `cold-endpoints/`. It was intentionally stopped during
`CohenBooleanLeastEmpty` (exit 143), then restarted after reusing 211 missing
interfaces from the original checkpoint. The restarted run is an incremental
check, not a complete cold benchmark. Agda rechecks changed sources/dependencies.

An overlapping named omega check was also intentionally terminated to avoid
duplicating expensive dependency checks. Its partial log is `omega-part.log`;
it is not successful evidence. Final acceptance depends on the resumed gate.

The GLM drafting request returned HTTP 429/code 1309 (expired subscription),
producing no draft. There was no approval rejection or retry loop.
The coordinator authored the changes; GPT 5.6 Sol supplied read-only source
review of endpoint assumptions, dependent types and proof orientations.

## Discovered historical source error

The resumed endpoint run returned exit 42 at
`K10/CohenBooleanInjKPairFwd.agda:308.26-45`:

```
error: [UnequalTerms]
4 != 2 of type ℕ
when checking that the expression sgl-unique s x σ hs has type
```

The open goal is
`val kpairSglφ (env4 σ p x y) ≤ᴮ eq (fst σ) (check s)`.
`sgl-match` identifies that four-slot formula value with the two-slot singleton
formula value. The inherited substitution used the path forward while supplying
a proof at its destination; it needs `sym (sgl-match σ p x y)`.
The original diagnostic is retained in `kpair-original-error.log`.

## Final endpoint regression

`sh verify-k10-k11.sh`: exit 0. All 69 positive endpoint modules passed.
`MissingFunction`, `MissingValueFunction`, `MissingCheckReading`, and
`MissingOnto` each returned the expected exit 42 and the required
`[UnequalTerms]` diagnostic. Final logs are in `endpoint-regression/`.
`checks.json` records the checked source hashes and exit codes.

Two intermediate launches returned exit 1 because all Agda slots were occupied.
The runner now waits in two-second intervals for a slot before each check.
Earlier overlapping CHBot attempts were intentionally stopped; the accepted
named log is `chbot-transport.log`, and the final regression checks it again.

`make lint` after the final prose changes: exit 0. No pending compiler process
belongs to this research verification. The remaining work is mathematical,
as listed in `../STATUS.md`, not a claim of completed K10/K11 acceptance.

The final pre-commit run of the installed-Agda `make check` command above also
returned exit 0; its complete log is `final-main-check.log`.

## Internal check recursion continuation

The new `CheckRecursion.agda` and `InternalCheck.agda` modules, and the changed
`K9/BooleanSupport.agda`, each pass named Agda checks with exit 0 under the same
8 GB runtime limit. The runner waits when two machine-wide Agda processes are
already active. The first attempted launch returned 75 at this guard and did
not start a third process.

Two development diagnostics were corrected before acceptance: an extra closing
parenthesis in `good-reading`, and importing `isPropIsContr` from `HLevels`
instead of `Cubical.Foundations.Prelude`. Neither was an unclosed mathematical
goal. The accepted sources contain no holes or unsafe constructs.

The Boolean check supplier is now connected to the existing `Checked` API.
The new proof and its actual stage-table discharge are described in
`CHECK-RECURSION.md`. Independent read-only Sol verification found no circular
use of MemberImage or hidden choice and confirmed the remaining poset-side
routing dependency. The expanded endpoint regression includes the two new
modules and `K9.BooleanSupport` in addition to its original 69 endpoints.

`make lint`: exit 0 after the new proof report and status update.
`sh -n active/verify-k10-k11.sh` and `git diff --check -- research/forcing`:
exit 0. No production `src/` file is changed by this continuation.

The first expanded regression passed its first 25 positive endpoints, then
`K10/CohenBooleanOmegaTop.agda` exhausted the fixed 8 GB heap (exit 251).
The diagnostic is preserved in `internal-check-omega-top-heap.log`. Its five
broad module aliases were narrowed to the definitions/submodules actually
used. This changes no theorem statement, proof step, axiom, or memory limit.
The complete runner was then restarted against the narrowed source.

The narrowed `CohenBooleanOmegaTop` then returned exit 0 under the same 8 GB
limit, and the runner continued. No proof-body rewrite or opacity change was
needed for this repair.


The completed expanded runner returned exit 0: all 72 positive modules passed,
and all four negative controls returned the required exit 42 with their
expected type mismatch. The final logs are in `internal-check-regression/`;
`checks.json` records all 76 source hashes, log paths, and exit codes. The
previous 69-module logs remain in `endpoint-regression/` as historical evidence.
This is an incremental source/dependency recheck, not a full cold benchmark.

Final `make lint`: exit 0, with the complete output in
`internal-check-lint.log`. A separate audit verified all 76 recorded source
hashes and log exits against the final files. Both new proof modules retain
`--safe` and contain no MemberImage parameter, postulate, unsafe termination
pragma, trust primitive, or hole.

## Full-weight check and K11 narrowing continuation

* `sh active/verify-k10-k11.sh`: exit 0, 76 positive modules each exit 0;
  four expected-failure controls each exit 42 with the required UnequalTerms
  diagnostic and fixture-specific pattern. Agda ran serially with the existing
  `GHCRTS="-A64m -I0 -M8g"` limit and machine-wide process guard.
* Fresh logs: `weighted-check-regression/`; `checks.json` records all 80 source
  hashes, exit statuses and log paths. This is incremental validation; changed
  dependencies were rechecked, not a cold benchmark.
* `make lint PY=/opt/homebrew/bin/python3.11`: exit 0. The first plain invocation
  failed because the relocated historical worktree has no `.venv/bin/python`;
  explicitly selecting installed Python 3.11 ran all lint targets successfully.
* Named checks of `WeightedCheckRecursion`, `InternalWeightedCheck`, and
  `K9.NameGround` passed before the full regression. The first development check
  of WeightedCheckRecursion reported an out-of-scope composition operator;
  spelling the application explicitly fixed it without changing the proof.
* Scoped read-only mathematical review verified the weighted formulas, stage
  functionality and Cartesian product, table compatibility, recursive graph,
  unique-existence extraction and diagonal generic-name graph. The final full
  regression includes the subsequent spread construction and actual consumer.
* No production `src/` file changed. The earlier production-tree validation
  above remains historical evidence, not a fresh production check on this branch.

`K9.NameGround` now consumes the new internal poset check, spreading and generic
name. `K11.CohenGeneric` and `K11.Corollary` omit Accessibility and MemberImage.
Remaining arbitrary-image consumers and all open endpoint hypotheses are
listed in `STATUS.md` and `WEIGHTED-CHECK.md`; none is claimed discharged by
this regression.

## Internal Cohen real names and countable extension

* `sh active/verify-k10-k11.sh`: exit 0, 80 positive modules each exit 0;
  four expected-failure controls each exit 42 with the required diagnostic.
* Logs: `internal-reals-regression/`. `checks.json` records the 84 source
  hashes, exits and log paths. This is an incremental regression, not a cold
  benchmark. The guard retained the maximum of two machine-wide Agda processes;
  every check used `GHCRTS="-A64m -I0 -M8g"`.
* `InternalCohenReals`, migrated `K9.RealNames`, and finite `K9.PairNames`
  passed named development checks and the full regression. The initial real-name
  draft exposed distinct seed-dependent ordered-pair implementations; using the
  recursive table's own pair witness fixed the interface without weakening it.
* `K11.CountableExtension` initially exited 251 (8 GB heap exhausted). The
  diagnostic is in `countable-extension-initial-heap.log`. Narrow module
  exports preserved its actual generic supplier and forwarded theorem while
  avoiding irrelevant module expansion. The retry passed at the same limit:
  `countable-extension-narrow.log`. The final regression independently returned
  exit 0 for the adapter.
* `make lint PY=/opt/homebrew/bin/python3.11`: exit 0, log
  `internal-reals-lint.log`. New modules retain --safe and no holes, postulates,
  unsafe termination pragma or trust primitive.
* A scoped read-only review checked the raw real-name formula, table and
  coordinate pair distinction, bound, realGraph uniqueness, and finite pair
  construction against their actual definitions. No mathematical defect found.

No production source changed. The latest K11 specialization supplies its generic
from the enumeration; it still forwards all K10 extension-axiom and
cardinal-preservation inputs. Ordinary-model completion remains open as recorded
in `INTERNAL-COHEN-REALS.md` and `STATUS.md`.
