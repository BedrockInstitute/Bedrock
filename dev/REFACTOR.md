# Proof refactoring: first 3,000 lines

The current goal is to simplify the completed development while preserving the
statements and assumptions of `L⊨ZFC` and `L⊨GCH`. Both are registered in
`src/Landmarks.lagda.md`. This work does not reopen either theorem.

## Baseline and acceptance

Baseline: 2026-09-06, revision `6da70f2e43fcfb7617bdf00d6bc5b758850846f7`.
The working tree was clean before this refactoring began.

| Measurement | Baseline | First milestone |
|---|---:|---:|
| Nonblank lines inside Agda fences | 28,973 | At most 25,973 |
| All lines inside Agda fences | 33,169 | Report alongside the primary count |
| Physical lines, including prose | 54,863 | Report, not an optimization target |
| Literate Agda modules | 112 | Preserve the reading catalog |

Run `python3 scripts/gate/count-agda.py`; `--json` adds the per-module counts.
All first-party proof code stays under `src/`. Removing blank lines or prose,
packing expressions onto fewer lines, or moving code outside the count earns
no progress. A new shared helper counts against the savings of its consumers.
Keep the internal meanings of cardinals, power sets, and coded injections.

For each batch, check the changed Agda modules and their theorem consumers with
`GHCRTS="-A64m -I0 -M8g" agda <file>`. Count running Agda processes first; use
one at a time for comparable timings. Record exit codes and warnings. Run the
linters and their tests. The final project-wide gate is `make check`; its
`Everything` typecheck needs a brief explicitly authorizing that entry point.

Compare fresh project interfaces with the same already-built cubical dependency,
on the same machine and entry point. A cache-only check is a separate metric.
Use temporary copies for fresh-interface comparisons, preserving workspace
caches. Do not infer build improvement from line counts alone.

## Work order

1. Audit current-status prose in all tracked documentation and Agda masters.
   Resolve old proof debts against definitions and consumers. Label dated external
   literature surveys as historical; retain their evidence about other projects.
2. Simplify repeated semantic adapters in `L.Choice.Before` and related chapters.
   Preserve the opaque formula boundaries and typed truncation payloads: both
   have measured importance to elaboration. Check each simplification before
   extending it to another module.
3. Consolidate repeated formula readers and constructor cases in `L.Coding.Model`,
   `L.Coding.Clauses`, and `L.Coding.Pinned`. The first two account for 3,250
   nonblank code lines. Share actual arguments and proofs, not merely layouts.
4. Refactor repeated graph construction, pair bounds, and counting arguments in
   `L.GCH.Hull`, `HullIn`, `HullCount`, `Pairing`, and `Sequences`. Those five
   modules account for 4,600 nonblank code lines. Check import dependencies
   before extracting helpers; preserve internal graph membership in L.
5. Review remaining one-consumer wrappers and repeated recursion scaffolding,
   then rerun the theorem checks and timing comparison. Continue batches until
   the net reduction reaches 3,000; the figures above are search priorities,
   not promises that any individual proof can lose a fixed fraction.

## Measurements and accepted batches

- Initial cached `src/Landmarks.lagda.md` check: exit 0, 3.78 s wall time.
  Existing warnings: a nonexistent `SatGraph` re-export in `L.GCH.SatFrame`,
  three nonexistent exports and a useless opaque block in `L.GCH.Hull`.
- Fresh project-interface baseline, `src/Landmarks.lagda.md`: exit 0,
  246.90 s wall, 245.73 s user, 1.02 s system. Project interfaces started empty;
  the installed cubical dependency retained its existing interfaces.
- First batch: 28,921 nonblank code lines, a net reduction of 52; 2,948 remain
  to the milestone. `L.Choice.Before`: 901 to 870, replacing three pairs of
  identity adapters with direct arguments. `L.GCH.Hull`: 1,140 to 1,119,
  removing an unconsumed stage-specific least-search chain; the actual closure
  proof continues to use `TermAlgebra.closed`. Removed invalid re-exports in
  `L.GCH.Hull` and `L.GCH.SatFrame`.
- Workspace theorem check after the code changes: `src/Landmarks.lagda.md`,
  exit 0, no warnings, 86.13 s with mixed cached/rebuilt project interfaces.
  This is an integration check, not a comparison to the cold baseline.
- `make lint test`: exit 0, all lint gates and 34 unittest tests passed, along
  with the existing lint-agda standalone checks.
- Same-condition fresh-interface check after the batch: `src/Landmarks.lagda.md`,
  exit 0, no warnings, 244.43 s wall, 243.40 s user, 0.97 s system. The source
  copy includes the final documentation changes. The observed wall-time change
  is -2.47 s (about -1.0%); one pair of runs does not establish a stable speedup.
  Both runs used Agda 2.8.0, the same cubical interfaces, one Agda process,
  and `GHCRTS="-A64m -I0 -M8g"`.
- Local logs and per-module counts are retained under `_build/refactor/2026-09-06/`.
  The fresh source/interface copies are `/private/tmp/bedrock-refactor-baseline`
  and `/private/tmp/bedrock-refactor-after`. These are local measurement artifacts;
  the baseline revision and reproducible commands above are the durable record.

## Documentation audit

Reviewed GCH-status matches in 159 tracked first-party text/documentation files,
including the Agda masters, multilingual docs, governance, configuration, and
literature notes. Generated `_build` output and vendored upstream files are
not source documentation and were not rewritten.

The current README translations and theorem statements already agreed. Corrected
settled source requests in `dev/literature/digest.md`, the old condensation
obligation in `devlin-II5.md`, and intermediate-code prose in `L.Coding.InL`,
`L.Choice.Table`, and `L.GCH.Condense`. Six research notes now explicitly identify
their assessments as historical and link the completed Bedrock landmarks.
Statements about the scope of other researchers' dated developments retain their
original evidence. The final status references agree with the two completed landmarks.

`AGENTS.md` now states the quantitative refactoring goal. `STYLE-agda.md` no longer
claims that a retired bridge is a live proof obligation, and its comments rule
agrees with `AGENTS.md`: explanatory comments belong outside Agda fences.


## Delegated execution

The owner authorized subagents on 2026-09-06. The coordinator owns scheduling,
file boundaries, integration checks, and milestone accounting; implementation
is delegated in disjoint batches.

| Workstream | Owned masters under `src/L/` | First batch |
|---|---|---|
| Coding | `Coding/Clauses`, `Coding/Pinned` | Share equality transport and semantic extension readers |
| Choice | `Choice/Before`, `Choice/Internal`, `Choice/Adequate` | Reuse transport lemmas and dependent truncated-existence elimination |
| GCH | `GCH/HullIn`, `GCH/HullCount`, `GCH/Pairing`, `GCH/Sequences` | Share bounded relation construction and its pair readers |

All batches start from the accepted 28,921-line tree. Each agent tests an isolated
copy of `/private/tmp/bedrock-dispatch-baseline`, overlaying only its own masters,
so a concurrently edited dependency cannot invalidate another agent's experiment.
The coordinator grants one exclusive Agda slot at a time. After the three batches,
integrate their checked sources, inspect theorem signatures and imports, and run
the project-wide gate, including `src/Everything.lagda.md`, in an explicitly
assigned verification brief. Use fresh project interfaces for final timing.
Continue batches and reassign scopes until the 25,973-line milestone is met;
acceptance of one batch is not completion of that milestone.


### Delegated batch ledger

The entries below are locally checked against isolated dispatch copies; a final
integration check is still required before milestone acceptance.

| Batch | Nonblank reduction | Check | Result |
|---|---:|---|---|
| Choice 1–3: transport naturality, environment reuse, reader simplification | 152 | `src/L/Choice/Before.lagda.md`, `src/L/Choice/Adequate.lagda.md` | Exit 0, no warnings |
| Coding 1: shared extension reader, code-equality transfer | 28 | `src/L/Coding/Pinned.lagda.md` | Exit 0, no warnings; owned-file linters clean |
| GCH 1: six bounded-relation consumers | 156 | `src/L/GCH/HullCount.lagda.md`, rebuilding HullIn and Pairing | Exit 0; owned-file linters clean |
| Coding 2: remove unconsumed clause branch and private frames | 147 | `src/L/Coding/Pinned.lagda.md`, rebuilding Model and consumers | Exit 0, no warnings; owned-file linters clean |
| Choice 4: reader continuation removal and shared transport proofs | 67 | `src/L/Choice/Order.lagda.md`, rebuilding Faithful and Name | Exit 0, no warnings; owned-file linters clean |
| GCH 2: shared raw recursion graph and four consumers | 67 | `src/L/Recursion.lagda.md`, `src/L/GCH/OrderType.lagda.md`, `src/L/GCH/HullCount.lagda.md` | Exit 0, no warnings |
| Coding 3: shared sum readers and tree inverse | 53 | `src/L/Coding/Pinned.lagda.md` | Exit 0, no warnings; owned-file linters clean |
| Choice 5: shared unpacking, subtype transport, ordinal bounds | 53 | CardinalAbove, GCH/Condense, GCH/StageCount | Exit 0, no warnings; owned-file linters clean |
| GCH 3: direct table readers and omega recursion graph | 43 | GCH/OmegaRec, GCH/HullCount | Exit 0, no warnings; owned-file linters clean |
| Coding 4: definable-set membership reuse and redundant certificates | 56 | Coding/Powerset | Exit 0, no warnings; owned-file linters clean |
| Choice 6: retained union readers and internal extensionality | 24 | Choice/Before, GCH/Hull | Exit 0, no warnings; owned-file linters clean |
| GCH 4: internal extensionality and unused index removal | 14 | GCH/HullCount, rebuilding HullIn and Sequences | Exit 0, no warnings; owned-file linters clean |
| Choice 7: shared transport and relation-reader continuation removal | 17 | Choice/Internal, Choice/Before | Exit 0, no warnings; owned-file linters clean |
| GCH 5: inclusion graph and shared domain bounds | 77 | L/InjChain, GCH/HullCount | Exit 0, no warnings; owned-file linters clean |
| Coding 5: direct satisfaction bridge and obsolete adapter removal | 115 | Coding/Uniform, rebuilding Clauses and Pinned | Exit 0, no warnings; owned-file linters clean |
| Choice 8: rank membership and shared denotation fibers | 21 | L/Rank, Choice/Adequate | Exit 0, no warnings; owned-file linters clean |
| Joint boundedness checker: four concrete endpoints | 141 | Coding/Uniform, rebuilding Clauses and Environment | Exit 0, no warnings; owned-file linters clean |
| Choice 9: shared rank bounds and constructible membership | 63 | Rank, Axioms/Basic, Ordinal/Stages | Exit 0, no warnings; owned-file linters clean |
| GCH 6: shared composite relation construction | 49 | L/InjChain, GCH/HullCount | Exit 0, no warnings; owned-file linters clean |
| Choice 10: shared indexed-union membership | 49 | V/Model, L/Rank, L/Reflect | Exit 0, no warnings; owned-file linters clean |
| Coding 6: shared pair characterization and environment transport | 28 | Coding/Uniform | Exit 0, no warnings; owned-file linters clean |
| GCH 7: checked boundedness certificates behind existing seals | 33 | GCH/DefDescribe, GCH/HierDescribe | Exit 0, no warnings; owned-file linters clean |
| Coding 7: retained pair characterization and boundedness endpoint | 28 | Coding/Uniform | Exit 0, no warnings; owned-file linters clean |
| Choice 11: shared collapse membership recovery | 26 | V/Collapse | Exit 0, no warnings; owned-file linters clean |
| GCH 8: indexed-union reader and pullback relation reuse | 52 | GCH/Complete, GCH/SuccIntoPower | Exit 0, no warnings; owned-file linters clean |
| Choice 12: collapse fixes and family congruence | 16 | V/Collapse | Exit 0, no warnings; owned-file linters clean |
| GCH 9: shared inverse collapse graph | 35 | GCH/OrderType, GCH/Pairing, GCH/SuccIntoPower | Exit 0, no warnings; owned-file linters clean |
| Choice 13: retained product and sum equivalences | 22 | V/Smallness | Exit 0, no warnings; owned-file linters clean |
| Coding 8: shared pair-expression semantics and eight readers | 112 | Coding/Uniform | Exit 0, no warnings; owned-file linters clean |
| GCH 10: direct finite witness selection | 11 | GCH/StageCount | Exit 0, no warnings; owned-file linters clean |
| Coding 9: tree-self and shared component rank descent | 28 | Coding/Uniform | Exit 0, no warnings; owned-file linters clean |
| Sol separation: shared local carving for separation and replacement | 65 | L/Axioms/Separation | Exit 0, no warnings; file gates clean |
| Sol readability corrections: typed stages and named expressions/witnesses | -59 | Choice/Before, Coding/Uniform | Exit 0; Agda lint clean |
| Sol functional image: common constructible stage bound | 23 | Axioms/Separation, Axioms/Full | Exit 0, no warnings; file gates clean |
| Sol application: one adequacy proof for term-valued graphs | 7 | Coding/Model, Coding/Uniform | Exit 0; file gates clean |
| Sol replacement: derive directly from full separation | 33 | Axioms/Full | Exit 0, no warnings; file gates clean |
| Sol bounded replacement: direct bounded-separation corollary | 9 | Axioms/Separation | Exit 0, no warnings; file gates clean |
| Sol hull extensionality: reflect one symmetric-difference witness | 32 | GCH/Hull | Exit 0; file gates clean |
| Sol replacement cleanup: retire unused stage-image branch | 9 | Axioms/Separation, Axioms/Full | Exit 0; proof-description consistency restored |
| Sol replacement boundary: prevent downstream proof expansion | -1 | Axioms/Full, GCH/HullCount | Exit 0 under the same 8 GB limit; no warnings |
| Sol satisfaction graph boundary: use semantic readers downstream | -3 | Coding/Graph, Coding/Uniform, Landmarks | Exit 0; no warnings; profiled downstream savings |
| Sol finite iteration table: finite image with one global stage bound | 14 | GCH/OmegaRec, GCH/HullCount | Exit 0; no warnings; independent readability review passed |
| Sol hull set operations: reuse constructible union and singleton readers | 11 | GCH/HullCount, GCH/HullIn, GCH/OmegaRec | Named checks and Landmarks exit 0; file gates clean |
| Sol transversal: use the constant relation directly in Pick | 11 | Choice/Transversal | Named check and Landmarks exit 0; file gates clean |
| Sol pair expressions: literal leaves and term carriers remove named slots | 17 | Coding/Model, Coding/Clauses, GCH/OrderType | Named checks and Landmarks exit 0; file lint clean |
| Sol collapse descriptions: pass the fixed relation through the existing reader chain | 8 | GCH/OrderType, GCH/HullIn | Named checks and Landmarks exit 0; file gates clean |
| Sol sequence membership: transport the final proposition once | 3 | GCH/Sequences | Named check and Landmarks exit 0; file lint clean |
| Sol inclusion graph: reuse DefinableMap/Inj and migrate the certificate consumer | 10 | InjChain, GCH/Assembly, GCH/Definable | Full guarded make check exit 0; no warnings |

Together with the initial 52 lines, these locally checked batches account for
2,024 lines. Other live edits are experimental until their checks finish. Per-batch
source checkpoints are retained under `_build/refactor/2026-09-06/`.

### Integration and review history

After accepting 602 lines of local reductions, the coordinator prepared
`/private/tmp/bedrock-integration-1` from the dispatch snapshot and accepted
checkpoints. The Choice agent received an explicit read-only verification brief for
`src/Everything.lagda.md` in that snapshot. Its interface cache is mixed, so this
check is not a fresh-build timing comparison.

The Coding agent was assigned the coding semantic pipeline (Model, Sat, Clauses,
Pinned, EnvSet, Environment, Sound, Tower, Closed, Shape, Recover, CodeSet, Bridge,
InL, AllCodes, Sequence, and Powerset) to investigate shared structural
sum maps and relabelling proofs. The GCH agent was assigned Recursion and GCH's
OrderType, Definable, SatFrame, Least, HullIn, HullCount, Pairing, and Sequences
to extract a common recursion graph construction. These implementation scopes
were disjoint. Previously checked Choice masters were frozen during integration.

Integration of the accepted 602-line reduction passed:
`GHCRTS="-A64m -I0 -M8g" agda src/Everything.lagda.md` in the isolated snapshot
exited 0 with no warnings. The count is 28,371 nonblank code lines. Both landmark
statements retain their original single LEM assumption. Completion was observed
within 230 seconds, including polling, with mixed project interfaces; this is
not a comparable cold-build measurement. A concurrent repository-wide
`make lint test` also exited 0; its log is
`_build/refactor/2026-09-06/delegated-lint-test.log`.

Second integration passed: the isolated accepted source snapshot
`/private/tmp/bedrock-integration-2` has 28,061 nonblank code lines, a net reduction
of 912. `GHCRTS="-A64m -I0 -M8g" agda src/Everything.lagda.md` exited 0 with no
warnings, including the final theorem consumers. Project interfaces were mixed;
this verifies combined correctness, not a cold-build speed improvement.

Fresh-interface paired measurement at the 1,121-line checkpoint (27,852 remaining):
original baseline Landmarks exited 0 in 261.215863 s wall (260.116089 s user,
1.051829 s system); refactored Landmarks exited 0 in 251.713377 s wall
(250.652045 s user, 0.989125 s system), with no warnings. The observed reduction
is 9.502486 s, or 3.64%. Both source copies started without project interfaces
and reused the same installed cubical cache, with one Agda process. The baseline
ran first. This is one paired observation, not repeated statistical evidence.
Logs and JSON are retained in `_build/refactor/2026-09-06/timing-*-Landmarks.*`.

Half-milestone integration passed: 1,505 fewer nonblank code lines, 27,468
remaining. The prescribed `agda src/Everything.lagda.md` command with the heap
guard exited 0 without warnings in `/private/tmp/bedrock-integration-4`.
The final ZFC and GCH statements retain their original sole LEM hypothesis.
This mixed-interface run verifies integration; it is not a cold benchmark.
Repository-wide `make lint test` also exited 0; logs are retained as
`integration-4.log` and `delegated-lint-test-3.log` in the measurement directory.

The owner clarified the priorities: seek structural refactoring and
mathematically simpler proofs, preserving readability; do not chase textual
line reductions. Routine refactoring and verification now use GPT 5.6 Sol;
GPT 6 Astra is reserved for difficult proof design. Existing work is being
reviewed for readability before further expansion. Unchecked drafts remain
excluded from accepted counts.

The Sol readability review identified four regressions in proof presentation:
deeply nested elimination in Choice.Before, repeated large key expressions,
compressed pair-expression induction handlers, and repeated bound-value terms.
Corrections are authorized even if they increase the line count. These fixes
are kept separate from the accepted count until checked. The review confirmed
that the main abstractions share substantive proofs; it did not justify keeping
these presentation regressions.

The four readability corrections passed the named Before and Uniform checks.
They restore typed stages and name repeated expressions and witnesses, adding
59 nonblank code lines. The net accepted reduction is therefore 1,841, leaving
27,132 lines. This increase is intentional; readability takes precedence over
the numerical milestone.

### Avoid repeating low-yield searches

The bounded Sol reviews found no worthwhile generic telescope abstraction for
Choice's remaining staged readers: the intermediate decoded equalities change
later dependent types, and named stages preserve the proof's structure.
Likewise, replacing Choice.Finite's ordered scan by `DecΣ` would lose its
leastness certificate; recovering that certificate needs the existing ordered
fold. The inspected FOL renaming, constant relabelling, partial bounding, and
parameter-placement inductions perform different operations, so merely moving
their constructor cases into a generic fold does not establish a simplification.
Do not repeat these searches without a concrete new mathematical idea.

The represented-map draft remains unapplied and unverified. It mainly packages
choice and transport plumbing; its line count alone is not sufficient reason
to adopt it under the clarified readability and cost priorities.

The readability-adjusted workspace passed `GHCRTS="-A64m -I0 -M8g" make check`
with exit 0 and no Agda warnings: Everything, all lint gates, 34 Python tests,
and 7 lint-agda fixture checks passed. Two Chinese adequacy terms were corrected
to the glossary spelling before the successful run. `git diff --check` passed;
112 modules contain 27,132 nonblank code lines. The successful log is
`_build/refactor/2026-09-06/full-gate-readability.log`. The glossary-only source
checkpoint is stored separately as `sol-glossary-1`, preserving prior snapshots.

The owner chose to continue using Sol to seek high-yield structural refactoring
this round. The 3,000-line milestone remains open; the checked count is 1,841
lines below baseline, with readability prioritized over numerical progress.

Additional bounded Sol audits found no useful new route in the inspected syntax
embedding inductions: Name erases constants into variables, so a simple constant
relabelling inverse does not apply. The L Cantor–Bernstein adapter already uses
the ambient theorem. The collapse transitive-subset fixed-point theorem also
already exists and has consumers. Internal Choice could select stage injection
graphs, but constructing its tagged, disjoint candidate family would reproduce
or exceed the existing HullCount construction; truncation alone is not the
logical obstruction. Avoid repeating these proposals without new evidence.


The final Sol follow-up uses elementarity for hull extensionality, replacing
both coded difference-witness branches with one symmetric-difference formula.
The checked reduction is 32 lines, below the initial estimate of 55–70.
The functional-image review also removed the unused stage-image branch (9 lines)
and corrected the English and Chinese prose to describe replacement through
separation. These batches leave 27,019 nonblank code lines: 1,954 below baseline,
with 1,046 still required for the first milestone. The milestone remains open.

Further bounded Sol reviews found no dependency-valid large reduction in Basic's
pairing/union construction, the ambient model facts, omega recursion, or the
satisfaction/definability/hierarchy semantic ladder. Their essential obligations
would have to be reproved, and some proposed shortcuts would be circular.
All modules above 500 code lines have received a targeted structural review.
Repeated broad searches were stopped to respect the owner's token-cost concern;
future work should start from a concrete new proof idea. The remaining general
hull membership and closure lemmas still have consumers.

The 1,954-line snapshot has not yet passed the full integration gate.
`GHCRTS="-A64m -I0 -M8g" make check` exhausted its 8 GB heap while checking
`L.GCH.HullCount` (Agda exit 251, make exit 2). Independent `make lint`,
`make test`, and `git diff --check` passed. The failure log is retained as
`full-gate-sol-final.failed-heap.log` in the measurement directory.
An isolated control also exhausted the same heap after restoring the old Hull
proof; making `Frame.Mext` abstract did not resolve the failure. That speculative
opacity change was not integrated. The recent axiom proof changes are being
investigated before final acceptance or timing claims.


The heap regression was resolved in the isolated downstream check by declaring
`hasReplacementL` opaque. Its statement and proof body are unchanged; the
boundary prevents downstream clients from unfolding the separation-based
construction. `HullCount` then exited 0 without warnings under the same 8 GB
limit. Both file linters passed. The additional line is deducted from progress:
1,953 fewer lines, 27,020 remaining, 1,047 short of the milestone. The checked
artifact is `sol-replacement-opacity`; a fresh full gate follows this fix.


The corrected 1,953-line snapshot passed the full workspace gate:
`GHCRTS="-A64m -I0 -M8g" make check` exited 0, including Everything, all
lint/weave gates, 34 Python tests, and the lint-agda fixture suite. There were
no warnings or errors; `git diff --check` also passed. The successful log is
`full-gate-sol-final.log`. The replacement chapter now explains the opacity
boundary in both English and Chinese. Final count: 112 modules and 27,020
nonblank code lines. The 3,000-line milestone remains 1,047 lines away.


### Final measured checkpoint for this Sol round

The source-frozen 27,020-line checkpoint was measured against the original
baseline with empty project interface caches and the same installed Cubical
cache. The original ran first; each run used one guarded Agda process and
`src/Landmarks.lagda.md`.

| Snapshot | Wall seconds | User seconds | System seconds | Result |
|---|---:|---:|---:|---|
| Original baseline, 28,973 lines | 244.825816 | 243.850739 | 0.932861 | Exit 0; three existing warning sites |
| Accepted, 27,020 lines | 252.357291 | 251.468930 | 0.848037 | Exit 0; no warnings |

The accepted snapshot was 7.531475 seconds (3.08%) slower in this single paired
observation. This does not establish a stable regression, but it provides no
support for claiming a final build speedup. It supersedes the earlier
1,121-line checkpoint's timing as evidence about the current source.
Logs and machine-readable results are `timing-final-{original,accepted}.{log,json}`
in `_build/refactor/2026-09-06/`.

Current outcome: 1,953 lines removed, 1,047 still needed to reach 25,973.
The separate below-27,000 threshold is also not reached. Both final theorems
and their sole LEM hypothesis are preserved, and the full gate passes under
8 GB. The size milestone and build-speed objective remain open. Further work
should begin with measured compilation hotspots or a concrete new mathematical
simplification, rather than another broad search through already-reviewed
modules. No formatting-only reduction is credited.


### Profiling the verified 1,953-line checkpoint

A fresh project-interface run of guarded Agda with `--profile=modules` on
Landmarks exited 0 in 254.62 seconds. The top four modules account for 41.83%
of profiled time: Choice.Order 36.134 s, Coding.Uniform 30.348 s,
Coding.Graph 20.792 s, and Coding.Clauses 19.228 s. Raw evidence is retained in
`profile-1953-modules.log`, `profile-1953-modules.json`, and
`profile-1953-report.txt` in the measurement directory. Follow-up experiments
target the transparent constant-carrier satisfaction graph and the broad
Ordered module instantiation; neither is accepted until checked.

A bounded design review considered a description interface separating logical
variables from emitted pair/container witnesses. Its potential is substantive,
but the existing readers expose arbitrary formula operators and concrete
witness-bearing environments. Replacing those interfaces requires coordinated
consumer changes. The 523-line reader deletion budget must pay for normalized
specifications, compositional constructors, boundedness, and S/V conversion;
the basic pair helpers remain live. No reliable bounded net gain was established,
so a wholesale semantic-framework migration was not started.


The constant-carrier `satGraph` now has the same opacity boundary as `satGraphAt`;
its existing readers explicitly unfold it. Public types are preserved. Graph,
Uniform, and downstream Landmarks checks exited 0 without warnings, and file
linters passed. The three added code lines reduce the net count to 1,950
(27,023 remaining). This is an intentional build-cost improvement, not a
line-reduction claim. Graph's own module cost stayed roughly flat; Uniform's
attribution fell from 30.348 s to 3.801 s and SatFrame's from 8.813 s to 0.084 s.
The changed runs used warm dependencies, so these are directional module-level
observations, not a fresh paired total. Raw logs are
`profile-1953-graph-opacity-{graph,uniform,landmarks}.log`.


A controlled Order experiment rejected narrowing the public `Ordered` opening.
With identical warm dependencies, the narrowed version took 34.218 s for Order
and the original 34.294 s (both exit 0). The 0.22% difference is negligible;
narrowing exported scope does not avoid elaborating the underlying parameterized
construction. No Order change was applied.


### Verified graph-boundary checkpoint: 1,950 lines removed

The workspace passed guarded `make check` with exit 0 and no warnings, including
Everything, all lint/weave gates, 34 Python tests and the lint-agda fixture suite.
The successful log is `full-gate-graph-opacity.log`.
A new source-frozen copy with zero project interfaces checked Landmarks in
218.23 s wall, 217.26 s user and 0.88 s system, exit 0 without warnings, using
the same installed Cubical cache and 8 GB heap guard. This is 26.60 s (10.86%)
faster than the recent original baseline at 244.825816 s, and 34.13 s (13.52%)
faster than the 1,953-line pre-boundary snapshot. These are single-run observations;
the earlier negative speed result does not describe this new source.
Timing evidence: `timing-graph-opacity-Landmarks.{log,json}`.

Current verified source: 112 modules, 27,023 nonblank code lines; 1,950 removed
and 1,050 still needed to reach 25,973. A semantic-description pilot is isolated
from this checkpoint and excluded from all accepted counts. Its bounded scope
is table-value binding and the negation reader pair in Clauses/Pinned. The full
constructor, specification, and consumer costs must be measured before extending
it; an upfront reusable-helper cost is not itself evidence of eventual savings.


The isolated negation description pilot typechecked Clauses and Pinned under
the heap guard and passed both file linters. The complete cost is +89 nonblank
lines (Clauses +86, Pinned +3), so it is not integrated or credited. Its semantic
interface genuinely removes the hidden entry/container environments in both
negation consumers. The next bounded scratch step tests `pairAll` and binary
relations to determine whether reuse can recover this measured upfront cost.
The verified workspace remains 27,023 lines and passes the full gate.


The binary extension was costed before editing. After retaining its normalized
reader interfaces and bridge obligations, it could remove only about 33–38
lines, while pair binding and certified operators would add about 66–80.
The checked negation pilot is therefore frozen, still excluded from the
workspace; no binary implementation was added. Incremental acceptance would
increase code size. Further work on this route requires a justified whole-family
budget, not repeatedly treating reusable-helper costs as future savings.
The next bounded structural reviews instead examine whether finite-table and
value constructions can carry their own correctness proofs in one recursion,
removing separately repeated recursions and transports.


The recursion-fusion reviews found different proof obligations rather than
repeated traversals: OmegaRec's correctness proves Zero/Step/Down from an
existing membership characterization, and HullIn already returns graph proofs
with its values. No fusion was applied. An alternative OmegaRec implementation
now uses the standard finite image of its entry sequence. The first prototype's
dependent finite-index stage bound was rejected; the checked replacement takes
one bound for the whole natural-indexed entry sequence, names its components,
and uses generic finite-image readers. OmegaRec and HullCount exited 0 under
the heap guard, file linters passed, and an independent Sol readability review
accepted the simpler construction. Public finite-table specifications and the
sole LEM parameter are preserved. Net reduction: 14 lines; current total 27,009,
net reduction 1,964, remaining milestone gap 1,036. The immutable checkpoint is
`sol-omega-finite-image`. The earlier 218.23 s timing belongs to its 27,023-line
predecessor; no new timing is claimed for this source yet.


The 27,009-line workspace passed full guarded `make check` with exit0: Everything,
all lint/weave gates, 34 Python tests and lint-agda fixtures passed without
compiler warnings. Log: `full-gate-omega-finite-image.log`. The now locally
unused OmegaRec pair readers remain external dependencies of HullIn, HullCount
and BoundedSubset; their earlier local-use explanation was corrected, and no
invalid deletion was made.

### Active isolated transitive-frame migration

A source-based design correction enabled a larger mathematical simplification.
No existing W/E/C/T carrier is transitive, but the graph already permits
unbounded existential witnesses. It can bind one transitive K containing E,C,T,
then quantify decoded components directly over K instead of repeatedly decoding
Kuratowski containers. SatDescribe must expose K freely to retain Delta0.
HierDescribe's existential wrappers are bounded, so they must NOT gain an
unbounded K: their existing z can serve as K, because completeness already
chooses it as a transitive Lset stage. These distinctions were checked against
actual formulas, rather than inferred from names.

The implementation is isolated in `/private/tmp/bedrock-sol-transitive-frame`,
with its exact API/ownership plan in `CONTRACT.md`. One Sol owns Clauses/Pinned;
another owns Graph/Uniform/Powerset and the SatFrame/SatDescribe/DefDescribe/
HierDescribe consumers. The original 27,009-line source is checkpointed as
`transitive-frame-baseline1964`. The previous Description pilot is not reused.
All bounds, wrapper and consumer costs count against potential savings; the
estimated 150–300-line gain is unverified and not credited. The main workspace
remains the fully checked 27,009-line version until integration succeeds.


The isolated bound kernel checked Clauses and Pinned with exit0. It currently
adds81lines and is not integrated. In particular, the normalized successor-table
reader recovers both the successor index and value bounds from an existing table
entry using transitivity alone; no pair/successor closure assumption is needed.
To coordinate the larger implementation, the next core phase first stabilizes
K/Bounds parameters while temporarily retaining old inner reader bodies. This
is interface scaffolding, not accepted refactoring. Consumers can then check
bound existence and retained Delta0 classifications before the later phase
removes the old container-based internals. The full migration and net reduction
remain required; scaffolding alone is not a successful endpoint.


The isolated parameter/outer-witness phase passed all eight named consumer
checks and guarded Landmarks with exit0 and no warnings; both file linters
passed. The verified scratch snapshot is `checkpoint-phase-a-full/src`, at
27,167 lines, +158 over the accepted 27,009-line source. This added cost is NOT
integrated or credited. It verifies constructible bound existence and preserves
the actual Delta0 descriptions before simplification of the old internals.
The next implementation chunk replaces the 12-slot table frame with six slots
and migrates Rel/Clause/subvalue readers/Frame/RelRead plus Pinned. External
Frame totality/domain reader meanings stay fixed. Shape/Close still use the old
container helpers, so those helpers cannot yet be retired indiscriminately.


A checked phase-B substep now provides normalized K-bounded pair binders and
uses them for Clause.onC and its Frame readers, preserving their public meaning.
Clauses and Pinned exited0. The snapshot is `checkpoint-phase-b-onc/src` in the
shared scratch. The original core agent reached a context-capacity boundary,
so a fresh Sol instance took over the remaining totality/relation/frame/Pinned
migration from that verified source. No checked work was discarded or rerun as
an architectural search. All transitional code remains outside the accepted
workspace and its line count.


The six-slot Clauses migration now typechecks with exit0, including normalized
totality and domain readers. Pinned is still being migrated, so this is not an
integration checkpoint. A bounded read-only audit is checking whether the old
container helpers can also be retired from the remaining GCH descriptions;
all such consumer costs remain part of the whole-route acceptance calculation.


Pinned's six-slot migration also typechecks with exit0. Landmarks and the exact
whole-tree cost are being checked before proceeding. A read-only audit found
that retiring every old pair/container reader requires additional Tower and
tmIs migrations as well as DefDescribe/HierDescribe. The removable helper body
is only about 78 lines, against an estimated 57–100 lines of consumer cost.
Model's PairExpression still needs container itself. Therefore full helper
retirement is not a sufficient payoff argument; phase C is paused pending
the measured phase-B result.


A separate Sol audit rejected reusing OmegaRec.Iterate for Sequences' finite
fold. Of the inspected 430 lines, roughly 150 remain necessary for pairing,
injectivity and public wrappers. Encoding (s,i,u) makes the step uniform, but
Iterate also fixes its initial value: supporting a variable initial state needs
a parameterized Zero/Correct/itFo/Fn-correct development. State totalization,
that generalization and final projection were estimated at 235–365 lines
against only 280 replaceable lines. There is no import cycle; chapter ordering
is not an obstruction. No implementation or savings are credited.


Phase B is a measured negative for the line-reduction goal. After deleting
zero-consumer sndExK/sndAllK, fstAll and legacy subAt/subSucAt reader families,
Clauses is 2052→2141 (+89) and Pinned 580→601 (+21). Frozen consumers add70,
so the checked trial totals 27,189, a net increase of180. Clauses, Pinned and
Landmarks all exited0. The estimated phase-C reduction of80–130 does not cover
this cost; even the optimistic additional helper-retirement estimate is not
enough. This route is frozen outside the workspace, with no savings credited
and no phase-C implementation authorized. The accepted tree stays27,009.

A separate lexical and manual audit of internal helpers with bodies of at
least15 nonblank code lines found no confirmed dead-proof candidates. This
negative result is scoped to that audit, not a claim of globally minimal code.


A follow-up soundness audit refined the negative result: if Tower, Shape and
Close expose K-membership in their existential readers, Bounds could be used
only for completeness. No residual soundness obstruction was found under that
explicit syntax change. Removing formula guards would save an estimated15–55
net lines after membership-witness plumbing. Together with phase C's80–130,
this still does not reliably recover the measured180-line increase, before
additional Tower migration costs. No further implementation was authorized.

A bounded Before/Limit audit also found no80-line replacement: L.Recursion's
contractibility obligation still requires Before's same-approximation entry
invariant and its well-founded uniqueness proof. Limit already shares the
applicable construction through Described. No new source edits were made.


A fresh-interface paired measurement now covers the accepted27,009-line source
including the finite-image OmegaRec change. Original6da70f2:244.31s wall,
242.33s user,1.63s system, exit0 and3 existing warning sites. Accepted source:
217.60s wall,215.98s user,1.24s system, exit0 and no warnings. Both retain the
same installed cubical interfaces and run one guarded Agda process. The
observed wall reduction is26.71s,10.93%; this is one paired observation, not
a statistical performance guarantee. Logs and machine-readable measurements:
`timing27009-{original,current}-Landmarks.{log,json}`.


The shared-set-operation batch replaces HullCount's independent binary-union
elimination and singleton decoding with the existing Coding.InL readers. HullIn
also uses that union API. This retires the last consumers of OmegaRec.pairʟ-out,
so that reader was removed; pairʟ-in remains used by BoundedSubset and both union
readers remain used inside OmegaRec. No public theorem or hypothesis changed.
The three named modules and Landmarks exited 0, and all applicable static gates
passed. The accepted source now has 26,998 nonblank Agda lines, a net reduction
of 1,975; 1,025 remain to the 3,000-line milestone. Guarded full make check
exited 0: Everything, all lint/weave gates, 34 Python tests and 7 lint-agda
fixtures passed, with no Agda warnings. git diff --check also exited 0.
Full gate log: `full-gate-union-reuse.log`.
Checkpoint and verification log: `sol-union-reuse`. The 217.60 s timing above
belongs to the 27,009-line predecessor, not this new source.


Transversal.Pick now uses appC for its fixed relation, removing the relation
existential, object equality, one truncated payload and its transport. The
remaining predecessor witness keeps an explicit type and a descriptive name.
The public Pick and reader meanings are unchanged. Transversal and Landmarks
exited 0 without warnings; file gates passed. The accepted source has 26,987
nonblank Agda lines, net 1,986 fewer. Full integration gate will follow the
next disjoint batch. Checkpoint: `sol-transversal-appc`.


PairExpression now supports literal L elements and takes a Term directly as
its membership carrier. Its existing three member APIs were generalized
in place; all variable consumers in Clauses explicitly pass var, avoiding
duplicate compatibility wrappers. OrderType.Approx retains the same Body
and pair-graph semantics while eliminating two constant-naming quantifiers,
renaming environments and their transport proofs. Model adds 7 lines, Clauses
adds none, and OrderType removes 24: net 17. All three modules and Landmarks
exited 0 without warnings. Model's bilingual description was updated and
prose-checked after the code checks. Checkpoint: `sol-pair-expression-literals`.
The integrated source is 26,970 nonblank Agda lines, net 2,003 fewer; 997 remain.
The full integration gate is pending the disjoint constant-relation cleanup.


The collapse-description chain completeAt/srcAt/valueAt/correctAt now receives
its relation as S directly, since both actual consumers (ColFo and piFo) use a
fixed relation. It uses appC and keeps table/argument variables in their original
roles, removing both consumers' relation-naming binders and associated transport
proofs. The original APIs were migrated in place, with no parallel descriptions.
OrderType removes 2 lines and HullIn removes 6, a measured net 8, below the
19–29 estimate. Both modules and Landmarks exited 0 with no warnings, and file
gates passed. Checkpoint: `sol-correct-constant`. The source is now 26,962
nonblank Agda lines, net 2,011 fewer; 989 remain. Guarded full make check
for the three combined constant-description batches exited 0. Everything and
Landmarks passed without Agda warnings; all lint/glossary/fence/weave gates,
34 Python tests and 7 lint-agda fixtures passed. git diff --check exited 0.
Log: `full-gate-constant-descriptions.log`.

The analogous Choice routes were not implemented: Faithful.CondCore needs
its StpFo table slot, and Before.RelBodyAt is a real free-slot consumer of
Limit.PrecedesAt. Specializing just Cond₀ or RelCond would not remove the
underlying interface obligations.


Further bounded audits rejected three routes without changing the accepted
source. OmegaRec.zeroAt via PairExpression costs one extra line in readable
form. Generalizing the environment alphabet to Term needs a two-binder lift
and its evaluation lemma; the full cost offsets Sequences' 9–10 removable
lines. Choice.Finite has no supplied injection suitable for pullOrder, and
abstracting its dependent lexicographic order would add a single-consumer
framework for at most 0–10 lines of estimated benefit. These routes are not
credited. A separate Sequences proof-boundary simplification is being checked.


Sequences.seqL-in first proves membership for the canonical envS A g, then
transports that final proposition along the representation equality. It no
longer transports the ambient membership and the environment formula separately.
The named canonical proof preserves readability. Net reduction: 3 lines;
Sequences and Landmarks exited 0 without warnings, and file lint passed.
Checkpoint: `sol-sequence-transport`. Current source: 26,959 nonblank Agda lines,
net 2,014 fewer; 986 remain. Guarded full make check exited 0: Everything,
all lint/weave checks, 34 Python tests and 7 lint-agda fixtures passed without
Agda warnings. git diff --check exited 0. Log: `full-gate-sequence-transport.log`.
A fresh project-interface Landmarks run exited 0 without warnings in 214.08 s
wall, 212.46 s user and 1.23 s system; installed cubical interfaces were retained.
The difference from the earlier original 244.31 s sample is 30.23 s (12.37%),
but this is a noncontemporaneous reference, not a new paired measurement.
Record: `timing26959-Landmarks.{log,json}`.

A bounded Astra mathematical audit found no defensible 100-line reduction in
HullCount from a finite-sequence evaluator or flattening of Skolem terms.
Sequences counts finite environments, but does not construct the internal
functional evaluator needed by HullCount's existing covering-relation injection
lemma. The strongest flattening alternative retains OneStep (253 code lines)
and removes at most the 218-line tail; achieving 100 net would leave only118
new lines for definitional composition, its correctness, a restricted-stage
semantic bridge, a common larger stage, parameter counting and inclusion.
This is a scoped interface/cost negative, not a truncation impossibility or
a lower bound on every possible mathematical proof. No implementation began.


The alternative of intersecting all constructible closed subsets of the
satisfaction stage does not bypass HullIn with the current interfaces. Code
induction gives Hull ⊆ H, but admitting Hull into the intersected family to
prove H ⊆ Hull requires isL Hull, the result being proved. Existing
hullStep⊆Hull and hullL-spec obtain the needed finite-iteration witness from
the explicit iterates. Separating by the existence of an external Code would
again require an internal evaluator formula and adequacy. This proposed
shortcut was rejected after a bounded source-based proof-direction check.


InclGraph now uses the existing definable-injection construction for the
identity map. Assembly consumes its InjCode package, so redundant individual
field/readback aliases were removed; G and the small inclusion retain their
opacity boundaries. GCH.Definable's unused Ren namespace and dedicated import
were also removed after checking consumers. Retaining compatibility wrappers
would have increased the source; migrating the actual consumer makes the
whole change reduce 10 lines (InjChain 8, Definable 2, Assembly 0). AGENTS now
explicitly permits intermediate API migration while preserving mathematical
statements and necessary opacity, so artificial compatibility costs do not
preclude structural refactoring.

All changed modules and Landmarks passed, followed by guarded full make check:
Everything, every lint/glossary/fence/weave gate, 34 Python tests and the
lint-agda fixtures passed without warnings. git diff --check exited 0.
Repository-counter totals: 112 modules, 26,949 nonblank Agda lines, 30,973
all fence-code lines, 52,627 physical lines. Net reduction: 2,024; 976 remain.
Checkpoint: `sol-inclusion-definable`; full log: `full-gate-inclusion-definable.log`.
A byte comparison confirmed that the scratch differed only in the three
authorized files; an ad-hoc scratch total was discarded in favor of the
repository's authoritative counter.


The isolated projected-body trial in
`/private/tmp/bedrock-sol-projected-binders` is a measured negative and frozen.
It kept the bounded-container formulas and embedded five compact relation
bodies with renameFo. The complete draft adds 154 lines in Clauses and removes
9 in Pinned, a net increase of 145. Sharing projection and lookup-tabulate
adequacy would still leave an estimated increase of 60–90 lines. Clauses
passed; Pinned's final atom-slot correction remains unverified after the run
was interrupted. No trial code was integrated. No Agda process remained at
the stop check. The accepted count stays 26,949, with 976 lines still required.

A bounded Sol audit identified a different candidate in Pairing.ProdMap:
construct the product injection directly with the existing Relation API,
removing the component-selection and DefinableMap round trip. Its domain proof
recovers component membership from the original injection's domain field;
Relation.out alone does not supply it. The complete estimated reduction is
20–40 lines, including all four InjCode fields. An isolated implementation in
`/private/tmp/bedrock-sol-product-map` is authorized for Pairing only, followed
by Pairing and Landmarks checks. No saving is credited before verification.
The first readable draft measured 26,951 total lines, two more than the
accepted tree; earlier draft counts are not acceptance figures. Its Pairing
check alone exceeded nine minutes and reached about 6.95 GB RSS, without
dependency rebuild output. This is a measured performance regression. The
next isolated check separates the graph construction's opaque block from the
four property proofs so those consumers cannot unfold the graph internals.
The final version also uses typed coordinate proofs and an image helper.
It passed Pairing (9.41 s), Landmarks (29.09 s), and all applicable linters,
without warnings. A same-condition old Pairing check took 9.53 s. The final
authoritative count is 26,948, only one line below the accepted tree. The four
explicit InjCode proofs offset almost all removed function-selection code.
This larger rewrite was not integrated: neither line reduction nor measured
time establishes a worthwhile return. Both checked versions and the log remain
in the isolated directory (`verification-product-map.log`). Main stays 26,949.

A source import-closure check found every module except Everything reachable
from Landmarks. It identifies no whole unused module to remove; it is not a
claim that every declaration inside those modules is essential.

A bounded follow-up on Pairing.Shift rejected the analogous direct-relation
route before implementation. Both actual consumers use only Shift.injL, but
replacing its function construction still needs the two nine-case proofs,
domain existence and recovery, range, and relation adapters. Complete typed
replacement costs 82–103 lines against about 72 removable lines. The resulting
estimated increase is 10–31, not a saving. This is a cost finding for this
route, not a claim that every possible proof needs those case tables.
Details: `/private/tmp/bedrock-sol-shift-relation/PLAN.md`.

A narrower Hull candidate avoids a new substitution framework. The only two
consumers of mapFo-close immediately transport satisfaction. Sol's bounded
audit therefore replaces those uses with the existing Relabelling.⊨-map and
CloseSem instantiated at the inclusion interpretation. This can remove
mapTm-rename, mapTm-close, and mapFo-close together, plus the two consumers'
syntax-equality scaffolding. The complete estimate is 38–48 lines after new
typed semantic paths and imports. Implementation is isolated in
`/private/tmp/bedrock-sol-hull-close-semantic`, restricted to Hull; Hull and
Landmarks verification is required before credit. Main remains 26,949.
The reviewed implementation removes the three syntactic commutation helpers
and, after their consumers migrate, the unused CloseSem.map-id proof. Only
Hull differs from the isolated baseline. Root verified all 112 source files
and the checked Hull hash before integration. Net reduction: 52 lines;
current source 26,897, cumulative reduction 2,076, with 924 still required.
Hull passed in 4.91 s and Landmarks in 28.10 s, both without warnings;
applicable file linters passed. These are verification timings, not a new
paired build-speed claim. Immutable checkpoint: `sol-hull-close-semantic`.
The integrated guarded make check exited 0: Everything, all lint/weave gates,
34 unit tests and lint-agda fixtures passed without warnings. git diff --check
also exited 0. This is the next complete gate checkpoint. Log and count:
`full-gate-hull-close-semantic.log` and
`full-gate-hull-close-semantic-count.json`.

A follow-up semantic-composition audit found that mapFo-comp still serves real
syntax data: empty-alphabet codes, stage keys, VCode and satisfaction indices.
It and mapTm-comp remain necessary for those consumers. Converting only the
remaining Hull/Condense satisfaction paths removes about 27 helper lines but
adds semantic composition, pinning and consumer adapters; estimated net saving
is at most 9, usually about 4. No implementation was authorized. Details:
`/private/tmp/bedrock-sol-semantic-composition/PLAN.md`.

The deferred simultaneous-substitution audit was completed against the current
post-Hull tree, restricted to Renaming, Relabelling and the remaining closure
code. Parameters and Name were excluded because occurrence-indexed abstraction
is not a fixed constant substitution. A complete substitution kernel needs
102–135 lines for lifting, fusion, semantic compatibility and naturality;
the three specializations remove only 99–124 after necessary interfaces and
dependent-index facts remain. The result ranges from 36 added to 22 removed,
with no defensible 30-line gain. No implementation began. This is a scoped
cost finding, not a rejection of simultaneous substitution as mathematics.
Details: `/private/tmp/bedrock-sol-substitution-audit/PLAN.md`.

A new Condense candidate uses the already supplied elementarity hypothesis
to transfer the complete existential formula in one step. All witnesses then
belong to the hull together; the old path first obtains only the level value
and makes a second coded hull-closure query for the remaining witness. Sol's
bounded design removes that second query, stageF/convF, and the dedicated
pinning/HullConvert chain; cover similarly transfers all its witnesses at once.
Superadequacy and level-complete still supply the stage witnesses, and
level-sound still identifies the level value. The conservative estimate is
110–172 lines. Implementation is isolated in
`/private/tmp/bedrock-sol-condense-elementarity`, restricted to Hull and
Condense, with their named checks and Landmarks required. No gain is credited
before verification; main stays 26,897.
The final joint-existential version uses levelFo directly in both queries,
so the old variable permutations and their adequacy proofs also disappear.
HullElemDown reuses its returned hull member instead of recovering a code just
to reconstruct that member. The checked and reviewed batch removes 213 lines:
26,684 remain, cumulative reduction 2,289, with 711 still required.
Hull, Condense and Landmarks exited 0 without warnings; file linters, weaving
and fence checks passed. Root compared all 112 masters, verified both v2
hashes, and integrated only Hull and Condense. Immutable checkpoint:
`sol-condense-elementarity`. The guarded main make check exited 0: Everything,
all linters and 34 unit tests passed without warnings. git diff --check exited
0. Full log: `full-gate-condense-elementarity.log`; authoritative count:
`count-condense-elementarity.json`.

The next isolated Hull refactoring exposes the arbitrary parameter arity
already supported by Code.wit through TermAlgebra.closed and hull-closed.
Tarski–Vaught can then pass its parameter-code vector directly, instead of
closing variables into constants and proving that transformation correct.
Sol's bounded audit places all consumers inside Hull and estimates 70–90
lines saved after vector concatenation and explicit semantic transports.
Implementation is running in `/private/tmp/bedrock-sol-hull-arity`, restricted
to Hull. Main remains the checked 26,684-line snapshot pending verification.
The reviewed implementation removes 75 lines, reaching 26,609: cumulative
reduction 2,364, with 636 still required. Code.wit and its evaluator stay the
same; closed concatenates the free-parameter and constant-code vectors and
uses the existing parameter abstraction theorem. Tarski–Vaught retains typed
environment equalities and its original conclusion. Hull and Landmarks passed
without warnings, as did all applicable linters, weaving and fence checks.
Root verified the checked hash and that only Hull changed among 112 masters
before integrating. Checkpoint: `sol-hull-arity`. The guarded main make check
exited 0: Everything, all linters and 34 tests passed without warnings.
git diff --check exited 0. Full log: `full-gate-hull-arity.log`; count:
`count-hull-arity.json`.

The next bounded Hull candidate abstracts the original formula's constants
before coding its environment. The existing occurrence-parameter theorem then
replaces codeTm/codeFo's syntax-preimage recursion. A bare Skolem closure uses
search and val-wit directly; one typed semantic path serves both input and
output. The independent empty-domain universe parameter of absFo matches
Code.wit's small formula type. Sol estimates 45–65 lines after all vector and
semantic adapters. Implementation is isolated in
`/private/tmp/bedrock-sol-hull-abstract-first`, restricted to Hull. Main remains
26,609 pending named checks and review.
The checked implementation removes 52 lines, reaching 26,557: cumulative
reduction 2,416, with 584 still required. Formula abstraction now happens
before the finite environment is coded. The bare search closure and a shared
typed body-path replace the formula-preimage recursion and stage adapter.
Hull and Landmarks passed without warnings; all file linters, weaving and
fence checks passed. Root verified the file hash and all 112 masters before
integrating the sole Hull change. Checkpoint: `sol-hull-abstract-first`.
The guarded main make check exited 0: Everything, all linters and 34 tests
passed without warnings. git diff --check exited 0. Full log:
`full-gate-hull-abstract-first.log`; count: `count-hull-abstract-first.json`.

A bounded Condense-limit audit found that the forward inclusion can use
Lset-in at the larger ordinal already provided by β-succ. It therefore need
not prove successor closure of β. Sharing the two collapse-cover transports
and reusing ord∈Lset→∈ gives a complete estimated reduction of 16–22 lines.
The isolated implementation in `/private/tmp/bedrock-sol-condense-limit` owns
only Hull; main remains 26,557 until verification and review.
The verified version retains typed covered/go and liftStage proofs, yielding
13 lines saved rather than the estimate. It removes the successor-closure
detour and shares coverage without compressing the remaining steps. Hull and
Landmarks passed without warnings, as did file linters, weaving and fences.
Root checked the source hash and the 112-master diff before integrating Hull.
Current count: 26,544, cumulative reduction 2,429, with 571 still required.
Checkpoint: `sol-condense-limit`. The guarded main make check exited 0:
Everything, all linters and 34 tests passed without warnings. git diff --check
exited 0. Log: `full-gate-condense-limit.log`; count:
`count-condense-limit.json`.

The bounded ambient level-soundness audit is negative for this milestone.
StepRead forms restricted-carrier witnesses with down before reading the
hierarchy certificate; ambient soundness needs StepRead, ApproxRead/HierRead
and the DefInRead/DefDescribe reader stack generalized together. Even if that
backend existed, verified deletion is at most 28 code lines. PiIn.good-at,
piFo and up remain StageCounted consumers; HullIn cannot be removed. No source
changes or Agda runs were made. Report:
`/private/tmp/bedrock-sol-ambient-level/PLAN.md`.

A bounded Before/Limit coherence audit found no 50-line replacement.
Recursion.Of.val-uniq requires the same rel-only proof through
Recursion.funct, so using it to establish rel-only is circular. Canonical
approximation equality still needs both value uniqueness and entry existence;
the estimated net benefit is 0–15 lines. No source changes were made.

Sol is drafting a simpler tagged-union injection in an isolated HullCount
copy. A relation allows both component preimages, then LeastPre chooses the
least tagged preimage. This can remove the explicit branch decision and
function evaluator. The conservative estimate is only 8–33 lines; acceptance
depends on the readable checked result, not on reaching the estimate. Main
remains at the checked 26,544 lines.

Two bounded sequence-map audits are also negative. Replacing SeqMap's
contractible-fibre evaluator with a direct relation repeats its presentation
uniqueness obligations and adds about 22 lines. Sharing a canonical-presentation
evaluator with Sequences retains both coverage adapters and StageCount.same;
its full estimate is 92 lines replacing 102, below a credible 30-line gain.
No implementation was scheduled. Reports:
`/private/tmp/bedrock-sol-seqmap/PLAN.md` and
`/private/tmp/bedrock-sol-sequence-evaluator/PLAN.md`.

The complete typed tagged-union draft reduces HullCount only from 807 to
803 lines. Relation and stage-bound adapters consume almost all of the
manual-map deletion. Root rejected this four-line payoff for a large
reconstruction before compilation; the draft is frozen and was never
integrated. Diff: `/private/tmp/bedrock-sol-hullcount-tagged/logs/draft.diff`.
Main remains 26,544, cumulative reduction 2,429, with 571 still required.

A fresh paired Landmarks measurement on the checked 26,544-line source and
original revision 6da70f2e43fcfb7617bdf00d6bc5b758850846f7 completed with exit 0
for both. All scratch project interfaces were deleted before each run;
installed cubical interfaces were retained. Both used the prescribed GHC
heap guard and the same Python monotonic/resource timer. Current: 209.98 s,
2,339,045,376 bytes peak RSS, zero warnings. Original: 241.11 s,
2,454,323,200 bytes peak RSS, three distinct existing warnings. This single
paired observation is 31.13 s (12.91%) faster and uses 4.70% less peak RSS.
An exploratory run with incomplete interface cleanup was excluded. Root
compared all 112 timed masters byte-for-byte with main. Logs:
`timing26544-current.log` and `timing26544-baseline.log`. The 3,000-line
milestone remains open: 2,429 lines removed, 571 still required.

Three further bounded Sol audits rejected genericization on full cost.
Choice.Internal's empty-alphabet recoding core is only 40 lines and already
uses mapFo-comp; a cross-carrier coding theorem adds 28–40 lines while the
empty-type conversion remains. Before/Table share 65 lines of induction
(or 89 including graph readers), but the theorem and adapters cost 75
(or 96): the canonical-entry normalization and distinct existence builders
remain. HierDescribe/PiIn share about 85 induction lines, with 66–90 lines
of theorem and operator adapters required; PiIn's constructible slice-table
construction has no hierarchy-reader counterpart. None was implemented.
Reports: `/private/tmp/bedrock-sol-empty-code/PLAN.md`,
`/private/tmp/bedrock-sol-wf-approximation/PLAN.md`, and
`/private/tmp/bedrock-sol-gch-approximation/PLAN.md`.

The next bounded audit ranks alpha-normalized proof-block similarities and
inspects only three previously unaudited clusters. Similarity alone is not
an acceptance criterion; all binder, environment and consumer costs count.
Main remains the verified 26,544-line snapshot.

The proof-clone audit found a real graph-table match between Hierarchy and
Choice.Table. Root corrected its initial cost accounting: two 27-line copies
mean 54 gross lines removed, giving 6–18 saved after the proposed helper and
both adapters, rather than a net increase. The explicitly excluded sequence
evaluator candidate was removed from the report. Broader combined readers
are estimated at 20–28 lines saved; the whole replacement constructor remains
negative because Choice.Table must also construct its current relation.
Reports: `/private/tmp/bedrock-sol-proof-clones/REPORT.md` and
`/private/tmp/bedrock-sol-all-approximation/PLAN.md`.

Sol is drafting the semantic-reader route in an isolated three-file copy
(Sequence, Hierarchy, Choice.Table). First it weakens Hierarchy.Entries to
existence of a recorded value, using Values where normalization is actually
needed. That may remove repeated canonical-value transports and reduce the
shared reader's adapters. Main is unchanged pending measured draft review.

The weaker Entries experiment exposed an important contract cost: the step
readers construct untruncated witnesses using canonical entries. Existential
entries require new truncation eliminators and value transports there,
consuming the reader-side savings. Sol is restoring that partial scratch
experiment from main and retaining the original Entries contract for the
combined semantic-reader draft. HierDescribe needs no change under that
contract and its temporary ownership is released. No partial experiment is
being integrated or counted.

The complete semantic-reader draft is a measured negative for acceptance:
Sequence adds 87 lines, Hierarchy removes 52, Choice.Table removes 40, and
HierDescribe is unchanged. The four-file count is 1,398 before and 1,393
after: only five lines saved across a 360-line diff. The explicit motives,
restriction proofs and instance adapters consume the predicted benefit.
Root rejected it before Agda; main is untouched. Frozen evidence:
`/private/tmp/bedrock-sol-recshape-readers/logs/`. This supersedes the earlier
20–28-line estimate. The milestone remains 571 lines short.

A new structural audit found a larger candidate: derive object negation from
implication and falsity, and object truth from falsity implying itself. The
syntax chapter already identifies these as constructive definitions. Removing
their primitive constructors also removes two cases from coding, shape and
closure predicates, satisfaction tables, and soundness proofs. Sol estimates
170–245 net lines after all consumer migration, with ten contiguous code tags.
The twelve-value semantic frame is independent of tag count and stays intact.

Implementation is isolated in `/private/tmp/bedrock-derived-connectives`.
Three Sol agents own disjoint core, Clauses/Pinned, and coding-consumer files;
only the core agent currently has the compiler slot. TruthAlgebra's independent
meta-level operations are not asserted equal to derived object connectives
for an arbitrary law-free instance. The concrete hProp interpretation must
retain the usual constructive meanings, and final ZFC/GCH assumptions stay
unchanged. Main remains at the checked 26,544 lines until the complete migration
and full gate pass. Audit: `/private/tmp/bedrock-sol-derived-connectives/PLAN.md`.

The derived-connective core now typechecks: LevyHierarchy, FOL.Coding, Count,
all five manipulation modules, Absoluteness, V.Smallness, Choice.Name and
ReflectFo exited 0. Concrete semantic adjustments use identity as the derived
truth witness and explicit lift/lower around falsity. Core prose and Agda
linters pass. These are intermediate checks only: the whole scratch migration
is not yet validated, and no reduced count has been accepted. Coding consumers
are being checked before Clauses/Pinned; the compiler remains exclusive.

The ten-tag backbone now typechecks: InL, Model, Shape, Closed and Recover
passed, followed by Clauses and Pinned. The latter two remove 123 lines
together (Clauses 2,052→1,967; Pinned 580→542); their named checks and both
file linters exited 0. The separate twelve-value semantic frame is unchanged.
The remaining Graph/Uniform/GCH consumers are now being checked in order,
with the compiler slot explicitly transferred. Main still has no integrated
syntax changes; the whole-tree milestone awaits the complete dependency gate.

The downstream migration has passed HierDescribe, DefDescribe and HullIn.
Actual clients in Faithful, Limit, Before, Adequate, OrderType, Pairing and
Least require paired lift/lower conversions between host refutations and the
derived object's lifted bottom; these have been assigned and linted. Semantic
review corrected an initial overstatement: old Logic.¬ returns Empty.⊥, so
its equality with the derived meaning is propositional via lift/lower, not
definitional. Pinned's duplicate imports were also removed.

HullCount triggered performance triage before integration. A run exceeded
five minutes; source review identified two new untyped projected separation
proofs as candidate normalization costs. The attempted tc.decl verbosity
channel emitted no declaration events and changed interface options, forcing
a dependency rebuild, so diagnostic elapsed time is not a per-module timing.
The next check uses normal options and explicit local proof types; any further
isolation uses closed safe prefixes, never postulates or holes. Main remains
the previous verified version while this regression is resolved.

The separation regression is resolved. Each partition set is sealed with its
hProp membership equation before its introduction/elimination readers are
checked. A normal full HullCount run after removing only its interface passed
in 12.17 s; the typed-local-only version exceeded 120 s. The complete source
was restored before validation, and no prefix was counted. Landmarks then
passed without warnings; the warm closure time is not a build benchmark.

Root verified all 112 scratch hashes and checked main against the previous
26,544-line timing snapshot, then integrated the 50 changed masters. The
exact new count is 26,308: this batch removes 236 lines, cumulative reduction
2,665, with 335 still required. Immutable before/after checkpoint:
`sol-derived-connectives`. The scratch full gate correctly refused the absent
Git metadata after Everything passed; no marker was fabricated. In the real
main repository, the guarded make check exited 0: no warnings, all linters,
112-master fence check, 34 unit tests and linter fixtures passed. git diff
--check exited 0. Log: `full-gate-derived-connectives.log`; result:
`full-gate-derived-connectives-result.json`. A fresh normal-option Landmarks
timing on the identical frozen scratch source is now running.

A separate read-only operator-enum audit is negative. Factoring atoms, binary
connectives and quantifiers into enumerated operators would reduce traversal
branches but retain ten real coded cases; its constructor, tag, Δ₀ and
semantic adapters bring the estimated net effect to between 35 lines saved
and 35 added. No implementation was scheduled. Report:
`/private/tmp/bedrock-sol-formula-operators/PLAN.md`.

Fresh timing on the integrated 26,308-line source passed with exit 0 and no
warnings: 201.38 s, peak RSS 1,865,891,840 bytes (1.737 GiB). All 112 project
interfaces were removed from the scratch build tree; installed Cubical
interfaces were retained. The Python monotonic/resource wrapper used the
normal memory guard. All 112 source hashes match before, after and main.
Evidence is archived as `timing26308-*`, including the deletion inventory and
`timing26308-result.json`. This single observation is 8.60 s (4.1%) faster
than the previous 26,544-line measurement, and 39.73 s (16.5%) faster than the
28,973-line baseline measurement under the same cache protocol. These are
observations, not repeated benchmark estimates. The line milestone remains
335 lines away; a bounded Sol audit is checking newly redundant proof chains.

The post-derived GCH/Choice audit found no such large dead chain. Hull's
SatTransfer is shared by Tarski–Vaught elementarity and collapse transport;
replacing it repeats the same induction. Internal.Adequacy and Adequate.At
serve distinct live consumers and already share their common proof. Neither
offers a credible 100-line reduction. Report:
`/private/tmp/bedrock-sol-post-derived-audit/PLAN.md`. A separate bounded audit
now checks V and Base rather than repeating these routes.

The V/Base audit is also negative. Kuratowski pair injectivity in V.Coding
and the choice construction in V.Model each contain about 50 lines of live,
distinct mathematical obligations, with no existing theorem that removes
them. Factoring either merely relocates its proof. No source was changed or
compiler run for this audit. Report:
`/private/tmp/bedrock-sol-v-base-audit/PLAN.md`. Verified progress remains
2,665 lines removed, 26,308 remaining; the 3,000-line milestone is not met.

## Derived bounded quantifiers: isolated pilot

Current source was recounted at 26,308 and diff whitespace checked clean.
The preceding turn made verified progress through the 236-line integration,
full gate and fresh timing; no completion is claimed for the line milestone.

Two Sol audits support expanding bounded quantifiers into ordinary quantifiers
with membership guards. Delta-zero evidence can still be indexed by those
expanded formulas; a term weakening inverse needs no equality on constants.
Unlike derived negation, the expansion introduces non-definitional weakening
commutation obligations in parameter operations. Full migration is estimated
at 205–285 net lines after that risk allowance, not a guaranteed 335.

A fresh isolated pilot at `/private/tmp/bedrock-derived-bounded` starts from
all 112 current masters, with a before-source manifest. Sol owns the nine
core syntax/semantics/manipulation files and the sole compiler slot. It first
checks Parameters and Bounding and stops for review if new commutation and
first-consumer code exceeds 55 lines. Main is unchanged. Coding migration
awaits this evidence; a separate Sol audit reconciles the removable Clauses
definition budget. Plans: `/private/tmp/bedrock-sol-derived-bounded/PLAN.md`
and `/private/tmp/bedrock-sol-derived-bounded-coding/PLAN.md`.

The core pilot passed all nine named modules with exit 0 and no warnings;
both owned-file linters passed. Net core change is -28, with 9 lines of
weakening commutation and 12 lines of witness transport. An initial attempt
to retain the old relativizer's distinction between primitive and expanded
bounded syntax failed at Relativize:83. Root checked the actual consumers
and instead selected uniform quantifier restriction, with matching semantics.
That standard structural operator and its correctness proof typecheck; no
dependent guard-recognition interface was needed. The earlier projected
55-line excess was not incurred. Core evidence: scratch `logs/core/`.

The coding audit reconciled its Clauses budget to exactly 193 removable
nonblank lines; the smaller estimate omitted the 61-line bqAll/bqEx/BqBridge
layer. Migration now proceeds in three disjoint Sol assignments: semantic
consumers; ordinary coding modules; Clauses/Pinned. Editing is parallel,
compilation serial. The main tree remains the verified 26,308-line version
until all consumers and the full gate pass.

Automatic approval review then rejected the first FOL.Coding mutation in
scratch: deleting the old primitive bounded-quantifier encoding equations
and changing the ten-tag description to eight tags. No part of that patch
was applied. Its stated reason was that the deletion was a substantial
semantic change likely to leave the definition incomplete and break downstream
proofs, beyond its interpretation of the user's authorization. It explicitly
forbids achieving the same outcome by workaround and requires a materially
safer alternative or informed explicit user approval. No retry, alternate
tool or reassignment was used to execute the rejected action.

The concrete proposal remains the audited eight-tag migration, confined to
scratch until complete checking. Syntax:92–108 already defines eight primitive
constructors and the two bounded notations as ordinary derived functions.
An attempted independent ReflectFo check confirms the current migration
boundary: FOL/Coding:132.1–12 rejects the old bounded encoding left-hand side
with NoParseForLHS. That is a scratch intermediate state, not a completed
proof. Core and independently checked semantic work are retained; other
agents were asked to stop at reviewable boundaries. Main stays at 26,308
verified lines. The rejected coding action awaits explicit user approval.

At the stop boundary all nine core modules, Absoluteness and Smallness have
exit-0 checks. ReflectFo's source migration is unverified because of the
external Coding error above. This owned set is -44 lines including that
unverified file. Clauses/Pinned are a frozen uncompiled draft, -208 and -83
lines respectively, with their file linters and whitespace checks passing;
they assume the proposed eight-case Shape API, which is not yet implemented.
Those draft counts do not count toward accepted progress. Source manifests
are in scratch `logs/core/semantic-consumers.sha256` and the Clauses/Pinned
handoff. There are no running compiler tasks at this boundary.

## Closeout at the user's request (2026-09-07)

The user ended this refactoring run and requested recording the verified
metrics in README, then committing and pushing. Accepted source remains
26,308 nonblank Agda lines, a reduction of 2,665. Fresh project typechecking
took 201.38 s with peak RSS 1,865,891,840 bytes (1.74 GiB). The full gate
passed without warnings. English, Chinese and Japanese READMEs now record
these figures and the cache/measurement conditions; machine-readable evidence
is retained in `dev/refactor-metrics.json`. All 112 master hashes were checked
against the passed-gate snapshot before closeout. The incomplete eight-tag
experiment remains outside the repository and is excluded from the commit.
The 3,000-line milestone was not reached; this run is closed at the user's
request rather than reported as meeting that milestone.
