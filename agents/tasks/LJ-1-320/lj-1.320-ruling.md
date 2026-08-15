# LJ-1.320 ruling: what the project funds next to close DD24's gap

STATUS: COMPLETE. Written incrementally (C-22). ASD-STE100 applies. Every
negative is marked MEASURED or INFERRED, in those words. Authorization: the
owner's delegation, dated 2026-08-15, scoped to this one set of rulings.

## DECISION

**The project funds ONE flag-only probe task on `src/L/Condensation.lagda.md`
that prices all three ranked mechanisms in four runs, and it stops funding
everything else on this table: R-41's line is CLOSED with its census recorded,
the `RowTies` build is NOT funded until a measured telescope account reaches
15 s, and the LJ-1-311 discipline plus the Miscellaneous instrument fact are
admitted as two LESSONS entries with their measurements.**

The five rulings, each one sentence:

1. **The next probe tests all three mechanisms in one task**, because each
   test is a flag and no test needs a code edit; the follow-up CURE funding
   order is rank 1, then rank 2, then rank 3, resolved by the decision table
   in action 4.
2. **R-41's sweep line is CLOSED**: the census is recorded into R-41 with the
   iterate CLASS named (`sucIter` AND `#`), and no further sweep or cure task
   on that shape is funded against the delivered tree.
3. **`RowTies` is DEFERRED behind a profile it mostly gets for free**: fund it
   only if the measured telescope-and-`KFacts`-consumer account in
   Condensation's definitions profile reaches 15 s, the band's own floor;
   otherwise it is REFUSED for seconds and left to DD13's lines pricing after
   the `[LJ-1.306]` port completes.
4. **The Miscellaneous finding changes how this project measures**: every
   future `--profile=definitions` verdict states the Total, the Miscellaneous
   share, and a same-run charged control arm; no retroactive audit is funded.
5. **The LJ-1-311 discipline is ADMITTED as one LESSONS entry with two
   measured clauses, and the empty-account instrument fact is ADMITTED as a
   second entry**; the orchestrator assigns both IDs.

## MACHINE STATE, AND WHAT THIS TASK RAN

This task ran NO Agda. At 23:07 the slot count
(`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`) returned 0 and the
load averages were 5.63 6.22 6.56. A timing measurement needs a quiet machine
(AGENTS.md, working rules), and this session's machine is not quiet. Every
seconds figure in this ruling is a quotation from the record at a named
`file:line`, and every count is my own grep or arithmetic, which load does not
touch.

## STANDING FACTS RE-DERIVED (C-44)

| claim | verdict | anchor |
|---|---|---|
| DD24's bar is 0.010514 s per line | **VERIFIED.** The live bar is `ac_baseline_module_rate` 0.009143 times 1.15 | `dev/ledger.toml:292-297` |
| the gap is 60.0 s | **VERIFIED.** "at 11,926 lines the on-bar allowance is 125.4 s, the wing measures 185.41 s, and the gap is 60.0 s" | `dev/ledger.toml:302-304`; `dev/PLAN.md:49` |
| Condensation is 132.28 s | **VERIFIED as a quotation chain**, `[LJ-1.218]` kept by `[LJ-1.222]`; NOT re-measured here (no quiet machine). The probe's baseline run re-measures it as a by-product | `agents/tasks/LJ-1-311/lj-1.311-report.md:113`; `dev/ledger.toml:303` |
| that is 71.4 percent of the GCH wing's seconds | **VERIFIED by my own arithmetic.** 132.28 over 185.41 is 0.7135 | the two rows above |
| its overage alone is about the size of the gap | **VERIFIED by my own count and arithmetic.** My awk count of non-blank in-fence lines returns 6,718; the allowance is 6,718 times 0.010514, which is 70.6 s; the overage is 132.28 minus 70.6, which is 61.7 s, against a 60.0 s gap | this task's count over `src/L/Condensation.lagda.md` at HEAD |
| the opaque seal took Cardinal 99.78 s to 9.31 s | **VERIFIED.** | `dev/LESSONS.md:4239-4242` (C-50) |
| the respelling took EnvSupply 495.23 s to 6.65 s | **VERIFIED.** | `dev/LESSONS.md:4317`, `:4335-4336` (R-41) |
| a telescope lift on a Condensation made it WORSE, 204.7 s to 308.8 s | **VERIFIED.** The P-l table row; the figure is the RETIRED route's Condensation, so it transfers as SHAPE only, never as a price | `dev/LESSONS.md:2355` |
| 117 module applications in Condensation | **VERIFIED by my own grep**, same regex, count 117 | this task's grep |
| zero `no-eta-equality` in the master | **VERIFIED by my own grep**, count 0. MEASURED | this task's grep |
| Miscellaneous is 54 to 61 percent of this project's runs | **VERIFIED against the raw files.** k1.out: Total 3,974 ms, Miscellaneous 2,417 ms, 60.8 percent; c1.out: Total 1,540 ms, Miscellaneous 838 ms, 54.4 percent | `agents/tasks/LJ-1-292/runs/k1.out:2-3`; `agents/tasks/LJ-1-309/runs/c1.out:2-3` |
| the raw profile always carried the `splitKey∈` row | **VERIFIED by my own read.** `sed -n '26p'` prints `KeyOver.splitKey∈ 26ms` | `agents/tasks/LJ-1-292/runs/k1.out:26` |
| no existing LESSONS entry covers the excerpt discipline or the Miscellaneous bucket | **MEASURED.** `grep -n "Miscellaneous\|excerpt" dev/LESSONS.md` returns nothing, so admission creates no double canon | this task's grep |

## REASONS

**R1. The gap and the file coincide, so Condensation is the only site worth a
next dispatch.** The wing's gap is 60.0 s (`dev/ledger.toml:303-304`) and
Condensation's own overage is 61.7 s by my re-derivation above. A cure
anywhere else cannot close the gap even in principle. DD24 allows the
intermediate debt (`dev/PLAN.md:49`, "only the whole wing at the end is
judged"), so the right next spend is the cheapest decisive measurement, not a
heavy rewrite.

**R2. All three ranked mechanisms are testable by flags, so ranking the probes
is unnecessary; one task tests all three.** Rank 1's test is
`--no-syntactic-equality` (agda#5801, `lj-1.317-report.md:85-99`). Rank 2's
test is reading `Serialization` against `Typing.CheckRHS` under
`--profile=internal` (agda#1646, `:124-136`), and `[LJ-1.281]` already showed
this project can read that mode (`lj-1.317-report.md:479-487`). Rank 3's
flag-only test is `--lossy-unification` (`:170-180`), with the one-line
`no-eta-equality` edit held back as a second-stage probe. Not one of the three
needs a master edited. The survey marks every mechanism HYPOTHESIS at this
site (P-l), and a flag run each is the cheapest way to turn one of them into a
price.

**R3. The follow-up funding order is rank 1, rank 2, rank 3, because cost of
cure rises in that order.** Rank 1's cure is a flag or a local respelling of
`twelveB` and `closedBS`, the two near-identical twin pairs the file's own
attribution already names (`lj-1.311-report.md:117-121`, from `[LJ-1.283]`
over `[LJ-1.218]`). Rank 2's cure is a restructuring of 117 module
applications, the widest edit on the table. Rank 3's cure is one line but can
break consumers ("Pattern matching is not allowed by default",
`lj-1.317-report.md:181-184`). When tests are equally cheap, the mechanism
with the cheapest cure gets cured first if confirmed.

**R4. R-41's line closes because two independent legs agree on the verdict and
the corrected census is now complete.** The probe found three sites, deepest
depth 2, and recommended DO NOT FUND (`lj-1.309-report.md:126-135`, `:409`).
The adversarial review UPHELD the NO-GO while overturning three measurements
and adding the one missed site, `src/L/Choice/Name.lagda.md:129-135`, at 17 ms
delivered (`lj-1.311-report.md:9-21`, `:184-193`). The delivered price of
everything the shape touches is about 219 plus 25 plus 17 ms, under 0.3 s
against a 60.0 s gap, with DD4 value ZERO because `Key.lagda.md` is in neither
closure (`lj-1.309-report.md:312-323`, re-derived by `[LJ-1.311]` at
`:262-263`). A line this cheap, swept twice, closes; what keeps it closed is
recording the CLASS, not the token, which is exactly the review's finding
(`lj-1.311-report.md:352-357`).

**R5. `RowTies` is deferred because its seconds band is a hypothesis standing
where a measured refutation of the same argument shape already stands.** The
15 to 20 s band is marked INFERRED by its own author
(`lj-1.307-report.md:252-256`). The only measured telescope lift on a
Condensation went 204.7 s to 308.8 s, the wrong direction
(`dev/LESSONS.md:2355`); that figure is the retired tree's and transfers as
SHAPE only, so the refusal rests on P-l the law, not on the number. The
literature points both ways on records (`lj-1.317-report.md:401-410`), and the
survey's own recommendation is one profile run on bytes that already exist
(`:446-458`). The probe's baseline run delivers that profile for free, so
deferral costs nothing. INFERRED, from the P-l table row: the band will not
survive measurement; the gate decides, not my expectation.

**R6. The Miscellaneous finding changes measurement practice because the
instrument's blind bucket is measured at half the run.** `Miscellaneous` is
the EMPTY account in Agda's own source (`Benchmark.hs`, READ by `[LJ-1.317]`
at `lj-1.317-report.md:267-282`), it is 54.4 and 60.8 percent on this
project's own runs (re-verified above against the raw files), and the manual
does not document it (`:289-294`, MEASURED by that survey's whole read). A
not-charged verdict over a 60-percent-dark instrument supports little unless a
charged control sits in the same run. Both standing not-charged verdicts in
this chain carried such controls (`lj-1.309-report.md:274-277`,
`lj-1.311-report.md:85-88`), so they stand and no retroactive audit is funded.

**R7. The discipline is admitted because both clauses carry measurements, and
a law is not admitted without its measurement.** Clause 1, name the CLASS:
`#_` is a second numeral iterate, named in-fence by all 96 masters at 972
occurrences, and the token filter missed one real site that measurement then
priced at 17 ms (`lj-1.311-report.md:33-65`, `:184-193`). Clause 2, read the
RAW artifact: `k1.out:26` always carried the 26 ms row, a report's excerpt
dropped it, and a false 522 ms range plus a false hypothesis were built on the
absence (`lj-1.311-report.md:123-157`); I re-derived the row myself above.
The second entry, the empty-account fact, carries R6's measurements.

**R8. Where the legs disagree, I rule with the leg that measured a controlled
pair.** LJ-1-309 against LJ-1-311 on filter completeness, on the 522 ms range,
and on the 42-times half-cure: LJ-1-311 wins all three, by the Bridge run, by
the raw file, and by the E1/E2 pair (`lj-1.311-report.md:67-109`, `:123-157`,
`:214-248`). LJ-1-307's seconds band against LJ-1-317's survey and the P-l
table: LJ-1-317 wins; the band is INFERRED and the same argument shape was
measured to fail. No disagreement in the three legs survives into this
ruling's actions.

## WHAT THE ORCHESTRATOR MUST DO

1. **Record R-41 CLOSED.** Amend R-41 in `dev/LESSONS.md` (the entry ends at
   `:4384`) with the 2026-08-15 census: the CLASS is an explicit `sucV` chain
   against ANY numeral iterate, `sucIter` AND `#_`
   (`Constructions.agda:164-166`); the sites are four, all depth 2, three in
   `src/L/Coding/Key.lagda.md:118-133` and one in
   `src/L/Choice/Name.lagda.md:129-135` at 17 ms delivered; the emitter-side
   closure argument (`pr∈Lset-suc` at `Basic.lagda.md:596-599` and its generic
   twin `T-pr` are the only depth-2 chain emitters, uses enumerated at
   `lj-1.311-report.md:60-65`); the `#` ladder sits two rungs lower (249 ms at
   depth 3, 10,903 ms at depth 4); verdict DO NOT FUND, about 0.3 s delivered
   against the 60.0 s gap, DD4 value zero. State in the entry that the sweep
   line is CLOSED and name the reopening condition from the reversal section
   below.
2. **Add the two-token file gate to the build-brief checklist** in
   `dev/ORCHESTRATION.md` section 1: a NEW master that matches both
   `sucV *( *sucV` and a numeral iterate (`sucIter *[0-9]` or a `#` base under
   a chain emitter) gets a read before it lands. No new checker is funded; the
   file-level proxy's price is recorded at `lj-1.309-report.md:344-368`.
3. **Land the two LESSONS entries**, IDs assigned by the orchestrator (owner's
   delegation, 2026-08-06). Entry A, two clauses: a sweep's filter names the
   CLASS, not the token, with the 972-occurrence and 17 ms measurements; a
   not-charged verdict is read from the raw `.out` file, never from a report's
   excerpt, with the k1.out:26 measurement. Related: C-42, C-44, C-50. Entry
   B: `--profile=definitions`' Miscellaneous row is the EMPTY account,
   measured at 54 to 61 percent on this project's runs and undocumented in the
   2.8.0 manual; every definitions-profile verdict states Total, Miscellaneous
   share, and a same-run charged control; `--profile=internal` is the
   activity-side attributor. Add the one-line reporting rule to the brief
   checklist; enforcement point: brief checklist plus review.
4. **Register and dispatch ONE probe task on `src/L/Condensation.lagda.md`**
   (PLAN section 6.0 rules 6 to 8 first). Quiet machine required; slot check
   before every run; `GHCRTS="-A64m -I0 -M8g"`; one process; 30-minute wall
   per run; cap never raised. Four runs, in this order:
   - **A1**: baseline, `--profile=definitions`. Re-measures 132.28 s, prices
     the `KFacts` consumers at `:6160`, `:6449`, `:6550`, `:6578`, `:6847`,
     `:7109` and the thirty `Agree` modules' definitions (the `RowTies` gate),
     and is the same-day control for B and C.
   - **A2**: baseline, `--profile=internal`. Rank 2's test: read
     `Serialization` plus `Import` against `Typing.CheckRHS`; comparable on
     record is `[LJ-1.281]`'s 90.7 of 100.8 s in `CheckRHS`.
   - **B**: `--no-syntactic-equality --profile=definitions`. Rank 1's test.
     The flag affects interface reloading, so the run must force a re-check of
     the module and report any dependency re-checks it triggers; report
     whether the flag co-exists with `--safe`, which the 2.8.0 options page
     leaves unstated.
   - **C**: `--lossy-unification --profile=definitions`. Rank 3's flag test.
     If the run goes red, report the arm UNMEASURABLE, not a wall: the
     heuristic is documented sound but incomplete.
   After the runs, restore the interface cache with one flagless check, and
   leave no undeclared file in `_build/`. Before dispatch, read the raw `.out`
   files of `[LJ-1.283]`'s existing Condensation profile and check their
   bytes-currency by commit; if current, they pre-answer the `RowTies` gate
   and cross-check A1.
5. **Apply this decision table, fixed now (D-1), to the probe's return:**

   | measured branch | ruling that follows |
   |---|---|
   | B cuts Condensation's own Total by 30 s or more | **Rank 1 CONFIRMED and it is the funded line.** Next dispatch is a cure brief: flag-landing against a term-sharing respelling of `twelveB` and `closedBS`, priced from A1 and B. Ranks 2 and 3 drop to unfunded |
   | B cuts less than 30 s, and A2 shows `Serialization` plus `Import` at 30 percent or more | **Rank 2 leads.** Fund its probe next: an export-trimming miniature in the task directory, priced before any master edit |
   | B and A2 both miss, and C cuts 30 s or more while staying green | **Rank 3 leads.** Fund the one-line `no-eta-equality` probe on a COPY of the `KFacts` region in the task directory |
   | all three miss | **All three mechanisms are refuted at this site.** Return to C-50 triage on A1's charged rows, which already name `satGraphB`, `twelveB` and `closedBS`, and write the cure brief at the charged definitions |

   The 30 s threshold is half the 60.0 s gap: a mechanism worth less than half
   the gap cannot be THE funded line while the attribution rows already name
   concrete definitions.
6. **Apply the `RowTies` gate.** Sum the A1 charges (or `[LJ-1.283]`'s
   current raw bytes) over the `KFacts` consumers and the thirty `Agree`
   modules. At 15 s or more, fund a `RowTies` PROBE, not the build. Under
   15 s, REFUSE the compression for seconds and record that the lines case
   returns to DD13 pricing after `[LJ-1.306]` wave 2 completes. Do not stop
   `[LJ-1.306]`.
7. **Stop funding**, and say so in the task index: further R-41 sweeps or
   cures against the delivered tree; the `RowTies` build ahead of its gate;
   any telescope-lift-shaped restructuring of Condensation argued from
   resemblance (P-l, `dev/LESSONS.md:2355`); further speculation about
   Miscellaneous attribution, which A2 replaces with measurement.
8. **If rank 1 confirms and the cure is a header flag**, check the OPTIONS
   header rule in `dev/STYLE-agda.md` before landing: all 96 masters carry
   exactly one identical header (MEASURED by `[LJ-1.317]`,
   `lj-1.317-report.md:242-244`), and if that uniformity is owner-ruled, ask
   first. This is the one conditional escalation this ruling creates.

## WHAT WOULD REVERSE THE RULING

- **R-41 reopens** if a change to `src/` introduces an explicit `sucV` chain
  of depth 3 or more against a numeral iterate in either channel, observed by
  the recorded grep pair firing on a new master; or if an Agda version bump
  re-shapes R-41's ladder, observed by re-running the ladder probe.
- **The probe-order ruling reverses itself by its own table**: each branch in
  action 5 is an observable measurement that hands the lead to a different
  rank.
- **The `RowTies` refusal reverses** if the measured telescope account
  reaches 15 s at the gate, or if post-port DD13 pricing funds the compression
  for LINES with seconds treated as unpriced.
- **The measurement rules retire** if a future Agda manual documents the
  unattributed bucket, or if the Miscellaneous share falls under 10 percent on
  this tree's runs, observed in any two consecutive profiled tasks.
- **The no-retroactive-audit half reverses** if anyone finds a standing
  verdict that rests on a not-charged claim WITHOUT a same-run charged
  control; that verdict is then re-measured before its next use.
- **The whole funding direction reverses** if the probe's A1 re-measure moves
  Condensation's 132.28 s materially (more than the run spread) in either
  direction, because every share in this ruling is computed from it.

## WHAT THIS RULING DOES NOT DECIDE

No trophy statement changes under any branch of this ruling: every funded
action measures or cures what PROVES the wing, never what either trophy
STATES. No edit to `AGENTS.md` is needed or ordered (DD19 reserves it). No
push is ordered. The one conditional escalation is action 8's header
question.

## DD4

Stated, as every return must: maximize the code the two proofs share, and
write it generic. This ruling funds measurement, not new code, so no shared
line moves. Deferring `RowTies` keeps the `Agree` family's generic port
(`[LJ-1.306]`, 23 modules at 0 changed lines) undisturbed, which is where the
family's DD4 value sits. Condensation is in the GCH WING's seconds account
(`dev/ledger.toml:303`) and in NEITHER trophy statement closure today
(`lj-1.307-report.md:305-309`, INFERRED there from the orchestrator's walk),
so a cure there pays the judged side alone, and P-y's warning runs in the
favorable direction: every second saved improves the DD24 ratio
(`dev/LESSONS.md:3837-3843`, read in reverse as `[LJ-1.317]` section 9 does).
If a cure lands, it lands in the generic module so the cost is paid once,
whatever the tower count.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-309/lj-1.309-report.md`, read WHOLE. TAKEN: the census,
  the strong-reading filter, the DO-NOT-FUND arithmetic (`:398-412`), and the
  free-instead recommendation (`:414-417`) that action 1 executes. NOT TAKEN:
  its completeness sentence (`:116-120`) and its 0-to-522 ms range
  (`:290-304`), both overturned by `[LJ-1.311]`.
- `agents/tasks/LJ-1-311/lj-1.311-report.md`, read WHOLE. TAKEN: the SPLIT
  verdict, the `#` channel, the Name site's 17 ms, the k1.out:26
  reconciliation, the half-cure refutation, and the two practice notes
  (`:348-357`) that ruling 5 admits. NOT TAKEN: nothing; every claim I used
  I re-anchored or re-derived.
- `agents/tasks/LJ-1-317/lj-1.317-report.md`, read WHOLE. TAKEN: the three
  ranks with their one-command tests, the empty-account finding with its
  Agda-source anchor, the `--profile=internal` comparable, and the
  KFacts-consumer recommendation (`:446-458`) that the gate in action 6
  executes. NOT TAKEN: its INFERRED pairing claim that
  `--profile=definitions --profile=conversion` is legal; the probe can test
  it but nothing here rests on it.
- `agents/tasks/LJ-1-307/lj-1.307-report.md`, read WHOLE. TAKEN: the
  partition, the 990-line telescope debt, the do-not-stop-the-port judgment
  (`:270-295`). NOT TAKEN: the 15 to 20 s band (`:252-256`), INFERRED by its
  own author and gated by action 6 instead.
- `dev/LESSONS.md` at C-50 (`:4224`), C-51 (`:4271`), R-41 (`:4307`), P-l
  (`:2323`, table at `:2349-2356`), P-y (`:3803`), C-44 (`:3849`), C-42
  (`:3704`). TAKEN: every law this ruling cites, read at the heading and the
  measurement. The four ARCHIVE files under `archive/dev/` were not read by
  this task: all four legs already carried their archive sections, and no
  claim in this ruling rests on the retired route beyond the P-l table row,
  which lives in `dev/LESSONS.md` itself. MEASURED: no archived file is cited
  above.

## LITERATURE USED (DD18)

This ruling dispatches no mathematics; the literature it weighs is the proof
assistant corpus that `[LJ-1.317]` delivered. USED: agda#5801 (rank 1's test),
agda#1646 (rank 2's mechanism, open since 2015), agda#6509 with the NAD AIM 32
notes (rank 3), the 2.8.0 lossy-unification and record-types pages, and
`Benchmark.hs` at v2.8.0 (the empty account). WHY NOT the rest of that
survey's table: rank 4 (`with`) is already cured and lawed as C-51; the
instance rows are CLOSED in 2.8.0 or refuted by the header grep; the 2.2.x
wiki figures are stale and the survey itself refuses them. No source outside
`[LJ-1.317]`'s table was consulted; a ruling adds no new literature.
