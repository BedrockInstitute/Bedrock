# review-of-LJ-1-517-1: adversarial review of the LJ-1.517#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-517/lj-1.517-report.md` with
its NO-GO statement `agents/tasks/LJ-1-517/review-of-approx-in-stage.md`.
I attacked the return, not the task. I re-opened every load-bearing cite,
re-ran nothing, and swept `src/` myself for census misses. The NO-GO
stands. Three defects are recorded below. None of them moves the verdict.

## 0. THE INSTANCE RECORD

The live transitions record is in the main tree. The worktree copy of
`dev/pod/transitions/2026-08.jsonl` stops at seq 158 (2026-08-19) and
carries no LJ-1.517 row. The record of instance #1:

- `dev/pod/transitions/2026-08.jsonl:2288` (main tree): READY to RUNNING,
  role `coder`, model `claude-opus-5`, effort `xhigh`, `heads_sha256`
  `a8d7e875`, `obl_before` 1. The task directory's `.pod` file carries the
  same heads value.
- `:2305`: RUNNING to RETURNED, why `pid dead`. The files were complete on
  disk when the process died. The return is not partial.
- `:2308`: CHECKING to READY, row `task-lj-1-517-stop-stated`. The fact
  bundle: `exit_code` 0, `obligations_delta` 0, `obligations_open` 1,
  `heap_wall` false, `lines` 0, `seconds` 2.47, `error_class` null,
  `changed_files` 20. The same facts are in
  `agents/tasks/LJ-1-517/runs/accept-1.out`, and that arm re-ran the probe
  today: `run agents/tasks/LJ-1-517/Probe517.agda rc 0 seconds 2.47`.

So the return's own numbers, checked at their source, are correct: the
probe is green, the obligation is open, and the stop is stated with a
`review-of-*.md`.

## 1. QUESTION ONE: DOES THE VERDICT LINE MATCH THE BODY?

Yes. Both halves of the line are backed by the body.

The line says NO-GO on `approx-in-stage`, and that the door `[LJ-1.494]`
left open does not close the way the brief expected. The body delivers
exactly that, in three steps:

1. The obligation is not built. The witness meter reads
   `1 UNRESOLVED of 1` (`agents/tasks/LJ-1-517/runs/witness.out:2`), and
   `--safe` is on (`agents/tasks/LJ-1-517/Probe517.agda:1`), so no
   postulate stands in.
2. The census does not close the door, because `hierL` is not the only
   approximation the tree builds: `approxSet`
   (`src/L/Choice/Before.lagda.md:1035`) is a second one, and it is
   stage-bounded. This is the half the brief did not expect, and the body
   says so in plain words (report section 2, THE ANSWER TO THE BRIEF'S
   STOP CONDITION).
3. The door closes anyway, by a price every witness pays, and that price
   is machine checked: `witness-forces-levelIn`
   (`agents/tasks/LJ-1-517/Probe517.agda:181`), `obligation-gives-levelIn`
   (`:191`), and `witness-forces-two-below` (`:204`) are green terms in a
   green file.

The body is also honest about the strength of the NO-GO. Report section 10
says there is no term of the negation and calls the result an obstruction.
That is the correct strength, and it matches the stop the branch table
fired (`stop-stated`, not a refutation row).

I pressed the strongest counter-reading I could build: report section 2
says row 5 is a real, delivered, stage-bounded approximation that is not
`hierL`, so did the return meet the GO after all? No. Row 5 approximates
the `relAt` recursion below a numeral, not the tower below `δ`, and its
stage is chosen by `smallStage`, not given in advance. The obligation's
`Approximates` is the tower spelling
(`src/L/Coding/Sequence.lagda.md:286-289`). The body states this distance
itself, at `src/L/Choice/Before.lagda.md:1013` and
`agents/tasks/LJ-1-517/Probe517.agda:106`. The counter-reading fails.

On the [LJ-1.375] and [LJ-1.376] failure class, a line the body does not
back: I found that class present once, in miniature, in one framing
sentence of report section 2. It does not sit on the verdict path. It is
defect D1 below.

## 2. QUESTION TWO: DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY?

I opened every cite. All resolve. The load-bearing chain:

- Probe internal lines: `:74` (`row2-generic`), `:98` (`row4-approxSet`),
  `:106` (`row5-smallStage`), `:144` (`ApproxInStage`), `:168` (the
  truncation elimination), `:181`, `:191`, `:204`. All present at those
  lines today.
- The probe is green today, not only on 2026-08-22: the acceptance arm
  re-ran it at rc 0 (`agents/tasks/LJ-1-517/runs/accept-1.out`).
- `src/L/Hierarchy.lagda.md`: `:274` `approx-val`, `:382` `graph-table`
  with the witness as a parameter, `:502` `IsHier` as a membership
  equivalence, `:560` the induction step that fills the slot with the
  induction hypothesis inside the `hierAt` build, `:621` `hierL`, `:646`
  `Lset-defines`, `:656` `H = hierL ...`, the witness.
- `src/L/Choice/Before.lagda.md`: `:1011-1013` `smallStage`, `:1035`
  `approxSet`.
- `src/L/Choice/Table.lagda.md`: `:511` that chapter's own generic
  `graph-table`, `:684-685` `tableAt`, `:715` its induction step filling
  the slot with the induction hypothesis.
- `src/L/Coding/Sequence.lagda.md`: `:286-289` `ApproxAt`, `:291-292`
  `GraphAt`, `:298` `ApproxAt-value`.
- `src/L/Constructible.lagda.md`: `:183` `layer-trans`, `:246`
  `Lset-layer`, `:301` `𝒟ₒ-intro`, `:313` `𝒟ₒ∋⊆`, `:336-337` `Lset-out`.
- `src/V/Coding.lagda.md:175-176` `pr`, and
  `src/V/Hierarchy.lagda.md:83` `_∈ˢ_ = _∈_`.
- `levelIn` is a hypothesis at every site in the live tree. The report
  cites `src/L/BoundedSubset.lagda.md:917` and `:1555`. I checked the
  whole tree: those two, plus `src/L/StageBound.lagda.md:80` and `:106`,
  are all the sites, and all four take it as a module parameter. The
  "every site" claim holds at sites the report did not list.
- The meter and the price numbers:
  `agents/tasks/LJ-1-517/runs/witness.out:1-2`; the W3 medians 2.21 s and
  417,808,384 bytes against `runs/w3-1.time`, `w3-2.time`, `w3-3.time`
  (2.20, 2.21, 2.27 s); the full-file medians 2.44 s and 427,933,696
  bytes against `runs/full-1.time`, `full-2.time`, `full-3.time` (2.44,
  2.43, 2.49 s). All match.
- The counts: 230 lines and 128 non-blank non-comment lines in the probe,
  and 66 in the obligation block from `:135`. All exact.
- External cites: `agents/tasks/LJ-1-494/lj-1.494-report.md:127` and
  `:358-360`, `agents/tasks/LJ-1-492/lj-1.492-report.md:336-337`,
  `dev/literature/devlin-II5.md:216`, `:218`, `:221`, and
  `archive/dev/LJ-dispatch-index.md:254`. All resolve with the quoted
  text.
- The tree state: `git status` shows only `agents/tasks/LJ-1-517/`
  untracked. Nothing under `src/` changed. The claim "nothing landed in
  src/" holds.

Three defects, none overturning:

- **D1.** Report section 2 opens with: "Each row is a name from `src/`,
  re-declared in the probe at the type this census claims for it" and "All
  seven rows are green". That is false for two of the seven table rows.
  Table row 4 (the induction hypothesis inside `hierAt`) and table row 7
  (`L.Choice.Table`'s `graph-table` and `tableAt`) are not re-declared in
  the probe: the probe imports nothing from `L.Choice.Table` and never
  names `hierAt` (`agents/tasks/LJ-1-517/Probe517.agda:11-27`). The
  probe's seven ascriptions are a different seven: its rows 6 and 7 are
  the readings `ApproxAt-value` and `approx-val`, which are not census
  table rows. By the return's own standard, "a census in a comment is not
  evidence" (report section 7), table rows 4 and 7 are comment-grade. I
  re-verified both rows at their own `file:line` today, so they are true,
  but the machine-checked claim for them is not. This is the [LJ-1.375]
  class in miniature, on two non-decisive rows.
- **D2.** The probe comment at `agents/tasks/LJ-1-517/Probe517.agda:84`
  cites `src/L/Hierarchy.lagda.md:653` for the `hierL` witness. The
  witness `H = hierL ...` sits at `:656`. The report cites `:656`
  correctly. Probe-internal comment defect only.
- **D3.** Report section 3.2 cites `src/L/Constructible.lagda.md:340` for
  `Lset-out`. Line 340 is inside its proof; the declaration is at
  `:336-337`. The cite resolves, but it is loose. The same nit applies to
  the verdict line's "GREEN, exit 0 (`runs/full-1.out`)": that file holds
  the `Checking` line only, and the rc for it is not printed inside it.
  The strong evidence is the acceptance arm's rc 0. True claim, weaker
  cite than it needed.

## 3. QUESTION THREE: IS THE ENUMERATION COMPLETE?

Yes. I swept `src/` myself, independent of the return. Every
approximation-shaped object the tree carries:

- The `L.Hierarchy` family: `hierL` (row 1), the generic slot `graph-table`
  (row 2), and its two fill sites for the tower, `Lset-defines` at
  `src/L/Hierarchy.lagda.md:649` with the witness at `:656` (row 3) and
  the `hierAt` build at `:560` (row 4). The usage map confirms there is no
  other call site: `graph-table` is used at `:387` (its own proof), `:560`
  and `:649` in that chapter, and `src/L/Choice/Table.lagda.md:715` in the
  other chapter.
- The `L.Choice.Before` family: `approxSet` (row 5) and `smallStage`
  (row 6). `beforeFam` is the family that collects the `approxSet` values,
  the same recursion, so row 5 covers it.
- The `L.Choice.Table` family: that chapter's own `graph-table` and
  `tableAt` (row 7).

Two places look like misses and are not:

- `src/L/Choice/Limit.lagda.md:733-735` names an approximation for the
  code order, but names it as work not done: it sits in the chapter's
  "what remains" section, and no set is built. There is nothing to
  enumerate.
- `src/L/Condensation.lagda.md:2459-2461` builds bounded approximation and
  graph matrices, but they are formulas, not sets. A formula cannot be the
  existential's witness.

No approximation set in `src/` is missing from the census. The decisive
answers stand: `hierL` is not the only one, `approxSet` is the one
stage-bounded approximation, and it does not transfer because its stage is
chosen by the construction and not given in advance.

## 4. WHY THE NO-GO STANDS

The obligation was not built, and the return shows machine-checked cause:
any witness in the stage forces `levelIn` below `δ`
(`agents/tasks/LJ-1-517/Probe517.agda:181`, `:191`), the tree carries
`levelIn` only as a hypothesis at every site, and the true price is two
membership steps below `α` (`:204`). The enumeration is complete. The
literature correction is sourced at `dev/literature/devlin-II5.md:218` and
`:221`, and the errata file does not contradict it. The cure the return
names, the limit hypothesis on `α` with the converse priced next, is the
right next question, and the return says itself that the converse is
unpriced (report section 8).

**Verdict: upheld.** The NO-GO of LJ-1.517#1 closes the task. The three
defects D1 to D3 are recorded for the next brief, and none of them touches
the verdict path.

## ARCHIVE USED

- `dev/ARCHIVE.md`: read at `:1`. Quote: # ARCHIVE.md: the archive registry.
  **DECLINED, not used.** W4 did not fire in the return: no module moved,
  and `git status` shows only the task directory changed. No archive row
  was owed, so the registry was not needed.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: # ARCHIVED 2026-08-20.
  **DECLINED, not used.** The per-episode journal is retired. The history
  this review needed is in the transitions record and the task reports.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote: # ORCHESTRATION: the orchestrator's operating rules.
  **DECLINED, not used.** The operating rules that bind this review are in
  the slot file and the brief, both live.
- `archive/dev/DD-archived.md`: read at `:1`. Quote: # THE `DD` RULING SERIES, archived in full 2026-08-18.
  **DECLINED, not used.** The clauses I judged under, W2 and W4, are live
  in the slot file. The archived series adds nothing to the three
  questions. (The backticks around DD are in the source line.)
- `archive/dev/PLAN-archived.md`: read at `:1`. Quote: # ARCHIVED 2026-08-20.
  **DECLINED, not used.** The retired plan does not bind this review.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED, and it carries the
  verification of the return's section 5.**
  Read at `:216`. Quote: from 2.7). The witness z bundles the level sequence and its bound.
  Read at `:218`. Quote: 2. Uniform Δ₁ at limit α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α,
  Read at `:221`. Quote: live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
  Used: the return's claims that the orthodox witness is the level
  sequence and that the missing piece is a limit hypothesis on `α` are
  both at these lines, as quoted. The quotes above are the full source
  lines, trimmed of leading spaces only.
- `dev/literature/devlin-errata.md`: read at `:140`. Quote: statement which is Σ^KPI_1 is Σ1 over any Lλ for limit λ > ω, but such is of
  **USED as a negative check.** I searched the errata for any correction
  that touches Devlin 2.6(ii), the level sequence witness, or the limit
  hypothesis. The hits are about other matters. The return's Devlin
  reading stands uncontradicted.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote: # Bibliography for the rud route.
  **DECLINED, not used.** No new source was needed; the return's Devlin
  cites were verified in `devlin-II5.md` directly.
- `dev/literature/digest.md`: read at `:1`. Quote: # Digest: the orthodox form of the rud route, pinned from the collected literature.
  **DECLINED, not used.** It pins the `rud` route. This task and this
  review sit on the `Def` side, at the hierarchy chapter.
- `dev/literature/geology.md`: read at `:1`. Quote: # Geology dossier: set-theoretic geology sources and the five questions.
  **DECLINED, not used.** Set-theoretic geology has no bearing on a
  witness for `ApproxAt` in a stage.
