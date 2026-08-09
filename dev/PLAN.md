# PLAN: the construction registry (V=L ⊨ ZFC, then GCH)

Bedrock's goal registry. It opened in July 2026 as the plan for one milestone,
re-landing the `fol-reification` result (V=L ⊨ ZFC) as textbook-grade literate
Agda; the campaign has since grown past that milestone, and the registry grew
with it. Developer doc, English only, not translated. Work is managed by the
goal codes of §6; the MASTER status table is §11.

**Read §0 first.** It states where the work stands today in one screen.
Everything after it is either standing legislation (§3), live rules (§6.0,
§6.2), pointers to the archived planning apparatus (§2, §4, §5, §7-§10), or history:
every row records what was ruled, when, and with what outcome, and points to
where the substance lives. A row's opening word is its status; status changes
go at the front of the row.

**What is NOT here.** The EXECUTION record (how each goal went, wave by wave,
with its dispatches, measurements and refutations) lives in `dev/JOURNAL.md`;
the large goal rows below point into it. The measured engineering laws
(performance, conversion, termination, inference traps, design doctrines) live
in `dev/LESSONS.md` and BIND new code. Route memos live in `dev/memos/`. The
campaign's reconnaissance and probe reports live in `_build/*.md`, with the
agent briefs that produced them archived beside them in `_build/briefs/`.

The division is by KIND, and a fact belongs in exactly one place: a **ruling**
is a row here, an **episode** is a journal entry, a **law** is a LESSONS entry.

- **Source repository:** `choukh/fol-reification`, local sibling checkout at
  `../fol-reification`. Reference pin at planning time: commit `8b190d5`
  (2026-07-16, M2.7 build-optimization landed; the Con(AC) mathematical
  milestone itself dates to 2026-07-14). Re-pin the exact source commit in §11
  when L1 porting starts.
- **Toolchain parity:** both repos use Agda 2.8.0 + cubical 0.9; all source
  modules are `--cubical --guardedness`. No toolchain migration is needed.

## 0. Where the work stands (2026-08-06)

**The endpoint.** `L ⊨ ZFC ∧ L ⊨ GCH`, stated on the Def tower (`isL`). The
AC-only trophy that opened this registry is a waypoint on the way there, not
the endpoint (ruled 2026-08-03; the successor-document plan `[L4.3]` was
absorbed into the active campaign rather than deferred).

**The architecture (ruled 2026-08-04, `[L3.32]`).** The Def tower keeps the
trophy: no re-founding onto the rud/J tower. The GCH wing is built on a
FRESH-GENERIC Sigma-1 face, written carrier-generic from birth, which serves as
the wing's own W1 and is instantiated by W2, by the bridge, and by the
condensation chapter. The reindexed bridge (the true form of the two-tower
identification) lands at wing tail as a corollary rather than as a
prerequisite. Choice re-homes through the bridge onto the delivered rud-side
well-order, after which the satisfaction-internalization cone, the choice tree,
the Goedel trees and the rud coded cluster retire.

**What is delivered and standing.** `L ⊨ ZF` and `L ⊨ ZFC` on the Def tower
(the current choice leg still runs through the internalization cone, which the
re-home replaces); the rud engine (basis, step, tower, comprehension switch,
the producer well-order); the bridge's true direction, `isJ → isL`,
unconditionally; and the corrective stop that records the per-level
identification as the classically FALSE statement it is (Devlin VI.2.4). The
tree is `--safe` and postulate-free (LEM is a module parameter, not a
postulate, per D2), and `make check` was green at the last commit.

**What is in flight** (2026-08-06). **The mathematics is FROZEN and the only
funded work is the check-cost campaign `[L3.32-F]`.** D30 ruled it on this
measurement: the subtree D18 retires costs **0.013 s/line over 26,483 lines**
while the surviving trunk cost 0.104, and `[T87]` then removed **767 of those
seconds with six lines** that changed no mathematics. Most of the gap is
therefore engineering, and writing new chapters onto that base makes every
future contributor pay a tax that is known to be removable.

Live: `[T88]` measuring `SquareLaw`, which is **44 percent of the whole
remaining tree**; `[T89]` repairing `L.Condensation`'s two open defects and
testing whether the variable-index shape also cools it; `[T93]` reading the
trunk for more of `Bridge`'s defect by shape. `[T92]`, the `below-lim` gate,
was briefed and **stopped before it fired** because it is new mathematics.

Frozen, and not for any mathematical reason: the bridge's landing, W3, the
StepInL rewrite, W7's residue. Each resumes when the exit condition in
`dev/ledger.toml`'s `[[freeze]]` block is met. The register with the per-task
verdicts is in `dev/JOURNAL.md`, together with the execution record; the
`[L3.32]` row of §11 carries the ruling, the current status and the pointer.

**The ledger.** It is no longer written here, and that is the point. The
canonical data is [dev/ledger.toml](ledger.toml), explained by
`dev/ledger.toml`'s header comment, and **standing is measured from the tree by
`scripts/ledger.py` and written down nowhere**. Quote
`python3 scripts/ledger.py --brief` for the current standing, endpoint in both
calibers, and overage against the 25k reference figure. This replaces a
standing number that lived in prose here, was fixed at `[T25]` as a projection
rather than a measurement, and was then re-quoted unchecked for nine
dispatches while the tree moved under it (`[T55]`); D27 and the `make check`
gate now keep it honest. **Under D26 that overage is a
recorded measurement and nothing more.** The CAMPAIGN ROUTE is settled: R2',
with the trophy stated in L. How it is walked is not settled and is decided
by results, so the face route for W3 is a working direction rather than a
ruling. The 25k figure is a reference line and a best-effort compression
target: evidence may move a technique, a number alone moves nothing, and no
report may reason from an overage to a change of route. Line calibers
and the two-caliber discipline are defined in §6.2.

**The narrative frame.** The `[L6]` row of the archived route tree
(`dev/memos/route-tree.md`) declares the terminus: set-theoretic
geology and inner model theory meeting at the bedrock, with `L is a bedrock` as
the second trophy. Every asset is valued against BOTH trophies from that
section onward.

**The two standing disciplines** (owner rulings, co-equal, 2026-08-04, recorded
as D16 and D17 in §3): route decisions ignore sunk cost, and retirement is
planned from the rewrite side rather than the survivor side.

**Retired code is archived, never deleted, starting now** (D20, superseding
D14). The archive is `archive/` at the repository root, OUTSIDE `src/`, so
every gate is structurally blind to it and D2's postulate-free `--safe` claim
stays literally true of the whole checked tree. Archived files are frozen and
nothing imports across the boundary; `dev/ARCHIVE.md` records for each module
what it is, why it went, the commit where it was last green, and what would
make it worth consulting again. The infrastructure is built at the first
archival, which is `[L3.32]`'s retirement surgery.

**The closing sequence is already ruled**, and it is NOT the order the L4 rows
suggest: endpoint, then `[L7]` (archive `main`, promote the working branch, and
complete the archive), then `[L8]` (D21: a foundation refactor on the
post-archival tree, a line-by-line polish over the whole tree, and **a report
that GATES the prose phase**, where the owner adds further code-shaping work),
and only after that gate does `[L4]`'s whole-book harmonization open.

## 1. The theorem, stated honestly (DD1)

The delivered claim, and the framing every chapter keeps, is:

> In Cubical Agda (the host), the constructible sub-universe L of the HIT
> cumulative hierarchy V is a ZFC model: `L⊨ZFC : isZFCModel 𝒮ʟ` where `𝒮ʟ`
> is `𝒮ᵥ` restricted to the inductive constructibility predicate. Semantically
> this yields the **relative** consistency Con(ZF) → Con(ZFC), relative to the
> host theory (Cubical Agda with universes, informally about ZFC plus an
> inaccessible).

The campaign's endpoint extends it (ruled 2026-08-03, §0):

> The same L satisfies the generalized continuum hypothesis, `L ⊨ GCH`, stated
> internally over `𝒮ʟ`. Semantically this yields Con(ZF) → Con(ZFC + GCH),
> under the same relativization to the host.

The unqualified claims "Con(ZFC)" and "Con(GCH)" are never made, in code names,
prose, or marketing. The root chapter opens with exactly this framing (this
matches the Charter's position that rigor is independent of metatheoretic
strength).

Assumption budget of the source proof, to be preserved or improved:

- The `--safe` framework core (FOL, Reification, ZF interface, HIT-V model) is
  zero-postulate, machine-enforced by `--safe`.
- The L development rides **exactly one postulate**, excluded middle
  (`Classical.lem`). No holes, no `TERMINATING`, no `--allow-unsolved-metas`
  anywhere in the source `src/`.
- Bedrock removes even that postulate by parameterization (D2), making the
  whole tree `--safe`.

## 2. Source material survey (pointer)

The port-era survey of the source repository and its measured cost anatomy moved to [dev/memos/source-material-survey.md](memos/source-material-survey.md) ([L3.32-T113]). Its measurements remain the calibration anchor for the two-caliber discipline (§6.2) and for the simplification history (archived §10). Read it when a recon prices a lever or quotes a source-scale figure; the live plan is §0 and the goal registry is §11.

## 3. Ratified decisions
**The `DD` series, rebuilt 2026-08-09 on the two-tower bridge ruling.** The owner ruled that the whole `D` series be archived and the list rebuilt, keeping only what does not contradict the new route and what is useful to it. **The retired `D` series lives in `dev/DECISIONS-archived.md`, unedited**, and `scripts/check-rule-ids.py` resolves `D` citations against it, so every old citation in `dev/JOURNAL.md`, the memos, the briefs and the git history still means what it meant. **A number is never reused, in either series.** Each row below names the `D` row it descends from.

**WHAT WAS DROPPED, and why.** D5, the target skeleton, was drawn for the retired route and section 4 now OWES a skeleton re-derived for two towers and a bridge. D18's retirement of the internalization route survives only as history: DD5 makes that route the BENCHMARK, so its arithmetic is load-bearing and the row could not stand as written. D21, the consolidation phase, is spent. **D30, the craft freeze, is dropped and this is the one drop that changes what is ALLOWED**: its exit condition was the absolute 600 s wall that DD5 replaces, and a freeze whose gate no longer exists cannot bind; cost discipline now lives in DD5 and DD8. D31 and D32 were written for a retirement whose shape DD2 changes, and D32's revival condition, that a revival reproduce the factorization, stands directly against DD4. D33, D36, D26 and D38 survive inside DD5, DD6 and DD7 rather than as rows.

| # | Decision | Ruling |
|---|----------|--------|
| DD1 | The theorem, stated honestly | As in section 1: V=L ⊨ ZFC, relative consistency, relative to the host, and never an unqualified "Con(ZFC)". The campaign's endpoint is the SAME L satisfying GCH, stated internally, giving Con(ZF) → Con(ZFC + GCH) under the same relativization; "Con(GCH)" is likewise never claimed unqualified. **Descends from D1, unchanged.** |
| DD2 | **THE ROUTE: two towers and a bridge, and BOTH trophies on it.** | **Ruled 2026-08-09 by the owner.** Build the L tower and the J tower, J through rud, and the bridge between them. Prove `L ⊨ AC` and `L ⊨ GCH` on that bridge. Both trophies, one route. The trophies stay stated in L, so no re-founding onto J is ordered. **This row is the route and every other row serves it. Descends from D39, and absorbs D18's surviving half.** |
| DD3 | The bridge is two-directional | The bridge delivers BOTH directions of the two-definition identification. The one-way variant is not the deliverable. DD2 names the bridge and this row is its content. **Descends from D19, unchanged.** |
| DD4 | **MAXIMUM REUSE is the architecture's objective, and the line total falls out of it.** | **Ruled 2026-08-09 by the owner, as the route's CORE constraint, which is architectural and not arithmetic.** Follow the textbooks to the best route and architecture, and maximize the code the two proofs share. **The total is not to be pursued by splitting, re-bucketing, or any move that lowers reuse.** The question is asked at three named moments: when a recon is dispatched, when a build is dispatched, and when a route is planned. A stop-line is never a reason to write fixed: say so and stop for a re-price. **Descends from D29, promoted from a practice to the route's governing principle, and from D39's core constraint.** |
| DD5 | **THE TWO QUANTITATIVE CONSTRAINTS are RELATIVE, and NEITHER BINDS until it is clear.** | **Ruled 2026-08-09 by the owner.** Both are taken at the DOUBLE-trophy endpoint and both are measured against the internalization route at ITS double-trophy endpoint. (1) LINES: this route's total must not exceed internalization's. (2) TIME: this route's total build time must not exceed internalization's. **By the owner's own instruction a benchmark that is not clear is to be made clear first.** Today NEITHER is. The line benchmark has one pass, `[T257]` at 25,485-28,258 naive, carrying a declared weak point worth 4,238-5,218, which is a fifth of the band and can decide the constraint by itself. **The time benchmark does not exist at all**: nobody has measured the internalization route's build time, its AC half is measurable on `main` in one run, and its GCH half was never built and can only be projected. **Descends from D39's quantitative half; replaces D26's reference line, D36's per-trophy cap and D30's absolute 600 s wall as the binding figures.** |
| DD6 | The caliber: the DOUBLE-trophy endpoint, in lines and in seconds | A size figure is the count of non-blank lines inside ` ```agda ` fences over git-tracked `*.lagda.md` under `src/`. **The PRIMARY figure is now the double-trophy endpoint**, and `scripts/ledger.py --brief` is its only admissible source. The per-trophy split and the AC cap survive as DIAGNOSTICS, useful for reading where content sits and not for deciding. The deletion test survives UNCHANGED, because it is the structural test that keeps the accounting honest whichever figure binds. **Descends from D33 and D36, both demoted.** |
| DD7 | Every estimate carries two calibers, and an estimate is a measurement | State each projection twice: naive, the component sum on delivered comparables, and calibrated, with this project's measured underestimation, about 1.3x where a probe or comparable reaches and 3x where only a survey does. **An estimate is a measurement, not a decision procedure.** Record an overage in both calibers, say plainly that it is an overage, and work it down where real compression exists. **Descends from D26's method, which is all of D26 that survives: its bar on a line count reopening the route is REVERSED by DD5.** |
| DD8 | Every block is gated before it is funded | Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work. A green gate moves the term from the 3x class to about 1.3x and lowers the top of the band. **A build brief that cannot name its widest unmeasured term, and the probe that measures it, is not ready to send.** Nobody commits a probe. **Descends from D22, unchanged, and it now serves DD5, whose benchmarks are exactly unmeasured terms.** |
| DD9 | Classical boundary | No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter; the whole tree is `--safe`. The archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree. A materially worse performance projection escalates to the owner. **Descends from D2, unchanged.** |
| DD10 | Macros and generated proof | **Descends from D13, unchanged; see the archived text.** |
| DD11 | Naming hygiene, and prose | **Descends from D7 and D6, unchanged; see the archived text and `dev/STYLE-i18n.md`.** |
| DD12 | Sunk cost is not decisive | "We already paid for it" never decides a question, in either direction. **Descends from D16, unchanged, and DD2 is itself an instance: the route changed after a year of work.** |
| DD13 | Retirement is planned from the rewrite side | A consumer does not prove that a chapter must stay. First price the ideal form of the content, written fresh today. Then compare. **Descends from D17, unchanged. It now has a second job: DD4 asks the same question of every existing chapter, since content that cannot be shared may be cheaper rewritten than adapted.** |
| DD14 | The archive regime: archive, never delete | Retired code goes to `archive/` at the repository root, outside `src/`, so every gate is blind to it by structure. Archived files are frozen and nothing imports across the boundary. `dev/ARCHIVE.md` records what each module is, why it left, where it was last green, what it did right from measurement, and what would make it worth a second look. **Descends from D20. It now also governs `dev/DECISIONS-archived.md`, which holds the whole retired `D` series.** |
| DD15 | The ledger is re-measured at every return that could move it | **Descends from D27, unchanged.** |
| DD16 | A full cold typecheck runs in the background, never in the foreground | **Descends from D28, unchanged, and DD5's time constraint makes the measurement itself more load-bearing, not less.** |
| DD17 | **The standing dispatch order: slots stay full until BOTH trophies are proved inside both constraints.** | Amended 2026-08-09 from an AC-only terminus. An idle agent slot is a defect: a slot stays empty only when a real block stops every remaining task, and an audit is not a reason to leave one idle. **Descends from D37 and D23.** |
| DD18 | Goal management, and revisability | **Descends from D9 and D11, unchanged; see section 6.0 and the archived text.** |
| DD19 | Every rule has one home, chosen by its enforcer | A rule that no machine enforces must name its enforcement point. Nothing is canonical twice. **Descends from D24, unchanged.** |
| DD20 | AGENTS.md is guarded: no edit lands without the owner's ruling on the diff | **Descends from D34, unchanged.** |
| DD21 | Terminology is settled by a two-agent pipeline; the owner reviews only what fails it | **Descends from D35, unchanged.** |
| DD22 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out. No in-file SPDX headers. **Descends from D4, unchanged.** |

## 4. Target skeleton (OWED a re-derivation for DD2)

The D5 target skeleton, its port-era diagram and the rename ledger moved to [dev/memos/target-skeleton-d5.md](memos/target-skeleton-d5.md). What stays binding from D5: the part level (Base, FOL, ZF, V, L, Landmarks) is fixed, below-part layout is provisional until the [L3.10] re-layering, and the authorities for what `src/` contains are `src/README.md` (the master symbol table) and `src/Everything.lagda.md` (the reading catalog), not this section. Read the memo when a rename's history or the port-era layout is needed.

## 5. Working mechanisms (pointer)

The mechanisms this section carried moved to their enforcers ([L3.32-T113]): the LEM parameterization convention is `dev/STYLE-agda.md` section 1 (the ruling is D2 in §3); the two-catalog doctrine and the named-hypothesis debt form are in `dev/STYLE-agda.md`; probes and gates are `AGENTS.md` and `dev/LESSONS.md` D-1; orchestration is `dev/ORCHESTRATION.md`. The port-era mechanism history (the Frontier record, its re-cuts, construction order) moved to [dev/memos/working-mechanisms.md](memos/working-mechanisms.md); the Frontier's deletion is recorded in the D8 struck row of `dev/JOURNAL.md` and in rows L2.4 and L4.0 of §11.

## 6. Route tree (DD18)

### 6.0 Coding rules (lightened from the source's ROUTE-TREE §0)

1. **Code form** = `L<goal>.<subgoal>…`, dotted decimal, rooted at L0 to L6.
   Always written in brackets in prose and commits (`[L2.3]`), which also keeps
   codes visually distinct from the `L/` module namespace and from `L⊨ZFC`.
2. **Codes are identity, not order.** Sibling numbers carry no temporal or
   priority meaning; scheduling lives in the status field and the gate
   conditions.
3. **Immutable and append-only.** A code, once assigned, is never renamed,
   deleted, reused, or renumbered. New work takes the next free number under
   its parent. A goal that gets re-stated or re-split gets a **new** code; the
   old one is marked SUPERSEDED with a pointer. **Carve-out (owner ruling,
   2026-07-25):** a branch whose codes have *all* never left PLANNED, with no
   work committed against any of them, may be renumbered once by explicit owner
   ruling; the old-to-new map is recorded in §11. Exercised once so far, for
   L3, on the day the reduction levers were registered; the carve-out is spent.
4. **What gets a code:** a goal with its own success criterion (a chapter
   cluster, a spike, a review, a piece of legislation), or a dispatched task
   (a briefed sub-agent assignment under a parent goal). Individual lemmas
   and modules are artifacts hanging under a code, not codes themselves.
5. **Status vocabulary:** PLANNED, ACTIVE, DONE, PARKED (viable but shelved,
   revivable), SUPERSEDED (points to successor), ABANDONED (with reason).
   Status changes are dated and updated in place; history lives in git.
6. **Bookkeeping:** register a code in §11 *before* starting the work; update
   the §11 row in the same commit that changes a goal's status. New codes
   discovered mid-work are registered immediately, not backfilled.
   **One-time reconciliation (2026-08-06, `[T111]`):** the dispatched-task
   codes `[T1]` through `[T110]` were created before this section recognized
   dispatched tasks, so they are backfilled into the task index once, as a
   closed reconciliation of existing history. This is a single exception
   with no force as precedent: rule 6's no-backfill requirement binds every
   future code, and the reconciliation pass is never repeated.
7. **Dispatched tasks carry extended codes.** A dispatched sub-agent task is
   coded `L<goal>.<subgoal>-T<n>` under the parent goal it serves, for
   example `[L3.32-T101]` under `[L3.32]`, with `n` the next free number in
   the parent's task series. The code is written in brackets wherever the
   task is named, exactly like a goal code, and obeys rule 3 (immutable and
   append-only) like any other code.
8. **The task index: one row per code, rows stay short.** Every dispatched
   task code occupies exactly ONE row in the task index in §11, added in the
   same commit that registers the code (rule 6). A row carries the code, a
   short title, a verdict in a few words, and a pointer to the detail;
   nothing else. **No row may exceed 200 characters**, measured as the full
   row line from the leading `|` to the trailing `|`.
   `scripts/check-task-index.py` enforces both one-row-per-code and the cap.
   The cap is sized for a one-line scannable entry: code (about 11), short
   title (about 70), verdict (about 30) and pointer (about 50) fit inside
   200, while the failure this rule prevents, the 12,633-token cell that hid
   the T1-T110 verdicts, is far beyond any single line. A row that outgrows
   the cap means the detail has not moved to `dev/JOURNAL.md` or the report,
   where it belongs.

### 6.1 The tree (pointer)

The goal tree's full statements, gates and the L3 execution phases moved to [dev/memos/route-tree.md](memos/route-tree.md). What stays live: the coding rules (§6.0), the two-caliber discipline (§6.2) and the status registry (§11), which is the authoritative one-row-per-goal index. The L6 narrative frame is summarized in §0 and detailed in the memo. Read the memo when a goal's statement or gate is needed.

### 6.2 Caliber and the two-caliber discipline

Every size figure in this registry, unless it says otherwise, is **non-blank
lines inside ` ```agda ` fences**. File lines, blank lines and prose are not
counted; a chapter's file is typically about twice its caliber.

Projections are stated in **two calibers**, and a projection given in only one
is incomplete:

- **Naive**: the bottom-up component sum, each component anchored on a
  delivered comparable or a probe measurement.
- **Calibrated**: the naive figure with this project's own measured
  underestimation applied (LESSONS D-6). The split in force since 2026-08-04:
  a component anchored by a PROBE or a delivered comparable carries about
  x1.3; a component that only a census could reach carries x3.

The point of the split is that it prices ignorance rather than pessimism, so
**a probe converts money**: each D-1 gate that goes green moves its component
from the x3 class to the x1.3 class and narrows the band. That is why gates are
designed with the estimate rather than after it, and why a wide unprobed term
is the first thing a recon is asked to name.

The record to keep in mind when reading any band here: down-corrections in this
campaign have landed on terms a probe could reach, and up-corrections on terms
only a census could reach.

## 7. Build constraints (pointer)

D10, which used to carry these constraints, was struck on 2026-08-05 because each constraint is now enforced where it fires. The numbered rows below are routing rows; the full original text is in [dev/memos/build-constraints.md](memos/build-constraints.md), and the older §7.5/§7.6 budgets cited by D13 are rules 5 and 6:

1. The trusted gate is one invocation, `agda src/Everything.lagda.md`: the build machinery (`Makefile`, [scripts/README.md](../scripts/README.md)).
2. Parallelism is a warm-up layer outside the trust base: the build config.
3. The import-closure audit: `scripts/check-tree.py` closure, [scripts/README.md](../scripts/README.md).
4. The dependency manifest is generated, never committed: the build config.
5. The cold-check budget and the seconds dimension: the ledger (`dev/ledger.toml` [timing] and [[hot]]) and the return checklist, `dev/ORCHESTRATION.md` section 6 step 2.
6. Per-module discipline (heap caps, conversion-blowup triage): `AGENTS.md`, `dev/ORCHESTRATION.md` section 2, `dev/LESSONS.md` C-12, and `scripts/check-timing.py` at every return.
7. Serial fallback stays available: the build config.
8. Reference machine and `-jN` defaults are documented in the build config.

## 8. Process tensions and their resolutions (pointer)

The T1-T6 tension register and its relief valves moved to [dev/memos/process-tensions.md](memos/process-tensions.md). D11's mechanisms are stated in the D11 row of §3; the live relief valves are the L0 standing track (§6.0), the fixed part level (D5), and the L4.1 harmonization (§11).

## 9. Risks and mitigations (pointer)

The dated risk register moved to [dev/memos/risks-mitigations.md](memos/risks-mitigations.md). Each mitigation is a standing rule with its own home: D1 and D26 in §3, `dev/LESSONS.md` D-1/D-6/D-10, the §6.0 rules, and the return checklist in `dev/ORCHESTRATION.md` section 6.

## 10. Candidate simplification register (pointer)

The S1-S18 register moved to [dev/memos/simplification-register.md](memos/simplification-register.md), with its statuses brought current to the `[L3.32-T8]` verdicts: S13 and S15 shipped, S14 and S16 reverted at their gates, S17's probe red, S18 deferred. Live tracking of the deferred row is `dev/ledger.toml`'s [[excluded]] table.

## 11. MASTER status table (live)

One row per goal code; update the row in the same commit that changes the
status (§6.0 rule 6). Dispatched-task codes are indexed separately below,
one row per code (§6.0 rules 7 and 8). Bookkeeping lines follow the table.

| Code | Goal | Status |
|---|---|---|
| L0 | Legislation (standing track) | ACTIVE (initial set gate cleared by owner 2026-07-16) |
| L0.0 | STYLE-agda.md initial edition | DONE 2026-07-16 |
| L0.1 | First glossary batch | DONE 2026-07-16 |
| L0.2 | LEM parameterization spike | DONE 2026-07-16, verdict green (details below) |
| L0.3 | Agda linter (import necessity) | DONE 2026-07-16 |
| L1 | Root and trunk skeleton | ACTIVE 2026-07-16 |
| L1.0 | Skeleton, src/README, agda-lib flag, source pin | DONE 2026-07-16 |
| L1.1 | Port Base/ | DONE 2026-07-16 |
| L1.2 | Port FOL/ core | DONE 2026-07-17 (four chapters: Syntax, Structure re-cut from ZF/, Semantics, Renaming) |
| L1.3 | Port FOL/Reification/ | DONE 2026-07-18 (five chapters, consumption-pruned; six deferrals in the ledger) |
| L1.4 | Port ZF/ | DONE 2026-07-18 (`ZF.Model` with the Ceiling compactness prose folded in; `Encoding`/`Coding` deferred by consumption audit; reading-order re-cut executed) |
| L1.5 | Port V/ | DONE 2026-07-18 (`V.{Hierarchy, Smallness, Model}`; `Def`/`Sat`/`Coding` and `InnerSmall` deferred to `[L2.x]` by consumption audit; `V⊨ZF`/`V⊨ZFC` delivered) |
| L1.6 | Port L.Constructible | DONE 2026-07-18 (`V.Definability` un-deferred as prerequisite; `∈-induction` re-homed to `V.Hierarchy`; `InnerSmall` added to `V.Smallness`; `isL` is the Lset-form predicate, `𝒮ʟ` delivered) |
| L1.7 | Frontier + root L.Model | DONE 2026-07-18 (Frontier: 11 fields; root proves extensional/regularity outright and assembles L⊨ZF/L⊨ZFC; field count was the progress meter) |
| L1.9 | Diaconescu + single-hypothesis V⊨ZFC | DONE 2026-07-18 (`Base.Choice` with `choice→lem`; `V⊨ZFC-fromChoice`; fourth landmark) |
| L1.8 | Landmarks + Everything order | DONE 2026-07-18 (owner rulings 2026-07-18: Landmarks reads **first**; the zero-consumer chapters read **last**; re-cut same day: Reification namespace = {Base, Combinators, Certified}; `ZF.Model`→`ZF`, `V.Definability`→`L.Definability`) |
| L0.4 | Two-catalog doctrine (reading vs structure) | DONE 2026-07-18 |
| L0.5 | Register `Ord` as an abbreviation (STYLE §3) | DONE 2026-07-25 (opened during L2.0; `IsOrd` had shipped at L1.6 unregistered) |
| L2 | Axiom branches | SUSPENDED 2026-07-25 after L2.1, by owner ruling: phase B of L3 runs first (§6.1). Resumed at L2.2; closed 2026-07-31 with `[L2.4]` |
| L2.0 | Basic axioms | DONE 2026-07-25 (`L.Ordinal` + `L.Axioms.Basic` + `L.Constructible` additions; extensionality and regularity re-homed from `L.Model`; Frontier 11 fields → 8; no `lem`, the whole goal is constructive) |
| L2.1 | Infinity | DONE 2026-07-25 (`L.Axioms.Infinity` + `L.Ordinal.Stages`; Frontier 8 → 4). The chain is constructive, the collection step is not: it needs `ω ∈ L`, hence `ord∈Lset-suc`, hence trichotomy |
| L2.2 | Separation and Replacement | DONE 2026-07-25 (resumed after L3.14 closed). Landed: `L.Stage`, `Relabel`, `L.Axioms.Separation`, `L.Reflect`, `L.ReflectFo`, `L.Axioms.Full`. **Frontier 4 fields → 2**; only the power set and choice remained. Six source chapters became three |
| L2.3 | Power by bounding the constructible subsets (re-scoped 2026-07-27 from "Power via Condensation") | **DONE 2026-07-27.** `L.Axioms.Power`, **79 lines of Agda**, against the source's ≈185 across three chapters. **Condensation is not used.** Assumption bill unchanged: `LEM (ℓ-suc ℓ)` alone. **Frontier 2 fields → 1** |
| L2.4 | Well-order and Choice trunk | **DONE 2026-07-31: THE FRONTIER IS EMPTY AND DELETED** (details below). About 5,900 lines across thirteen chapters against an audit band of 1,900 to 3,150 |
| L3 | Technical layer (big lever first, D12; renumbered 2026-07-25 into execution order) | ACTIVE 2026-07-27. Re-inventoried after the internalization finding: six goals closed as clutter, three new codes registered for unowned obligations. Open children as of 2026-07-29: the container itself, `[L3.1]` (standing), `[L3.10]` (planned). `[L3.28]` and `[L3.29]` are open at the bottom of the L3 sequence |
| L3.0 | Internalization theorem for L-recursion (S5) | **DONE 2026-07-28, without exception**: theorem delivered at 99 lines; verdict green; the instance half (satisfaction) closed the same day. Record of the earlier state in the bookkeeping below |
| L3.0.0 | Design memo (single) | SUPERSEDED 2026-07-25 by L3.0.3 + L3.0.4; never started |
| L3.0.3 | Subsumption probe, source-reading only | DONE 2026-07-25, memo delivered; verdict amber (route alive, projection corrected) |
| L3.0.4 | Theorem statement in Bedrock's idiom | DONE 2026-07-25, memo delivered; prerequisite narrowed to `BoundedFo` + the closure engine. **Two amendments from the phase-C re-evaluation**: stage 7 is `[L3.0.5]`, not `[L3.2]`; `reads`'s `isL` certificates must be sealed where built |
| L3.0.5 | Finite families at a stage (stage 7) | DONE 2026-07-25 (`finSetL` in `L.Axioms.Basic`; registered on the phase-C re-evaluation) |
| L3.0.1 | Two-instance proof of concept | **RE-POINTED 2026-07-26** to satisfaction as the instance. **Theorem DONE 2026-07-26**: `L.Recursion` complete at 99 lines. **INSTANCE HALF DONE 2026-07-28.** Satisfaction is a `Recursion`: `L.Coding.Satisfaction` is 74 lines and checks in 9 s, the whole cone 4,034 lines across ten chapters, every one under 2 s. The three things it did not predict (environment as an interface; twelve clauses stated twice; five conversion walls) are in the bookkeeping and in `dev/LESSONS.md` |
| L3.0.2 | Verdict and rollout ruling | DONE 2026-07-26, memo [memos/L3.0.2-verdict.md](memos/L3.0.2-verdict.md). **Green, for a different reason than D12 expected**: the 43k remaining becomes a projected 3,000 to 6,400; the `L` side lands at 6,500 to 10,000 total. L3.5 to L3.7 proceed as instantiations; L3.4 does not open |
| L3.1 | Transition-layer sweep (S9) | **STANDING; accumulated drop list EXECUTED 2026-07-29: −529 agda lines** (`L.Coding.{Entry, Tagged, Length, Recursion}` and the whole `FOL.Reification` namespace, seven modules with zero importers, verified by grep; `src/` 11,872 to 11,336). Closes with `[L3.10]`. First drop recorded at `FOL.Coding` (`⌜⌝-inj`, no consumer) |
| L3.2 | `reify!` industrialization (S6) | **CLOSED, REJECTED 2026-07-27; nothing further is owed and no later goal may reopen it under this code (§6.0 rule 3).** Net +9 lines over the two modules the plan rated best (`Entry` 78 → 56, hub `Base` 187 → 218); `L.Coding.Model` went +25% to +33%; both D13 tests fail. Source commits reverted; the measurement is the deliverable. Re-open trigger: a congruence family hand-written a third time with no combinator available, or the traversal-dense share passing 20% |
| L3.3 | Coding cluster (as originally scoped) | SUPERSEDED 2026-07-25 by L3.14; `FOL.Coding` and `V.Coding` landed under it and stand |
| L3.16 | The object language over the model | **DONE 2026-07-28** (was ACTIVE 2026-07-26). `L.Coding.Model` 1,289, `L.Coding.InL` 330 at close (against 647 and 52 quoted while open; growth is normal). Audited clause by clause: 14 proposed, 11 confirmed, 6 distinct defects, two fatal. Details in bookkeeping |
| L3.15 | Re-base the coding readers onto `S` | **DONE 2026-07-26, and it is not a re-base.** `L.Absoluteness`, **34 lines**: one instantiation of `Relabel` at the bound "constructible", and a four-step transfer chain with no induction of its own |
| L3.14 | Coding substrate: the Δ₀ code readers | DONE 2026-07-25. Seven chapters: `L.WellOrder.Base`, `FOL.Coding`, `V.Coding`, `L.Coding.{Base, Environment, Tagged, Length, Entry}`. The source's `SatCert*` split by subject rather than by session |
| L3.11 | Per-tag clause bundle (S10) | **ABANDONED 2026-07-27 on a measurement, not a projection.** The only instance ever written answers **no**: `L.Coding.Model`'s twelve clauses factor through two shared frames plus `extAt`, not a per-tag record |
| L3.12 | Stage-indexed theorem, tier 2 (S11) | **ABANDONED 2026-07-27.** Tier 2 existed because `Order*` sat outside tier 1's complexity boundary, and that boundary dissolved. Re-open under a new code only if a concrete instance fails to fit |
| L3.13 | Partial-certificate variant, tier 3 (S12) | **ABANDONED 2026-07-27.** Its subject (the `(C,S)`-pair partial certificate) was retired by the `[L3.0.1]` design change (slot as index, table as value); the circularity rationale was itself adjudicated false (the mechanism is witness-locality) |
| L3.4 | Scaffolding parameterization (S3) | **ABANDONED 2026-07-27.** Its gate is "opens only on a red `[L3.0.2]`", and that verdict returned **green**. The condition is not unmet, it is impossible |
| L3.5 | Satisfaction cluster | **DISSOLVED as a cluster 2026-07-27.** The genuine residue moved to `[L3.19]`; the unruled `L.Recursion` `Definition` shipped at `[L3.0.1]` as `L.Coding.Satisfaction` |
| L3.6 | Closure cluster | **DISSOLVED 2026-07-27.** Not one member survives as closure work; the "closure engine" sense shipped as `L.Axioms.Basic.defSet→isL`. Strike `L/Closure/` from §4 |
| L3.7 | Certificate cluster | **CLOSED, SCOPE RE-ATTRIBUTED, 2026-07-28.** Every source it named has moved; nothing measurable remains; the code is closed rather than planned |
| L3.8 | Dispatch-grid generation (S8) | **ABANDONED 2026-07-27, premise spent.** The Δ₀ obligations that forced grids are gone, and the one real grid (`⌜⌝-inj`, 132 clauses) was dropped by consumption audit at `[L3.1]` |
| L3.9 | Transport and cast solver (S7) | **ABANDONED 2026-07-27.** The inherited 3,300-site figure is source-side; Bedrock's whole `src/` has **456** sites, so the lever is an order of magnitude smaller than registered. A future need returns as a new code |
| L3.10 | Re-layering review of L/ | PLANNED. Boundary against `[L3.28]` ruled 2026-07-31: split by **purpose, not by file**; `[L3.28]` owns quantity, `[L3.10]` owns arrangement that serves no compression; **`[L3.28]` runs first**. `[L3.1]` still closes with this row |
| L3.17 | The ambient environment set exists | **DONE 2026-07-27 at 229 lines** (`src/L/Coding/EnvSet.lagda.md`, three importers), against the 60-to-120 estimate. **This row read PLANNED until 2026-07-28** while the unit table recorded it DONE; the status lives here and the unit table defers to it |
| L3.18 | The parameter alphabet (was "the parameter bridge") | **CLOSED 2026-07-29.** Its one deferred obligation (a spike on whether an absolute code set is needed) is answered by `[L3.19]`'s audit: no. **RULED 2026-07-27**: take the third option, widen the satisfaction table's alphabet and move neither representation, about 20 net code lines; the fork was mis-framed (the two options are nested, not alternatives) |
| L3.19 | The L-hierarchy internalized | **DONE 2026-07-29 at +490 lines** (`L.Coding.Sequence` 135, `L.Hierarchy` 354, assembly 1), against the re-scoped 370 to 650. `Lset-only`/`Lset-defines` and `hierL`; the fork was ruled 2026-07-29 option (ii), generalize in place. The last mathematical content on the `hasChoiceL` chain before `[L2.4]` |
| L3.20 | Subformula closure, and the first measurement of the lever | **DONE 2026-07-27** (+631 end-to-end: `L.Coding.Closed` 163, `L.Coding.Recursion` 62, `L.Coding.Model` +189, `L.Coding.InL` +208, `L.Recursion` +9). `L.Recursion` has an importer for the first time; the design finding: the value is the least set containing the key and closed under subcodes |
| L3.21 | The code set at a stage, in `L`, with an object predicate | **DONE 2026-07-28 at 670 lines across four chapters** (`L.Coding.Descent` 44, `Shape` 334, `Recover` 190, `CodeSet` 102), plus `rank-mono` re-homed into `L.Rank` (+18), for a measured tree delta of **+692** against the 100-to-250 estimate: **2.7x to 6.9x**. The closing entry records causes; the constants conjunct is owed to `[L3.24]` |
| L3.22 | `⌜⌝`-injectivity at a fixed arity | **REGISTERED 2026-07-27** (the return of the obligation `[L3.1]` dropped by consumption audit, under a new code). **DONE the same day at 100 lines, 1.2 s**: the grid is avoidable, the constructor is recoverable from the tag (`Match`/`matches`), so the 132 off-diagonal `clash` cases are not written at all |
| L3.23 | Satisfaction uniform in the carrier | **REGISTERED 2026-07-28** (unowned, found by the post-`[L3.0.1]` inventory). **DONE 2026-07-28 at +124 net code lines**: `L.Coding.Uniform` (124 lines), plus +20 in `FOL.Manipulation.Relabelling` and −20 in `L.Coding.Bridge`. The overturn did not fire: `Table`/`Slot`/`Sound`/`Unique` have zero edited lines |
| L3.24 | The constants bound: codes over a carrier, not over the model | **REGISTERED 2026-07-28** (fourth time the unowned-prerequisite failure mode was caught; first inside a goal already declared done). **DONE 2026-07-28 at +36 net lines**: the alphabet target is cheaper than the model target; `Codes-spec : (x ∈ˢ Codes) ≡ IsKeyOver x` closes the round trip as an equality |
| L3.25 | The subcode-closed code set at every arity | **REGISTERED 2026-07-28** (unowned; `[L3.23]`'s actual domain). **DONE 2026-07-28 at +91 net lines** (`L.Coding.CodeSet` 118 to 201, `L.Coding.Closed` 163 to 171). The arity conjunct is `x`'s first component lying in omega; the brief's `∈#-elim` was corrected by the probe |
| L3.26 | The satisfaction bridge | **REGISTERED 2026-07-28** (unowned; the adequacy that makes internalization mean anything). **DONE 2026-07-28 at 308 lines** (`L.Coding.Bridge`): `Sat-spec`, `Sat-out`, and **`defSet-Sat`** close the connection to the definable powerset. The probe corrected the route: the right-hand side is the **inner semantics of the same module application `defSet` is built from**, not `relativize`'s reading |
| L3.27 | The definable powerset at a variable carrier | **DONE 2026-07-29 at about +480 lines** (`L.Coding.Powerset` 400 new, plus the two in-place generalizations), against 405 to 735. Registered 2026-07-29 by the `[L3.19]` route audit; the graph binds the stage, so the description is at a carrier that is a bound variable. Probe green at 147 lines and 1.9 s |
| L3.28 | Compression pass over `L/` (widened 2026-07-31 to all of `src/`) | **REGISTERED 2026-07-31 by owner request**, runs **before** `[L4]`. Candidate (3) DONE 2026-07-31 by deletion (−74 Agda lines: `L.Coding.Satisfaction`). **SURVEYED the same day**: baseline 17,492 non-blank Agda lines; no module-level dead weight; levers (a)-(g) sum to **−755 conservative, −1,486 optimistic**, landing 16.0k to 16.7k; the 10k target is not reachable by compression. **RESOLVED 2026-07-31: the ruling is C (D15)**; the gate dissolves, the fork executes as `[L3.29]` on `godel-route`, and this row closes when `[L3.29]` lands or aborts. Full record in the bookkeeping below |
| L3.29 | AC by the operations calculus (route C), then the B pivot | **SUPERSEDED 2026-08-02** by the `[L3.30]` re-architecture, after delivering route C's operations calculus and then the B (kinded closure) pivot on top of it. The AC route was ruled by D15 on the `dev/memos/L3.28-ac-route.md` numbers; the B pivot by `dev/memos/L3.29-b-pivot.md`. Nothing retired at the time: every route's code stayed in place pending the `[L3.30]` ruling. Execution record: `dev/JOURNAL.md`. |
| L3.30 | The rud re-architecture (exploratory) | **CLOSED 2026-08-02, ADOPTED IN FULL.** The exploratory re-architecture: posed completion-state-blind (the first application of what became D16), it surveyed the literature, priced the routes, and recommended the rudimentary-function trunk with `Def` keeping its satisfaction face and the equivalence as a named theorem. All four ruling questions of `dev/memos/L3.30-rud-route.md` section 8 were answered yes. The build executes as `[L3.31]`. Execution record, including the literature sweep and the advance-wave probes: `dev/JOURNAL.md`. |
| L3.31 | The rud build, then the architecture fork | **CLOSED 2026-08-04.** Two phases under one code. The BUILD delivered the rud trunk in waves R1 to R5 (basis, step, tower, realization, the comprehension switch, the producer well-order) and then the bridge campaign, whose kernel left the identification conditional on one named hypothesis. The FORK INVESTIGATION that followed began when the tripwire fired and ended when that hypothesis was found to be classically FALSE (Devlin VI.2.4): eleven reconnaissance and probe tasks priced every repair and every architecture, in both calibers and in ideal form, and the owner ruled the configuration that executes as `[L3.32]`. Three durable outcomes: the corrected identification story, the two-caliber discipline (section 6.2), and D16. Execution record: `dev/JOURNAL.md`. |
| L3.32 | The L-trophy build (the ruled configuration) | **RULED AND ACTIVE 2026-08-04** by D18. The Def tower keeps the trophy; the wing rides a fresh-generic Sigma-1 face; the reindexed bridge lands at wing tail as a corollary; choice re-homes through it; the internalization cone, the choice tree, the Goedel trees and the coded cluster retire. Wave 1 (the R4 corrective stop, the face probe, the choice re-home probe, the retirement design recon, the W7 scoping) has returned; wave 2 builds the face chapter, then W2, then W3 and W5 in parallel, then the bridge, the re-home, the retirement surgery and W7. The check-cost campaign (D30's freeze, and the work that lifts it) and the current gates run in the `[L3.32-F*]` rows below. **The retirement surgery ARCHIVES rather than deletes** (D20, in force from 2026-08-04) and builds the archive infrastructure on its first use. Standing and endpoint figures are in section 0. Execution record, with the wave-by-wave measurements: `dev/JOURNAL.md`. |
| L3.32-F | **The check-cost campaign** (D30's freeze, and the work that lifts it) | **ACTIVE 2026-08-06**, inserted into the route by owner ruling as the ONLY funded work until its exit condition is met. **The finding:** the retiring subtree costs 0.013 s/line, the surviving trunk 0.104, and `[T87]` removed 767 s of that gap with six lines, proving most of it engineering. Exit: measurement-complete, with no projected number, per D30. **THE ROUTE, WITH EVERY BRANCH DECIDED IN ADVANCE, IS `dev/memos/L3.32-burn-the-boats.md`.** The campaign's execution record is in `dev/JOURNAL.md`. |
| L3.32-F0 | **Settle the caliber**, before any threshold is argued | **DONE 2026-08-06, and CORRECTED the same day, which is itself the entry's lesson.** The owner's ruling: how much of the cost is really mathematics is a per-OBLIGATION question, not a per-line one, and pinning that caliber comes before arguing any exit condition. `scripts/obligations.py` counts obligations mechanically. **THE CORRECTED RESULT, counting obligations at any depth:** the two trees write **4.9 against 3.9 lines per obligation**, which is nearly the same density, and cost **0.074 against 0.277 s per obligation, a real 4.2x**. **ADVERSARIALLY REVIEWED 2026-08-06 by `[T95]`, dispatched by the owner precisely because the author of a measurement is its worst reviewer. It found seven defects and they are fixed.** **All of it is recorded in the ledger's `[caliber]` block rather than resolved, because resolving it quietly is exactly how this went wrong three times.** The defect record and the ledger recovery are in `dev/JOURNAL.md`. |
| L3.32-F1 | Seal `SquareLaw`, the single largest cost in the tree | **IN FLIGHT** as `[T88]`. 856 s over 907 lines, **0.94 s/line against a tree average of 0.05**, and 44 percent of everything left. `[T86]` diagnosed it as the I-4/I-5 class, stating memberships at concrete tower positions, but **diagnosed without measuring**, so the brief orders a per-definition profile first and a fix measured in a scratch copy before it is proposed. Stop-line 60 lines against Bridge's six; export-preserving, or it is a different and larger piece of work. **This one row carries more of the exit condition than every other row combined.** |
| L3.32-F2 | Cool `Condensation` while repairing it | **DEFECTS FIXED, COOLING REFUTED.** `[T89]` returned. **THE COOLING IS REFUTED, and it is a real measurement against `[T86]`'s diagnosis: 203.3 s after against 203.5 s before, unchanged within noise.** **`[T106]` MEASURED IT AND REFUTED `[T104]`. `[T96]`'s ORIGINAL VERDICT STANDS.** **THE PRICED REFUSAL IS ITSELF THE DELIVERABLE**, and it closes D30's exit condition (2) for this module. **One lever stays open and needs the owner's word:** `[T106]`'s B1, the export-changing `Crossing` parameterization, **minus 61.3 s for plus 5 lines**, with every other signature byte-identical and **zero tree consumers** of any crossing name confirmed by `rg`. It needs a ruling only because the changed statement is what D5 and W1' will later consume. The full record of `[T89]`, `[T96]`, `[T104]` and `[T106]` is in `dev/JOURNAL.md`. |
| L3.32-F3.1 | Sweep the tree OUTSIDE the three theorems against the ORIGINAL playbook | **DONE 2026-08-06 by `[T100]`, at the owner's instruction that the internalization route's experience was already documented and the campaign kept re-deriving it. It was: `dev/LESSONS.md` carries `Rule 1` through `Rule 20`, sixteen rules written DURING that build, each from a measured wall, plus `P-i`'s imported decision tree with twenty source cases.** **THE RESULT IS A CLEAN BILL AND THAT IS THE FINDING: exactly ONE live violation in the entire sweep.** **THE STANDING LESSON, now the third instance today: a measured cure does not transfer to a new site by analogy.**  The rule-by-rule record and the refutation by measurement are in `dev/JOURNAL.md`. |
| L3.32-F3 | Profile the 697-second tail: floor, or three more Bridges? | **ANSWERED 2026-08-06 by `[T93]`, read-only, without spending an Agda slot: the tail is the FLOOR for the six-line-seal class.** **The consequence is that F1 and F2 carry the exit condition by themselves**, which is exactly why D30's condition is now measurement-complete rather than a projected total: there is no third lever to make up a shortfall. The tail arithmetic and the residue are in `dev/JOURNAL.md`. |
| L3.32-F5.1 | **Root cause, ruled on by the owner: burn the boats, or understand exactly why not** | **ANSWERED 2026-08-06 by `[T97]` and `[T98]`, from two directions, and they agree: THE COST IS PRESENTATION, NOT MATHEMATICS.** The counter-example (`L.Rud.HF`) and the history-side evidence are in `dev/JOURNAL.md`. |
| L3.32-F5 | **The worst part first**: `L.Ordinal.SquareLaw` | **THE SEAL IS REFUTED BY MEASUREMENT, AND SO ARE BOTH CHEAP REWRITES.** `[T88]` returned with a per-definition profile and four measured probes. **THE DECISION, from `[T98]`: BURN THE BOATS, gated on ONE probe**, per D22 and the funding rule that a build whose widest term is unmeasured is not fundable when a probe can measure it. **RULED 2026-08-06 BY THE OWNER: BURN THE BOATS. The rewrite is under way.** **DISPATCH 2b LANDED. `SquareLaw` IS CLOSED: 856 s to 64.4 s in one day, a 13x reduction on the tree's most expensive module, for NET ZERO LINES across the two dispatches.** `[T103]` measured 470.6 s to 64.4 s, with the `h₀-inj` pair going **393.4 s to 71 ms**. **The tree goes 1,956 s to 1,162 s.** The profile, the probes, the gate and both dispatches are recorded in `dev/JOURNAL.md`. |
| L3.32-F6.0 | **What should `L.Rud` CONTAIN at all**: the architecture question, before any batch | **RULED 2026-08-06 by the owner, and it corrects the row below.** The instruction: do not rewrite item by item; first ask what the items even ARE, whether they can be simplified, and start from the top-level module design. **It gates B1.** **ANSWERED 2026-08-06 by `[T94]`, and the answer is a STOP: the current decomposition is close to ideal, so the wholesale rewrite is NOT the move.** The full answer, with the per-module reasoning, is in `dev/JOURNAL.md`. |
| L3.32-F6 | The `L.Rud` rewrite, batched: **what the CURRENT decomposition would cost, superseded by F6.0** | **PARTLY SUPERSEDED 2026-08-06.** The exit condition and the funding rule stand; **the batch ORDER does not**, because it takes the existing 22 modules as given, which the owner ruled against (see `[L3.32-F6.0]`). **THE RULED NUMBER MOVED, 0.063 to 0.074, and the ruling did not.** **RULED 2026-08-06 by the owner**: the retiring subtree's measured rate is the exit condition, and the rewrite runs in batches. **FUNDING RULE:** B1 is dispatched on its own merit and gates B2 and B3; no batch is funded at the 3x class once B1 has measured the real rate. The batch arithmetic and the module-by-module numbers are in `dev/JOURNAL.md`. |
| L3.32-F4 | Capture the craft before the code that carries it is archived | **OPEN, and the part of the freeze that cannot be re-run later.** Three items. **(a)** `[T86]`'s diagnosis stands as a numbered LESSONS law, proposed and awaiting the owner's ID: a cost regression of this class is invisible to every gate the project has, because nothing typechecks slower than it should, it only typechecks slowly. **(b)** `dev/ARCHIVE.md` gains a **what this code did right** field, so the retiring tree's discipline (state at abstract carriers and variable indices, so nothing re-normalizes) is recorded in the registry rather than leaving with the files. **(c)** A mechanical guard, because 'a cold-check regression is a defect' is today a review rule with no measurement behind it: per-module seconds are already in `dev/ledger.toml`, so the gate can compare rather than trust. |
| L4 | Convergence | PLANNED (runs after `[L3.32]`'s surgery lands) |
| L4.0 | Empty Frontier, unconditional root | DONE in substance under `[L2.4]` (Frontier empty and deleted, root unconditional) |
| L4.1 | Whole-book harmonization pass | PLANNED (scope grown: the retirement surgery deletes chapters, and the identification story is corrected) |
| L4.2 | Landmarks/README/Charter updates | PLANNED (the Charter status must read `L ⊨ ZFC ∧ L ⊨ GCH`) |
| L4.3 | Seed the GCH successor plan | **CLOSED, ABSORBED 2026-08-03**: the GCH endpoint is the active campaign's own (§0); no successor document is seeded, and the post-GCH narrative is `[L6]` |
| L5 | Build and site infrastructure | PLANNED |
| L5.0 | Build machinery port | PLANNED |
| L5.1 | make check split | PLANNED (the three named gate defects belong here: the two linters that skip untracked files, the glossary avoid-list keying off markers, and the missing end-of-file check) |
| L5.2 | CI strategy | PLANNED |
| L5.3 | Site pipeline load test | PLANNED |
| L6 | The narrative master plan (the meeting at bedrock) | **REGISTERED 2026-08-04 by owner direction.** The standing narrative frame: geology and inner model theory meet at the bedrock, with `L is a bedrock` as the second trophy; every asset is valued against both trophies from this row onward. Phases and the asset re-coloring rule are in §6.1; the geology entry fee and the two mandatory corpus gates are measured in `_build/l3.31-glprobe-report.md` |
| L7 | The endpoint promotion and the archive's completion | **PLANNED**, ruled by D20 2026-08-04; the archive REGIME is in force now, this row is the endpoint work |
| L7.0 | Archive `main`, promote the working branch | PLANNED (same day as the endpoint, before any tidying) |
| L7.1 | Final archival sweep, pre-regime deletions entered | PLANNED |
| L7.2 | Verify the exclusions end to end; REUSE still covers `archive/` | PLANNED |
| L7.3 | Final pass on `archive/README.md` | PLANNED |
| L7.4 | Final pass on `dev/ARCHIVE.md` | PLANNED |
| L8 | Consolidation, and the gate before prose | **PLANNED**, ruled by D21 2026-08-04; opens when `[L7]` closes |
| L8.0 | Foundation refactor at T8 scale, on the post-archival tree | PLANNED (candidates re-examined, not inherited) |
| L8.1 | Line-by-line polish over the whole tree | PLANNED |
| L8.2 | **THE GATE**: report to the owner before any prose phase | PLANNED (the owner adds further code-shaping work here; `[L4.1]` waits on it) |

### Task index (one row per dispatch, §6.0 rules 7 and 8)

The dispatched tasks under `[L3.32]`, one row per code. The verdict cell is a
few words; the detail lives in the named report, `dev/JOURNAL.md`, the
deliverable or the brief. Rows T1-T110 were backfilled once by `[T111]` under
the one-time reconciliation clause of §6.0 rule 6; `[T111]` is that
reconciliation task itself and is in progress. `scripts/check-task-index.py`
enforces one row per code and the 200-character cap (§6.0 rule 8).

| Code | Task | Verdict | Detail |
|---|---|---|---|
| L3.32-T1 | The R4 corrective stop | DELIVERED | `dev/JOURNAL.md` |
| L3.32-T2 | Fresh-generic Sigma-1 face probe (gates 1+2) | GO | `_build/l3.32-t2-report.md` |
| L3.32-T3 | Choice re-home probe (gate 5) | GO | `_build/l3.32-t3-report.md` |
| L3.32-T4 | Retirement design recon (gate 6) | PARTIAL | `_build/l3.32-t4-report.md` |
| L3.32-T5 | W7 scoping recon | COMPLETE | `_build/l3.32-t5-report.md` |
| L3.32-T6 | Foundation rewrite recon | COMPLETE | `_build/l3.32-t6-report.md` |
| L3.32-T7 | Wholesale-retirement recon | REWRITE-AND-RETIRE | `_build/l3.32-t7-report.md` |
| L3.32-T8 | Foundation kit batch (C3,C1,C4,C5; C2 gate) | SPLIT | `_build/l3.32-t8-report.md` |
| L3.32-T9 | W7 cardinal gate, run | RED | `_build/l3.32-t9-report.md` |
| L3.32-T10 | StepInL ideal-form gate (T7 gate 1) | NO-GO | `_build/l3.32-t10-report.md` |
| L3.32-T11 | Realize-strip compile gate | RED | `_build/l3.32-t11-report.md` |
| L3.32-T12 | Geology corpus fetch | DELIVERED | `dev/literature/geology.md` |
| L3.32-T13 | Archive infrastructure | DELIVERED | `dev/JOURNAL.md`; `archive/` |
| L3.32-T14 | W3 recon: internal order, priced | COMPLETE | `_build/l3.32-t14-report.md` |
| L3.32-T15 | Face chapter batch 1 (W1 core) | DELIVERED | `_build/l3.32-t15-report.md` |
| L3.32-T16 | Ordinal pairing chapter | DELIVERED | `_build/l3.32-t16-report.md` |
| L3.32-T17 | Shape-count probe | GO | `_build/l3.32-t17-report.md` |
| L3.32-T18 | GCH scope gate | NO-GO | `_build/l3.32-t18-report.md` |
| L3.32-T19 | W3's gate, run | RED | `_build/l3.32-t19-report.md` |
| L3.32-T20 | Face's first instantiation (W2 gate) | GO | `_build/l3.32-t20-report.md` |
| L3.32-T21 | Square law's core, probed | GO (re-priced) | `_build/l3.32-t21-report.md` |
| L3.32-T22 | W3 sealing design probe | SPLIT | `_build/l3.32-t22-report.md` |
| L3.32-T23 | Bridge's remaining rows, gated | GO | `_build/l3.32-t23-report.md` |
| L3.32-T24 | Re-home's carve half, gated | CORRECTED | `_build/l3.32-t24-report.md` |
| L3.32-T25 | Bridge's successor hypothesis, gated | SPLIT | `_build/l3.32-t25-report.md` |
| L3.32-T26 | Shared pair kit | GO | `_build/l3.32-t26-report.md` |
| L3.32-T27 | Count layer, productionized | DELIVERED | `_build/l3.32-t27-report.md` |
| L3.32-T28 | Code-set supplier, ideal form | REFUTED | `_build/l3.32-t28-report.md` |
| L3.32-T29 | Realize cone's retirement, executed | DELIVERED | `_build/l3.32-t29-report.md` |
| L3.32-T30 | Level formula (face's first consumer) | DELIVERED | `_build/l3.32-t30-report.md` |
| L3.32-T31 | Square law, discharged | DELIVERED (transfer blocked) | `_build/l3.32-t31-report.md` |
| L3.32-T32 | Bridge's sigma at a rud carrier | DELIVERED | `_build/l3.32-t32-report.md` |
| L3.32-T33 | Condensation crossing | DELIVERED | `_build/l3.32-t33-report.md` |
| L3.32-T34 | DefInJ and SatTable re-type | DELIVERED | `_build/l3.32-t34-report.md` |
| L3.32-T35 | Reshaped reduction | DELIVERED | `_build/l3.32-t35-report.md` |
| L3.32-T36 | Level formula's remaining two clauses | DELIVERED | `_build/l3.32-t36-report.md` |
| L3.32-T37 | Cardinal predicates, built generally | DELIVERED | `_build/l3.32-t37-report.md` |
| L3.32-T38 | Terminology dossier (14 renderings) | DELIVERED | `dev/literature/terms-2026-08.md` |
| L3.32-T39 | Mostowski collapse | DELIVERED | `_build/l3.32-t39-report.md` |
| L3.32-T40 | Definable hull (W7's other half) | DELIVERED | `_build/l3.32-t40-report.md` |
| L3.32-T41 | Glossary review (119 entries) | DELIVERED | `dev/literature/glossary-review-2026-08.md` |
| L3.32-T42 | W3 chapter A: order-family table | DELIVERED | `_build/l3.32-t42-report.md` |
| L3.32-T43 | Where counting calls the square law | RED (wall confirmed) | `_build/l3.32-t43-report.md` |
| L3.32-T44 | W3 chapter B: order formula and adequacy | SPLIT | `_build/l3.32-t44-report.md` |
| L3.32-T45 | Bridge's two sequence residues | STOP | `_build/l3.32-t45-report.md` |
| L3.32-T46 | Cardinal chapter's counting side | DELIVERED | `_build/l3.32-t46-report.md` |
| L3.32-T47 | Truncated square law at initial ordinals | DELIVERED | `_build/l3.32-t47-report.md` |
| L3.32-T48 | Is W3's internal order reachable? | GO (route corrected) | `_build/l3.32-t48-report.md` |
| L3.32-T49 | Stale-obstruction sweep | COMPLETE (15 stale) | `_build/l3.32-t49-report.md` |
| L3.32-T50 | W3 gate: sequence-witness order at omega | COMPLETE | `_build/l3.32-t50-report.md` |
| L3.32-T51 | Condensation crossing's transfers | COMPLETE | `_build/l3.32-t51-report.md` |
| L3.32-T52 | Carried sequence: one object, two residues | GO (cheaper) | `_build/l3.32-t52-report.md` |
| L3.32-T53 | Carried-sequence gate at the first limit | SPLIT | `_build/l3.32-t53-report.md` |
| L3.32-T54 | Levy-certificate gate | SPLIT | `_build/l3.32-t54-report.md` |
| L3.32-T55 | Ledger re-sum | COMPLETE | `_build/l3.32-t55-report.md` |
| L3.32-T56 | Variable-form op-graph frame | DELIVERED | `_build/l3.32-t56-report.md` |
| L3.32-T57 | W7 residue: itemized row with a gate | COMPLETE (band corrected) | `_build/l3.32-t57-report.md` |
| L3.32-T58 | Adversarial review of the dispatch wrapper | COMPLETE (18 defects) | `_build/l3.32-t58-report.md` |
| L3.32-T59 | Tower-induction gate at omega | RED (gate) | `_build/l3.32-t59-report.md` |
| L3.32-T60 | Which disciplines can be tooled | COMPLETE | `_build/l3.32-t60-report.md` |
| L3.32-T61 | Honest-segment tower story, rud carrier | DELIVERED | `_build/l3.32-t61-report.md` |
| L3.32-T62 | Init boundary correction, pairing re-pointing | DELIVERED | `_build/l3.32-t62-report.md` |
| L3.32-T63 | Four inexpressible operations | REFUTED (wall not real) | `_build/l3.32-t63-report.md` |
| L3.32-T64 | W1' fundability: build plan | SPLIT (fundable) | `_build/l3.32-t64-report.md` |
| L3.32-T65 | Close Q-lim at the first limit | STOP (refuted step 3) | `_build/l3.32-t65-report.md` |
| L3.32-T66 | Def-step gate | GO | `_build/l3.32-t66-report.md` |
| L3.32-T67 | Retirement boundary: nine crossings | COMPLETE | `_build/l3.32-t67-report.md` |
| L3.32-T68 | One-way successor clause, domain bound | DELIVERED | `_build/l3.32-t68-report.md` |
| L3.32-T69 | W1' D2: Sigma-1 form at the set carrier | GO | `_build/l3.32-t69-report.md` |
| L3.32-T70 | W1' D4+D5: class carrier, AmbientOnly | SPLIT | `_build/l3.32-t70-report.md` |
| L3.32-T71 | W7's cheap residue: Cantor, 5.4 half | DELIVERED | `_build/l3.32-t71-report.md` |
| L3.32-T72 | Retirement set re-derived, rewrite side | COMPLETE (SatSets out) | `_build/l3.32-t72-report.md` |
| L3.32-T73 | Adversarial review of the notification path | COMPLETE (defects fixed) | `_build/l3.32-t73-report.md` |
| L3.32-T74 | The landing: close Q-lim at omega | DELIVERED | `_build/l3.32-t74-report.md` |
| L3.32-T75 | The sndIn defect: comment or code? | DEFECT CONFIRMED | `_build/l3.32-t75-report.md` |
| L3.32-T76 | Fix sndIn and audit its consumers | DELIVERED | `_build/l3.32-t76-report.md` |
| L3.32-T77 | Rewrite the structural story | STOP (price) | `_build/l3.32-t77-report.md` |
| L3.32-T78 | Re-scope the StepInL rewrite | COMPLETE (re-scope) | `_build/l3.32-t78-report.md` |
| L3.32-T79 | Standing tree: big compression levers | COMPLETE | `_build/l3.32-t79-report.md` |
| L3.32-T80 | Lever A: level-story clause kit | DELIVERED | `_build/l3.32-t80-report.md` |
| L3.32-T81 | CSB literature survey | COMPLETE (keep ours) | `_build/l3.32-t81-report.md` |
| L3.32-T82 | Finite-tally harvest | DELIVERED | `_build/l3.32-t82-report.md` |
| L3.32-T83 | Knaster-Tarski or g-point for CSB? | NO RETURN RECORDED | `_build/briefs/l3.32-t83-brief.md` |
| L3.32-T84 | Lever B: condensation story onto the kit | STOP (D-10) | `_build/l3.32-t84-report.md` |
| L3.32-T85 | Re-design the tower-induction gate | GREEN (gate re-design) | `_build/l3.32-t85-report.md` |
| L3.32-T86 | Cold check: can sealing get under five? | COMPLETE | `_build/l3.32-t86-report.md` |
| L3.32-T87 | Bridge read-lemma fix, in place | DELIVERED | `_build/l3.32-t87-report.md` |
| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | `_build/l3.32-t88-report.md` |
| L3.32-T89 | Repair the structural story in place | FIXED; COOLING REFUTED | `_build/l3.32-t89-report.md` |
| L3.32-T90 | Design the below-lim build | GO (first limit) | `_build/l3.32-t90-report.md` |
| L3.32-T91 | Walk the whole path to L ⊨ GCH | COMPLETE (owed gaps) | `_build/l3.32-t91-report.md` |
| L3.32-T92 | Below-lim gate at the first limit | STOPPED (before firing) | `dev/PLAN.md:71` |
| L3.32-T93 | Find the next Bridge by reading | COMPLETE | `_build/l3.32-t93-report.md` |
| L3.32-T94 | What the rud route should contain | COMPLETE | `_build/l3.32-t94-report.md` |
| L3.32-T95 | Adversarial review of the caliber | COMPLETE (7 defects) | `_build/l3.32-t95-report.md` |
| L3.32-T96 | Last untested lever: Condensation's 203 s | COMPLETE (priced refusal) | `_build/l3.32-t96-report.md` |
| L3.32-T97 | Archaeology: how the internalization got cheap | COMPLETE | `_build/l3.32-t97-report.md` |
| L3.32-T98 | Root cause: presentation or mathematics? | COMPLETE | `_build/l3.32-t98-report.md` |
| L3.32-T99 | Burn-the-boats gate: abstract chase | GREEN | `_build/l3.32-t99-report.md` |
| L3.32-T100 | Sweep outside the three theorems | COMPLETE (clean bill) | `_build/l3.32-t100-report.md` |
| L3.32-T101 | Burn the boats, dispatch 1: SquareLaw chase | DELIVERED | `_build/l3.32-t101-report.md` |
| L3.32-T102 | Dispatch 2 gate: h₀ without the tower | GREEN | `_build/l3.32-t102-report.md` |
| L3.32-T103 | Burn the boats, dispatch 2b: h₀ reshape | DELIVERED | `_build/l3.32-t103-report.md` |
| L3.32-T104 | Does T102's cure apply to Condensation? | OVERTURNED (by T106) | `_build/l3.32-t104-report.md` |
| L3.32-T105 | Adversarial review: context layering | REFUTED (diagnosis) | `_build/l3.32-t105-report.md` |
| L3.32-T106 | Dispatch 3 gate: measure the lift | NO (gate; refutes T104) | `_build/l3.32-t106-report.md` |
| L3.32-T107 | Dispatch 3: Crossing parameterization | DELIVERED | `_build/l3.32-t107-report.md` |
| L3.32-T108 | Move episode content into JOURNAL | DONE | `_build/l3.32-t108-report.md` |
| L3.32-T109 | Adversarial review of slimmed AGENTS.md | COMPLETE | `_build/l3.32-t109-report.md` |
| L3.32-T110 | Maintenance mechanism for dev/ docs | DELIVERED. check-dev-docs.py, in the gate | `_build/l3.32-t110-report.md` |
| L3.32-T111 | Task index: one code, one row (this dispatch) | DELIVERED. The rule amendment, the index and check-task-index.py | `_build/l3.32-t111-report.md` |
| L3.32-T112 | Goal table held to the index discipline | DELIVERED | `_build/l3.32-t112-report.md` |
| L3.32-T113 | Strip dev docs to the agent workflow | DELIVERED. PLAN 24.8k to 13.9k words; sections 2,4,5,7-10 became memo pointers | `_build/l3.32-t113-report.md` |
| L3.32-T114 | Build the owner's dashboard, generated from canonical data | DELIVERED. scripts/dashboard.py and check-dashboard.py | `_build/l3.32-t114-report.md` |
| L3.32-T115 | dev/ doc recon: what the agent workflow needs | DELIVERED | `_build/l3.32-t115-report.md` |
| L3.32-T116 | Dashboard: render the raw panels, re-order | DELIVERED | `_build/l3.32-t116-report.md` |
| L3.32-T117 | Dashboard made two-dimensional: merge, graph, pies | DELIVERED | `_build/l3.32-t117-report.md` |
| L3.32-T118 | Dashboard visual pass against the taste library | DELIVERED | `_build/l3.32-t118-report.md` |
| L3.32-T119 | Adversarial review of the dispatch mechanism | DELIVERED | `_build/l3.32-t119-report.md` |
| L3.32-T120 | Cold start: what AGENTS.md alone conveys | DELIVERED | `_build/l3.32-t120-report.md` |
| L3.32-T121 | Profile the four masters over 2 percent | DELIVERED. Three cures, ~104 s for ~18 lines; Bridge NO-GO per T93. Gate lands at 8.3 min against 7.5 | `_build/l3.32-t121-report.md` |
| L3.32-T122 | Archival arm A: sixteen zero-consumer masters, 320.4 s | DELIVERED. All moved, ARCHIVE.md written; its wiring checklist had one range defect, caught | `_build/l3.32-t122-report.md` |
| L3.32-T123 | Land T121's Pairing seal in the master: 56.7 s to about 19 | DELIVERED. 57,985 to 20,195 ms, 37.8 s off, all 72 exports byte-identical, +7 lines | `_build/l3.32-t123-report.md` |
| L3.32-T124 | Land T121's Images left-seal | DELIVERED. Images 52.9 to 6.7 s, Step 28.8 to 4.6 s with zero Step edits, 70.3 s total, exports intact | `_build/l3.32-t124-report.md` |
| L3.32-T125 | The below-lim gate at the first limit | RED at the line budget, TARGET LANDED. Kit runs at the L-carrier; a third wall fired, O4 at 2-3x band | `_build/l3.32-t125-report.md` |
| L3.32-T126 | O4 as its own master, generic over carrier and graph layer | BUILT. L.Rud.StepStory, 313 lines, green, 1.25 s; instantiated unchanged, no growth | `_build/l3.32-t126-report.md` |
| L3.32-T127 | The B4 gate at the L-carrier | GREEN at the first limit; REFUTED the recorded O7/O8 at general beta, the story needs a sixth limit clause | `_build/l3.32-t127-report.md` |
| L3.32-T128 | The limit-clause gate | EXPRESSIBLE, clause and two-way decode built, 353 lines, carrier-generic. The T84 obstruction does not transfer | `_build/l3.32-t128-report.md` |
| L3.32-T129 | Archival arm B: the two Condensation crossings | STOPPED at the cone map; T67's band refuted. The re-home IS the internalization cone | `_build/l3.32-t129-report.md` |
| L3.32-T130 | Can the tower-graph crossing ride the rud-side story? | NO, refuted read-only: the index question and the S-versus-L tower mismatch | `_build/l3.32-t130-report.md` |
| L3.32-T131 | The honest segment at a limit index | KILLED after looping 1,622x; salvage wrote the report. T138 later found its state NEVER typechecked whole | `_build/l3.32-t131-report.md` |
| L3.32-T132 | D22 gate on Build A's widest term: one adequacy arm | Arm GREEN at 174 lines; the 700-900 ESTIMATE RED. Build A is ~2.0-2.5k naive, not 1.1-1.5k | `_build/l3.32-t132-report.md` |
| L3.32-T133 | Build A block 1: the fresh home, frame, and T132's arm | LANDED. L.TowerGraph, 304 lines, green, ZERO retiring imports; the arm now 2.7 s vs 21.7 | `_build/l3.32-t133-report.md` |
| L3.32-T134 | Build A block 2: the four description arms | 6 lines, not 165. The frame makes every arm a PARAMETER, so no arm is provable until the text block lands | `_build/l3.32-t134-report.md` |
| L3.32-T135 | A per-trophy caliber: what the AC trophy alone costs | DELIVERED, then CORRECTED by the owner: the caliber now measures the surviving tree, AC 10,026 | `_build/l3.32-t135-report.md` |
| L3.32-T136 | Build A text block: two atoms, two readings | PARTIAL. 179 lines; hasWitnessAt stops at the table boundary. 11 of 18 parameters remain | `_build/l3.32-t136-report.md` |
| L3.32-T137 | The trophy matrix: three calibers by three trophies | DELIVERED. AC endpoint 13.7-15.7k naive; every remaining row carries a trophy, enforced | `_build/l3.32-t137-report.md` |
| L3.32-T138 | Close the limit segment: the four story clauses | GREEN x4 in a 35.7 s harness. T131's segDom-0 is a check-time WALL: one proof walls past 7.5 min | `_build/l3.32-t138-report.md` |
| L3.32-T139 | Adversarial review of D31's five measurements | 3 HOLD, 2 WEAK. AC has two readings, 10,026 route vs 5,949 delivered; the tail band is unmeasured | `_build/l3.32-t139-report.md` |
| L3.32-T140 | The tail probe | RED. The readings reduce to the tail's own theorems; no compression path. Build A moves to about 3.2-3.4k naive | `_build/l3.32-t140-report.md` |
| L3.32-T141 | Write today into the JOURNAL: nineteen dispatches, T121 to T139 | DELIVERED. 19 of 19 entries, +1,435 words; seven unsupported claims flagged | `_build/l3.32-t141-report.md` |
| L3.32-T142 | The code block gate | RED. The readings reduce to the shape machinery's own theorems, 2,378 delivered; the arity pin saves zero | `_build/l3.32-t142-report.md` |
| L3.32-T143 | Kill the exact-domain wall | CURED, 595 s to 27 ms. The disease was I-5: two inline lambdas at the eliminator; named with written types, 29 lines | `_build/l3.32-t143-report.md` |
| L3.32-T144 | Execute D32: delete the Crossing section | DELETED, 86 lines, docs shipped. Condensation fell 150.2 to 11.5 s: ambientOnly-from was 92 percent | `_build/l3.32-t144-report.md` |
| L3.32-T145 | Gate the graph-layer supply | RED, outcome 3: the slice IS the full rewrite. The roles reduce to StepInL's own theorems, ~1,718 delivered lines | `_build/l3.32-t145-report.md` |
| L3.32-T146 | Opus recon: pin the AC remainder | DELIVERED. The 1.5-2.9k is 3.7-5.6k: a documented leak (the graph layer) plus a band wrong both ways | `_build/l3.32-t146-report.md` |
| L3.32-T147 | Opus audit: is GCH-alone alone? | HOLDS-WITH-EDGES, worktree-verified; all ten ambiguous modules need the 22. Proposal 2 RULED as D33 | `_build/l3.32-t147-report.md` |
| L3.32-T148 | StepInL rewrite block 1: the fresh master and the frame layer | LANDED. L.Rud.StepGraph, 504 lines, ~1.6 s warm, survivors only, wired; rate x1.21 | `_build/l3.32-t148-report.md` |
| L3.32-T149 | JOURNAL entries for the dispatches T140 to T147 | DELIVERED. 8 of 8 entries, +723 words, insertions only; six unsupported claims recorded in place | `_build/l3.32-t149-report.md` |
| L3.32-T150 | Route memo: the below-lim general build, consolidated | DELIVERED. 1,983 words; sizes tied to the ledger, both calibers; five contradictions pinned | `_build/l3.32-t150-report.md` |
| L3.32-T151 | Run the cured below-lim probe end to end | STOPPED at 46:16 wall, contended. Deps complete; a SECOND wall exists, site unknown; zero repairs | `_build/l3.32-t151-report.md` |
| L3.32-T152 | Terminology dossier: the eleven terms StepGraph uses uncovered | DELIVERED. Keep all except 像片 which becomes 切片. Drift at Images:460. Enters D35 | `_build/l3.32-t152-dossier.md` |
| L3.32-T153 | Opus adversarial review of the T152 dossier (D35 arm 2) | DELIVERED. 4 PASS landed; the 7 escalations ruled under owner delegation, all landed | `_build/l3.32-t153-review.md` |
| L3.32-T154 | Bisect the below-lim probe: find the second wall | FOUND, one wall: the depth-6 ordinal witness; cured 631 s to 59 s in harness; five tail errors named | `_build/l3.32-t154-report.md` |
| L3.32-T159 | Close the below-lim probe end to end, first time ever | GREEN. 57.8 s cold, 2.5 s warm, clean; 13 fix lines of 80; the wall count stays one | `_build/l3.32-t159-report.md` |
| L3.32-T160 | The Step split: the transitivity theory to its natural home | STOPPED, naturalness held: ConcreteS consumes the set in-file and feeds Bridge; C-23 | `_build/l3.32-t160-report.md` |
| L3.32-T162 | The WellOrder.Base split: the SWO combinators | SPLIT. L.WellOrder.Combinators, 247 lines moved, C-23 clean; natSWO and pullSWO stay, AC reads them | `_build/l3.32-t162-report.md` |
| L3.32-T163 | JOURNAL entries T148 to T162 and the three rulings | DELIVERED. 15 of 15 entries, +1,211 words, insertions only, lint green | `_build/l3.32-t163-report.md` |
| L3.32-T164 | StepGraph block 2: the decodes for ops 0-7 | LANDED. 339 lines at rate x0.79, the first under-size block; master 843, ~1.8 s warm | `_build/l3.32-t164-report.md` |
| L3.32-T165 | StepGraph block 3: the ops 8-15 decodes, dispatchers, graphs | LANDED. 609 lines; the BigOr telescope closes; master 1,452, ~1.9 s warm | `_build/l3.32-t165-report.md` |
| L3.32-T166 | C-23 deep check: the Order and Coding/Base movable subsets | Order MOVABLE 114, ordSWO and opIx stay; Base MOVABLE 46, shared until retirement | `_build/l3.32-t166-report.md` |
| L3.32-T167 | The duplication sweep: content written twice in the AC closure | 210-430 survey, floor 35-55; nine candidates with carriers; C1 leads | `_build/l3.32-t167-report.md` |
| L3.32-T169 | D22 probe: the C1 description-scaffold dedup at F1Desc | GO, but small: measured -6 at one module, -25 to -30 at eight; the 60-140 survey corrects down | `_build/l3.32-t169-report.md` |
| L3.32-T170 | StepGraph block 4: the values lex and the step description | LANDED, 460 lines: THE REWRITE IS COMPLETE at 1,912, inside the calibrated band | `_build/l3.32-t170-report.md` |
| L3.32-T171 | Split L.Rud.Order: the level readings to their natural home | SPLIT. L.Rud.OrderReadings, 115 moved, C-23 re-verified; all four touched masters green | `_build/l3.32-t171-report.md` |
| L3.32-T172 | D22 probe: the C2 formula-coding dedup at Count | NO-GO at the 120 stop: the carrier needs 143 fresh; the two-sided net is -65 to -70, real but small | `_build/l3.32-t172-report.md` |
| L3.32-T173 | The re-home design memo: one document for the AC endgame | DELIVERED. 1,707 words; every discharge obligation itemized with its supplier | `_build/l3.32-t173-report.md` |
| L3.32-T174 | Fable strategy recon: compression and the cap options | DELIVERED. F2 the doubled description layer; F1 HF+Finite exit; the landing can pass 16k | `_build/l3.32-t174-strategy.md` |
| L3.32-T175 | D22 probe: one arm's defSet equation from StepGraph (F2) | GREEN at 133 of 150: the pin frame derives F1's equation; the Arms rebuild is funded | `_build/l3.32-t175-report.md` |
| L3.32-T176 | The F1 walk: what does AC consume from HF and Finite? | EXIT-AT-COST: five lemmas, re-home 75-95; STAY refuted; net -642 to -1,290 | `_build/l3.32-t176-report.md` |
| L3.32-T177 | Adversarial review: break the F2 finding before it is funded | HOLDS-WITH-EDGES, four edges priced; the net re-derives to -1,018 to -1,184 | `_build/l3.32-t177-report.md` |
| L3.32-T178 | F2 block 1: the extraction, the pin frame, the sixteen equations | LANDED, 328 of 350: L.TowerKit born; Bridge falls 8.2 s cold; all green | `_build/l3.32-t178-report.md` |
| L3.32-T179 | D22 probe: the carried order-story's successor clause (F3) | GREEN at 135 of 150: both T161 walls dissolve; the slice re-prices, calibrated top halves | `_build/l3.32-t179-report.md` |
| L3.32-T180 | F2 block 2: Arms rebuilds over StepGraph | LANDED, net -83 lines; Bridge cold falls 55 s (-34%); 64 signatures byte-identical | `_build/l3.32-t180-report.md` |
| L3.32-T181 | JOURNAL entries T163 to T180, the F-series day | DELIVERED. 18 of 18 entries, insertions only, lint green | `_build/l3.32-t181-report.md` |
| L3.32-T182 | D22 gate: the general-beta transfer at a second limit carrier | RED at 213 of 150: it needs its own residue at the previous limit; band up ~1k | `_build/l3.32-t182-report.md` |
| L3.32-T183 | F2 block 3a: localize F10Desc, cut the last Describe edge | LANDED, 109 of 130: the edge is gone, StepGraph green; the archival is unblocked | `_build/l3.32-t183-report.md` |
| L3.32-T184 | Opus assessment: the F series' effect on the GCH wing | NO TAX: costs the wing 41 lines, saves 1,290; the wing endpoint falls ~3.1-3.6k | `_build/l3.32-t184-gch-impact.md` |
| L3.32-T185 | Statement-shape probe: below-lim as an induction over limits | GREEN at 139 of 150: the induction assembles and the T182 wall IS the hypothesis | `_build/l3.32-t185-report.md` |
| L3.32-T186 | F1 execution: re-home the five lemmas from HF and Finite | LANDED 75 of 140, three homes green; REFUTED its own avoidance: the landing needs more | `_build/l3.32-t186-report.md` |
| L3.32-T193 | D22 gate: the carve's own landing, without the identification | GREEN at 84 lines: the carve lands itself; HF and Finite archive after block 2 | `_build/l3.32-t193-report.md` |
| L3.32-T194 | D22 gate: the Q-lim residue at a general limit | RED: the frame re-instantiates at 62, but the family equality rests on a FALSE bridge; 612-1,062 | `_build/l3.32-t194-report.md` |
| L3.32-T195 | The below-lim master, block 2: the STEP, and the theorem closes | PARTIAL: the first limit closes, 948 of 900; the seconds watch FIRED at 216 s cold | `_build/l3.32-t195-report.md` |
| L3.32-T215 | Cure the below-lim master's check time: 216 s must come down | STOPPED: T221's reshape deletes the content it was curing, and P-n predicted the floor | `_build/l3.32-t215-report.md` |
| L3.32-T216 | JOURNAL entries T206 to T215, the campaign day | DELIVERED, insertions only, lint green | `_build/l3.32-t216-report.md` |
| L3.32-T217 | Block 3's scope, priced before it is funded | SPLIT REQUIRED and THE GATE BREAKS AT BOTH RATES: 513-529 s cured, 836-893 uncured | `_build/l3.32-t217-report.md` |
| L3.32-T218 | The wall arithmetic: can the AC landing fit 498 s at all? | 745-813 s uncured DOES NOT FIT; 422-448 cured TURNS ON T215 and four unmeasured terms | `_build/l3.32-t218-wall.md` |
| L3.32-T219 | The seconds doctrine: what makes a master expensive here | Five diseases; the 21-60x gap is a CONTENT CLASS, not a defect. P-m and P-n admitted | `_build/l3.32-t219-seconds.md` |
| L3.32-T220 | Time the four unmeasured landing terms, in master shape | Four measured, 29.69 s floor; cured wall 452-478 fits by 20-46 on the measurements | `_build/l3.32-t220-report.md` |
| L3.32-T221 | The parameterization question: can the master need less instantiation? | RESHAPEABLE: the general STEP subsumes block 2; -898 to -933 lines, 20-34 s | `_build/l3.32-t221-report.md` |
| L3.32-T222 | The deciding rate: what does a generic STEP cost per line? | 0.085 s per line, a STRADDLE: the tree lands 484-514 against 498, by plus 14 or minus 16 | `_build/l3.32-t222-report.md` |
| L3.32-T223 | The reshape's build plan, written against the measured rates | TWO blocks, order fixed; its seconds predate T222, so the orchestrator re-derived them | `_build/l3.32-t223-plan.md` |
| L3.32-T224 | JOURNAL entries T216 to T223, the seconds day | DELIVERED, 8 of 8, insertions only, lint green | `_build/l3.32-t224-report.md` |
| L3.32-T225 | C3: dedup the one-way successor clause and its bounded atoms | DEDUPED, -92 net in-fence lines, inside the 60-100 band; found P-p, the stale-interface  | `_build/l3.32-t225-report.md` |
| L3.32-T226 | C4: one story assembly, before the general STEP is written | KEPT: +72 naive, +0.85 s; the block A saving is a WASH at audit; found P-o | `_build/l3.32-t226-report.md` |
| L3.32-T227 | C5: one induction frame, and whether the four sites unify | DOES NOT UNIFY as a saving: the frame is delivered twice, the clauses are per-site | `_build/l3.32-t227-report.md` |
| L3.32-T228 | The endgame status memo, for a reader who was not here | DELIVERED `dev/memos/L3.32-endgame-status.md`, 1,808 words; found the C-23 collision too | `_build/l3.32-t228-report.md` |
| L3.32-T229 | Adversarial: block A's inl case without `member-a0-not-limit` | GREEN, 6 attacks failed: at a general limit it PROVES rather than refutes | `_build/l3.32-t229-report.md` |
| L3.32-T230 | Block A: the general STEP at a variable limit, written in place | STOPPED RED: floor 1,249 nbl vs the 1,080 stop-line; 589 landed green; the six | `_build/briefs/l3.32-t230-blockA.md` |
| L3.32-T231 | Adversarial: is the induction hypothesis really vacuous at a-0? | GREEN, 15-site walk: every limit-reachable site goes through the IH, the rest by the  | `_build/l3.32-t231-report.md` |
| L3.32-T232 | Adversarial: can block A consume Bridge's `Below` row instead of writing it? | GREEN: the row falls from 50-90 lines to 10-14 of glue; no circularity;  | `_build/l3.32-t232-report.md` |
| L3.32-T233 | Lift `Below` out of `Reduce` so block A can consume it | DONE at 13 semantic lines; Bridge exit 0; its A/B proved the HF failure predates it | `_build/l3.32-t233-report.md` |
| L3.32-T234 | The fold's last clause must be BARE: the tree is red at HF | GREEN: one fold clause so a non-empty list ends bare; no consumer changed; Everything exit | `_build/l3.32-t234-report.md` |
| L3.32-T235 | Hunt seconds in the 388.9 s tree base, not in block A | NOT THERE as a price: only 48-68 pct of the base has current figures; found the D30 screen's st | `_build/l3.32-t235-report.md` |
| L3.32-T236 | Archive HF and Finite: the ruled removal whose condition is now met | ARCHIVED 1,290 lines (HF 664, Finite 626), byte-identical, catalog rewired by the | `_build/l3.32-t236-report.md` |
| L3.32-T237 | Finish block A, delete the a-0 module, and measure the landing | STOPPED at the gate: GO but 904 nbl / 186 s for the limit case alone, 4.3x the floor;  | `_build/l3.32-t237-report.md` |
| L3.32-T238 | Adversarial: is the nested-carrier port really unavoidable? | PARTLY AVOIDABLE: the clause must exist at the nested carrier, but 250-300 lines of resta | `_build/l3.32-t238-report.md` |
| L3.32-T239 | Make the limit clause carrier-generic, as the successor clause already is | GREEN, net +26 at the first site (StepStory +350, BelowLim -324); the neste | `_build/l3.32-t239-report.md` |
| L3.32-T240 | Re-measure the carried sequence with the generic clause: lines AND seconds | 589 nbl / 174.62 s / 0.297 per line: the 315 lines transferred, the second | `_build/l3.32-t240-report.md` |
| L3.32-T241 | Profile the carried sequence's 174.62 s: where does the time go? | CONCENTRATED then NO-GO: top 11 carry 71.4 pct, all decode content at the carrier; g | `_build/l3.32-t241-report.md` |
| L3.32-T242 | Two decode shapes, both bound-variable, 3.5x apart: why? | ARTIFACT: 0.085 was a slice rate, the content is 0.297; the miss is 303-311 s not 6-14; foun | `_build/l3.32-t242-report.md` |
| L3.32-T243 | The two profiles nobody ran: Bridge 103.1 s and StepGraph 59.0 s | NOT THERE: both CONCENTRATED, both NO-GO; Bridge's once-pair 78.8 s is P-l's floor,  | `_build/l3.32-t243-report.md` |
| L3.32-T244 | Gate the choice re-home: price its ideal form from the rewrite side | GATED: ideal form 188-248 naive (booked 300-650); all 12 Choice masters archive f | `_build/l3.32-t244-report.md` |
| L3.32-T245 | Finish block A: the stop-line was wrong and it gates the only lever left | COMPLETE: below-lim closes at a GENERAL limit, a-0 module deleted, master 2, | `_build/l3.32-t245-report.md` |
| L3.32-T246 | The JOURNAL catch-up: 22 entries for T224 to T245 | DELIVERED 22 of 22, insertions only, lint green; found the word stop-line at 48,245 against 45,000 | `_build/l3.32-t246-report.md` |
| L3.32-T247 | Tidy the JOURNAL: mark what later measurements superseded, never rewrite | 9 markers on 8 entries, zero tokens lost; 4 more checked and NOT marked with | `_build/l3.32-t247-report.md` |
| L3.32-T248 | Refresh the endgame status memo: every headline number in it is now wrong | REWRITTEN, 1,455 words; 16 headline figures corrected, each traced to the m | `_build/l3.32-t248-report.md` |
| L3.32-T249 | Time the covering code predicate: T211's named gate | GO: 0.0113 s per line whole, not 0.0603 from a slice; the row is 15.2-20.0 s and FITS at every ca | `_build/l3.32-t249-report.md` |
| L3.32-T250 | The third compression campaign: 500-line levers, from first principles | ONE lever, 285-695 naive UNGATED: recover the witness from a strengthened induct | `_build/l3.32-t250-math.md` |
| L3.32-T251 | Gate 1: does the strengthened induction actually recover the witness? | STOPPED at 304 min by the orchestrator: 0 typechecks in 67 min; resumed as T251 | `_build/l3.32-t251-report.md` |
| L3.32-T251r | Gate 1 resumed: write the negative result first, measure second | FROZEN 2026-08-09 by the owner before it launched; its queue waiter was stopped, ses | `_build/l3.32-t251-report.md` |
| L3.32-T252 | The naturalness review of today's four settled masters | StepStory NOT NATURAL, announces one subject and holds two; the other three stand; six repairs | `_build/l3.32-t252-report.md` |
| L3.32-T253 | The naturalness repair: prose only, four masters | 4 of 4 applied, prose only, every code fence byte-identical; the orchestrator rewrote the two stale  | `_build/l3.32-t253-report.md` |
| L3.32-T254 | The closure boundary: gch_assign, and a natural split that follows it | ZERO legal gch_assign, ZERO natural splits; the 2,100-2,700 premise is stale at | `_build/l3.32-t254-report.md` |
| L3.32-T255 | The seconds question: is the interleaving cost mathematics or engineering? | The TWICE is MATHEMATICS, refuting the orchestrator; the gap does not clo | `_build/l3.32-t255-seconds.md` |
| L3.32-T256 | Gate 0: the first per-definition profile of the finished master | DONE by the orchestrator; segma-in-C 61.2 s and psi-in 35.3 s unexamined;  | `_build/l3.32-t256-belowlim-profile.txt` |
| L3.32-T257 | Price the GCH wing on the internalization route, calibrated to the rud wing | Internalization 25.5-28.3k vs rud 34.9-39.8k naive; the crossing assumpti | `_build/l3.32-t257-routes.md` |
| L3.32-T258 | The two rows nobody examined: seg-in-C at 61.2 s and psi-in at 35.3 s | DISPATCHED 2026-08-09; seg-in-C is 17 lines at 3.6 s each on a depth-SIX sucV c | `_build/l3.32-t258-report.md` |
| L3.32-T259 | Adversarial: is the rud-side crossing really refuted, or foreclosed by engineering? | VIABLE, ungated: re-target the description to the S-tower; T130 | `_build/l3.32-t259-crossing.md` |
| L3.32-T260 | Settle by probe: does the GCH wing actually consume the bridge rows? | NO, D18 wins: the row's sentence has zero support in its own evidence; the gap S | `_build/l3.32-t260-bridge.md` |
| L3.32-T261 | Run B's probe, and adversarially review B's own conclusion | QUEUED 2026-08-09 for an Agda slot; T260's answer is a reading and the owner asked for it  | `_build/l3.32-t261-report.md` |
| L3.32-T262 | Q-lim's general transfer: the other half of bridge-landing | FROZEN 2026-08-09 by the owner before it launched; the brief stands and needs no rework to | `_build/l3.32-t262-report.md` |
| L3.32-T263 | T259's desk pre-gate: are all sixteen Fof specs Delta-0? | FAIL at the delivered formulas, all sixteen; but a set-level conditional PASS. T259 must write  | `_build/l3.32-t263-fof.md` |
| L3.32-T264 | The JOURNAL catch-up: T246 to T263 | DISPATCHED 2026-08-09; 18 tasks unrecorded, including four laws, the deletion test PASS and the route comparison | `_build/l3.32-t264-report.md` |
| L3.32-T196 | Refresh the below-lim design memo to the measured state | DELIVERED, 1,983 to 2,530 words; eight stale claims quoted and refuted with evidence | `_build/l3.32-t196-report.md` |
| L3.32-T197 | The bridge landing: what remains once the two residues land | Band 50-150 naive, 4 of 6 hypotheses delivered; found one un-gated term, blockPowLim | `_build/l3.32-t197-report.md` |
| L3.32-T198 | D22 gate: the blockPowLim relation instance | RED at 114 lines: the instance needs archived content AND a relation nobody ever built | `_build/l3.32-t198-report.md` |
| L3.32-T202 | Can the AC route avoid blockPowLim entirely? | NEEDED: isL-to-isJ reaches it through Q-suc. The mirror never crosses the bridge at all | `_build/l3.32-t202-report.md` |
| L3.32-T203 | The route question: must L models AC cross the bridge at all? | CROSS. Not crossing costs +4.1k naive: a syntax-free key exists on Sset, none on Lset | `_build/l3.32-t203-route.md` |
| L3.32-T204 | D22 probe: the bounded family formula at the second limit | GREEN at the 200 cap: the chain needs no new ordinal content; one classical gate remains | `_build/l3.32-t204-report.md` |
| L3.32-T205 | Where did the 16,000 compression floor come from? | UNSUPPORTED: a 2026-07-31 survey's optimistic end, never probed; the measured bar is 17,496 | `_build/l3.32-t205-report.md` |
| L3.32-T206 | JOURNAL entries T200 to T205 | DELIVERED. 6 of 6, insertions only; T204 correctly recorded as dispatched, no verdict | `_build/l3.32-t206-report.md` |
| L3.32-T207 | The AC endgame execution plan: block 2 to the deletion test | DELIVERED, 2,410 words, eight steps ordered; the blockPowLim ruling is the honesty gate | `_build/l3.32-t207-report.md` |
| L3.32-T208 | Pin the 16,000: measure the L3.28 survey's seven levers on main | MEASURED -620 to -860 (survey said -755 to -1,486): the landing is 16,632-16,872, so  | `_build/l3.32-t208-report.md` |
| L3.32-T209 | D17 gate: the code predicate's ideal form over the graph layer | WASH: the ideal form is 1,120-1,275 against 1,379 delivered, 7-19 percent, not half | `_build/l3.32-t209-report.md` |
| L3.32-T210 | The compression campaign from first principles (fable, max) | -2,333 to -3,575, does NOT close; the cofinality escape closes NEGATIVE | `_build/l3.32-t210-campaign.md` |
| L3.32-T211 | The seconds gate: does any honest blockPowLim fit the wall? | TOO CLOSE TO CALL: 7.6 s slice projects 68-77 s naive, 88-100 calibrated, 203-231 survey | `_build/l3.32-t211-report.md` |
| L3.32-T212 | Cut the verified fat: ten wrappers and one unreached export | CUT 11 of 11, both masters green, exports byte-identical, no prose left stale | `_build/l3.32-t212-report.md` |
| L3.32-T213 | The mathematical campaign: generalize and restructure | Five candidates; C1 takes the widest survey term; crossing-rebuild verified irreducible | `_build/l3.32-t213-math.md` |
| L3.32-T214 | D22 gate: satisfaction-as-member on the Sat engine (C1) | GREEN: 13 lines and 0.19 s per constructor; the survey half falls to 0.24-0.30k | `_build/l3.32-t214-report.md` |
| L3.32-T199 | The carve-supset repair: is the general family equality feasible? | FEASIBLE at 592-1,052: a bounded family formula, and the false bridge never enters | `_build/l3.32-t199-report.md` |
| L3.32-T200 | JOURNAL entries T188 to T199 | DELIVERED. 12 of 12, insertions only, lint green; the D37 ruling gets a standing record | `_build/l3.32-t200-report.md` |
| L3.32-T201 | The D36 decision brief: every term measured, what is the landing? | Landing 17.8-19.4k naive, gap +1.8-3.4k; four options ranked, honesty first | `_build/l3.32-t201-decision.md` |
| L3.32-T187 | The coverage audit: did this week's re-cuts lose AC content? | CLEAN, nothing untracked; seven citation and arithmetic defects found and applied | `_build/l3.32-t187-report.md` |
| L3.32-T188 | JOURNAL entries T181 to T187 and the day's two measurements | DELIVERED. 7 of 7 entries, insertions only, lint green | `_build/l3.32-t188-report.md` |
| L3.32-T189 | Arm C recon: the two surviving crossings into the choice tree | Band re-priced 180-310 naive with two itemized terms; Hull re-homes by the bridge route | `_build/l3.32-t189-report.md` |
| L3.32-T192 | The naturalness review: do this week's cuts stand on their own? | 4 of 6 stand; 2 needed prose, all applied; five blurbs and the order repaired | `_build/l3.32-t192-report.md` |
| L3.32-T190 | Build the deletion test: D36's judgment, runnable on demand | DELIVERED. Shadow 14,379, agrees with the split by import; guards exercised | `_build/l3.32-t190-report.md` |
| L3.32-T191 | The below-lim master, block 1: shell, story, carried sequence | LANDED. L.Rud.BelowLim, 604 of 650, 6.3 s cold against a 70 s stop, survivors only | `_build/l3.32-t191-report.md` |
| L3.32-T168 | The compression-class sweep: dead content, generality, re-proofs, case-bloat | New AC value ~70-105, the Describe scaffolding leads; re-proofs zero | `_build/l3.32-t168-report.md` |
| L3.32-T161 | D22 gate: price W3's elimination slice on today's face | RED at 193 lines. The wiring closes green; the core is W3's own theorem; the band stands | `_build/l3.32-t161-report.md` |
| L3.32-T155 | D36 gate G1: the fat audit of the shared part | Movable ~1,471-1,650 after the HF-imports-Finite catch; saves-now 757-930 stands | `_build/l3.32-t155-report.md` |
| L3.32-T156 | D36 gate G2: the carried-sequence AC-necessity re-split | ZERO re-booked. General beta is AC-forced by the choice quantifier; all five terms stay BOTH | `_build/l3.32-t156-report.md` |
| L3.32-T157 | D36 gate G3: ideal-form pricing of the largest AC masters | Five of seven at ideal form. Delta 490-580 naive; 130-170 on the description fork | `_build/l3.32-t157-report.md` |
| L3.32-T158 | The description-discharge gate: does AC need the description side? | VERDICT (c): AC-forced. The carve re-enters L through the description side | `_build/l3.32-t158-report.md` |

### Bookkeeping

The dated records (spike verdicts, landed-batch records, tripwire changes,
retirement hashes) have moved to `dev/JOURNAL.md`, section *Dated records*,
together with the execution narratives of the large goal rows. This section
stays as the pointer so the registry's structure is unchanged: a fact that is
a RULING belongs in a row above; a fact that is an EPISODE belongs in the
journal; a fact that is a LAW belongs in `dev/LESSONS.md`.
