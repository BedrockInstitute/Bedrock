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
| DD23 | **NO MATHEMATICAL PROSE until both trophies land. The prose phase comes AFTER.** | **Ruled 2026-08-09 by the owner.** Until `L ⊨ AC` and `L ⊨ GCH` are both proved on the two-tower bridge inside DD5's constraints, write NO mathematical prose: no chapter narrative, no `<!--en--> <!--zh--> <!--ja-->` exposition of the mathematics, no reader-facing explanation of a construction. Code and its own comments only. **The prose phase opens when the double trophy lands, and not before.** This is not a licence to write badly: DD11's naming hygiene, `dev/STYLE-agda.md` and the OPTIONS header all still bind, and so does the ASD-STE100 rule for every brief, report and message, which is working text and not mathematical prose. **The reason is DD4.** Prose written against an architecture that reuse has not settled is prose written twice, and the retired route paid that bill: its chapters were narrated at a shape the route then left behind. **What this does NOT suspend**: the i18n marker grammar where prose already exists, the reader-facing documents under `docs/`, and `dev/JOURNAL.md`, which is a record and not exposition. |
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

### Task index (one row per dispatch, section 6.0 rules 7 and 8)

The dispatched tasks under `[LJ1]`, the two-tower bridge route, one row per
code. The verdict cell is a few words; the detail lives in the named report,
`dev/JOURNAL.md`, the deliverable or the brief.

**The retired route's 264 rows are `dev/TASKS-archived.md`, unedited**, under
the `L3.32-T` series. Both series resolve and neither reuses a number.
`scripts/check-task-index.py` enforces one row per code and the 200-character
cap.

**EVERY BRIEF SURVEYS THE ARCHIVE BEFORE IT IS SENT, AND EVERY REPORT NAMES
WHAT IT USED.** Ruled by the owner 2026-08-09 as a mechanism rather than an
encouragement. A brief carries an ARCHIVE section listing the archived code,
the archived task rows and the lessons that may bear on the task; a report
carries an ARCHIVE USED section naming what it actually read and what it took
from each. The retired route cost a year of measurement and the whole of it
is still on disk: `archive/` for the code, `dev/ARCHIVE.md` for why each
module left and what it did right, `dev/TASKS-archived.md` for what every
dispatch found, `dev/DECISIONS-archived.md` for the rulings, and
`dev/LESSONS.md`, which is NOT archived and still binds.

| Code | Task | Verdict | Detail |
|---|---|---|---|

### Bookkeeping

The dated records (spike verdicts, landed-batch records, tripwire changes,
retirement hashes) have moved to `dev/JOURNAL.md`, section *Dated records*,
together with the execution narratives of the large goal rows. This section
stays as the pointer so the registry's structure is unchanged: a fact that is
a RULING belongs in a row above; a fact that is an EPISODE belongs in the
journal; a fact that is a LAW belongs in `dev/LESSONS.md`.
