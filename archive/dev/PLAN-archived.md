# ARCHIVED 2026-08-20

Live screen: `dev/pod/screen.toml`. Live DD index: `dev/pod/rulings.toml`.
This file is the construction registry as it stood on archival day. Nothing below is current.

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
campaign's reconnaissance and probe reports live in `agents/tasks/`, with the
older ones in `agents/tasks/archive/` and the agent briefs that produced them
in `agents/tasks/`. All three are tracked.

The division is by KIND, and a fact belongs in exactly one place: a **ruling**
is a row here, an **episode** is a journal entry, a **law** is a LESSONS entry.

- **Source repository:** `choukh/fol-reification`, local sibling checkout at
  `../fol-reification`. Reference pin at planning time: commit `8b190d5`
  (2026-07-16, M2.7 build-optimization landed; the Con(AC) mathematical
  milestone itself dates to 2026-07-14). Re-pin the exact source commit in §11
  when L1 porting starts.
- **Toolchain parity:** both repos use Agda 2.8.0 + cubical 0.9; all source
  modules are `--cubical --guardedness`. No toolchain migration is needed.

## 0.0 WHERE LJ-1 STANDS, rewritten 2026-08-16

**Status: HISTORICAL from the POD cutover of 2026-08-18, cutover step 12b.** This
screen is the state at the 2026-08-16 pause. The cutover replaced the flow that
wrote it. `dev/pod/queue.toml` produces a task now, `scripts/pod/pod.py` runs the
loop, and `dev/pod/table.toml` holds the rule table. **The mathematical rows below
still hold, because no measurement in them changed.** **Read every sentence about
an orchestrator, a gate or a dispatch as the record of its own date.** Section 0.1
carries two dated corrections for the sentences the cutover made false.

**This screen holds the LATEST state and nothing else.** What it replaces sits
in `dev/JOURNAL.md` under its date. The 2026-08-13 resumption block is SPENT
and all four of its items returned; that record is in the journal.

**Three rows are open and they block in this order. Superseded status moves to
`dev/JOURNAL.md`; only the latest state stays here** (owner, 2026-08-14).

| row | blocked on, as of 2026-08-14 |
|---|---|
| `[LJ-1.7]` | **IT COSTS ABOUT 400 LINES, AND THE PRICE WAS ALREADY IN THIS SECTION** (`[LJ-1.251]`). **The words CHAPTER, TWO LEMMAS, LEAF SUPPLY and STEP 6 all name ONE OBJECT:** `agents/tasks/LJ-1-173/lj-1.173-report.md:857` says step 6 IS the 28 fields, and **open work item 1 below has read「Step 6 re-prices at about 255 and is UNBUILT」all along.** **The figure: about 400**, being 255 for the 28 fields plus a 147-line delivered comparable (`agents/tasks/LJ-1-124/ProbeLJ1124A.agda`, six directions green). **Unpriced tail:** `LeafAgree`'s 14 site facts, `SF`, and `[LJ-1.199]`'s `ω ∈ σ` term. **`sucK` is inside the 28 and is the known 8 GB waller.** **Per-tower share about 28 lines, about 7 percent**, split by `[LJ-1.113]:219-239` before this chain began. **`[LJ-1.249]`'s port is green and re-sited 30 known-good lines; its `ψs` and `ψa` are BARE at `ProbeLJ1249.agda:150-152` and so is `SF`, so it has THREE unsupplied interfaces, not two.** **`[LJ-1.240]`'s inhabitability finding is INFERRED, not MEASURED: its probe never ran.** **`[LJ-1.233]:247` calls `TwelveAgree:519-522` stale; `[LJ-1.251]` checked and the COMMENT is true at HEAD** |
| `[LJ-1.8]`, the trophy | **ROUTE A-PRIME HAS A PRICE: 1,089 LINES** (`[LJ-1.253]`), and it is the first price this route has ever had. `54 + 186 + 26 + 43 + 348 + 399 + 33`. **THE READING RESIDUE IS ZERO**, down from 555 this morning. **Both remaining gaps DISSOLVED rather than closing:** A4's inferred 30-line master gap does not exist, and A6's 47 was a DOUBLE-COUNT of the very graph `[LJ-1.217]` later measured at 296, so A6 is 103 plus 296 and not 150 plus 296. **A6 falls 446 to 399 and A7 falls 47 to 33.** **Five objects dissolved this month** and two of them are inside A5's 348. **Per-tower half: 146 to 196** (`[LJ-1.251]`'s band, because `[LJ-1.248]`'s partition is a survey and excludes A5). **What is UNBUILT: A4's master, A5's 348 and A6's 399.** A1, A2, A3 and A7 exist as green probes |
| `[LJ-1.9]`, the audit | **ANSWERED** (`[LJ-1.218]`, corrected by `[LJ-1.222]`). The wing is **1.70x**, 185.41 s over 11,926 lines, and the gap to DD24's bar is **60.0 s**, an upper bound taken on a loaded machine. `dev/ledger.toml` carries `lines_removable = 83`, of which 64 are unaudited against D-27. **DD24 is the whole rule** (owner, 2026-08-14): the bar was fixed when the AC trophy landed, it does not drift, every GCH module uses it, and intermediate debt is ALLOWED because only the whole wing at the end is judged |

## 0.1 The pause of 2026-08-16 (moved)

**Moved to [dev/memos/2026-08-16-pause.md](memos/2026-08-16-pause.md) on 2026-08-18.**
That pause ended and `[LJ-4]` replaced the flow it planned to resume into. The live screen
is section 0 below and the live task producer is `dev/pod/queue.toml`.

## 0. Where the work stands (2026-08-16)

**REWRITTEN 2026-08-09 for the route change, and re-measured 2026-08-10 at the `[LJ-0.4]` closeout.** The text this replaces described
the internalization route and read as current for the whole day the route
changed. `[LJ-0.1]` caught it. What follows is the two-tower bridge route.

**The endpoint, which is RULED.** BOTH trophies, `L ⊨ AC` and `L ⊨ GCH`, both
stated in L (DD2). The AC-only trophy that opened this registry is a waypoint,
not the endpoint.

**The architecture, which is a CANDIDATE and is ruled at `[LJ-2.5]`.** Build
the L tower, the J tower through rud, and the bridge between them, with the
bridge two-directional. That is the leading architecture and the plan builds
toward it. **It is not yet the binding ruling**, because `[LJ-0.3]` found the
2026-08-09 warrant self-contradictory: the same measurement that changed the
route is declared too weak to bind the constraints it set. The retrospective
refuted the TIMING and not the target, and the owner moved the ruling to where
the evidence will be: after `[LJ-2.1]` measures, `[LJ-2.2]` writes the
benchmarks in, and `[LJ-2.3]` delivers the reuse map.

**The core constraint is architectural and it is DD4, whose row in section 3 is
its only canonical statement.** The total falls out of it and is never pursued
by splitting a chapter, by re-bucketing lines between the two wings, or by any
other accounting move; `[LJ-0.1]`'s predecessors caught that
class of argument twice, and D36's deletion test exists because of it.

**The two quantitative constraints, and NEITHER BINDS TODAY** (DD5). One on
lines, one on build seconds, both at the DOUBLE-trophy endpoint, both measured
against what the internalization route costs for the same two trophies. The
internalization route has never proved GCH, so neither benchmark exists yet.
Both thresholds are SUSPENDED behind flags in `dev/ledger.toml`, every checker
that read them now reports instead of failing, and the re-arm condition is
`[LJ-2.1]`: measure the internalization double trophy, set both benchmarks,
then flip the flags. **A suspended threshold is not a relaxed one.** Nothing
may be argued from the absence of a number.

**The quality bar that DOES bind, today** (DD24). Cold build seconds over
in-fence lines. **This paragraph states NO figure, by design (DD19).** The
applied bar is `dev/ledger.toml`'s `[ratio]` table read at
`scripts/measure/check-ratio.py`, which is the ONE place either number lives;
`scripts/gate/check-baseline-home.py` refused a live restatement anywhere
else, and it was ARCHIVED on 2026-08-18 at commit `fc676cb`. **Nothing
mechanical enforces the one-home rule now, and review is all there is.** The
`[ratio]` header of `dev/ledger.toml` records that loss and names the one live
restatement the audit found. **For the record and not as the bar:** the whole-cone rate was
0.007913 over 16,897 lines, HISTORICAL(2026-08-10), re-measured by `[LJ-0.5]`
after the compression, and 0.008793 over 17,185 lines HISTORICAL(2026-08-13).
`scripts/measure/check-ratio.py` holds the GCH wing to it
within a declared tolerance, **but it will not render a verdict yet**: it
times module slices and the bar is a whole-cone rate, so it refuses until
`--recalibrate` supplies `ac_baseline_module_rate`. A ratio is the right
single bar because a total can be met by writing less of a worse thing and a
ratio cannot: LESSONS P-m measured a twentyfold spread between content classes
that no line count reveals, and P-t measured a twentyeightfold spread inside
one file.

**What is delivered and standing.** `src/` is the internalization tree plus
the first GCH wing masters: **78 masters, 16,897 countable in-fence lines on
the AC side, 133.70 s cold, exit 0**. DD26 excludes the two catalogs,
`Everything` and `Landmarks`, from every size figure. It proves `L ⊨ ZF` and `L ⊨ ZFC` on the Def tower. The
tree is `--safe` and postulate-free, with LEM a module parameter rather than a
postulate (DD9). Quote `python3 scripts/measure/ledger.py --brief` for standing, never
a number found in a paragraph.

**What is in flight: NOTHING, and phase 1 is open.** `[LJ-0.1]` to `[LJ-0.5]`
are closed. The compression prerequisite DD5 set is DISCHARGED at 16,897, and
`make check` is green. Phase 1 (`[LJ-1.1]` to `[LJ-1.9]`) proves GCH on the
internalization route with NO prose, to measure what a GCH wing costs. **Read
`[LJ-1.2]`'s NO-GO and `[LJ-1.11]`'s refutation before funding any of it:** the
first planned crossing has no Delta-0 witness, and route C's structural story
collapses to a step that recognizes no level. Phase 2 sets the benchmarks. Phase 3 builds the
two towers and the bridge and lands both trophies.

**Mathematical prose is FROZEN until both trophies land** (DD23). This is not
the retired check-cost freeze, which is closed. It is narrower and simpler: the
code goes first, the prose phase opens after.

**THE ARCHIVE IS RETRIEVED, NOT CARRIED.** `archive/` holds every retired thing and
`archive/dev/README.md` is the table that says which file answers what. A brief's
`## ARCHIVE` block is injected by the program, which searches the archive scope at brief
build; the return names what it used at `file:line`. **You do not need to know the
history to start work, and this file does not carry it.**

**Retired code is archived, never deleted.** The archive sits OUTSIDE `src/`, so every
gate is structurally blind to it and the postulate-free `--safe` claim stays literally
true of the whole checked tree. Nothing imports across the boundary.

**The closing sequence.** `[L4]` through `[L8]` are route-neutral and none of them opens
until both trophies land: endpoint, then `[L7]`'s archival promotion, then `[L8]`'s gate,
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
- Bedrock removes even that postulate by parameterization (archived D2; the
  live ruling is DD9 in §3), making the whole tree `--safe`.

## 2. Source material survey (pointer)

The port-era survey of the source repository and its measured cost anatomy moved to [dev/memos/source-material-survey.md](memos/source-material-survey.md) ([L3.32-T113]). Its measurements remain a calibration anchor for pricing (§6.2) and for the simplification history (archived §10). Read it when a recon prices a lever or quotes a source-scale figure; the live plan is §0 and the goal registry is §11.

## 3. Ratified decisions (index)

**Every `DD` ruling the owner made is KEPT, and the full text is
[archive/dev/DD-archived.md](../archive/dev/DD-archived.md), unedited.** This section is
the index. It moved on 2026-08-18 because the rows had two defects a live document must
not carry: their ENFORCEMENT sentences named eight archived checkers, `dispatch_policy.py`
seven times; and for the ten a checker now enforces end to end, the row restated a rule
the code already carries, which clause W5 forbids.

**A ruling is not repealed by moving.** Read the disposition column for what enforces it
today, and `dev/memos/LJ-4-pod-program-design.md` section 7.1 for the full reasoning.
**DD0 still binds: a `DD` row is the owner's, and an agent edits one only when asked.**

| DD | What the owner ruled | Date | Disposition | Where it lives now |
|---|---|---|---|---|
| DD0 | `DD` ROWS ARE THE OWNER'S: EDIT ONE ONLY WHEN ASKED | 2026-08-14 | **SUPERSEDED IN PART** | clause W9, and the slot files carry it |
| DD1 | The theorem | 2026-08-09 | **MECHANISED** | `scripts/pod/check-spec-surface.py` |
| DD2 | THE ENDPOINT IS RULED | 2026-08-09 | **WRITTEN RULE** | clause W1, and the slot files carry it |
| DD4 | MAXIMUM REUSE is the architecture's objective | 2026-08-09 | **WRITTEN RULE** | clause W2, and the slot files carry it |
| DD5 | THE TWO QUANTITATIVE CONSTRAINTS are RELATIVE | 2026-08-09 | **MECHANISED** | `ledger.py` validate_benchmark() |
| DD8 | Every block is gated before it is funded | 2026-08-09 | **WRITTEN RULE** | clause W3, and the slot files carry it |
| DD9 | Classical boundary | 2026-08-09 | **MECHANISED** | `lint-agda.py` |
| DD11 | Code and prose craft | 2026-08-09 | **MECHANISED** | `lint-prose.py` |
| DD13 | Retirement is planned from the rewrite side | 2026-08-09 | **WRITTEN RULE** | clause W4, and the slot files carry it |
| DD15 | Measurement discipline: re-measure at every return | 2026-08-09 | **MECHANISED** | `ledger.py --write` at every close |
| DD17 | The standing dispatch order: slots stay full until BOTH trophies a | 2026-08-09 | **SUPERSEDED** | `dev/pod/heads.toml`, a static slot |
| DD18 | THE ARCHIVE AND LITERATURE SURVEYS are sections of the brief and o | 2026-08-09 | **MECHANISED** | `check-survey-quotes.py` + the brief builder |
| DD19 | Governance: one home per rule | 2026-08-09 | **WRITTEN RULE** | clause W5, and the slot files carry it |
| DD22 | Licensing | 2026-08-09 | **MECHANISED** | `reuse lint` |
| DD23 | NO MATHEMATICAL PROSE until both trophies land | 2026-08-09 | **WRITTEN RULE** | clause W6, and the slot files carry it |
| DD24 | THE QUALITY BAR IS SECONDS PER LINE | 2026-08-09 | **MECHANISED** | `dev/pod/table.toml` row `sys-dd24-ratio-bar` |
| DD25 | A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT | 2026-08-10 | **MECHANISED** | pre-flight P18 and rule (f) |
| DD26 | THE CATALOGS ARE NOT COUNTED | 2026-08-10 | **MECHANISED** | `ledger.py` UNCOUNTED |
| DD27 | THE HULL IS INDEXED BY A META TERM ALGEBRA | 2026-08-10 | **WRITTEN RULE** | clause W7, and the slot files carry it |
| DD28 | A PROVABILITY PROBE SURVEYS THE LITERATURE FIRST | 2026-08-16 | **WRITTEN RULE** | clause W8, and the slot files carry it |

## 4. Target skeleton (OWED a re-derivation for DD2, and `[LJ-2.3]` owes it)

The archived D5 target skeleton, its port-era diagram and the rename ledger moved to [dev/memos/target-skeleton-d5.md](memos/target-skeleton-d5.md). Note that DD5 in §3 is a DIFFERENT rule, the two quantitative constraints: the D and DD numbers do not correspond. **`[LJ-2.3]` delivers this section's skeleton for the two-tower route**, and §11 carries that row. So the re-derivation has an owner and a place in the order, and this heading is not an unowned debt.

**TWO CLAUSES THIS SECTION CARRIED ARE NO LONGER TRUE OF THE TREE**, found by `[LJ-1.149]` 2026-08-13. They are corrected here, not repeated. **(1) THE PART LEVEL.** Archived D5 fixed it as Base, FOL, ZF, V, L and Landmarks. **`src/` holds no `ZF/` part today**: it was re-cut into `FOL/`, which `src/README.md:53` records. The measured part level is Base, FOL, V, L and Landmarks, and it is still fixed at that level. **(2) THE PROVISIONAL LAYOUT.** The below-part layout was provisional until the `[L3.10]` re-layering. **`[L3.10]` is a child of `[L3]`, which §11 supersedes wholesale**, and its own row is at `archive/dev/STATUS-archived.md:84`. That re-layering will not run, so its condition is dead and `[LJ-2.3]` inherits the arrangement question with the skeleton.

The authorities for what `src/` contains are `src/README.md` (the master symbol table) and `src/Everything.lagda.md` (the reading catalog), not this section. Read the memo when a rename's history or the port-era layout is needed.

## 5. Working mechanisms (pointer)

The mechanisms this section carried moved to their enforcers ([L3.32-T113]): the LEM parameterization convention is `dev/STYLE-agda.md` section 1 (the ruling is DD9 in §3); the two-catalog doctrine and the named-hypothesis debt form are in `dev/STYLE-agda.md`; probes and gates are `AGENTS.md` and `dev/LESSONS.md` D-1; orchestration is `dev/ORCHESTRATION.md`. The port-era mechanism history (the Frontier record, its re-cuts, construction order) moved to [dev/memos/working-mechanisms.md](memos/working-mechanisms.md); the Frontier's deletion is recorded in the struck D8 row, whose text is at `archive/dev/JOURNAL-archived.md:4275`, and in rows L2.4 and L4.0 of `archive/dev/STATUS-archived.md`. `archive/dev/DECISIONS-archived.md` names struck D8 only in its retired-decisions paragraph and does not carry the row.

## 6. Route tree (DD19)

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
   ruling; the old-to-new map is recorded in §11. **Exercised TWICE.** First
   for L3, on the day the reduction levers were registered. Second on
   2026-08-09 for the new route's own task codes, by the owner's explicit
   instruction to restructure them into a phase hierarchy: `LJ1-T1` to
   `LJ-1.1`, `LJ1-T3` to `LJ-1.3`, `LJ1-T8` to `LJ-1.8`, `LJ1-T11` to
   `LJ-2.1`, `LJ1-T12` to `LJ-3.1`, and the rest by the same phase-and-step
   rule. Every code was PLANNED with no work committed against it, so the
   carve-out's own conditions held.
   **A SECOND RESTRUCTURE, 2026-08-18, by the owner's explicit instruction:** the POD
   goal and its eight children were registered as `L9` and `L9.0` to `L9.7`, in the
   `L` GOAL series. The owner ruled that a TASK carries an `LJ-<phase>.<step>` code,
   so they are `LJ-4` and `LJ-4.0` to `LJ-4.7`. **The carve-out's conditions did NOT
   hold this time**: the codes had left PLANNED and 21 commits named them, so this is
   the owner's ruling and not the carve-out. **`LJ-9` was rejected as the phase**
   because `LJ-9.0`, `LJ-9.1`, `LJ-9.8` and `LJ-9.99` are the SYNTHETIC codes that
   frozen test fixtures use, and a real code there would collide with them; `LJ-4` is
   the next free phase after `LJ-3`. Frozen records keep the old code: 11 commit
   messages and the reports inside `agents/tasks/LJ-4-0/`, whose file names are the
   ones they were born with. **`[LJ-0.3]` found the map unrecorded and
   this text still reading "spent", which is the defect: the ruling existed
   and the record of it did not.** The carve-out is spent again.
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
   `scripts/gate/check-task-index.py` enforces both one-row-per-code and the cap.
   The cap is sized for a one-line scannable entry: code (about 11), short
   title (about 70), verdict (about 30) and pointer (about 50) fit inside
   200, while the failure this rule prevents, the 12,633-token cell that hid
   the T1-T110 verdicts, is far beyond any single line. A row that outgrows
   the cap means the detail has not moved to `dev/JOURNAL.md` or the report,
   where it belongs.

### 6.1 The tree (pointer)

The goal tree's full statements, gates and the L3 execution phases moved to [dev/memos/route-tree.md](memos/route-tree.md). What stays live: the coding rules (§6.0), the projection discipline (§6.2) and the status registry (§11), which is the authoritative one-row-per-goal index. The L6 narrative frame is summarized in §0 and detailed in the memo. Read the memo when a goal's statement or gate is needed.

### 6.2 Caliber, and the single best-effort projection

Every size figure in this registry, unless it says otherwise, is **non-blank
lines inside ` ```agda ` fences**. File lines, blank lines and prose are not
counted; a chapter's file is typically about twice its caliber.

**THE TWO-CALIBER DISCIPLINE IS REVOKED** (owner, 2026-08-09, retiring DD7),
**and DD8's row is where that ruling lives; this section records what the
revoked discipline WAS, so a reader meeting it in an old document can date it.**
It required every projection twice, naive and calibrated, with a x1.3 factor
where a probe or comparable reached and x3 where only a survey did. It existed
because a line total was a hard constraint and the spread between the two
faces was the honest width of the ignorance. **Lines are no longer a hard
constraint in their own right**: DD5 binds a relative total that is not yet
measured, and DD24 binds a ratio.

**A projection is now stated ONCE, best effort, and it NAMES ITS BASIS.** The
basis is one of three words and it does the work the second figure used to do:

- **probe**: a miniature measured in this setting, for this term.
- **comparable**: a delivered chapter of the same content class.
- **survey**: a reading of the literature or of the source repository, with
  nothing measured here.

**Say which.** A reader who knows the basis knows the width without being
handed a band, and `dev/LESSONS.md` P-l still holds: a figure anchored on a
comparable elsewhere is a hypothesis, not a price. The measured
underestimation factors are NOT deleted; they move to LESSONS as history, and
anyone who wants a band may still apply them. They are simply not required.

**An overage is recorded plainly and worked down where real compression
exists.** Evidence can move a technique. A number alone cannot.

## 7. Build constraints (pointer)

**Three rows below name a home the POD cutover of 2026-08-18 moved, and this note
repairs them without rewriting the rows.** Row 3's `scripts/gate/check-tree.py` is
archived; it was rewritten as `scripts/pod/check-closure.py`, which runs at
acceptance conjunct 3 and at pre-flight P16. Rows 5 and 6 name
`dev/ORCHESTRATION.md`, which is archived at `archive/dev/ORCHESTRATION.md`. The
return checklist it held is now the six acceptance conjuncts of
`dev/memos/LJ-4-pod-program-design.md` section 5.4. The heap caps are rule R13's one
caliber and `admits()` at `scripts/pod/pod.py:1112`.

Struck D10, which used to carry these constraints, went on 2026-08-05 because each constraint is now enforced where it fires. The numbered rows below are routing rows; the full original text is in [dev/memos/build-constraints.md](memos/build-constraints.md), and the older §7.5/§7.6 budgets cited by archived D13 are rules 5 and 6:

1. The trusted gate is one invocation, `agda src/Everything.lagda.md`: the build machinery (`Makefile`, [scripts/README.md](../scripts/README.md)).
2. Parallelism is a warm-up layer outside the trust base: the build config.
3. The import-closure audit: `scripts/gate/check-tree.py` closure, [scripts/README.md](../scripts/README.md).
4. The dependency manifest is generated, never committed: the build config.
5. The cold-check budget and the seconds dimension: the ledger (`dev/ledger.toml` [timing] and [[hot]]) and the return checklist, `dev/ORCHESTRATION.md` section 6 step 2.
6. Per-module discipline (heap caps, conversion-blowup triage): `AGENTS.md`, `dev/ORCHESTRATION.md` section 2, `dev/LESSONS.md` C-12, and `scripts/measure/check-timing.py` at every return.
7. Serial fallback stays available: the build config.
8. Reference machine and `-jN` defaults are documented in the build config.

## 8. Process tensions and their resolutions (pointer)

The T1-T6 tension register and its relief valves moved to [dev/memos/process-tensions.md](memos/process-tensions.md). Archived D11's mechanisms are in `archive/dev/DECISIONS-archived.md`; the live relief valves are the L0 standing track (the L0 row of §11) and the L4.1 harmonization (§11). Note that `DD11` is a DIFFERENT rule, code and prose craft: the D and DD numbers do not correspond.

## 9. Risks and mitigations (pointer)

The dated risk register moved to [dev/memos/risks-mitigations.md](memos/risks-mitigations.md). Each mitigation is a standing rule with its own home: DD1 and DD5 in §3, `dev/LESSONS.md` D-1/D-6/D-10, the §6.0 rules, and the return checklist in `dev/ORCHESTRATION.md` section 6. **`dev/ORCHESTRATION.md` is archived** at `archive/dev/ORCHESTRATION.md` since 2026-08-18, and the six acceptance conjuncts of `dev/memos/LJ-4-pod-program-design.md` section 5.4 replace that checklist.

## 10. Candidate simplification register (pointer)

The S1-S18 register moved to [dev/memos/simplification-register.md](memos/simplification-register.md), with its statuses brought current to the `[L3.32-T8]` verdicts: S13 and S15 shipped, S14 and S16 reverted at their gates, S17's probe red, S18 deferred. Live tracking of the deferred row is `dev/ledger.toml`'s [[excluded]] table.

## 11. MASTER status table (live)

**Status: SET ASIDE AS THE TASK PRODUCER by the POD cutover of 2026-08-18,
amendment A7.** `dev/pod/queue.toml` produces tasks now and the program-written
transition log replaces the dispatch index. **The rows are KEPT as the record**, and
cutover step 13 seeded the queue with one entry per PLANNED row, so no planned goal was
lost. The goal codes themselves are unchanged and still name the work.

A script path inside a
task-index row is the path as of that row's own date; scripts moved into
`scripts/gate/`, `scripts/measure/`, `scripts/dispatch/` and `scripts/site/` on
2026-08-15, so resolve an unqualified `scripts/<name>.py` by basename.

One row per goal code; update the row in the same commit that changes the
status (§6.0 rule 6). Dispatched-task codes are indexed separately below,
one row per code (§6.0 rules 7 and 8). Bookkeeping lines follow the table.

**THIS TABLE HOLDS OPEN WORK ONLY.** A goal that reached DONE, CLOSED or SUPERSEDED is
`archive/dev/L-goals-archived.md`, and the fuller status text of the retired route is
`archive/dev/STATUS-archived.md`. **A live screen that carries a dead route's history
stops being read**, and the program retrieves from the archive when a task needs it.

**`[L4]` THROUGH `[L8]` ARE ROUTE-NEUTRAL** and none of them opens until the `LJ` series
lands BOTH trophies inside both constraints. `[L8.2]` is the gate that `[L4.1]` waits on.

| Code | Goal | Status |
|---|---|---|
| LJ-0 | Recon and pricing for the LJ route | **CLOSED.** 23 dispatches. Its measurements are why the two-tower route was funded |
| LJ-1 | THE LIVE CAMPAIGN: both trophies, stated in L | **RUNNING.** 426 dispatches. `dev/pod/queue.toml` produces the next one; `[LJ-1.386]` is the resumption task. **Owner 2026-08-20:** one W4 collection of `src/` after this campaign closes, not gated on `[LJ-2.5]` |
| LJ-2 | The architecture ruling and the internalization measurement | **OPEN**, 6 entries queued. `[LJ-2.5]` is clause W1's address: the two towers are a CANDIDATE until it lands |
| LJ-3 | The GCH wing | **OPEN**, 7 entries queued |
| LJ-4 | The orchestration flow becomes a program | **DONE 2026-08-18** at `fc676cb`. The design is `dev/memos/LJ-4-pod-program-design.md` |
| L4 | Convergence | PLANNED (runs after `[L3.32]`'s surgery lands) |
| L4.0 | Empty Frontier, unconditional root | DONE in substance under `[L2.4]` (Frontier empty and deleted, root unconditional) |
| L4.1 | Whole-book harmonization pass | PLANNED (scope grown: the retirement surgery deletes chapters, and the identification story is corrected) |
| L4.2 | Landmarks/README/Charter updates | PLANNED (the Charter status must read `L ⊨ ZFC ∧ L ⊨ GCH`) |
| L5 | Build and site infrastructure | PLANNED |
| L5.0 | Build machinery port | PLANNED |
| L5.1 | make check split | PLANNED (the three named gate defects belong here: the two linters that skip untracked files, the glossary avoid-list keying off markers, and the missing end-of-file check) |
| L5.2 | CI strategy | PLANNED |
| L5.3 | Site pipeline load test | PLANNED |
| L6 | The narrative master plan (the meeting at bedrock) | **REGISTERED 2026-08-04 by owner direction.** The standing narrative frame: geology and inner model theory meet at the bedrock, with `L is a bedrock` as the second trophy; every asset is valued against both trophies from this row onward. Phases and the asset re-coloring rule are in §6.1; the geology entry fee and the two mandatory corpus gates are measured in `agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md` |
| L7 | The endpoint promotion and the archive's completion | **PLANNED**, ruled by archived D20 2026-08-04; the archive REGIME is in force now, this row is the endpoint work |
| L7.0 | Archive `main`, promote the working branch | PLANNED (same day as the endpoint, before any tidying) |
| L7.1 | Final archival sweep, pre-regime deletions entered | PLANNED |
| L7.2 | Verify the exclusions end to end; REUSE still covers `archive/` | PLANNED |
| L7.3 | Final pass on `archive/README.md` | PLANNED |
| L7.4 | Final pass on `dev/ARCHIVE.md` | PLANNED |
| L8 | Consolidation, and the gate before prose | **PLANNED**, ruled by archived D21 2026-08-04; opens when `[L7]` closes |
| L8.0 | Foundation refactor at T8 scale, on the post-archival tree | PLANNED (candidates re-examined, not inherited) |
| L8.1 | Line-by-line polish over the whole tree | PLANNED |
| L8.2 | **THE GATE**: report to the owner before any prose phase | PLANNED (the owner adds further code-shaping work here; `[L4.1]` waits on it) |

### Task index (one row per dispatch, section 6.0 rules 7 and 8)

The dispatched tasks on the two-tower bridge route, one row per code.

**The code is `LJ-<phase>.<step>`** and the phase is the hierarchy the owner
asked for: **1** is the internalization GCH wing, **2** is quantifying DD5's
benchmarks from it AND RULING THE ARCHITECTURE on them, and **3** is the
double trophy on whatever phase 2 rules. A phase is a barrier: phase 2 cannot
start before phase 1 delivers, because it measures what phase 1 built, and
phase 3's constraints are the numbers phase 2 sets.

**The evidence the `[LJ-2.5]` ruling is owed, and the record `[LJ-1.149]`
corrected, live in `dev/JOURNAL.md`, 2026-08-14, under `[LJ-1.187]`.**

**THE ARCHITECTURE RULING SITS AT `[LJ-2.5]`, not at the route change**
(DD2, amended 2026-08-09 on `[LJ-0.3]`). The endpoint is ruled and closed; the
two-tower architecture is the leading CANDIDATE. So phase 2 gained the reuse
map and its adversarial review, which were phase 3's first two rows: the
evidence has to exist before the ruling that rests on it. Those two rows are
marked SUPERSEDED and point at their new codes, because rule 3 forbids a
third renumbering and prescribes exactly this instead. Inside a phase the steps run as their own dependencies allow, and a
row says which. The verdict cell is a few words; the detail lives in the named report,
`dev/JOURNAL.md`, the deliverable or the brief.

**THE ARCHIVE IS SEARCHED BY THE PROGRAM, not remembered by a reader.** At brief build
it injects an `## ARCHIVE` block from the archive scope, and the return names what it
used at `file:line`. `archive/dev/README.md` is the table that says which archived file
answers what. **`dev/LESSONS.md` is NOT archived and still binds.**

**THE DISPATCH INDEX IS ARCHIVED.** Its 464 rows moved to
[archive/dev/LJ-dispatch-index.md](../archive/dev/LJ-dispatch-index.md) on 2026-08-18,
unedited. **`dev/pod/queue.toml` produces a task now and `dev/pod/transitions/` indexes
one.** A citation to any `LJ` code still resolves there, and `agents/tasks/<CODE>/` holds
that task's brief, report and probes.


### Bookkeeping

The dated records (spike verdicts, landed-batch records, tripwire changes,
retirement hashes) have moved to `dev/JOURNAL.md`, section *Dated records*,
together with the execution narratives of the large goal rows. This section
stays as the pointer so the registry's structure is unchanged: a fact that is
a RULING belongs in a row above; a fact that is an EPISODE belongs in the
journal; a fact that is a LAW belongs in `dev/LESSONS.md`.
