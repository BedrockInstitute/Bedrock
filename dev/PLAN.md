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

## 0.0 WHERE LJ-1 STANDS, rewritten 2026-08-14

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

**THE OPEN WORK, in dependency order.**

**1. The supply chain for the satisfaction layer.** `[LJ-1.172]` built steps 1
to 5 and REFUTED step 6 at the join. `[LJ-1.173]` swept the refutation to **21
fields across three records and CURED all 21**, for 77 lines, green.
**2026-08-15: step 6 is NO LONGER UNBUILT, and the 255 STANDS at about 305.**
`[LJ-1.252]` reopened the join `[LJ-1.199]` closed by reading, at five lines.
`[LJ-1.254]` built `envSetK` and `sucK`, and **measured that `sucK` does NOT
wall**. `[LJ-1.255]` built **5 of the 28** and read a marginal rate that
`[LJ-1.256]` then OVERTURNED: **the five bodies are ONE PROOF WRITTEN FIVE
TIMES, so zero variance across five is one observation**, and the copies are
avoidable because `src/L/Condensation.lagda.md:2926` is a slot-generic
`EnvSet` whose own comment says one copy serves every frame layout and both
towers. **Three of the nine shape rows are now MEASURED and all three came in
AT OR UNDER budget:** L3 25 against 30, L4 11 against 12, L9 13 against 25.
**The figure: about 255 plus about 50 for `sucK`'s union closure, which no row
prices.** **What survives from `[LJ-1.255]`: four `envInK-*` fields lack the
numeral premise, a real defect in `[LJ-1.173]:843-846`, whose row 1 gave them
`ar ∈ K` instead.** **They are NOT blocked: the supplier is delivered at
`src/L/Coding/CodeSet.lagda.md:185-204` and the block was my brief's own
no-master-edit rule.** **And `someEnv`'s second blocker is delivered in FOUR
lines at `src/L/Condensation.lagda.md:3042`, not the 120 the report priced.**

**2. Route A-prime's five probes, and DD8 now allows them.** `[LJ-1.227]` named
the widest unmeasured term and the probe for every one of A1, A2, A3, A4 and
A7, so five build briefs are writable for the first time. **None of the five
blocks dissolves**, which the same task asked first for each. **A2 is the one
to run first**: every downstream block names its predicate, `injAt` exists
nowhere in `src/**/*.lagda.md`, and measuring it also pins the one surviving
double-count.

**3. The wing's seconds have a LOCATION, and the cure is the owner's call.**
`[LJ-1.214]` measured that the telescope component at `Deserialization` carries
**7,925 of 8,236 ms, 96 percent**. All three cheap levers measured void:
sealing moves 83 ms, emptying the numeral content moves 47 ms the WRONG way,
and instantiation is 0.9 percent. **Removing the component would recover the
8.2 s and restore 21 fields that were FALSE before `[LJ-1.173]` cured them.**
So it is a design question and not an edit.

**WHAT IS WAITING ON THE OWNER, and none of it blocks the three above.**

- **DD4 against DD24.** A cure in shared machinery made every master faster and
  the ratio WORSE, 1.56x to 1.91x, because the AC side gained 41.7 percent and
  the wing 7.9. **It is a property of the bar, not an accident of that edit.**
  `[LJ-1.155]` then found the counter-case: a wing-local cure does not move the
  denominator, and the wing went 2.06x to 1.60x. **So the ruling is no longer
  forced, but the bar still reads a shared cure as a regression.**
- **The `build` bundle is FULL at the cap of 12, and C-42 did not go in.** I
  routed the new law to `recon` and `probe`, which had room, and to four trigger
  words. **A build acting on a refutation therefore reaches it through layer 2
  and not through its bundle.** Evicting one of the twelve is the alternative
  and `dev/rules.toml`'s own header says the cap exists to make that question
  audible. **I am asking it rather than answering it.**
- **`src/L/Choice/Name.lagda.md`.** `[LJ-1.172]`'s step-1 drop-in is blocked by
  **DD23** and not by code. It makes three narrative sentences false, and
  repairing them is mathematical prose.
- **The three `*Agree` masters.** Measured stable on the cured tree, but
  `[LJ-1.146]` found that retiring them retires the wing, because the whole
  chain is unconsumed only because the trophy is unwritten.
- **`check-unbound-hyp.py` rule 3.** `answers` and `ih` are NOT refutable,
  MEASURED, so the fix belongs in the checker.
- **`dev/memos/source-material-survey.md:3`** is marked STANDING while it
  endorses the revoked two-caliber rule.

**ONE ORCHESTRATOR HABIT THAT COST THREE TIMES ON 2026-08-13**: the episode
and its rule live in `dev/JOURNAL.md`, 2026-08-14, under `[LJ-1.187]`.

## 0. Where the work stands (2026-08-10)

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
in-fence lines. The delivered AC wing measures **0.007913 s/line**, from a
133.70 s mean of three cold runs over 16,897 lines, re-measured by `[LJ-0.5]`
after the compression. `scripts/check-ratio.py` holds the GCH wing to it
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
postulate (DD9). Quote `python3 scripts/ledger.py --brief` for standing, never
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

**FOUR ARCHIVES, and surveying them is a brief section rather than a hope**
(DD19). `archive/` holds retired code, with `archive/src/2026-08-09-rud-route/` holding the 72
files of the retired route; `archive/dev/STATUS-archived.md` holds the 96 goal rows of
the internalization route; `archive/dev/TASKS-archived.md` holds what each of 265
dispatches found; `archive/dev/JOURNAL-archived.md` holds why; and
`archive/dev/DECISIONS-archived.md` holds the rulings that route ran on. Every brief
names what may bear on its task, and every return names what it used, at
`file:line`. **`dev/LESSONS.md` is NOT archived and still binds.**

**Retired code is archived, never deleted.** The archive sits OUTSIDE `src/`,
so every gate is structurally blind to it and the postulate-free `--safe` claim
stays literally true of the whole checked tree. Archived files are frozen and
nothing imports across the boundary.

**The closing sequence.** `[L3]` and its 59 children are superseded wholesale
by the `LJ` series. `[L4]` through `[L8]` survive because they are
route-neutral, and none of them opens until both trophies land: endpoint, then
`[L7]`'s archival promotion, then `[L8]`'s consolidation and its gate, and only
after that gate does `[L4]`'s whole-book harmonization open.

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

## 3. Ratified decisions
**The `DD` series, rebuilt 2026-08-09 on the two-tower bridge ruling and CONSOLIDATED the same day.** The owner ruled that the whole `D` series be archived and the list rebuilt, keeping only what does not contradict the new route and what is useful to it. **The retired `D` series lives in `archive/dev/DECISIONS-archived.md`, unedited**, and `scripts/check-rule-ids.py` resolves `D` citations against it, so every old citation still means what it meant. **A number is never reused, in either series.**

**Consolidated and revoked codes.** The first cut ran to 25 rows and the owner ruled it down under 20 by merging like with like. **DD3** merged into DD2, **DD6** into DD5, **DD10** into DD9 and DD11, **DD12** and **DD14** into DD13, **DD16** into DD15, **DD20** and **DD21** into DD19, **DD25** into DD24, and the old DD18 content into DD19, freeing DD18 for the archive-survey mechanism. **DD7 is REVOKED outright**, not merged: lines are no longer a hard constraint in their own right, so the two-caliber rule it carried is gone and a projection is now ONE best-effort figure with its basis named, which lives in DD8. These codes still resolve, so a commit message or brief that cites one is not broken. **No pure pointers.** Every row states its own minimum content; a rule you must open another file to read is a rule with a broken home, which DD19 forbids.

| # | Decision | Ruling |
|---|----------|--------|
| DD0 | **`DD` ROWS ARE THE OWNER'S: EDIT ONE ONLY WHEN ASKED, AND RECORD EVERYTHING ABOUT IT IN THE JOURNAL. A TEMPORARY INSTRUCTION IS NOT A READING OF THE RULES AND NOT PERMISSION TO BREAK THEM. THE OWNER MAY DISREGARD ANY `DD`; THE AGENT MAY NOT.** | **Ruled 2026-08-14 by the owner, in the owner's own words**, and numbered below DD1 because it governs how EVERY other row is read. **THREE PARTS, and the third is the one that was missed.** (1) A temporary instruction from the owner binds the task it names and nothing else. (2) It changes NO ruling, because a ruling it does not mention was never being read. (3) **It is not evidence about what the AGENT may do.** The owner setting a rule aside is the owner using their authority; it is not a precedent, not a reading, and not permission. **SO THE ORCHESTRATOR NEVER DERIVES A STANDING RULE FROM A ONE-OFF OWNER INSTRUCTION**, and the test is one question: **would the sentence justifying this choice write, citing the RULING rather than the owner's past act?** If it will not write, take what the rule gives, which is DD17's own clause generalized to every row. **Enforcement: REVIEW ONLY, and this row says so rather than claiming a gate.** No checker can hold it, because the act it forbids is an inference and the resulting tokens are legal by construction. The enforcement points are the brief's tier line, which names the head AND the version, and the written justifying sentence whenever the head is not the table's. **The episode and the checker finding live in `dev/JOURNAL.md`, 2026-08-14, under `DD0`.** **TWO STANDING PROHIBITIONS, ruled 2026-08-14 by the owner.** **(1) A `DD` ROW IS NOT EDITED UNLESS THE OWNER ASKS FOR THE EDIT.** Not to clarify it, not to refresh a figure inside it, not to record what happened to it. The orchestrator PROPOSES a change and the owner rules it. **(2) EVERY RECORD *ABOUT* A `DD` GOES TO `dev/JOURNAL.md`, and never onto the row.** An episode, a measurement, a correction, a note on how a rule was applied or misapplied: all journal. **The row states the rule and nothing else.** Enforcement: REVIEW ONLY, because nothing mechanical can tell an authorized edit from an unauthorized one. |
| DD1 | The theorem, stated honestly | As in section 1: V=L ⊨ ZFC, relative consistency, relative to the host, and never an unqualified "Con(ZFC)". The endpoint is the SAME L satisfying GCH, stated internally, giving Con(ZF) → Con(ZFC + GCH) under the same relativization; "Con(GCH)" is likewise never claimed unqualified. |
| DD2 | **THE ENDPOINT IS RULED. THE ARCHITECTURE IS THE LEADING CANDIDATE, and it is ruled at `[LJ-2.5]` against measurement.** | **Ruled 2026-08-09 by the owner, and AMENDED the same day on `[LJ-0.3]`'s finding.** **WHAT IS RULED AND NOT REOPENABLE:** both trophies, `L ⊨ AC` and `L ⊨ GCH`, both stated in L, so no re-founding onto J is ordered; and where a bridge is built it delivers BOTH directions of the two-definition identification, never the one-way variant. **WHAT IS A CANDIDATE:** the two towers and the bridge, L plus J through rud. It is the leading architecture and the plan builds toward it. It is not yet the binding ruling. **SO THE RULING MOVES TO WHERE THE EVIDENCE IS**, `[LJ-2.5]`, after `[LJ-2.1]` measures the internalization double trophy, `[LJ-2.2]` writes both DD5 benchmarks in, and `[LJ-2.3]` delivers the reuse map that DD4's core constraint turns on. The candidate is confirmed, amended or replaced there, on measured evidence and not before. **WHAT THIS DOES NOT LICENSE.** Phases 1 and 2 are unchanged and are dispatched normally; a return may not re-table the ENDPOINT, which is ruled; and nobody re-opens the architecture question outside `[LJ-2.5]` on an argument rather than a measurement. Absorbs DD3. **The amendment's warrant and the evidence for `[LJ-2.5]` live in `dev/JOURNAL.md`, 2026-08-14, under `DD2`.** |
| DD4 | **MAXIMUM REUSE is the architecture's objective, and it is the same rule as WRITE IT GENERIC.** | **Ruled 2026-08-09 by the owner, as the route's CORE constraint, which is architectural and not arithmetic.** Follow the textbooks to the best route and architecture, and maximize the code the two proofs share. **The total is not to be pursued by splitting, re-bucketing, or any move that lowers reuse.** **THIS ROW HAS NO HARD METRIC, and that is the owner's decision, not an omission** (ruled 2026-08-09, when a sufficiency audit proposed a reuse checker). A shared-line count would be gamed the moment it gated anything: code can be moved into a shared module without either proof needing it there, and the number would rise while the architecture got worse. **So there is no threshold and no pass-or-fail on the SUBSTANCE, and there never will be. The STATEMENT is gated: `scripts/check-dd4-stated.py` refuses a brief that carries no DD4 section, reading the heading and never a word of the content, which is this row's own enforcement point made mechanical rather than a metric smuggled in.** **THE COMPENSATING MECHANISM IS REPETITION, and it is the enforcement point this row names:** the principle is stated in EVERY brief this project sends, whatever the task kind, and every return says what it did about it. A rule with no meter has to be said out loud every time or it decays into a preference. **IT IS THE SAME RULE AS "WRITE IT GENERIC", absorbed here 2026-08-09 from archived D29 so it has one home.** Sharing between the two proofs is what generic writing BUYS; they are one discipline seen from two ends. **THE THREE MOMENTS, from D29, unchanged:** (1) a RECON brief asks out loud whether the content can be written once at a generic carrier and instantiated, and the report answers with a price for BOTH shapes, so a recon that returns only the fixed shape has not finished; (2) a BUILD brief states generic or fixed and why, and the default is generic; (3) the orchestrator asks it of the ROUTE's shape before any brief exists, because the cheapest generic decision is made before two chapters exist to unify. **THE ATTITUDE CLAUSE, the owner's own emphasis: keep a level head about the up-front cost.** Generic is more expensive on the first instance and cheaper from the second, so a stop-line is the standing temptation to write fixed and apologise later. **A stop-line is NEVER a reason to write fixed:** say so and stop for a re-price, rather than silently delivering the fixed shape inside the cap. **THE ONE MEASURED EXCEPTION is narrow and named**, `dev/LESSONS.md` P-r: a fold over a clause list costs about 3x the hand-written conjunction when its result type must be UNFOLDED by every consumer. That shape, and only that shape, is written out. **Enforcement:** the standing brief clause in `dev/ORCHESTRATION.md` section 3, which fires on every task kind; the route-planning clause in section 5; and the return audit in section 6, which rejects a build that chose fixed without saying so. Absorbs D29. **The `ledger.py --reuse` report, the P-h measurements and the two paid-for episodes live in `dev/JOURNAL.md`, 2026-08-14, under `DD4`.** |
| DD5 | **THE TWO QUANTITATIVE CONSTRAINTS are RELATIVE, and NEITHER BINDS until it is clear.** | **Ruled 2026-08-09 by the owner.** Both are taken at the DOUBLE-trophy endpoint and both are measured against the internalization route at ITS double-trophy endpoint. (1) LINES: this route's total must not exceed internalization's. (2) TIME: this route's total build time must not exceed internalization's. **A benchmark that is not clear is made clear first**, by the owner's own instruction. **THE CALIBER**, absorbed from DD6: a size figure is the count of non-blank lines inside ` ```agda ` fences over git-tracked `*.lagda.md` under `src/`, the PRIMARY figure is the double-trophy endpoint, and `scripts/ledger.py --brief` is its only admissible source. The per-trophy split and the AC cap survive as DIAGNOSTICS. The deletion test survives UNCHANGED, because it is the structural test that keeps the accounting honest whichever figure binds. **DD5 measure 1 applies exactly as written: the a-priori ceiling STAYS at `[LJ-1.1]`'s figure, recorded before any build, and the excess is the finding.** A re-price may not raise a ceiling; that is the whole point of recording it early. **THREE MEASURES, and the first is the one that removes the incentive.** **(1) THE A-PRIORI CEILING.** `[LJ-1.1]` owes one best-effort projection with its basis, recorded BEFORE anything is built and before anyone could gain from inflating it. **The line benchmark is then the SMALLER of that projection and the measurement.** Building fat cannot raise the bar; building tight still lowers it. **(2) THE BUILDERS ARE NOT TOLD they are setting a bar.** A phase-1 build brief says write this as the deliverable, as tight as if it shipped, and does NOT say the result becomes the number phase 3 must beat. Naming an incentive creates it. **(3) `[LJ-1.9]` REPORTS NET REMOVABLE LINES**, from an independent reader asking what did not need to be there, and `[LJ-2.1]` records measured, projected and removable side by side. **The owner's judgment is the backstop, not the primary guard:** `[LJ-2.2]` does not flip the flags until it is on the record. A benchmark nobody questioned is not a measurement, it is a number the project chose for itself. **ENFORCEMENT, per measure, and stated as it really is.** Measure 1 is MECHANICAL: `dev/ledger.toml` carries `lines_apriori`, and `ledger.py --check` refuses a binding line benchmark that has no a-priori projection, or one larger than it. The gate is silent while `lines_state` reads unbound, so it costs nothing through phase 1 and fires on the day the number starts to matter. Measure 3 is HALF mechanical: `lines_removable` has a field, so the figure has a home and its absence is visible, but nothing checks that the reader was independent. **Measure 2 is REVIEW ONLY and says so**: nothing can read a brief, so the clause in `dev/ORCHESTRATION.md` section 3 and the return audit are all there is. A row that claimed a checker it does not have would be worse than this one. **The benchmark status, the compression-prerequisite history and the self-set-hole analysis live in `dev/JOURNAL.md`, 2026-08-14, under `DD5`.** |
| DD8 | Every block is gated before it is funded, and an estimate is ONE best-effort number | Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work. A green gate narrows the band and lowers its top. **A build brief that cannot name its widest unmeasured term, and the probe that measures it, is not ready to send.** A probe IS committed, in `agents/tasks/<TASK>/` beside its brief and its report, and never under `src/` (`dev/LESSONS.md` D-1). **THE TWO-CALIBER RULE IS REVOKED** (owner, 2026-08-09, retiring DD7). Lines are no longer a hard constraint in their own right, so a projection is stated ONCE, as a best-effort figure, with its basis named: probe, delivered comparable, or survey. **Say which**, because the basis is what a reader needs and the second decimal never was. An overage is still recorded plainly and worked down where real compression exists. |
| DD9 | Classical boundary, and generated proof | No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter; the whole tree is `--safe`. The archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree. A materially worse performance projection escalates to the owner. **GENERATED PROOF**, absorbed from DD10: a macro or reflection layer is admissible only where it is cheaper to READ than what it replaces, never merely cheaper to write, and `dev/STYLE-agda.md` names the forbidden constructs that `lint-agda.py` enforces. |
| DD11 | Code and prose craft | **NAMING**: a name says what the thing IS, not how it was built; an implicit nobody can infer is dissolved; a name with zero or one consumer is inlined. **PROSE**: no em dash in any language, CJK full-width sentence punctuation with half-width parentheses and `「」` quotes, English only inside ` ```agda ` fences, one master `.lagda.md` per module with the `<!--en--> <!--zh--> <!--ja-->` marker grammar. `scripts/lint-prose.py` and `weave-i18n.py` enforce most of this and `dev/STYLE-i18n.md` is the canonical statement. Absorbs DD10's craft half. |
| DD13 | Retirement is planned from the rewrite side, sunk cost decides nothing, and nothing is deleted | A consumer does not prove that a chapter must stay. **First price the ideal form of the content, written fresh today. Then compare.** "We already paid for it" never decides the question, in either direction, and DD2 is itself an instance: the route changed after a year of work. DD4 now asks the same question of every existing chapter, since content that cannot be shared may be cheaper rewritten than adapted. **ARCHIVE, NEVER DELETE**, absorbed from DD14: retired code goes to `archive/` at the repository root, outside `src/`, so every gate is blind to it by structure; archived files are frozen and nothing imports across the boundary; `dev/ARCHIVE.md` records what each module is, why it left, where it was last green, what it did right from measurement rather than praise, and what would make it worth a second look. This also governs `archive/dev/DECISIONS-archived.md`, `archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`. Absorbs DD12 and DD14. |
| DD15 | Measurement discipline: re-measure at every return, and never in the foreground | The ledger is re-measured at every return that could move it, and no standing figure is ever quoted from a paragraph. **A full cold typecheck runs in the BACKGROUND, never in the foreground**, absorbed from DD16: it costs minutes to tens of minutes and must not block a session. DD5's time constraint makes the measurement more load-bearing, not less, so the protocol is fixed: interface cache moved aside, single process, quiet machine, `/usr/bin/time -p`, and the figure recorded with its protocol beside it. Absorbs DD16. |
| DD17 | **The standing dispatch order: slots stay full until BOTH trophies are proved inside both constraints, and every dispatch takes the head the SWITCH gives unless a named exception applies** | Amended 2026-08-09 from an AC-only terminus. An idle agent slot is a defect: a slot stays empty only when a real block stops every remaining task, and an audit is not a reason to leave one idle. **THE TIER, restored 2026-08-09 and REPLACED BY A SWITCH 2026-08-13 (owner's ruling).** The head is no longer written here, because a table restated in a second file drifts and DD19 forbids a rule that is canonical twice. **`scripts/dispatch_policy.py` is the ONE home**: it holds both versions of this rule, the head for each case, the date the current version was set, its reason and its revert condition, and `python3 scripts/dispatch_policy.py` prints all of it. **TWO MODES, exactly one in force, and THIS ROW NAMES NEITHER'S HEADS.** They are `deepseek-subagent-mode` and `in-harness-subagent-mode`, **each named for the head it LEADS with** (owner, 2026-08-14). The retired names still RESOLVE, because 52 frozen briefs carry one of them; `scripts/dispatch_policy.py` holds the alias map and C-41 is why. The heads per case, the version in force, the date it was set, its reason and its revert condition all live in `scripts/dispatch_policy.py` and are printed by running it. **A head named here would be canonical twice, which DD19 forbids and which is exactly how the old fixed-tier text drifted.** What this row fixes is that there ARE two versions, that exactly one is in force, and that the switch is the only place to learn which. One version is TEMPORARY, and its reason is QUOTA and never quality; the owner cancels it by word. **THE INVARIANT UNDER BOTH: the critic is never the same head as the author**, which is why the two tables swap the default row and the adversarial row. Enforcement is the brief header, which names the head AND the version it was chosen under, and `scripts/check-dispatch-policy.py` reads every brief against the switch. **The switch cannot force the choice and this row does not pretend otherwise:** an in-harness dispatch never passes through `.claude/skills/codex-dispatch/dispatch.py`, so the switch drives that dispatcher's default harness, the checker and the inspection command, and makes a wrong head DETECTABLE rather than impossible. **If the sentence justifying another head will not write, take the head the table gives.** **WHAT A MODE SWITCH REQUIRES, and it is written down so nobody derives it again** (owner's instruction, 2026-08-14). **SIX STEPS, in order.** **(1) Set `VERSION_IN_FORCE` in `scripts/dispatch_policy.py` and change NOTHING ELSE in the tables.** **(2) Update that file's provenance**, `SET_ON`, `SET_BY`, `REASON`, `REVERT_CONDITION`. **Never invent a reason the owner did not give**; record that none was given, and record what the OUTGOING mode's reason was, so a later reader cannot read the cancellation as a judgement on a head. **(3) Run `scripts/check-dispatch-policy.py` and expect red.** A brief written under the old mode names that mode on its tier line and WAS CORRECT. **A frozen record is never rewritten, so red here is a defect in the GATE**: the checker must judge a brief by the mode it NAMES, never by today's switch. **(4) If a mode is RENAMED, the retired name must keep resolving**, through `ALIASES` in the same file, because briefs carry it. C-41 is the law. **(5) Delete or rewrite any memory or document that asserted the outgoing mode**, or it will be read as current. **(6) Agents already RUNNING keep their head.** It was correct when they were sent, and the owner ruled exactly that on 2026-08-14. **AND KNOW WHAT ACTUALLY CHANGES, which is more than the table.** An in-harness dispatch passes through NO tool, so under a mode that leads in-harness the DD4 and DD18 refusals in `dispatch.py` never fire and C-12's Agda slot accounting counts nothing. Under a mode that leads through `herdr` they all fire again, and `dispatch.py` becomes load-bearing: a defect in it is invisible while nothing walks that path. **Check that path works BEFORE the flip, not after.** **THE EMERGENCY BREAKTHROUGH TIER.** When a return does NOT do its task well AND the point is a critical breakthrough, the orchestrator may re-dispatch to Fable 5 at maximum effort without asking. **The clause is written for whichever head the switch gave**, and it named codex when codex was the default. BOTH conditions bind and the second is the scarce one: a critical breakthrough is a point where the loop cannot advance, so a gate whose verdict blocks the next funded build, a wall no measured cure passes, or a refutation that would re-price the route. Ordinary slowness or a task worth redoing at the same tier is NOT one. **A stop, a refutation and a RED are GOOD returns and never a trigger**; this campaign's most valuable results came back as REDs. Each use names its trigger in the brief, records the escalation in the task index row, and reports what the higher tier found that the first return missed, including when the answer is nothing. Operational form: `dev/ORCHESTRATION.md` sections 1 and 2. **The mode-rename history, the flip's cost and the two gate-fix episodes live in `dev/JOURNAL.md`, 2026-08-14, under `DD17`.** |
| DD18 | **THE ARCHIVE AND LITERATURE SURVEYS are sections of the brief and of the return, not a hope.** | **Ruled 2026-08-09 by the owner as a MECHANISM.** Before a brief is sent it carries an **ARCHIVE** section listing what may bear on the task in each archive: `archive/` for retired code, with `archive/src/2026-08-09-rud-route/` holding the retired route's 72 files and `dev/ARCHIVE.md` describing modules retired before it; `archive/dev/TASKS-archived.md` for what each of 265 earlier dispatches FOUND; `archive/dev/JOURNAL-archived.md` for WHY; and `archive/dev/DECISIONS-archived.md` for the rulings that route ran on. **A return carries an ARCHIVE USED section** naming what it actually read and what it took from each item, at `file:line`. "I looked at the archive" is not a return, and a brief whose archive section is empty must say why. `dev/LESSONS.md` is NOT archived and still binds, cited the usual way through `scripts/rules.py`. **A port is priced against a fresh write, never assumed** (DD13), and P-l holds: a measured cure does not transfer by analogy. **ENFORCEMENT IS REVIEW ONLY.** Nothing mechanical reads a brief, so the orchestrator refuses a return whose ARCHIVE USED section is missing. A row that claimed a checker it does not have would be worse than this one. **THE LITERATURE HALF, added 2026-08-10 by the owner, and it is the same mechanism for a second corpus.** `dev/literature/` holds the digested mathematics: `digest.md` for the orthodox route, `j-hierarchy.md` for condensation and the stratification, `fine-structure.md`, `rudimentary-functions.md`, `devlin-errata.md` for the known errors in the primary text, `primary-sources.md` and `BIBLIOGRAPHY.md` for what was fetched and what it was consumed by, and `formalizations-landscape.md` for prior art. **A brief that dispatches mathematics carries a LITERATURE section naming what may bear on it, and a return carries a LITERATURE USED section** saying what it read, what it took, and, for anything it did not use, WHY NOT. **The why-not is the half that earns its keep:** a note saying a source is OCR-degraded, or covers the wrong chapter, or was superseded, is worth as much as one that supplies a lemma, and it stops the next agent paying the same reading twice. **ENFORCEMENT, AND THE TWO HALVES ARE NOW IDENTICAL** (owner, 2026-08-10). `dispatch.py` REFUSES a brief that carries no ARCHIVE section, and refuses one that carries no LITERATURE section, **on every brief regardless of kind**. Each is satisfied by one honest line naming the corpus and saying nothing in it bears on the task, which is cheap to write and still forces the author to look. **THIS BINDS THE CODEX PATH ONLY**, and the limit is stated rather than hidden. An in-harness dispatch does not pass through `dispatch.py`. There the orchestrator applies DD18 by hand, and a return that arrives without both USED sections is sent back. **Why the literature half was added, why both halves gate, why the gate binds every brief, and the `[LJ-1.11]` gap episode live in `dev/JOURNAL.md`, 2026-08-14, under `DD18`.** |
| DD19 | Governance: one home per rule, goals registered before they start, and two guarded surfaces | **ONE HOME.** Every rule lives in exactly one canonical place, chosen by who enforces it, and a rule that no machine enforces must NAME its enforcement point: a gate, a brief section, a review step. A rule with no enforcement point is a wish. Nothing is canonical twice. **GOALS**, absorbed from DD18's old content: a ruling is a PLAN row and an episode is a JOURNAL entry; every dispatch is registered in the task index BEFORE it starts, one row per code, 200 characters, enforced by `scripts/check-task-index.py`; a ruling may be revised, and a revision is recorded rather than a row being rewritten. **TWO GUARDED SURFACES.** `AGENTS.md` takes no edit without the owner's ruling on the diff and a dated `AGENTS-diff-approved:` trailer, which `scripts/check-agents-guard.py` refuses to go without. `dev/glossary.toml` takes no entry chosen by an agent: a term it lacks goes through the two-agent pipeline, and the pipeline names its tiers: **arm 1 is codex**, which searches the literature for each rendering's provenance and marks every guess where the literature is silent, and **arm 2 is opus, adversarial**, which verifies the sources and attacks the collisions and PASSes or FAILs per term. A PASS lands the entry without the owner's review and the landing commit cites both; a FAIL, or a genuine fork, escalates that term and only that term. The owner's veto always stands. Absorbs the old DD18, DD20 and DD21. |
| DD22 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out; everything else inherits AGPL-3.0. Three buckets, declared centrally, with no in-file `SPDX-*` headers. `reuse lint` enforces it. |
| DD23 | **NO MATHEMATICAL PROSE until both trophies land. The prose phase comes AFTER.** | **Ruled 2026-08-09 by the owner.** Until `L ⊨ AC` and `L ⊨ GCH` are both proved on the two-tower bridge inside DD5's constraints, write NO mathematical prose: no chapter narrative, no trilingual exposition of the mathematics, no reader-facing explanation of a construction. Code and its own comments only. **The prose phase opens when the double trophy lands, and not before.** This is not a licence to write badly: DD11 still binds, and so does ASD-STE100 for every brief, report and message, which is working text rather than mathematical prose. **The reason is DD4.** Prose written against an architecture that reuse has not settled is prose written twice, and the retired route paid that bill. **What this does NOT suspend**: the marker grammar where prose already exists, `docs/`, and `dev/JOURNAL.md`, which is a record and not exposition. |
| DD24 | **THE QUALITY BAR IS SECONDS PER LINE, and on the internalization GCH wing it is the ONLY threshold.** | **Ruled 2026-08-09 by the owner.** Code written for `L ⊨ GCH` on the internalization route must reach the SAME quality as that route's delivered `L ⊨ AC` wing, and quality here means one measured thing: **the ratio of cold build seconds to in-fence lines.** The bar is a number rather than a judgment. **THE WING CARRIES NO OTHER THRESHOLD**, absorbed from DD25: no line cap and no seconds cap, and the omission is deliberate. **The bar also governs DD5's own benchmark and the two-tower route.** **THE BASELINE BELONGS TO ONE TREE, and both tools refuse it on another** (owner, 2026-08-09). A seconds-per-line figure is not a constant, so `dev/ledger.toml` records `ac_baseline_lines` beside the figure, and `ledger.py --check` and `check-ratio.py` both REFUSE when standing has drifted from it, naming `[LJ-0.5]` as the re-measurement. Without that guard a stale bar reports exactly like a live one, which is C-28. **Enforced staged by `scripts/check-ratio.py`**, from the first GCH module onward, because a bar readable only at the end is read too late to act on. Read P-m, P-n, P-q and P-t before optimizing. The formula does. **Why a ratio, the wing-exists-to-measure reasoning and the P-m/P-q/P-t measurements live in `dev/JOURNAL.md`, 2026-08-14, under `DD24`.** |
| DD25 | **A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ TOGETHER. THE HEADS COME FROM THE SWITCH.** | **Ruled 2026-08-10 by the owner.** When a return's headline verdict is negative, the orchestrator dispatches an adversarial review at maximum effort to attack that return, before auditing it and before acting on it. **THE HEAD IS THE SWITCH'S ADVERSARIAL ROW, never a head written here**, and the invariant that decides it is DD17's: **the critic is never the same head as the author.** `scripts/dispatch_policy.py` prints the pair in force. The switch now supplies both, and a name here would be canonical twice. **THE TRIGGER, stated so it cannot be argued away:** a refusal, a NO-GO, a RED gate, a stop taken as the deliverable, a refutation of the brief's premise, or a landed result that misses its band floor. If the verdict line would disappoint the person who wrote the brief, it is negative. **WHAT THE REVIEWER ATTACKS IS THE NEGATIVE, NOT THE TASK.** It is not a re-run and not a second attempt. The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed. **A review that AGREES is a real result** and costs one dispatch to buy confidence in a number the campaign is about to build on. **THEN BOTH ARE READ TOGETHER.** The orchestrator audits the original return and its adversarial review as one pair, and reports both to the owner, including where they disagree. Neither is accepted alone. **THIS STANDS UNDER DD17's SWITCH RATHER THAN AMENDING A FIXED TIER.** **DD17 no longer names a head at all**, so what survives is narrower and clearer: DD25 fixes WHEN an adversarial review is mandatory, and the switch fixes WHO runs it. **IT DOES NOT CONTRADICT DD17's "a RED is never a trigger":** that clause forbids re-dispatching the TASK on a RED, and it still binds. DD25 dispatches a REVIEW of the RED, which is the opposite move. **THE HAND-APPLIED RULES.** An in-harness dispatch does not pass through `.claude/skills/codex-dispatch/dispatch.py`, so the DD4 and DD18 refusals do not fire. The orchestrator writes DD4, ARCHIVE and LITERATURE into the review prompt by hand. **Enforcement:** the audit, and the PLAN section 11 row for a negative return must name its review's code. **No machine enforces the trigger today**, because reading a verdict as negative is a judgment; the honest enforcement is that the row is empty and visible. Operational form: `dev/ORCHESTRATION.md` section 1. **The sign-error episode and the fixed-tier history live in `dev/JOURNAL.md`, 2026-08-14, under `DD25`.** |

| DD26 | **THE CATALOGS ARE NOT COUNTED. `src/Everything.lagda.md` and `src/Landmarks.lagda.md` are excluded from EVERY size figure, past and future.** | **Ruled 2026-08-10 by the owner.** Both are indexes rather than mathematics: one is the import catalog with its per-chapter prose, the other states the two trophies and imports what proves them. **The reason is DRIFT, and it is the owner's:** a catalog GROWS WITH THE PROJECT, so a threshold measured against a total containing one drifts further from the mathematics it is meant to bound, and drifts in the direction that flatters the tree. **RETROSPECTIVE, by the owner's word:** the ruling re-bases figures already recorded, so `[LJ-0.4]`'s prerequisite is met at 16,897 rather than 16,995 and DD24's baseline is 0.007913 over 16,897 rather than 0.007904 over 16,916. **DD8's caliber is untouched:** non-blank lines inside ` ```agda ` fences, still. This ruling says which FILES that caliber runs over. **Enforced by `scripts/ledger.py`'s `UNCOUNTED` and `countable_masters()`**, which every size site now calls, and pinned by `scripts/tests/test_ratio_baseline.py` and `test_deletion_test.py`, whose assertion that Everything IS counted was flipped in the same commit. **The two-numbers discrepancy this ruling collapsed lives in `dev/JOURNAL.md`, 2026-08-14, under `DD26`.** |
| DD27 | **THE HULL IS INDEXED BY A META TERM ALGEBRA, not by object-language formulas.** | **Ruled 2026-08-10 by the owner**, on a measured fork. `[LJ-1.3]` built the hull as `sett (Σ[ φ ∈ Formula ⟪X⟫ 1 ] Witnessed-small φ)`, so every membership certificate is an X-formula. That choice, not the mathematics, is what blocked condensation: the criterion at HULL parameters needs the order named inside the model, `relL α` sits at rank at least α while `Lset α` holds only rank below α, and the index type leaves no room to widen, because a hull-expressible order yields a hull-formula and the index demands an X-formula. **WHAT IT REVISES:** `[LJ-1.3]`'s delivered hull, its index, and the statements over that index; it also RETIRES `[LJ-1.3]`'s booked residue piece one, 30 to 80 lines. **TWO CAVEATS STAND AND ARE NOT BURIED:** the 120-line and 2-second counting figures are ESTIMATES from same-class module rates, not measurements, and the mutual `enc`/`encs` termination is unchecked at that site, though the probe's `val`/`vals` passed the analogous shape. **The prices, the counting objection and the DD4 reason live in `dev/JOURNAL.md`, 2026-08-14, under `DD27`.** |
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
   carve-out's own conditions held. **`[LJ-0.3]` found the map unrecorded and
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
   `scripts/check-task-index.py` enforces both one-row-per-code and the cap.
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

Struck D10, which used to carry these constraints, went on 2026-08-05 because each constraint is now enforced where it fires. The numbered rows below are routing rows; the full original text is in [dev/memos/build-constraints.md](memos/build-constraints.md), and the older §7.5/§7.6 budgets cited by archived D13 are rules 5 and 6:

1. The trusted gate is one invocation, `agda src/Everything.lagda.md`: the build machinery (`Makefile`, [scripts/README.md](../scripts/README.md)).
2. Parallelism is a warm-up layer outside the trust base: the build config.
3. The import-closure audit: `scripts/check-tree.py` closure, [scripts/README.md](../scripts/README.md).
4. The dependency manifest is generated, never committed: the build config.
5. The cold-check budget and the seconds dimension: the ledger (`dev/ledger.toml` [timing] and [[hot]]) and the return checklist, `dev/ORCHESTRATION.md` section 6 step 2.
6. Per-module discipline (heap caps, conversion-blowup triage): `AGENTS.md`, `dev/ORCHESTRATION.md` section 2, `dev/LESSONS.md` C-12, and `scripts/check-timing.py` at every return.
7. Serial fallback stays available: the build config.
8. Reference machine and `-jN` defaults are documented in the build config.

## 8. Process tensions and their resolutions (pointer)

The T1-T6 tension register and its relief valves moved to [dev/memos/process-tensions.md](memos/process-tensions.md). Archived D11's mechanisms are in `archive/dev/DECISIONS-archived.md`; the live relief valves are the L0 standing track (the L0 row of §11) and the L4.1 harmonization (§11). Note that `DD11` is a DIFFERENT rule, code and prose craft: the D and DD numbers do not correspond.

## 9. Risks and mitigations (pointer)

The dated risk register moved to [dev/memos/risks-mitigations.md](memos/risks-mitigations.md). Each mitigation is a standing rule with its own home: DD1 and DD5 in §3, `dev/LESSONS.md` D-1/D-6/D-10, the §6.0 rules, and the return checklist in `dev/ORCHESTRATION.md` section 6.

## 10. Candidate simplification register (pointer)

The S1-S18 register moved to [dev/memos/simplification-register.md](memos/simplification-register.md), with its statuses brought current to the `[L3.32-T8]` verdicts: S13 and S15 shipped, S14 and S16 reverted at their gates, S17's probe red, S18 deferred. Live tracking of the deferred row is `dev/ledger.toml`'s [[excluded]] table.

## 11. MASTER status table (live)

One row per goal code; update the row in the same commit that changes the
status (§6.0 rule 6). Dispatched-task codes are indexed separately below,
one row per code (§6.0 rules 7 and 8). Bookkeeping lines follow the table.

**COMPRESSED 2026-08-09, and the full table is `archive/dev/STATUS-archived.md`.** It
held 96 rows of a route that is retired. A live screen that carries a dead
route's whole history stops being read. So a DONE goal keeps its top-level row
only, `[L3]` keeps the six rows that were its route switches, and every status
text is in the archive unedited.

**`[L3]` IS SUPERSEDED WHOLESALE BY THE `LJ` SERIES.** Not amended, not
re-scoped: the two-tower bridge route (DD2) replaces the technical layer
entirely, and no `L3` child may be re-opened under its old code. The `LJ`
series is indexed below and carries all live build work.

**THE `LJ` SERIES GATES `[L4]` THROUGH `[L8]`.** Those rows survive unchanged
because they are route-neutral: convergence, build infrastructure, the
narrative, the archival promotion, and the consolidation gate describe work
that any route must do last. **None of them opens until the `LJ` series lands
BOTH trophies inside both constraints.** DD23 states the same bar for prose,
and `[L8.2]` is the gate that `[L4.1]` waits on.

| Code | Goal | Status |
|---|---|---|
| L0 | Legislation (standing track) | **DONE.** Five children: STYLE-agda, the first glossary batch, the LEM spike, the import linter, the two-catalog doctrine. All landed 2026-07-16 to 07-25 |
| L1 | Root and trunk skeleton | **DONE 2026-07-18**, ten children. Base, FOL, ZF, V and `L.Constructible` ported; Landmarks and the `Everything` reading order ruled the same day |
| L2 | Axiom branches | **DONE 2026-07-31**, five children. Basic, Infinity, Separation and Replacement, Power at 79 lines without Condensation, then `[L2.4]`: **the Frontier is empty and deleted** |
| L3 | Technical layer | **SUPERSEDED WHOLESALE 2026-08-09 by the `LJ` series** (DD2). Fifty-nine children ran here, and the six rows below are the route switches among them. Every child, with its full status text, is in `archive/dev/STATUS-archived.md` |
| L3.0 | Internalization theorem for L-recursion | **DONE 2026-07-28**, 99 lines, verdict green. This is the route the `LJ` series now measures against: `src/` today is its tree |
| L3.29 | AC by the operations calculus (route C), then the B pivot | **SUPERSEDED 2026-08-02.** The first switch. Route C's operations calculus was delivered, then the kinded-closure pivot on top of it, and the `[L3.30]` re-architecture replaced both |
| L3.30 | The rud re-architecture (exploratory) | **CLOSED 2026-08-02, ADOPTED IN FULL.** The second switch. Posed completion-state-blind, it priced the routes and recommended the rudimentary-function trunk |
| L3.31 | The rud build, then the architecture fork | **CLOSED 2026-08-04.** The third switch, and a refutation: the bridge kernel rested on one hypothesis that proved classically FALSE (Devlin VI.2.4). Eleven recons priced every repair |
| L3.32 | The L-trophy build (the ruled configuration) | **CLOSED 2026-08-09** when the route changed. The fourth switch: the Def tower kept the trophy, the wing rode a fresh-generic Sigma-1 face, and the rud-route code is now in `archive/src/2026-08-09-rud-route/` |
| L3.32-F | The check-cost campaign | **CLOSED 2026-08-09.** It measured what the two towers really cost, and that measurement is why the new route's constraints are seconds and lines rather than lines alone. `SquareLaw` went 856 s to 64.4 s for net zero lines |
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

**The retired route's 265 rows are `archive/dev/TASKS-archived.md`, unedited**, under
the `L3.32-T` series. Both series resolve and neither reuses a number.
`scripts/check-task-index.py` enforces one row per code and the 200-character
cap.

**EVERY BRIEF SURVEYS THE ARCHIVE BEFORE IT IS SENT, AND EVERY REPORT NAMES
WHAT IT USED. THE RULE IS DD18 AND THIS IS NOT A SECOND COPY OF IT**: read the
row in section 3 for what a brief and a return must carry, and
`dev/ORCHESTRATION.md` for the operational form, exactly as DD17 and DD25
point. What follows is WHY the archive is worth surveying, which is this
section's business. The retired route cost a year of measurement and the whole of it
is still on disk: `archive/` for the code, `dev/ARCHIVE.md` for why each
module left and what it did right, `archive/dev/TASKS-archived.md` for what every
dispatch found, `archive/dev/DECISIONS-archived.md` for the rulings, and
`dev/LESSONS.md`, which is NOT archived and still binds.

| Code | Task | Verdict | Detail |
|---|---|---|---|
| LJ-0.1 | Consistency audit of the edits since the branch point | CLOSED | 30 defects, 6 load-bearing. ALL repaired. Also surfaced that make test ran 3 of 7 suites, hiding a real regression |
| LJ-0.2 | Sufficiency audit: what the route switch has NOT reached | CLOSED | 3 blocking gaps and 8 more, all closed. N1's reuse checker refused as a gate, adopted as ledger.py --reuse |
| LJ-0.3 | Retrospective: was the route change itself the right call | CLOSED | Timing premature, route not refuted. Moved the architecture ruling to LJ-2.5. Two laws admitted, C-28 and C-29 |
| LJ-0.4 | Compress the AC tree to 17,000 | MET and DISCHARGED | AC 16,897 under DD26; 16,995 on the target's own caliber. Every KIT block measured net positive; only deletion and one kit paid |
| LJ-0.4j | The prose-freed dead names, orchestrator only | DELIVERED -59 | The 14 names block A found dead but could not touch, held only by prose in Everything, src/README or the chapter |
| LJ-0.4n | The SHAPE half of the recursion assembly, ONE parameter | LANDED -104, seconds FELL | Kit 53, ONE parameter, break-even 0.91 over 5 sites, hosted IN Sequence. Tree -0.53 s. D-28 |
| LJ-0.4p | Re-test every name kept by a citation, READ ONLY | 34 lines traced, 2 keeps | No Agda slot, ran beside LJ-0.4n. Confirmed my CodeSet protection was circular prose I wrote hours earlier |
| LJ-0.4q | Take LJ-0.4p's two DELETE rows | LANDED -34; AC 16,995, then 16,897 under DD26 | The arity-one code set retires, finishing what [L3.27] ruled on 2026-08-05 |
| LJ-0.4m | The dead-name re-scan, four rounds on | LANDED -17 of -68; I reverted 51 | D-27 came out of it: the criterion was mine and it was wrong for a stated result and a seal's readings |
| LJ-0.4k | Is any whole MODULE dead? | ANSWERED NO | Closure over Landmarks: 74 of 78 masters are load-bearing, 3 outside are wing. A dead module would be a kitless deletion. The class is empty |
| LJ-0.4c | Block C: the Unique and Sound frames | STOPPED; the BRIEF dominates | Its band floor sat above the real surface, its stop trigger named seconds only, and it omitted the chapter rule |
| LJ-0.4e | Blocks E and G: traversal share, lex kit | REFUSED BOTH on measurement | E +19, G +49; G's table reads 146 to 195 and the -49 label was a sign error I repeated. Kits LOST, S22 |
| LJ-0.4b | Block B: the existential frame across L/Choice | REFUSED on measurement | Kit 43, cleanest site saves 19. Net +24 measured against a band of -190 to -340. Kit kept, register S19 |
| LJ-0.4d | Block D: the Model arity-generic clause frame | SKIP, refuted by class | Model has ZERO repeated 4-line blocks over 1,289 lines. Its in/out pairs are two-way decode content |
| LJ-0.4f | Block F: the recursion-assembly triplication | NO-GO, UPHELD by LJ-0.4f-R | Kit 208 at 11 parameters, one site -96, two-site net about +4 and +1.23 cold seconds. Register S20 |
| LJ-0.4f-R | DD25 adversarial review of LJ-0.4f's NO-GO | UPHOLD WITH A CONDITION | Killed a FALSE D-10 claim I had propagated: Before DOES hold a third assembly. Found the -106 cure |
| LJ-0.4h | Block H: preamble and shift helpers | DROPPED, register S23 | Only admissible folded into F, and F was NO-GO. 229 raw preamble lines cannot be shared away; every module keeps its opens |
| LJ-0.4i | The measured dedup sweep, within-file first | LANDED -30 of a -80 to -140 band | One file of seven: Separation 351 to 321 via a local helper, 11 lines over 8 sites. Six refused |
| LJ-0.4a | Compression block A: the dead names | DELIVERED -240 | 48 names over 18 masters, 17,492 to 17,252. Kept 3 the plan rides and the ones only Everything's prose held. 𝒟ₒ→isL refused |
| LJ-0.6 | Restore the V.Presentation shim the src/ restore deleted | DONE | +19 in-fence, 76 masters. Cold 132.87 s, exit 0. Unblocks the archived Collapse and Hull ports |
| LJ-0.5 | RE-MEASURE the DD24 baseline | DONE: 0.007913 over 16,897 | Three cold Landmarks runs, spread 2.15 s, +2.85% and inside the 1.15 bar. Caught a confound: make typecheck builds the wing too |
| LJ-0.8 | ADVERSARIAL review of the AC compression, done and planned | dispatched | tier: fable 5, owner-named. The survey missed 2 of 3 measured blocks. Deliverable is brief corrections |
| LJ-1.1 | Recon: the GCH route on the internalization tower | RETURNED, one mis-cite | Wing 8.0-10.8k. LJ-1.11 F5: its warrant cites Devlin VI.4.1, a projectum lemma. The true one is II.5.2 |
| LJ-1.2 | Gate: probe the widest unmeasured term LJ-1.1 names | NO-GO, re-prices the wing | Its Delta-0 answer was the wrong question, and its 5,047 was quoted not measured. See LJ-1.168 |
| LJ-1.10 | RE-PRICE the crossing after LJ-1.2's NO-GO | RETURNED, but REFUTED by LJ-1.11 | It read the ⊤̇ Def-step as a saving. T130 had recorded the same fact as the MISSING content |
| LJ-1.11 | ADVERSARIAL review of LJ-1 vs the literature | RETURNED, 2 math defects | F1: route C's story is trivial in the Def-step, so its target is FALSE. F2: the collapse is trivial where used |
| LJ-1.3 | Build: the Skolem hull, a least-witness search over the order | DELIVERED 343 lines | Ported from 241 archived. 0.0070 s/line, 0.91x the bar. Does NOT use σ₁-up: LJ-1.5 does |
| LJ-1.4 | Build: the Mostowski collapse | DELIVERED 239 lines | Ported from the archive's 181, plus Devlin 5.2(ii) which the archive lacked. Carrier-generic. Cold tree 133.39 s, exit 0 |
| LJ-0.7 | Digest Devlin II.5 into the literature | DELIVERED 626 lines | Level-hood is SIGMA-1 with a Sigma-0 matrix, not Delta-0. Template 5.1-5.6 is SHARED; per-tower content is two objects |
| LJ-1.12 | RE-TARGET the crossing | RETURNED: take Route A at 3.3k | All three rest on ONE deep layer, so the choice barely matters and the price does. Sigma-1 re-opened it and did NOT shrink it |
| LJ-1.13 | Build: the collapse at an EXTENSIONAL carrier | DELIVERED +96 | isExt at :31, InjExt at :220. Trivial Inj kept per D-27. F2 corrected: the induction is the same, Xtr was dead code |
| LJ-1.14 | Build: Tarski-Vaught at a NON-transitive carrier | DELIVERED +29, seconds FELL | Mtr gone entirely, TV holds at any carrier. Priced 50-70, landed 29. Hull-parameter criterion still owed |
| LJ-1.5 | Build: the condensation lemma, block 1 | DELIVERED | src/L/Condensation.lagda.md, 308 lines at 0.0079, which is 0.60 of DD24's bar. NO placement anywhere; all eleven obligations landed |
| LJ-1.33 | GATE the next block: measure leg D | NO-GO, under DD25 review | 0.34 per line, 25.7x the bar. Leg D alone is 102 to 272 s against a 99.6 to 147.7 s budget. The machine side is what costs |
| LJ-1.33-R | DD25 review of LJ-1.33's NO-GO | OVERTURN | Same theorem, same hypotheses: 0.334 to 0.0108, 38x. BOTH causes were my brief. But it prices a PROXY, not the real leg D |
| LJ-1.34 | GATE leg D: the certificate story vs the machine | NO-GO, under DD25 review | 0.436 per line, and the Delta-0 certificate does NOT close: the delivered leaves carry unbounded quantifiers |
| LJ-1.34-R | DD25 review of LJ-1.34's NO-GO | OVERTURN | Same theorem: 0.436 to 0.0079, 46x on my own re-runs. Spell the story ONCE. Delta-0 IS the target and my brief was right |
| LJ-1.35 | GATE: price the bound-fact construction | BETWEEN, leans GO | 0.0241 per line, 0.48 of the NO-GO bar. The block funds. But the per-clause figure rests on ONE measured clause |
| LJ-1.36 | GATE: is the leaf reading really 2 s PER CLAUSE? | GO | NO. The 2 s is ONE deep leaf; eleven rows read under 0.12 s TOTAL. The 22-31 s projection was wrong by about 12x |
| LJ-1.37 | BUILD: the eleven table clauses and the description | DEFECTIVE, see LJ-1.38-R | Landed 1,723 lines and passed every MECHANICAL check. The rows are false of the satisfaction table. C-35 |
| LJ-1.38 | BUILD: the step and graph stack, and leg D | REFUSED, under DD25 review | Matrices land at 110 lines. The agreement does NOT: it says LJ-1.37's story rows are VACUOUS at empty values |
| LJ-1.38-R | DD25 review of LJ-1.38's refusal | UPHOLD, and worse | Not merely vacuous: the rows are FALSE of the satisfaction table. 968 of 2,141 lines re-open. The nonemptiness cure is refuted |
| LJ-1.39 | PROBE: compress the de Bruijn index padding | GO, -318 lines and FASTER | 2,031 to 1,713, and 9.26 to 8.9 s. The rate RISES 0.00456 to 0.00520: de-padding costs the ratio, as it should |
| LJ-1.40 | REPAIR: re-index the rows TRUE, close the agreement | REPAIRED, agreement PARTIAL | 2,498 lines at 0.00512, zero placement. Bot row and the shared machinery close. Eleven rows owe theirs |
| LJ-1.41 | Close the eleven row agreements | 2 of 11, under DD25 review | And and Or close. Nine share ONE blocker: envHyp is K-bounded, envSetAt is unbounded, and Delta-0 has no unbounded witness |
| LJ-1.41-R | DD25 review of LJ-1.41's envSetAt blocker | OVERTURN | The impossibility is refuted by four probes. The real defect is ONE missing conjunct, about 100 lines and 0.22 s |
| LJ-1.42 | Add the conjunct, close nine rows, price PropAgree | 3 of 9, cure right | Closed Top, Neg, Forall. It found LJ-1.41's And and Or sat OUTSIDE the fence, as prose, with four defects |
| LJ-1.43 | Close the six row agreements and block 1 | ALL SEVEN CLOSED | The twelve-row table is complete and machine-checked. LJ-1.42's wall was inferred and wrong. Module rate 1.07x |
| LJ-1.44 | Locate the class that costs 65 s in Condensation | THE AGREEMENT LAYER | 79 percent of the seconds. Two spellings per leaf, the P-v family. One spelling measured 10.1x at the hottest row |
| LJ-1.45 | Restate the agreement layer in ONE spelling | LANDED where positive | 62.07 to 59.6 s on my own three runs, 0.0131. Leaves gained 10-15x; two shapes measured NET LOSS and were reverted |
| LJ-1.46 | GATE LJ-1.7: price Devlin 5.5 | 1,675 lines, 36 s | And it found LJ-1.8 hides ~2,500 lines: no cardinal chapter at all, and the square law is an UNBUILT module parameter |
| LJ-1.47 | PROBE: can the square law's 41.36 s come down? | YES, 5.45x | 43.26 s to 7.94 s. Both levers were DELETIONS of content with no consumer. The wing flips 1.25x over to 0.96x under. D-30 |
| LJ-1.48 | GATE LJ-1.7: measure the condensation theorem assembly | GO | 0.0087 to 0.0099 on my own three runs against a 0.0127 GO line. Transfer statements at 0.003, the parameterized end |
| LJ-1.15 | PROBE: one bounded table clause | NO-GO, OVERTURNED by LJ-1.15-R | My 40-line gate sat below the band it tested: the booked row allows 133 lines per clause and the hardest measured 155 |
| LJ-1.6 | Build: cardinality of a stage | DELIVERED half; the refusal's REASON overturned | The quotient objection is true but was CURED at T85, and the descent is 52 measured lines, not 250-450 |
| LJ-1.6-R | DD25 review of LJ-1.6 | UPHOLD the stop, OVERTURN reason and price | Found the cure already GREEN, a 20 percent caliber error in the route's own figure, and the wing's seconds budget |
| LJ-1.16 | Build: the criterion at hull parameters | REFUSED all three, OVERTURNED by LJ-1.16-R | A fourth shape exists at 150-300 lines and 0.8-3.9 s against the refused 1.0-3.0k and 220-890 s |
| LJ-1.16-R | DD25 review of LJ-1.16 | OVERTURN the operative clause | The obstruction is the hull's INDEX TYPE, a LJ-1.3 design choice, not the mathematics. Owner's fork; LJ-1.18 prices it |
| LJ-1.15-R | DD25 review of LJ-1.15's NO-GO | OVERTURN | Crossing FITS the budget: 0.0052 s/line means 15-17 s of 99.6-147.7. Two obstructions, not one: 1.16's is permanent, 1.15's removable |
| LJ-1.18 | PROBE: the meta term algebra, the fourth shape | GO at 116 lines | Plain inductive, strictly positive, 0.0103 s/line under the bar. Corrected the review on four details. OWNER'S FORK |
| LJ-1.17-R | DD25 review of LJ-1.17, fired late | OVERTURN; keep the measurement | My budget arithmetic divided by TODAY's wing, not the projection. C-31 records it. The transfer is NOT owed |
| LJ-1.22 | PRICE the counting interaction the fork creates | NEUTRAL | Code needs the SAME cardinal law as Formula K 1: ~120 lines, ~2 s, 20x below the pair. The objection dies |
| LJ-1.23 | Build: the hull on the meta term algebra (DD27) | DELIVERED | Hull 372 to 431 lines at 0.0039, under the bar. hull-closed now gives the criterion at HULL parameters. Piece one retired |
| LJ-1.20 | Build: the stage-arithmetic kit, +omega and its bounds | DELIVERED | StageArith.lagda.md, 75 lines at 0.0100, under the AC baseline. Omitted +omega-out and +omega-limit, both priced |
| LJ-1.21 | Build: the carrier-level descent for the level size | DELIVERED, and it cost | StageCardinal 174 to 484 lines, 0.90 to 42.03 s. Init dropped, so every infinite alpha. LJ-1.25 cured it |
| LJ-1.24 | PROBE: is StageCardinal's limit half curable | ARM 1 WINS | 29.1 s to 2.3 s, 12.8x, for about 6 lines. R-38's class, NOT P-n's floor: the transport over a TRANSPARENT sett index costs |
| LJ-1.25 | Build: apply LJ-1.24's cure to the master | DELIVERED | 41.21 s to 11.22 s for 7 lines. The limit half went 0.270 to 0.014. stage-card-upper unchanged. Master 0.024, still over the bar |
| LJ-1.26 | GATE LJ-1.5: price condensation in SECONDS | DELIVERED | About 60 s at route A's 3.3k centre. The archived 0.395 does NOT transfer. One probe decides a 100x spread, 13-17 s or 700-1300 |
| LJ-1.27 | GATE PROBE: one level-story clause at the carrier | NO-GO, under DD25 review | 0.12 against a 0.10 gate. But 31 of its 33 s sit in TWO obligations, and its own base variant runs 0.0053 |
| LJ-1.27-R | DD25 review of LJ-1.27's NO-GO | UPHOLD | Built the Delta-0 lemma: it WALLS at 8 GB. 16 of 17 constants come from consAtL, so the brief did NOT cause it. Route A does not fund |
| LJ-1.29 | ARCHITECTURE: can the crossing drop the shared formula? | NO | The 0.0053 base variant is NOT the crossing: it omits the transfer. The 31 s is the PLACEMENT price, not the sharing price |
| LJ-1.30 | PRICE the cure: make consAtL constant-free | GO, ~110 lines | The 16 constants are ALL con (# 0), and # 0 IS the empty set, so the reader goes constant-free IN PLACE. Zero consumer edits |
| LJ-1.31 | BUILD the constant-free reader in the coding layer | DELIVERED, not sufficient | 109 lines, ZERO consumer edits, rates all GO. consAtL reaches 0, but real clauses count 1 to 5 elsewhere |
| LJ-1.32 | PROBE: does the placement wall scale with the count? | NO, under DD25 review | It WALLS at count 0 too, flat at 63 s across 0, 1, 2, 5. The cost tracks the TREE, not the constants |
| LJ-1.32-R | DD25 review of LJ-1.32's wall verdict | OVERTURN | THE GATE WAS ALREADY OPEN. LJ-1.31's cure cut the unchanged gate probe 41 percent, 32.07 to 18.95 s, and nobody re-ran it |
| LJ-1.28 | Can the equivalence legs ride the delivered graph theorems? | RIDE | Legs A and B delivered at 0 lines. Leg D's rate spans 0.0052 to 0.085, so its residue is 5 s or 68 s, not one number |
| LJ-1.19 | PROBE: Cure A, limits closed under plus omega | GO at 30 body lines | The consumer survives: the wing condenses ONCE, at 5.5, whose free lambda can be +omega-closed at zero cost |
| LJ-1.17 | GATE: is the square law affordable at DD24? | NO SHAPE FITS, OVERTURNED | The seconds are sound; every conclusion from them was wrong. At the PROJECTED wing it passes at 0.72-0.82x |
| LJ-1.7 | Build: the condensation theorem, then Devlin 5.5 | STRUCTURE only, under DD25 | 888 lines at 0.0111, under the bar. But levelIn and cover are HYPOTHESES: the semantic transfer is assumed |
| LJ-1.7-R | DD25 review of LJ-1.7's transfer residue | OVERTURN both | The 328 wall is a P-v second spelling and the file documents the cure itself. collapseCode dies on a fibre conflation |
| LJ-1.49 | Discharge levelIn and collapseCode, price the rest | BOTH CURES LANDED | collapseCode DELETED. levelIn and cover survive, Mext enters. One leaf transfer measures 150.13 s |
| LJ-1.50 | Attack the 150 s transfer, then price the unpriced step | NO, overturned by 1.50-R | The variable-slot move is SLOWER, measured. But the 150 s itself was a probe artefact |
| LJ-1.50-R | DD25 review of LJ-1.50's stand | OVERTURN, 681x | Naming ONE count proof takes 150,133 ms to 220. The EraseTransfer exit is built and green at 1.56 s. The route FITS |
| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master | fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and levelIn survive on the hull adequacy |
| LJ-1.52 | The level-hood adequacy at the hull | PINNED, not discharged | The chain is assembled and machine-checked. Three named leaves remain, each written as the term not written |
| LJ-1.53 | The three walls of the hull adequacy | 1 of 3 fell, 1 dissolved | Wall 2 FELL, built and machine-checked. Wall 3 is NOT a wall: the collapse serves. Wall 1 half green at 1.617 s |
| LJ-1.54 | The last unbuilt term, then the hypotheses | 4 atoms, plus a blocker | Four leaf atoms green. FOUND: the twelve agreements do not instantiate at their consumer's frame |
| LJ-1.55 | The agreements' slot convention | PARTIAL, half closing | Fix is every slot, not K alone. Master green, line-neutral. TwelveAgree composes. WitnessAgree blocked on oneSameB |
| LJ-1.55-C | Orchestrator cure of the oneSameB defect | CURED, verified | The story read (c, ar) where the machine reads (ar, a). Two lines. oneSameB = oneSameAt now holds by refl, machine-checked |
| LJ-1.56 | The closedness transfer and SatGraphAgree | 4 of 5 steps, 3 cures | ClosedAgree, DomainAgree and SatGraphAgree two-way and green. Three more delivered definitions convicted |
| LJ-1.56-C | The three cures audited: arTagBS, isTmBS, satGraphB | UPHELD, each consumer-tested | isTmAt is a disjunction and the story had one branch. Each cure is proved two-way against the machine's imported definition |
| LJ-1.57 | The shapedness walk, WitnessAgree, LeafAgree | ALL THREE BUILT | The leaf adequacy is proved both ways against the machine's DefBody. No fifth defect. levelIn and cover still survive |
| LJ-1.57-A | Orchestrator audit: the leaf proof is not in the tree | GATE OWED, priced | A probe is never committed. Placing 884 lines at the measured 0.0755 puts Condensation at 0.0220, 1.73x over DD24's bar |
| LJ-1.58 | The placement gate for the leaf adequacy | AMBER, 0.01765 marginal | The walk places 4.28x cheaper than the probe spelling. Whole file 0.01202, under the bar. Narrowed one-way |
| LJ-1.58-A | Orchestrator audit: is the dropped direction owed? | RISK FLAGGED | Every consumer that EXISTS is one-way, verified at file:line. But nothing produces Adeq m, and its production is the dropped direction |
| LJ-1.59 | The direction question, then place the chain | YES, out is owed | Adeq production needs machine-to-story, measured. Two placements land under the bar; the two-way walk hit a price wall |
| LJ-1.59-A | Orchestrator audit: the load caveat is overstated | CORRECTED | Like-for-like at 5,027 lines is 60.41 to 62.60, 3.6 pc not 16.8. The gap was charged to load but is mostly the placement |
| LJ-1.60 | Build Lift12Out | NO-GO on a criterion I wrote wrong | Lift12Out is 3.5x fewer lines and 2.6x fewer seconds than the hand-written chain. The file is over the bar; the wing is not |
| LJ-1.60-A | Orchestrator audit: DD24 judges the wing, not a file | GATE PASSES | check-ratio: wing aggregate 0.0125 over 7,323 lines, within the bar. My briefs since LJ-1.58 set the criterion on the file |
| LJ-1.60-B | Fix check-ratio's mixed caliber | FIXED, second occurrence | It paired HEAD line counts with worktree seconds. ledger.count already took at_head=False; measure() now passes it |
| LJ-1.61 | Place the rest of the leaf chain | NO-GO, wing 1.38x | 165 lines cost 27.6 s. The wing had 5.74 s of headroom. 63 pc of the cost was module-header elaboration, not any definition |
| LJ-1.62 | Change the content class, or price the wall | BUNDLE WORKS; chain over | KFacts cuts Miscellaneous by 34 s and takes the wing to 1.02x. The whole leaf chain then places, at wing 1.28x |
| LJ-1.62-A | Orchestrator audit: the gate re-run, and where the seconds are | VERIFIED, 1.28x | 11.83 s must come off the WING, not the chain. StageCardinal holds 4.34 s and Presentation 0.42 s of it |
| LJ-1.63 | Find 11.83 seconds in the wing | 9.85 s found, 1.28x to 1.18x | StageCardinal's Successor cluster had no consumer and cost 83 pc of it. Sealing, frames and aliasing all regressed |
| LJ-1.63-A | Orchestrator audit of the Successor removal | UPHELD | No master takes a stage-card-suc shaped hypothesis and the two master hits are a comment and a substring. Removal is sound |
| LJ-1.64 | The last 2.33 seconds | REJECTED by audit | It passed the gate by removing the row-agreement band, which is what discharges TwelveAgree's 24 hypotheses. Restored |
| LJ-1.64-A | Orchestrator audit: the gate passed by moving the obligation | REVERTED, C-35 again | TwelveAgree takes mem-out..exin-back as parameters; the removed MemAgree proves exactly mem-out and mem-back |
| LJ-1.64-D | Fable 5 max-effort diagnosis of the DD24 residual | BAND, NOT ROWS | The residual is a net: Condensation +18.19 s against 15.88 s under-run elsewhere. Recommends a band-wide record bundle |
| LJ-1.65 | The band bundle, one family, probe-gated | NO-GO, 0.06 to 0.34 s | Under the 0.5 s line, inside a 1.5 s spread. P-o did NOT fire. The band's mass is not the restated telescopes |
| LJ-1.66 | Price one module application, then hoist | 1.016 s each; hoist +10.88 s | 18 applications are worth 18.29 s. Hoisting to three frames regressed, and is now false at two sites |
| LJ-1.66-R | DD25 review of LJ-1.66 and LJ-1.67 | SPLIT: measures upheld, conclusions overturned | The four hoists are ONE mechanism, admitted as P-w. Names the untested narrowing class |
| LJ-1.67 | Abstract the stack, one row | REGRESSED, +2.82 s | The P-h spelling at the row. Statements unchanged, tree green, ranges disjoint. Reverted. Six restructuring moves, six failures |
| LJ-1.68 | Narrow EnvSet to what consumers reach | REGRESSED, +3.18 s | Class (b) measured false. EnvSet exports 11, not 15: consumers reach 10, only memE-at is dead |
| LJ-1.68-A | Orchestrator audit: my export count was wrong | CORRECTED | I read 2761-2900 and swept in TmVal's exports. EnvSet ends at 2873. I stated 15 and 12-unused as verified |
| LJ-1.69 | Price one discharge | 3.6 s per row; x13 is about 47 s | The discharge alone exceeds the wing's whole budget. But the copy is LAZY: unused applications cost 0.089 s |
| LJ-1.69-A | Orchestrator audit: P-w amended the day it was admitted | AMENDED | The copy is paid at USE. The cost is the frame telescope, not the copy. A generic frame swings 47 s to 5 s |
| LJ-1.70 | The generic frame and the discharge | 24 DISCHARGED, 14.7 s | TwelveAgree takes 47 facts once and instantiates the twelve rows. The record shape heap-walled; the telescope is green |
| LJ-1.70-A | Orchestrator audit: I conflated two multiples | CORRECTED | check-ratio prints x the BASELINE 0.011057, not x the bar 0.012716. My 1.28x and 1.39x were baseline multiples |
| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |
| LJ-1.71-A | Orchestrator audit: I shipped a vacuous module | C-38 ADMITTED | I checked parameter count, instantiation count and both directions. None asks whether the telescope is satisfiable |
| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |
| LJ-1.72-A | Orchestrator audit: the tree was left non-compiling | REVERTED | Backed the repair up, removed five .lagda.md probes check-fences counted as masters, restored HEAD green |
| LJ-1.73 | Does TwelveAgree apply at an ABSTRACT frame | NO, WALLS AT 265 s | Worse than the concrete env's 210 s. The where-block is unaffordable at ANY frame; the abstract env is not the lever |
| LJ-1.74 | Split the twelve across modules | PEAK PER PROCESS | 3 and 6 rows green, 9 and 12 wall. A one-file split walls too. Separate invocations are green: 4 partials plus a composer |
| LJ-1.74-A | Orchestrator audit: the measured split is not the cheapest | REFINED | Six is the largest green rung, so 2 partials beat 4. Each re-pays the 105 s floor. 449 s against 699 s |
| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |
| LJ-1.76 | Build the split composition as masters | THREE MASTERS GREEN, 53.20 s | Five times cheaper than the probe price: the probes re-copied the row machinery, the masters import it |
| LJ-1.76-A | Orchestrator audit: the composer re-associates | BRIDGE OWED | SatGraphB.twelveB is one right-nested chain of twelve; the composer proves sixB and sixB. Different Formula terms |
| LJ-1.76-D | Fable 5 adversarial review of the MATHEMATICS | RIGHT THEOREM, WRONG HYPOTHESES | TwelveAgree is Devlin II.2.4 unrolled and faithful. But KFacts self-refutes against regularity |
| LJ-1.77 | Machine-check whether KFacts is uninhabitable | CONFIRMED, one step | arityK gives X in X through the singleton; ∈-irrefl refutes it. 6 masters take KFacts, 20 take a field |
| LJ-1.77-A | Orchestrator retraction | THE MATHEMATICS IS NOT DONE | I reported the leaf adequacy as the phase's completed mathematics. It typechecks and proves nothing as stated |
| LJ-1.78 | Conditional closure facts, on one row | MEMAGREE SURVIVES, mechanical | The premises come from the row's own codesK, already in the telescope. No new hypothesis. Probe green |
| LJ-1.79 | Guard the closure facts across the band | WHOLE BAND REPAIRED, GREEN | KFacts and every row guarded; arityK bound by transitivity. The LJ-1.77 refutation no longer typechecks |
| LJ-1.79-A | Orchestrator audit: refuted is not inhabited | GAP KEPT OPEN | Showing the refutation fails is not exhibiting an inhabitant. KFacts is still unconsumed, so C-35 still applies |
| LJ-1.80 | Build a KFacts value at the hull | VALUE EXISTS, at the STAGE | 27 fields all supplied at K = Lset lam. Killed mid-transplant after a six-process Agda pileup; master reverted |
| LJ-1.80-A | Orchestrator audit: the C-12 pileup | STOPPED, DETECTOR ADDED | Six agda under one wrapper, 48 GB worst case on 64 GB. The owner saw it, no tool did. status now counts children |
| LJ-1.81 | Is the stage enough, or is the hull needed | THE STAGE IS THE SITE | K' in Adeq is existentially quantified, so the proof picks the bound. No isL certificate for M or πX is needed |
| LJ-1.82 | Supply KFacts to the chain, at the stage | REACHES ShapesAgree, blocks there | The value extends to the 15 and 17 frames by KFactsCons, both green. The chain also needs a CODE SET C |
| LJ-1.82-A | Orchestrator audit: the field count | CORRECTED | KFacts has 29 fields, not the 27 my brief said. The return caught it. Association mismatch is real but not the first blocker |
| LJ-1.83 | Supply the code set and its facts | SUPPLIED; chain reaches WitnessAgree | C = K at the stage; compK/unCompK generic over any transitive set. Three more modules green |
| LJ-1.83-A | Orchestrator audit: C = K is a probe convenience | OWED, RECORDED | The real C is AllCodes, needing AllCodes in K, unproved. The stop at witK is independent of the choice |
| LJ-1.84 | Is witK satisfiable at all | REFUTABLE, machine-checked | Shapedness leaves the arity slot free, so a junk member pr K (pr #6 0) keeps w closed and shaped and lifts its rank past K |
| LJ-1.85 | Repair witK with a suppliable premise | PREMISE FOUND, both halves checked | w in AllCodes A kills the refutation and the closure supplies it. Truth still needs AllCodes A in Lset lam |
| LJ-1.86 | Is there a stage containing AllCodes A | EXISTS; proof cannot choose it | AllCodes-stage is green. But lam is a module parameter at every frame, so the obligation moves to the frame |
| LJ-1.87 | Does witK follow from both premises | NO: fourth statement defect | The premises bound w's MEMBERS, never w. The conclusion needs w definable over a stage, which is condensation itself |
| LJ-1.88 | Is the witness step circular | NOT CIRCULAR; finiteness | w is a finite union of key singletons, so finSet in the definable power set puts it one level up. Wiring, not redesign |
| LJ-1.88-A | Orchestrator retraction of the LJ-1.87 framing | REVERSED | I called it a design question needing the owner. It is wiring, and I should have tested my inference first |
| LJ-1.89 | Prove witK by the finite-family route | PROVED, staged not discharged | One open premise, the frame's stage hypothesis. Assembly green at 0.98 s user, verified by the orchestrator |
| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES cardκ | Every other hypothesis takes a value, including AllCodes A in Lset lam. Nothing in the tree proves any set is a cardinal |
| LJ-1.90-A | Orchestrator audit: IsCardinal is never inhabited | CONFIRMED | Two hits in src: the definition and the hypothesis. The probe's own kappa, sucV omega, is not a cardinal either |
| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |
| LJ-1.92 | Probe the order-type module | 365 LINES, 18.4 s, GREEN | The image block is 17 of the 18.4 s. V/Collapse does NOT carry it. The inferred seconds were 4.7x low |
| LJ-1.93 | Be the first consumer of the three split masters | NOT DISCHARGED | The twelve conjuncts match and the association bridge is green, but 39 of the composer's 69 facts have no supplier |
| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |
| LJ-1.95 | Refute tmKeyK, or show it inhabitable | REFUTED, MEASURED | Applied at the K slot's own element, closed by delivered in-irrefl. All three split masters state it, so all three are empty |
| LJ-1.96 | Price the ideal form of the three split masters | RETIRE, NOT RULED | Its no-home table is mostly INFERRED rows, so the verdict rests on inference. LJ-1.97 tests the family first |
| LJ-1.97 | Are the satisfier-in-K facts TRUE? | TEN REFUTED, MEASURED | Every one quantifies over a set nothing binds. With tmKeyK that is eleven facts of the shared frame |
| LJ-1.98 | Can the eleven refuted facts be TIED? | ONE TIE MEASURED NOT SUPPLIED | The T-slot tie fails at the EnvSet site. My abort criterion then stopped it, and it hid a second candidate |
| LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |
| LJ-1.100 | Extend the consumer's frame and re-measure the 39 | 39 BECAME 11, MEASURED | The 11 are exactly the refuted facts, whose types are empty. No frame extension can supply an empty type |
| LJ-1.101 | Close the cardk type gap, then price sq | GAP CLOSED, GREEN | cardk checks at the master's IsCardinal, no transport. And absorbs-subset is REFUTED, so Devlin55 is vacuous |
| LJ-1.102 | Restate ONE row in tied form and re-prove it | NO, MEASURED | Two components need two different premises, one arityK step apart. The row's telescope has neither arityK nor transK |
| LJ-1.103 | Restate absorbs-subset and re-check Devlin55 | REPAIRED, MASTER GREEN | The premise is alpha not in omega, matching sq. My suggested premise was too strong: the site runs at omega |
| LJ-1.104 | Give the row arityK and re-prove it in tied form | YES, BOTH DIRECTIONS | Telescope 44 to 51 lines. tmKeyK becomes a derivation costing zero hypotheses; its tied form was itself refuted |
| LJ-1.105 | Land the tie repair in EnvSet and the Mem row | MASTER GREEN | 122.3 s to 140.5 s cold, +184 lines. The other eight rows keep the refuted names UNUSED, so they are still vacuous |
| LJ-1.106 | Build Init at the Hartogs cardinal | YES, NO HYPOTHESIS LEFT | 507 lines, 31.2 s, choice-free and LEM-free. sq at the Hartogs cardinal follows from the delivered via-col-square |
| LJ-1.107 | sq at every infinite ordinal | PARTIAL: initial ordinals only | The non-initial case needs an injection the truncated least-of witness cannot give: the inject type is not a prop |
| LJ-1.108 | Delete the unused refuted hypotheses from the rows | ALL NINE ROWS, GREEN | Six of the eleven names are out of the master. Net -12 lines; +8.1 to +8.6 s against a +2 to +4 s projection |
| LJ-1.109 | Tie the key-fact family, the last five | ALL FIVE TIED, GREEN | All eleven refuted names are now tied or gone. A KFacts FIELD for the successor closure walls the master: P-x |
| LJ-1.110 | Restate the three split frames | ALL THREE GREEN, make check PASSES | Frames 43/43/69 facts to 37/36/59. The eleven names are gone from all three; sucK is a telescope fact per P-x |
| LJ-1.111 | Can Devlin55 take the TRUNCATED sq? | TRUNCATED CHAIN GREEN | Truncated sq holds at EVERY infinite ordinal, no choice. The cheap cure is NO; threading costs about 350 lines |
| LJ-1.112 | Instantiate the repaired composer | ZERO METAS, GREEN | 39 to 11 to 0. Every one of the 59 frame facts is supplied, but 29 come from consumer hypotheses that are NOT discharged |
| LJ-1.113 | Who supplies the twenty nine? | PROVABLE 1, NEW CONTENT 28 | None is refutable. Twenty five are one pattern, K closed under a machine construction; someEnv is the odd one |
| LJ-1.114 | Thread the truncation from StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs ONE honest injection; two truncation eliminations collide. Reverted; the cause is proved |
| LJ-1.115 | Probe someEnv, the K-closure family's widest term | ONE GAP, NOT FIFTEEN | It needs ONE closure beyond the 25: K closed under a CONSTRUCTED environment-set. The other three are supplied |
| LJ-1.116 | At which alpha does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is every infinite ordinal below alpha; the site is omega. Init is false at omega and at successors |
| LJ-1.117 | Restrict sq to the ordinals the consumer reaches | LANDED, make check PASSES | sq is bounded by sucV alpha0; the site at omega supplies it honestly. No conclusion changed |
| LJ-1.118 | Enter Devlin55 at the site | SITE VALUE BUILT, NOT ENTERED | The site instance is green at 13 lines against an inferred 20 to 30. The module still demands the whole function |
| LJ-1.119 | Restrict absorbs-subset the way sq was restricted | ENTERED, make check PASSES | Devlin55 now has NO parameter. BoundedSubsetAt is entered at the site; the stop is levelIn and cover |
| LJ-1.120 | Build the generic environment-set | BUILDS, someEnv CLOSES | Tower-free coding machinery, so the J tower gets the family unchanged. Only envSetK is still a hypothesis |
| LJ-1.122 | Land the generic environment-set by ADDING | BOTH MASTERS GREEN | The numeral version is DERIVED from the generic one, byte-identical type. Adding cost 179 lines |
| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |
| LJ-1.123 | Re-price the level-hood certificate | 2.8k TO 3.3k BECAME 0.6k | The LJ-1 series built the substrate under it; only the hull transfer remains. Read evidence, no probe |
| LJ-1.125 | Give envSetK a home in the frame | NOT REFUTED, FRAME GREEN | Stated at the frame telescope per P-x, not as a KFacts field. The instantiation re-measures at 0 metas |
| LJ-1.127 | Codify DD17's two versions and enforce them | SWITCH LANDED, DIFF APPROVED | scripts/dispatch_policy.py is the one switch; the AGENTS.md half landed in cfe2b5a under DD19 |
| LJ-1.128 | Re-measure the DD24 ratio baseline | BASELINE RE-MEASURED | The rise was the machine: an identical tree cost 11.2 percent more. The module rate was left owed |
| LJ-1.124 | Probe the bounded level-graph decode | GO, 147 LINES | Both directions close under the 150-line gate. The LJ-1.123 assembly claim holds; three delivered layers compose |
| LJ-1.126 | Wire pi streaming and resume into the dispatcher | BOTH DONE, PROVEN | pi --mode json streams per event; resume by --session. It also found that every resume ran on the codex path |
| LJ-1.129 | Adversarial review of the route, LJ-1.60 to LJ-1.127 | ROUTE DRIFT AT STATEMENT LEVEL | Devlin 5.5 assumes V=L and our Devlin55 dropped it. No delivered proof is false |
| LJ-1.130 | Move agent reports out of _build into git management | DONE | Owner ruled the layout: agents/reports, /archive, /briefs. 271 citations rewritten; agents/ is CC and lint-exempt |
| LJ-1.131 | Price the V = L route against the ambient one | ROUTE A-PRIME, 760 TO 1,320 | The tree already owns the order; V=L buys its DOMAIN. Superseded on price by LJ-1.136 |
| LJ-1.132 | Salvage what is left in _build | 24 DELETED, 11 REHOMED, 14 ARCHIVED | Seven lifecycle classes, not four. literature/ must stay: copyrighted, and a re-fetch loses the OCR line numbers |
| LJ-1.133 | Give the probes a lifecycle and settle where evidence lives | 284 TO 1, 257 ARCHIVED | the stale rule was backwards and would have deleted 234 |
| LJ-1.134 | Probe block A2, the A-prime route's widest term | GO, 207 LINES | The fibre extraction and the composite elaborate. A-prime's 760 to 1,320 price stands; a carrier crossing is new |
| LJ-1.135 | Re-measure ac_baseline_module_rate | 0.014367, UP 29.9 PERCENT | The sign was opposite to the brief: the bar gets LOOSER. Control run says 6.9 percent machine, 21.6 percent content |
| LJ-1.136 | Gate the remaining A-prime blocks | GO, BOTH PROBES | pick-canonical elaborates, so LJ-1.114's wall falls. A5's risk is seconds, not lines: 2.594 s per line |
| LJ-1.137 | Apply the four ruled AGENTS blocks and pay for them by trimming | 2,244 WORDS, 56 FREE | Two sentences are false today. The blocks cost 129 words and 43 are free, so the file funds them |
| LJ-1.138 | Give the probe lifecycle a correct trigger and a real execution point | TRIGGER IS A TASK, GATED | The clock is mtime and nothing runs the sweep, so 284 probes accumulated |
| LJ-1.139 | Repair the memo STATUS headers | 7 OF 9 REPAIRED, 8 RESOLVED WRONG | A D code cited with no home resolves against a DD row of the same number that means something else |
| LJ-1.140 | Close the D against DD retarget and give it a checker | 87 LINES, ALL RESOLVE | Six numbering series write D<n>, not two. A checker refuses a bare code when a DD row shares its number |
| LJ-1.141 | Rehome the probes beside their reports, tracked | 258 PROBES REHOMED, TRACKED | include: src agents/reports works. A staged rename walked past --diff-filter=ACM into src/ |
| LJ-1.142 | One directory per task, holding its brief, its report and its probes | 547 DIRS, ROOT IS agents/tasks | Brief, report and probes in one dir. A 14th consumer sat outside make check |
| LJ-1.143 | Split the DD25 bucket, retire archive/probes, and mirror the root in archive | 55 PLACED, ARCHIVE MIRRORS ROOT | Eight reviews declare what they built; disjoint sets summing to 55 |
| LJ-1.144 | Settle the three Agree masters: no consumer, bridge owed | BUILD THE BRIDGE, DO NOT RETIRE | The bridge is built in a probe at the consumer's exact types. About 38 lines |
| LJ-1.145 | Diagnose why the Condensation family is slow | ONE CONVERSION, 65 PERCENT OF ONE DEF | Both leads refuted. Seal satGraphAt: 2,459 ms to under 1 ms, about 21 s off, 40 percent of the gap |
| LJ-1.146 | Price levelIn and cover, the root of the unconsumed chain | A WALL, NAMED TWICE AT ONE TERM | The trophy needs them. About 1.0k lines. C-35 fires wing-wide, the trophy is unwritten |
| LJ-1.147 | Seal satGraphAt and measure what unfolding costs | SEAL GREEN, MINUS 38.78 s | unfolding cost nothing, 21 of 21 consumers green. The AC side gained more, so 1.56x became 1.91x |
| LJ-1.148 | DD24's tolerance is narrower than the machine's swing | A BIAS, NOT NOISE: A WARM-UP PENALTY | Run 1 is 1.811 s and runs 2 to 25 are 0.787 s. Fixed at about 0.9 s per series |
| LJ-1.149 | Audit the six standing OWED markers | ONE OWED FACT IS FALSE, TWO ARE PAID | T261's probe RAN on 2026-08-09; four live sentences said it never did |
| LJ-1.150 | Place the twelve-row bridge that LJ-1.144 built in a probe | GREEN, DISCHARGES NOTHING | 88 lines, 2.11 s, 40 percent under projection. The seal forced no unfolding, P-y holds twice |
| LJ-1.151 | Probe the one term two dispatches named and nobody ran | GO AT 21 LINES, AND valK IS FALSE | The band tightens on 9 of 25, not all 25. The wall stayed out: the two halves are separable |
| LJ-1.152 | Can two L-graphs compose without a second hasReplacementL | GO: 2.50 s, NO REPLACEMENT | Separation carries it, 2,500 to 1. The seal was NOT the cure and A5 is unpriced again |
| LJ-1.153 | Repair the refutable frame hypotheses that check-unbound-hyp flags | 38 TO 2: 36 REFUTED AND REPAIRED | One tie for all 36. Every site already held the premise and threw it away |
| LJ-1.154 | Carve the identity graph by separation, not by replacement | GO: 1.73 s AGAINST 254.22 s | The device BUILDS, not only composes. Devlin's base theory has no replacement at all |
| LJ-1.155 | Is there a second dominant term, or is the wing intrinsically this expensive | BOTH WORLDS, SPLIT PER MASTER | The Agree masters have a second term, WING-LOCAL, zero baseline impact |
| LJ-1.156 | Does A5 need CSB at all | DISSOLVED: A5 CARRIES ZERO REPLACEMENT | CSB is out and the swap is not dearer. The new gate is LeastCardInj: 44 lines, 100.64 s |
| LJ-1.157 | Adversarial review: what did the new route rebuild that the archives held | FOUR MISSES, A MEASURED DRIFT | The heading survived, the content decayed. CSB surfaced twice, lost twice |
| LJ-1.158 | Collapse the Agree telescopes into one record | WING 2.06x TO 1.60x, HALF THE GAP | TwelveAgree behaved BETTER, not worse: DeadCode by 138x. sucK is the only waller |
| LJ-1.159 | LeastCardInj is 48 times the bar and nobody has attacked it | 133 s TO 46 s, 13 LINES | My order-type lead REFUTED. The cause is sucV at a variable; the cure is prior art next door |
| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |
| LJ-1.161 | Gate the transfer half of CrossOut at the collapse image | GO AT 20 LINES, AND A NEW WALL | The transfer is cheap. The certificate CrossOut actually needs walls at 20 min, 9.03 GB |
| LJ-1.162 | Leg 3 of CrossOut | NO-GO ON PRICE: 125 LINES, NOT 60. DD25 review [LJ-1.182] UPHELD | The chain typechecks whole. Both NO-GO branches are MEASURED FALSE. CrossOut is 163 lines |
| LJ-1.163 | ElemDown, the residue common to all three open facts | ALREADY SUPPLIED, IN THE WRONG PLACE | My premise was FALSE: my grep excluded the file holding it. 0 new lines, it needs a move |
| LJ-1.164 | Move elem-down out of Co, which is a pure move | PURE MOVE, 146 IN 146 OUT, NET 0 | Zero proof lines changed. Reachability measured BOTH ways: the pre-move tree exits NotInScope |
| LJ-1.165 | BUILD the crossing face | STOP: SIX GATES PRICED DERIVATIONS. DD25 review [LJ-1.181] UPHELD | The assembly works at 17 lines. Nothing supplies the face: KFacts is never CONSTRUCTED |
| LJ-1.166 | Gate K(u), the SUPPLY that six gates never priced | GO: 88 LINES, 2.69 s, BOUND FITS | Devlin's engine transfers. Three of four closure classes were proved and no gate cited them |
| LJ-1.167 | The definable power at a general argument, and pairing at a general limit | GAP 2 GO AT 35, GAP 1 NO-GO | Gap 2 sat in the prior dispatch's file. Devlin leaves gap 1 as an exercise |
| LJ-1.168 | Re-measure the satisfaction layer, 5,047 lines never re-priced | 5,047 COLLAPSES TO ABOUT 270 | The figure was never measured. LJ-1.10 had already called it a false anchor |
| LJ-1.169 | powIter, the last term with no provenance | NO-GO OVERTURNED by DD25 review [LJ-1.179] | Devlin's codes are sequences over a fixed set; ours bake parameters into the code tree. P-l |
| LJ-1.170 | Price BOTH arms of the coding fork | A THIRD ARM SETTLES IT, 37 LINES GREEN | Devlin's split is already delivered on the AC side. The archive ASSUMED arm A's bound, never reached it |
| LJ-1.171 | The last gate before the build | GO AT 56, AND THE CHAIN IS MEASURED | The search paid a fifth time and changed the ingredient: finSet cannot be read back, env can |
| LJ-1.172 | BUILD the supply | 1 TO 5 BUILT; 6 REFUTED AT THE JOIN. DD25 review [LJ-1.180] UPHELD | envSetK asks a level to hold a function space. Six names, one fact, no supplier |
| LJ-1.173 | Restrict envSetK to a numeral arity | ALL 21 CURED, 77 LINES | My ruling's scope was one record; its sweep measured three. Patch by SHAPE, not name: one field has four aliases |
| LJ-1.174 | Rewrite the spent resumption block as the live status | THREE FIGURES WERE FALSE | A5 unpriced, DD24 1.91x, unbound-hyp 18: all had answers. A status screen has no checker |
| LJ-1.175 | Sum Route A-prime to ONE total | BLOCKED AT 705, BLOCKS DO NOT PARTITION | A5 has no live line price and five overlaps are quoted. My brief's premise was MEASURED FALSE |
| LJ-1.176 | Price A5 under a stated partition | PRICED: 547 LINES, ZERO REPLACEMENT | An A5 object builds into L by ONE separation, 1.72 s. The 300-line item is DISSOLVED, not divided |
| LJ-1.177 | Cure the Agree masters' second term | STOP: CURED FIVE DISPATCHES AGO | My premise was false, and LJ-1.158's row sits directly below LJ-1.155's in this table. Next lever caps at 5.2 s |
| LJ-1.178 | Build levelIn and cover | BUILT, THEOREM DOES NOT DERIVE | Two of three facts discharged and the debt moves to the STAGE. New wall: Devlin's (a) at the AMBIENT carrier |
| LJ-1.179 | DD25 review of LJ-1.169's rank NO-GO | OVERTURNED: A FIXED-SHAPE NO-GO | Right for the coding it measured, wrong for the tree, which already carries the parameter split |
| LJ-1.183 | Audit the orchestrator against every DD, under DD0 | SIX FINDINGS, FOUR NEW | The struck ruling still shipped in a live brief and my own rulebook still named the heads |
| LJ-1.184 | AmbientRead, Devlin's (a) at the AMBIENT carrier | SUPPLIED UNDER AN ASSUMED q. See LJ-1.243 | Its 0.2 declared six readings and omitted q, a parameter nothing instantiates |
| LJ-1.186 | Compress the DD series to the rule itself | 41,981 TO 28,662, NOTHING LOST | Nine rows were already pure rule. Every removed sentence is in the JOURNAL under its own DD heading |
| LJ-1.187 | Put every part of dev/ where its KIND belongs | DONE: 2 MOVED, 4 DEFECTS FOR THE OWNER | The division HOLDS across dev/. I misread its status field as death; the work was on disk |
| LJ-1.188 | Write the dispatch and herdr knowledge into a SKILL | BUILT, AND IT CORRECTED MY BRIEF | The tier line does not drive the model: dispatch.py reads the flag, never the brief |
| LJ-1.189 | Which recurring orchestrator errors would a SKILL prevent | FOUR PROPOSALS, ONE DISEASE | Seven errors in seven costumes: a claim acted on without being bound to an artifact opened |
| LJ-1.190 | Reconcile dispatch.py against the SKILL | 3 CONTRADICTIONS, 2 FIXED, 1 OPEN | The DD canon rules any tie. A refusal is never deleted without evidence its failure cannot recur |
| LJ-1.191 | Build P1, the load-bearing-claim SKILL | BUILT AND LIVE | LJ-1.189's first proposal. C-32 exists and did not reach the moment of action; the moment is a WRITE |
| LJ-1.192 | Build P2, the artifact-over-proxy SKILL | BUILT AND LIVE | The artifact is the evidence and the status field is a hint. Three outcomes were recorded from a proxy |
| LJ-1.193 | Build P3, the commit gate against live write territory | BUILT AND GREEN, IN make check | Two git add -A sweeps took a sibling's work. dispatch.py already computes the intersection |
| LJ-1.194 | Build P4, the DD number-uniqueness check | BUILT, ONE CODE PATH FOR EVERY SERIES | I minted a duplicate DD27 and check-rule-ids reported CLEAN: it verifies resolution, never uniqueness |
| LJ-1.195 | Consistency audit by document rank | 4 LIVE, 1 ALREADY FIXED | DD4's no-checker claim stood in four documents against a checker that gates. All four repaired |
| LJ-1.196 | DefAt's ambient reading: 84 lines or a chapter | NO-GO: IT IS A CHAPTER | u's slot is d, the definable powerset of the recorded value, and the induction never pins it |
| LJ-1.197 | Do build-manifest.toml and rules.toml actually FIRE | 7 FIRE, 5 SILENT, 1 UNPROVOKABLE | All five silent rules are build-manifest's, and its checker was in no gate at all |
| LJ-1.198 | Close A6's open charge | A WALL, NOT A NUMBER. DD25 review [LJ-1.215] | One typecheck ran 3.06 hours and did not finish. The seven cells do not sum and LJ-1.8 stays blocked |
| LJ-1.199 | BUILD step 6, the satisfaction layer supply | STOP AT ZERO LINES: A JOIN | envSetNumeral needs omega in lam and HullStage's telescope has not got it. Found by reading, no Agda run |
| LJ-1.200 | DD25 review of LJ-1.196's NO-GO | UPHELD BUT MISATTRIBUTED | The verdict and the reading are right. The cause is not Delta-0 and A CHAPTER is an unmeasured consequent |
| LJ-1.201 | DD25 review of LJ-1.185's refutation of the 16 s | UPHELD BUT MISATTRIBUTED | The 16 s is dead, but the term is UNPRICED not unmeasurable, and Deserialization rose 8.3 s unowned |
| LJ-1.202 | Is omega in lam DERIVABLE at the HullStage site | DERIVABLE, CONFIRMED BY TYPECHECK | No new hypothesis: the instantiator derives it from its own telescope, so the prohibition stands |
| LJ-1.203 | Can herdr Agent Automation replace dispatch.py | OPTIMIZE AND COMPLETE, NEVER REPLACE | 74 pc is Bedrock law no herdr feature can carry. Only the wait protocol has a supersession |
| LJ-1.204 | Deserialization rose 8.3 s at Condensation | CAUSED: OUR OWN arNum FIELD | Interface size REFUTED, 0.85 pc size against 8.1x time. The cure is a seal hypothesis, UNPRICED |
| LJ-1.205 | Reconcile our dispatch SKILL against herdr's official one | 7 DELETED, 59 ADDED, ONE RULING OWED | Neither skill supersedes the other. blocked read as FINISHED and the owner ruled it |
| LJ-1.206 | Measure herdr's wait supersession | DOES NOT HOLD. DD25 [LJ-1.215] | events.wait reproduces the at-once-idle flaw and cannot wait on a death. Nothing landed |
| LJ-1.207 | Auto-switch the mode on DeepSeek's peak clock | LANDED, AND THE PIN STILL WINS | VERSION_IN_FORCE = auto lets the clock select, and the printout names the window and next boundary |
| LJ-1.208 | Gate DD25: a negative return whose row names no review | BUILT, PLUS A REGISTER I DID NOT ASK FOR | It found me misreporting DD25's record, and read it back: 71 pc overturn rate |
| LJ-1.209 | Price the seal | SEAL DOES NOT REACH: 83 ms. DD25 [LJ-1.215] | Emptying the numeral content moved 47 ms the WRONG way, so no restatement reaches the 8.2 s |
| LJ-1.210 | Is the chapter really 17 lines | THE CHAPTER DISSOLVES: 42 WRITTEN, 1,272 SURVIVE | Model is class-generic and typechecks first try. Both instantiations green. Devlin agrees |
| LJ-1.211 | Why is the DD25 overturn rate 71 percent | BRIEFS CAUSED 8 OF 10, REVIEWER 0 | And the rate was my miscount: 71 became 64 became 46 once the register read the decided rows |
| LJ-1.212 | Build the PREMISES gate | BUILT, AND THE RAW LIST FIRED 118 OF 118 | It measured first and refused to build the list it was given. The active list fires on 23.7 pc |
| LJ-1.213 | Gate the chain: Powerset and DefAt-stage | NOT AT MODEL'S RATE; THE GATE IS ORDER | Plumbing is 12 not 17, DefAt-stage is 8 lines. Suppliers import the tower, so port bottom-up |
| LJ-1.214 | Is the 8.2 s the telescope component | THE COMPONENT CARRIES 7,925 OF 8,236 ms | Reverting it alone recovers 96 pc. The cure un-cures 21 fields, so it is the owner's design call |
| LJ-1.215 | DD25 review of three negatives | UPHELD, UPHELD, MISATTRIBUTED | A6 is UNPRICED not WALLED, and my missing clock cap caused it. Re-price starts from the green E interface |
| LJ-1.216 | Does Powerset serve BOTH towers | NO, AND IT NAMED THE BLOCKER | The delivered L.Coding.Model leaks the tower into the body, so the chain's first brick is now certain |
| LJ-1.217 | Re-price A6 from the green interface, with a clock cap | A6 = 446, ONE NUMBER WITH ITS BASIS | The wall was fixed-shape: fibre walls at 1,810 s, direct equality is green in 15.0 s |
| LJ-1.218 | LJ-1.9's audit: the wing's ratio and removable lines | 1.70x, GAP 60.0 s, 695 REMOVABLE | 523 of the 695 are one superseded chain, so the figure is 695 or 172. LJ-1.222 checks it |
| LJ-1.219 | Join GenModel to Powerset at the ambient class | MODEL LINK COMPOSES, BRICK TWO LEAKS. DD25 [LJ-1.221] | Five Model names green ambient. Recover's keyOf leaks at :142. Plumbing 21 lines |
| LJ-1.220 | Parameterize every leak and census the chain once | EXIT 0. WIDTH 8 MODULES, 19 NAMES | LJ-1.224 corrected 9 and 22 down. extAt-in and the domAt trio now MEASURED. The 17 was inferred |
| LJ-1.221 | DD25 review of LJ-1.216, LJ-1.219 and the brief pattern | UPHELD, MISATTRIBUTED, WASTEFUL | Brick two is two one-liners GenModel holds. I turned a typecheck order into a dispatch order |
| LJ-1.222 | Check LJ-1.218's 523-line supersession before it lands | 695 REFUTED, THE NUMBER IS 83 | The chain holds Condensation's only carrier transfer and both uses of abs₀ and σ₁-up |
| LJ-1.223 | Read the suppliers in one pass, thin against thick | 2 THIN, 8 THICK, 2,971 SHARED | Graph was already ported at GenGraph.agda. Plumbing about 200 for ten, per-tower residual 0 |
| LJ-1.224 | Is LJ-1.220's exit 0 bought? Check the 22 types | NOT BOUGHT. 22 of 22 FAITHFUL | Five reconstructions sound; InL.lagda.md:253 holds the same reduction. Width falls to 8 and 19 |
| LJ-1.225 | Does the ported chain discharge LJ-1.7's residue at all | NO. IT STOPS ONE MODULE SHORT | The lift is six ambient readings of L.Coding.Sequence, in no port scope. sl and sc stay open |
| LJ-1.226 | Build pairω into L, the route's widest line | OVER 160 UPHELD, 700 UNQUANTIFIED. DD25 [LJ-1.231] | 83 lines MEASURED green at 1.69 s. Its rows sum to 743 and 190 cite no basis |
| LJ-1.231 | DD25 review of LJ-1.226, where 160 became 700 | UNQUANTIFIED. 83 IS THE EVIDENCE | Band is half-open from about 355. The consumers demand an injection, not object-language arithmetic |
| LJ-1.232 | A1 and A3, the gate list's two cheap probes | A1 IS 54 AND NEEDS 3 LEMMAS; A3 IS 26 | isL alone does not suffice. stageBound DOES supply beta free, and A3 lands under its 45 |
| LJ-1.227 | The gate list for A-prime's reading residue, five blocks | ZERO DISSOLVE, FIVE NAMED TERMS | One overlap stands and double-counts A2 inside A4, so the sum is 1,470 to 1,521, not 1,548 |
| LJ-1.229 | A2's range set and ranAt, the block others name | 186 AGAINST 170, AND THE DOUBLE IS 27 | Replacement was needed; separation does not carry it. The 27-to-78 band closes at 27 |
| LJ-1.228 | Price sl and sc, the two hypotheses nothing on record prices | NOT SUPPLIED. ABOUT 0.15k EACH | Both records priced something else: 2.8k was the bypassed hull route, 16 was the assembly |
| LJ-1.230 | The stage-carrier decode, named by LJ-1.123, never run | NO-GO, THREE WALLS NAMED. DD25 [LJ-1.233] | The delivered decode reads the UNBOUNDED graph; level-hood needs the BOUNDED one |
| LJ-1.233 | DD25 review of LJ-1.230's NO-GO | OVERTURNED. WALL (a) WAS ALREADY GO | LJ-1.124 ran that probe on 2026-08-13 at 147 lines. Two briefs missed the row and I wrote one of them |
| LJ-1.234 | Does pairω need an object-language arithmetic | NO. DISSOLVED AT 60 GREEN LINES | The order route closes the base at omega, 1.19 s, zero object-language formula. Dissolution four |
| LJ-1.235 | Strengthen the bound hasReplacementL discards | THE BOUND COMES OUT, 18 LINES | A sibling lemma; hasReplacementL unchanged and its five consumers untouched. Step zero exit 0 |
| LJ-1.236 | A4 and A7, the gate list's last two, A7 first | SHAPES MATCH. A7 IS 47, A4 IS 43 AT 1.14 s | The inferred seconds RISE is REFUTED: A4 is 88x cheaper because orderAt is sealed |
| LJ-1.237 | Assemble sl and sc now that all three walls are down | BOTH BUILD ON ONE UNSUPPLIED TERM | sl 14 lines, sc 38, both over `lh` which enters as a PARAMETER. The floor stands, direction UP |
| LJ-1.238 | Port L.Coding.Sequence, the six readings | IT PORTS. 40 WRITTEN, 145 VERBATIM, RESIDUAL 0 | The six readings are tower-neutral. The DefAt trio leaks and the ambient body supplies it |
| LJ-1.239 | Supply lh, the one term LJ-1.7 still owes | NOT SUPPLIED. THE TYPE IS WRONG. DD25 [LJ-1.240] | lh names arity 2; the stage level-hood has arity 4+n because its tag numerals are slots |
| LJ-1.240 | DD25 review of LJ-1.239's refutation | RECIPE UPHELD, MY ESCALATION REFUTED | The type stands and costs sl and sc zero. The archive holds an arity-2 level story nobody read |
| LJ-1.241 | Build phi-zero at arity two, read the declined archive | IT BUILDS. 77 LINES, TOP TYPECHECKS | The archive gave the shape and two primitives, no discharge. It verified the slot trace |
| LJ-1.242 | The fifth step: does amb hold at the real phi-zero | NO. THE SUPPLY WAS CONDITIONAL. DD25 [LJ-1.243] | It assumes q, an equation false at a constant-free phi-zero, never declared |
| LJ-1.243 | DD25 review of LJ-1.242's re-opening of amb | UPHELD. NEVER SUPPLIED OUTRIGHT | theorem is equally conditional. A third route exists, and absFo is LIVE and inverts route 1 |
| LJ-1.244 | The third route: build q-prime | IT COLLAPSES INTO ROUTE 2. DD25 [LJ-1.246] | q-prime IS route 2's hard half. The blocking term is the coding-transfer bridge at the class carrier |
| LJ-1.246 | DD25 review of LJ-1.244's route collapse | UPHELD BUT MISATTRIBUTED. NOT A CHAPTER YET | The stuck goal priced a REFUTABLE target. graph-assembly is proved green in the archive |
| LJ-1.249 | Port graph-assembly to the class abstraction | IT PORTS. NO CHAPTER. 132 LINES | Step zero green today. The 30-line assembly is verbatim with three renames. DD4 split HELD |
| LJ-1.250 | Price StepAgree and ApproxAgree | NEITHER BUILDS: UNCONSTRAINED INTERFACES. DD25 [LJ-1.251] | Refutable at that generality. The residue is the leaf-adequacy supply, not one term |
| LJ-1.251 | DD25 review of LJ-1.250 | UPHELD. THE PRICE WAS ALREADY IN PLAN 0.0 | About 400 lines. Ten dispatches re-derived open work item 1, which I rewrote around twice |
| LJ-1.252 | Can omega in lam be supplied | MUST BE ADDED, AND IT IS CHEAP | Five lines at one consumer. Branch 1 refuted by COUNTERMODEL at lam = omega. Step 6 is fundable |
| LJ-1.253 | Close A-prime's last two reading residues | 1,089. A PRICE. BOTH RESIDUES DISSOLVE | A6's 47 was a double-count of the graph LJ-1.217 later measured at 296. Reading residue is now ZERO |
| LJ-1.254 | BUILD step 6, the 28 fields | 1 OF 28, PLUS THE JOIN. sucK DOES NOT WALL | envSetK is green, and it sits beneath 11 of the 28. 141 lines for the first field plus two lemmas |
| LJ-1.255 | Build the eleven fields envSetK unlocks | 5 OF 11, AND THE 255 IS REFUTED. DD25 [LJ-1.256] | Marginal 11 to 17 lines per field against the 255's implied 9.1. The entry estimate was 1.5 |
| LJ-1.256 | DD25 review of LJ-1.255's refutation | OVERTURNED. THE 255 STANDS, PLUS ABOUT 50 | Five copies of one proof are one observation. someEnv's 120-line blocker is delivered in FOUR |
| LJ-1.257 | The four envInK fields and someEnv | 5 OF 5. COLLAPSE IS 67 AGAINST 85 | Bodies shrink 55 to 30. The numeral premise is a MASTER change, priced at 40 to 60 mechanical lines |
| LJ-1.260 | Land the numeral premise in TFacts, LFacts and UFacts | DISPATCHED | The master's own note at TwelveAgree:298-301 says it costs consumers nothing, and codesK proves it |
| LJ-1.258 | The fifteen fields that do not touch envSetK | 12 OF 15. RATES ARE 2, 1, 1 BODY LINES | Far UNDER 9.1. LJ-1.168's 1.5-line entry estimate HOLDS. The three consK need an env closure |
| LJ-1.259 | Build the env closure, the one L-row the nine-lemma table never priced | DISPATCHED | envConsK. The same shape as the sucK hole LJ-1.256 found. It unblocks the last three fields |
| LJ-1.247 | Re-derive A5 and measure its last inferred row | ROW 4 DISSOLVES. A5 = 348, ALL MEASURED | The column square is in NO src file, three greps, zero hits. Dissolution five |
| LJ-1.248 | Route A-prime's total | 1,150 ARITHMETIC, and THREE named causes | Per-tower half MEASURED at 146. The last reading residue is 47 lines, 4 percent, down from 555 |
| LJ-1.245 | Apply C-45 to the record | 7 UNDISCHARGED, 0 ROWS REST ON THEM | The record is clean and src carries only the idiom form. LJ-1.243's set was wrong: 8 sites, 1 discharged |
| LJ-1.185 | The 16 s billed outside every definition | THE 16 s DOES NOT EXIST | A double subtraction. The residue is OccursCheck plus TypeSig, and instantiation is 0.9 pc of it |
| LJ-1.180 | DD25 review of LJ-1.172's refutation at the join | UPHELD | Every load-bearing citation re-derived at the commit the target measured, not at the working tree |
| LJ-1.181 | DD25 review of LJ-1.165's stop on the crossing face | UPHELD, BY TWO HEADS | Both re-derived the citations at the pinned commit. The sibling build is aimed at the RIGHT term |
| LJ-1.182 | DD25 review of LJ-1.162's NO-GO on price | UPHELD | It re-derived the 125 lines from the PROBE, not from the report's account of the probe |
| DD25-GAP | Orchestrator audit: DD25 was not followed | SEVEN TRIGGERS MISSED | LJ-1.55, 1.56, 1.59, 1.60, 1.61, 1.65, 1.66 all triggered and none was reviewed. I invented a MEASURED-class exemption DD25 does not grant |
| LJ-1.8 | Build: assemble L models GCH | planned | The measuring trophy. Needs LJ-1.7. ARCHIVE: CardinalPredicates, 399 lines, PORTABLE per the LJ-1.1 recon |
| LJ-1.9 | Quality audit: the wing's ratio AND its net removable lines | ANSWERED: 1.70x AND 83 | LJ-1.218 measured both, LJ-1.222 cut 695 to 83. Ledger carries 83; 64 of them stay unaudited |
| LJ-2.0 | Re-price the owed evidence: T257's weak point and T261's probe | planned | Gates LJ-2.5. LJ-1.11 F4 adds: price ONE bounded op-clause x16, since 470-610 covers only the 6 structural |
| LJ-2.1 | MEASURE the internalization double trophy, lines and cold seconds | planned | Records measured, LJ-1.1's projection and LJ-1.9's removable together. Line benchmark is the SMALLER. C-12 |
| LJ-2.2 | Re-arm the thresholds, rebuild [[remaining]] and [[owed]] | planned | OWNER JUDGES the wing a fair paper BEFORE the flags flip (DD5). Four stale flags to clear |
| LJ-2.3 | Recon: the reuse map and the architecture that MAXIMIZES sharing | planned | DD4 decided here. Supersedes LJ-3.1. Delivers section 4's skeleton. Quote ledger.py --reuse |
| LJ-2.4 | Adversarial review of LJ-2.3's reuse map | planned | The critic is never the author. Supersedes LJ-3.2. A failing reuse claim sends LJ-2.3 back before the ruling |
| LJ-2.5 | THE ARCHITECTURE RULING (owner), on measured evidence | planned | DD2's candidate confirmed, amended or replaced. Needs LJ-2.0, 2.1, 2.2 and 2.4. Nothing in phase 3 starts first |
| LJ-3.1 | Recon: the two-tower architecture for MAXIMUM shared code | SUPERSEDED | Moved ahead of the architecture ruling as LJ-2.3 (DD2, amended 2026-08-09). Rule 3: new code, old row kept |
| LJ-3.2 | Adversarial review of LJ-3.1's reuse map | SUPERSEDED | Moved ahead of the architecture ruling as LJ-2.4. Rule 3: a re-stated goal takes a new code and the old row points at it |
| LJ-3.3 | Gate: probe the widest unmeasured term in the ruled architecture | planned | DD8, and it needs LJ-2.5's ruling first. Both constraints are relative, so an ungated term risks the endpoint |
| LJ-3.4 | Build: the J tower through rud | planned | ARCHIVE FIRST: the rud route delivered sixteen operations and a Story layer. Price port against fresh write per module |
| LJ-3.5 | Build: the two-directional bridge, L to J and J to L | planned | DD2 keeps BOTH directions. ARCHIVE: archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md |
| LJ-3.6 | Build: L models AC on the bridge | planned | The first trophy on the new route. Needs LJ-3.4 and LJ-3.5 |
| LJ-3.7 | Build: L models GCH on the bridge, reusing what LJ-2.3 mapped | planned | Second trophy. The reuse map is the deliverable's test, not just its plan |
| LJ-3.8 | MEASURE the double trophy against both DD5 benchmarks | planned | Lines and cold seconds. The pass-or-fail of the whole route |
| LJ-3.9 | The prose phase opens | planned | DD23. Only after LJ-3.8 passes. Chapter narrative and the trilingual exposition, nothing before |

### Bookkeeping

The dated records (spike verdicts, landed-batch records, tripwire changes,
retirement hashes) have moved to `dev/JOURNAL.md`, section *Dated records*,
together with the execution narratives of the large goal rows. This section
stays as the pointer so the registry's structure is unchanged: a fact that is
a RULING belongs in a row above; a fact that is an EPISODE belongs in the
journal; a fact that is a LAW belongs in `dev/LESSONS.md`.
