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

## 0.0 RESUME HERE, written 2026-08-13 at a machine restart

**Read this first and delete it when it is spent.** The tree is clean at this
commit and every dispatch has landed. **Nothing is half-applied.**

**FIRST COMMAND, before anything else:** `make check` in the background. Four
masters changed on 2026-08-13 and each was typechecked alone; **the whole-tree
gate has not run since.**

**WHERE LJ-1 STANDS.** Three rows are open and they block in this order:

| row | blocked on |
|---|---|
| `[LJ-1.7]` | `levelIn` and `cover`. **STRUCTURE ONLY**: 888 lines at 0.0111, under the bar, but the semantic transfer is assumed |
| `[LJ-1.8]`, the trophy | Route A-prime has no total, because **A5 is unpriced** |
| `[LJ-1.9]`, the audit | **DD24 reads 1.91x** and the ruling that decides it is the owner's |

**THE FOUR THINGS TO PICK UP, in value order, each with its own evidence
already on disk.**

**1. Carve the identity graph by SEPARATION instead of replacement.**
`[LJ-1.152]` named this as the highest-value next hour and measured why: one
`hasSeparationL` costs under 0.1 s and one `hasReplacementL` costs 259 to 269 s,
**at least 2,500 to 1**. **If the identity graph lands near 2.5 s, `[LJ-1.136]`'s
254 s construction was never necessary and A5's seconds collapse.** A5 is
UNPRICED, not priced low: `[LJ-1.152]` refused to multiply 2.50 by five and said
so.

**2. Finish `[LJ-1.153]`'s sixteen rule-2 repairs.** Refuted and unrepaired, and
**it is NOT a C-38 stop**: it found no site that cannot supply the repair and ran
out of time at the checkpoint. Its report section 10.3 carries the plan whole.
The tie is `w ∈ K` for all sixteen, the shape is `prK`, and **the suppliers are
already bound and already unused at both call sites.** The chain terminates at
`LeafAgree`, which has no consumer, so nothing downstream can break.
`check-unbound-hyp.py` stands at 18.

**3. Diagnose the Condensation family to exhaustion.** `[LJ-1.145]` found ONE
term worth 87 percent at one site and **nobody has looked for a second.** This
decides whether the DD4-against-DD24 conflict has to be ruled at all: if the
wing has more terms of that size, it closes its own gap; if it does not, the
owner has the full evidence and must rule.

**4. The `levelIn` wall itself**, `π (Lset m') ≡ Lset (π m')`. `[LJ-1.51]`
titled it the term I cannot write, `[LJ-1.121]` reached it by another method
and stopped, and four dispatches went around it. **Nobody has ever been funded
to build that chapter.** `[LJ-1.151]` MEASURED that the instantiation half is
separable from it, so the wall is now isolated rather than entangled.

**WHAT IS WAITING ON THE OWNER, and none of it blocks the four above.**

- **DD4 against DD24.** A cure in shared machinery made every master faster and
  the ratio WORSE, 1.56x to 1.91x, because the AC side gained 41.7 percent and
  the wing 7.9. **It is a property of the bar, not an accident of that edit.**
  Item 3 above decides whether the ruling is needed.
- **The three `*Agree` masters.** Measured stable on the cured tree, but
  `[LJ-1.146]` found that retiring them retires the wing, because the whole
  chain is unconsumed only because the trophy is unwritten.
- **`check-unbound-hyp.py` rule 3.** `answers` and `ih` are NOT refutable,
  MEASURED, so the fix belongs in the checker.

**ONE ORCHESTRATOR HABIT THAT COST THREE TIMES ON 2026-08-13**, recorded here
because no checker catches it: **do not change anything under a running agent.**
Twice a directory-wide `git add -A` swept in a sibling's work in progress; once
a tool rewrite landed while another agent was measuring with that tool, and it
lost four figures. **Commit by explicit path, and land a tool change only when
no agent holds it.**

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

**The core constraint is architectural, and it is the one that matters:
MAXIMIZE THE CODE THE TWO PROOFS SHARE.** The total falls out of that. It is
never pursued by splitting a chapter, by re-bucketing lines between the two
wings, or by any other accounting move; `[LJ-0.1]`'s predecessors caught that
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
| DD1 | The theorem, stated honestly | As in section 1: V=L ⊨ ZFC, relative consistency, relative to the host, and never an unqualified "Con(ZFC)". The endpoint is the SAME L satisfying GCH, stated internally, giving Con(ZF) → Con(ZFC + GCH) under the same relativization; "Con(GCH)" is likewise never claimed unqualified. |
| DD2 | **THE ENDPOINT IS RULED. THE ARCHITECTURE IS THE LEADING CANDIDATE, and it is ruled at `[LJ-2.5]` against measurement.** | **Ruled 2026-08-09 by the owner, and AMENDED the same day on `[LJ-0.3]`'s finding.** **WHAT IS RULED AND NOT REOPENABLE:** both trophies, `L ⊨ AC` and `L ⊨ GCH`, both stated in L, so no re-founding onto J is ordered; and where a bridge is built it delivers BOTH directions of the two-definition identification, never the one-way variant. **WHAT IS A CANDIDATE:** the two towers and the bridge, L plus J through rud. It is the leading architecture and the plan builds toward it. It is not yet the binding ruling. **WHY THE AMENDMENT.** The original row ruled the architecture on 2026-08-09, and `[LJ-0.3]` found the warrant self-contradictory: archived D26 held that a number alone may never put the route back on the table, and D39 changed the route on `[L3.32-T257]`'s figure, which `dev/ledger.toml` declares NOT YET CLEAR ENOUGH TO BIND the constraints that same figure set. **One pass by one agent cannot be too weak to set a threshold and strong enough to overturn a route.** The retrospective did NOT refute the architecture; it refuted the timing, and the owner adopted that. **SO THE RULING MOVES TO WHERE THE EVIDENCE IS**, `[LJ-2.5]`, after `[LJ-2.1]` measures the internalization double trophy, `[LJ-2.2]` writes both DD5 benchmarks in, and `[LJ-2.3]` delivers the reuse map that DD4's core constraint turns on. The candidate is confirmed, amended or replaced there, on measured evidence and not before. **A MEASUREMENT FOR `[LJ-2.5]`, recorded 2026-08-10 and NOT a re-opening.** `[LJ-1.2]` probed the Def tower's level-story certification and returned NO-GO: the step clause has no Delta-0 witness at ANY carrier, because the coded satisfaction leaves carry unbounded quantifiers. `[LJ-1.10]` traced that to **D-26 being paid**: a definable-power stage carries no generation data, so its level-hood must run through codes and satisfaction, and those leaves are unbounded. On the J tower the same story is structural with the Def-step collapsed to `⊤̇`, and its bounded clause layer is priced at 470 to 610 lines. **So the level-story certification is a few hundred lines on one tower and thousands on the other**, and that asymmetry is a fact about the architecture rather than about this wing. `[LJ-1.10]` states its own limits: the J tower is not free, its equivalence still needs fresh bounded clauses, and the hull, collapse and counting cost the same on both. **QUALIFIED 2026-08-10 by `[LJ-1.11]` F4, which tested this argument on the owner's instruction.** **The DIRECTION holds on three independent legs**: D-26's own measurement, `[LJ-1.2]`'s probe, and now the literature, since SZ's Sigma-1 engine exists precisely because the S-step is syntax-free. **The MAGNITUDE does not.** The 470 to 610 figure covers only the six STRUCTURAL clauses on the J side, and `[L3.32-T263]` records the sixteen op-clauses as unmeasured, so this row previously overstated the price as covering the story whole. **Before `[LJ-2.5]` rules, strengthen it**: run the queued `[L3.32-T261]`-class probe and price one bounded op-clause times sixteen. Until then the asymmetry is a direction with an unpriced magnitude, and `[LJ-2.5]` should be told exactly that. **This is evidence for `[LJ-2.5]` to weigh, and nothing here re-opens the ruling early.** **WHAT THIS DOES NOT LICENSE.** Phases 1 and 2 are unchanged and are dispatched normally; a return may not re-table the ENDPOINT, which is ruled; and nobody re-opens the architecture question outside `[LJ-2.5]` on an argument rather than a measurement. Absorbs DD3. |
| DD4 | **MAXIMUM REUSE is the architecture's objective, and it is the same rule as WRITE IT GENERIC.** | **Ruled 2026-08-09 by the owner, as the route's CORE constraint, which is architectural and not arithmetic.** Follow the textbooks to the best route and architecture, and maximize the code the two proofs share. **The total is not to be pursued by splitting, re-bucketing, or any move that lowers reuse.** **THIS ROW HAS NO HARD METRIC, and that is the owner's decision, not an omission** (ruled 2026-08-09, when a sufficiency audit proposed a reuse checker). A shared-line count would be gamed the moment it gated anything: code can be moved into a shared module without either proof needing it there, and the number would rise while the architecture got worse. **So there is no threshold and no pass-or-fail, and there never will be.** **BUT IT DOES CARRY A REPORT, amended 2026-08-09 after `[LJ-0.3]` drew the distinction the first ruling missed.** Refusing the GATE is right; refusing the MEASUREMENT is one step too far, because a report cannot be gamed when nothing passes or fails on it, and the machinery already existed in `scripts/ledger.py`'s import closures. **`ledger.py --reuse` prints what the two proofs actually share**, in masters and in lines, with each closure's own total and the shared share of their union. It exits 0 whatever it finds, it is NOT in `make check`, and it refuses to compute while no GCH endpoint exists rather than inventing a number. **The report is evidence for a human, never a score to maximize:** a high share won by fattening the shared core is precisely the failure the no-gate ruling protects against, so it is read beside `[LJ-2.3]`'s reuse map and never instead of it. **THE COMPENSATING MECHANISM IS REPETITION, and it is the enforcement point this row names:** the principle is stated in EVERY brief this project sends, whatever the task kind, and every return says what it did about it. A rule with no meter has to be said out loud every time or it decays into a preference. **IT IS THE SAME RULE AS "WRITE IT GENERIC", absorbed here 2026-08-09 from archived D29 so it has one home.** Provenance: `dev/LESSONS.md` **P-h** is the measured law, twice on 2026-08-02, a walk taking set arguments as FUNCTION parameters ran past four minutes cold and never finished, and the same walk as a MODULE parameter with the arguments abstract dropped the file to about 13 s, then 30 s at the second site. Content written structure-generic at full strength makes every re-instantiation nearly free. **This campaign has paid for the converse twice:** a satisfaction cone whose 134 readings were written fixed to one carrier, and `[L3.32-T70]` mirroring at the class carrier what `[L3.32-T69]` had just written at the set carrier. Sharing between the two proofs is what generic writing BUYS; they are one discipline seen from two ends. **THE THREE MOMENTS, from D29, unchanged:** (1) a RECON brief asks out loud whether the content can be written once at a generic carrier and instantiated, and the report answers with a price for BOTH shapes, so a recon that returns only the fixed shape has not finished; (2) a BUILD brief states generic or fixed and why, and the default is generic; (3) the orchestrator asks it of the ROUTE's shape before any brief exists, because the cheapest generic decision is made before two chapters exist to unify. **THE ATTITUDE CLAUSE, the owner's own emphasis: keep a level head about the up-front cost.** Generic is more expensive on the first instance and cheaper from the second, so a stop-line is the standing temptation to write fixed and apologise later. **A stop-line is NEVER a reason to write fixed:** say so and stop for a re-price, rather than silently delivering the fixed shape inside the cap. **THE ONE MEASURED EXCEPTION is narrow and named**, `dev/LESSONS.md` P-r: a fold over a clause list costs about 3x the hand-written conjunction when its result type must be UNFOLDED by every consumer. That shape, and only that shape, is written out. **Enforcement:** the standing brief clause in `dev/ORCHESTRATION.md` section 3, which fires on every task kind; the route-planning clause in section 5; and the return audit in section 6, which rejects a build that chose fixed without saying so. Absorbs D29. |
| DD5 | **THE TWO QUANTITATIVE CONSTRAINTS are RELATIVE, and NEITHER BINDS until it is clear.** | **Ruled 2026-08-09 by the owner.** Both are taken at the DOUBLE-trophy endpoint and both are measured against the internalization route at ITS double-trophy endpoint. (1) LINES: this route's total must not exceed internalization's. (2) TIME: this route's total build time must not exceed internalization's. **A benchmark that is not clear is made clear first**, by the owner's own instruction, and today neither is. The line benchmark has one pass, `[T257]` at 25,485-28,258 naive, with a declared weak point worth 4,238-5,218, a fifth of the band, which can decide the constraint by itself. The time benchmark is half-built: the internalization AC wing measured 133.19 s over 17,492 lines on 2026-08-09, and its GCH half does not exist until `[LJ-1.8]`. **THE CALIBER**, absorbed from DD6: a size figure is the count of non-blank lines inside ` ```agda ` fences over git-tracked `*.lagda.md` under `src/`, the PRIMARY figure is the double-trophy endpoint, and `scripts/ledger.py --brief` is its only admissible source. The per-trophy split and the AC cap survive as DIAGNOSTICS. The deletion test survives UNCHANGED, because it is the structural test that keeps the accounting honest whichever figure binds. **THE WING NOW PROJECTS ABOVE ITS OWN CEILING, and this row records the gap rather than moving the ceiling.** `[LJ-1.11]` refuted `[LJ-1.10]`'s route C: the archived structural story's Def-step collapses to `⊤̇`, so it recognizes no level and its target is classically FALSE. The crossing therefore reverts to route A's 1.7 to 3.8k, or to an alternative nobody has priced, and `[LJ-1.1]`'s wing projection of 8.0 to 10.8k no longer holds. **DD5 measure 1 applies exactly as written: the a-priori ceiling STAYS at `[LJ-1.1]`'s figure, recorded before any build, and the excess is the finding.** A re-price may not raise a ceiling; that is the whole point of recording it early. `[LJ-1.12]` prices the surviving candidates, and `[LJ-1.13]` and `[LJ-1.14]` carry two more gaps the review found in delivered work. **None of it is funded yet: the owner's priority is the AC-side compression** (2026-08-10). **THE COMPRESSION PREREQUISITE IS 17,000, RE-RULED BY THE OWNER 2026-08-10**, after 16,000 was refuted and 16,400 was then tested to destruction. **Both earlier figures failed the same way and the sequence is worth keeping:** 16,000 came from `[L3.32-T205]`, which found it an unprobed survey optimum; 16,400 rested on measurement only for the DELETION class, which block A banked in full at minus 240. Five of eight blocks were then measured and FOUR refused, B at plus 24, E at plus 19, G at plus 49, and C at minus 59 by gutting two chapters. `[LJ-0.8]` then scanned for the remainder and found the mass ABSENT rather than mispriced. **The one systematic error behind all four refusals:** a kit costs 31 to 111 lines and its sites save less, because every survey priced the savings and never the kit. **17,000 is therefore the first target set from measurement rather than from a survey**, and the ratio cost falls with it, from plus 5.3 percent at 16,400 to plus 1.6 percent, which barely moves DD24's bar. **MET 2026-08-10 and the prerequisite is DISCHARGED.** At 16,897 on DD26's caliber, 103 under, or at 16,995 and five under on the caliber the target was set with; both are met and the 98-line difference is the two catalogs coming out, not a line of mathematics moving. Nine blocks ran and eight bands were tested. What landed was DELETION (A minus 240, the prose-freed names minus 59, the citation re-test minus 34) and exactly ONE kit: `[LJ-0.4n]` at minus 104, which took ONE parameter where its refused predecessor `[LJ-0.4f]` took eleven. That kit also made the tree FASTER by 0.53 s, so it is the only compression here that improved the ratio instead of trading against it. `dev/LESSONS.md` D-28 records the law and C-30 the gate list. **The seconds half is NOT discharged by that number:** `[LJ-0.5]` re-measures the DD24 baseline cold, because the old figure was taken over 17,271 lines and both terms of the ratio have moved (P-q). The owner first set 16,000 as a prerequisite to phase 1. `[LJ-0.4]` refuted it, and the refutation was already on the record: `[L3.32-T205]` asked where the 16,000 floor came from and answered UNSUPPORTED, a survey's optimistic end never probed; `[L3.32-T208]` then MEASURED the seven levers at minus 620 to minus 860 against the survey's minus 755 to minus 1,486. The honest floor is 16.3k to 16.6k. **The shared-base foundation kit does not close the gap and moves the wrong way**, measured at plus 13 to plus 15 net, so it is judged on readability alone. The owner set the target at about 16.4k and ruled the phase proceeds. **The blocks land regardless of the total**, because `[LJ-0.4]`'s N1 to N4 and levers (c) to (f) are the DD4 move: they replace repeated fixed content with one generic frame, and the GCH wing's twelve clauses instantiate the same frames. What they make cheaper later outweighs the lines they remove today. **THE BENCHMARK IS SELF-SET, AND THAT IS A HOLE THIS ROW NAMES RATHER THAN CLOSES.** Found by `[LJ-0.3]` 2026-08-09 and not previously stated anywhere. **Phase 1 builds the internalization GCH wing, and `[LJ-2.1]` measures THAT WING to set the benchmark the two-tower route must then beat.** So this project writes its own examination paper. A long or wasteful wing sets a high benchmark, which the two-tower route then clears while being worse in absolute terms, and every threshold here would report a pass. **DD24 guards the wing's RATIO and nothing guards its TOTAL**, which is deliberate, because the wing exists to measure what GCH costs and a cap would make it report the cap. **DD24 IS NOT A DEFENCE HERE, and a first version of this row wrongly said it was.** `scripts/check-ratio.py` fails only when the aggregate is ABOVE the bar. Padding with cheap lines LOWERS seconds per line, so a padded wing passes DD24 more easily, not less. The ratio guards the wing's content CLASS and says nothing whatever about its SIZE, which is exactly the quantity that sets the line benchmark. **THREE MEASURES, and the first is the one that removes the incentive.** **(1) THE A-PRIORI CEILING.** `[LJ-1.1]` owes one best-effort projection with its basis, recorded BEFORE anything is built and before anyone could gain from inflating it. **The line benchmark is then the SMALLER of that projection and the measurement.** Building fat cannot raise the bar; building tight still lowers it. **(2) THE BUILDERS ARE NOT TOLD they are setting a bar.** A phase-1 build brief says write this as the deliverable, as tight as if it shipped, and does NOT say the result becomes the number phase 3 must beat. Naming an incentive creates it. **(3) `[LJ-1.9]` REPORTS NET REMOVABLE LINES**, from an independent reader asking what did not need to be there, and `[LJ-2.1]` records measured, projected and removable side by side. **The owner's judgment is the backstop, not the primary guard:** `[LJ-2.2]` does not flip the flags until it is on the record. A benchmark nobody questioned is not a measurement, it is a number the project chose for itself. **ENFORCEMENT, per measure, and stated as it really is.** Measure 1 is MECHANICAL: `dev/ledger.toml` carries `lines_apriori`, and `ledger.py --check` refuses a binding line benchmark that has no a-priori projection, or one larger than it. The gate is silent while `lines_state` reads unbound, so it costs nothing through phase 1 and fires on the day the number starts to matter. Measure 3 is HALF mechanical: `lines_removable` has a field, so the figure has a home and its absence is visible, but nothing checks that the reader was independent. **Measure 2 is REVIEW ONLY and says so**: nothing can read a brief, so the clause in `dev/ORCHESTRATION.md` section 3 and the return audit are all there is. A row that claimed a checker it does not have would be worse than this one. |
| DD8 | Every block is gated before it is funded, and an estimate is ONE best-effort number | Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work. A green gate narrows the band and lowers its top. **A build brief that cannot name its widest unmeasured term, and the probe that measures it, is not ready to send.** A probe IS committed, in `agents/tasks/<TASK>/` beside its brief and its report, and never under `src/` (`dev/LESSONS.md` D-1). **THE TWO-CALIBER RULE IS REVOKED** (owner, 2026-08-09, retiring DD7). Lines are no longer a hard constraint in their own right, so a projection is stated ONCE, as a best-effort figure, with its basis named: probe, delivered comparable, or survey. **Say which**, because the basis is what a reader needs and the second decimal never was. An overage is still recorded plainly and worked down where real compression exists. |
| DD9 | Classical boundary, and generated proof | No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter; the whole tree is `--safe`. The archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree. A materially worse performance projection escalates to the owner. **GENERATED PROOF**, absorbed from DD10: a macro or reflection layer is admissible only where it is cheaper to READ than what it replaces, never merely cheaper to write, and `dev/STYLE-agda.md` names the forbidden constructs that `lint-agda.py` enforces. |
| DD11 | Code and prose craft | **NAMING**: a name says what the thing IS, not how it was built; an implicit nobody can infer is dissolved; a name with zero or one consumer is inlined. **PROSE**: no em dash in any language, CJK full-width sentence punctuation with half-width parentheses and `「」` quotes, English only inside ` ```agda ` fences, one master `.lagda.md` per module with the `<!--en--> <!--zh--> <!--ja-->` marker grammar. `scripts/lint-prose.py` and `weave-i18n.py` enforce most of this and `dev/STYLE-i18n.md` is the canonical statement. Absorbs DD10's craft half. |
| DD13 | Retirement is planned from the rewrite side, sunk cost decides nothing, and nothing is deleted | A consumer does not prove that a chapter must stay. **First price the ideal form of the content, written fresh today. Then compare.** "We already paid for it" never decides the question, in either direction, and DD2 is itself an instance: the route changed after a year of work. DD4 now asks the same question of every existing chapter, since content that cannot be shared may be cheaper rewritten than adapted. **ARCHIVE, NEVER DELETE**, absorbed from DD14: retired code goes to `archive/` at the repository root, outside `src/`, so every gate is blind to it by structure; archived files are frozen and nothing imports across the boundary; `dev/ARCHIVE.md` records what each module is, why it left, where it was last green, what it did right from measurement rather than praise, and what would make it worth a second look. This also governs `archive/dev/DECISIONS-archived.md`, `archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`. Absorbs DD12 and DD14. |
| DD15 | Measurement discipline: re-measure at every return, and never in the foreground | The ledger is re-measured at every return that could move it, and no standing figure is ever quoted from a paragraph. **A full cold typecheck runs in the BACKGROUND, never in the foreground**, absorbed from DD16: it costs minutes to tens of minutes and must not block a session. DD5's time constraint makes the measurement more load-bearing, not less, so the protocol is fixed: interface cache moved aside, single process, quiet machine, `/usr/bin/time -p`, and the figure recorded with its protocol beside it. Absorbs DD16. |
| DD17 | **The standing dispatch order: slots stay full until BOTH trophies are proved inside both constraints, and every dispatch is codex unless a named exception applies** | Amended 2026-08-09 from an AC-only terminus. An idle agent slot is a defect: a slot stays empty only when a real block stops every remaining task, and an audit is not a reason to leave one idle. **THE TIER, restored 2026-08-09 and REPLACED BY A SWITCH 2026-08-13 (owner's ruling).** The head is no longer written here, because a table restated in a second file drifts and DD19 forbids a rule that is canonical twice. **`scripts/dispatch_policy.py` is the ONE home**: it holds both versions of this rule, the head for each case, the date the current version was set, its reason and its revert condition, and `python3 scripts/dispatch_policy.py` prints all of it. **TWO VERSIONS, exactly one in force.** The **normal** version leads with pi and reviews with in-harness Opus 5; **its default is pi and NOT codex, which is a real change to this row rather than a restatement**, since `[LJ-1.126]` made pi viable on 2026-08-13 by landing streaming and resume. The **override** version leads with in-harness Opus 5 and reviews with pi; **it is TEMPORARY and its reason is QUOTA, never quality**, and the owner cancels it by word. **THE INVARIANT UNDER BOTH: the critic is never the same head as the author**, which is why the two tables swap the default row and the adversarial row. Enforcement is the brief header, which names the head AND the version it was chosen under, and `scripts/check-dispatch-policy.py` reads every brief against the switch. **The switch cannot force the choice and this row does not pretend otherwise:** an in-harness dispatch never passes through `.claude/skills/codex-dispatch/dispatch.py`, so the switch drives that dispatcher's default harness, the checker and the inspection command, and makes a wrong head DETECTABLE rather than impossible. **If the sentence justifying another head will not write, take the head the table gives.** **THE EMERGENCY BREAKTHROUGH TIER.** When a codex return does NOT do its task well AND the point is a critical breakthrough, the orchestrator may re-dispatch to Fable 5 at maximum effort without asking. BOTH conditions bind and the second is the scarce one: a critical breakthrough is a point where the loop cannot advance, so a gate whose verdict blocks the next funded build, a wall no measured cure passes, or a refutation that would re-price the route. Ordinary slowness or a task worth redoing at the same tier is NOT one. **A stop, a refutation and a RED are GOOD returns and never a trigger**; this campaign's most valuable results came back as REDs. Each use names its trigger in the brief, records the escalation in the task index row, and reports what the higher tier found that the first return missed, including when the answer is nothing. Operational form: `dev/ORCHESTRATION.md` sections 1 and 2. |
| DD18 | **THE ARCHIVE AND LITERATURE SURVEYS are sections of the brief and of the return, not a hope.** | **Ruled 2026-08-09 by the owner as a MECHANISM.** Before a brief is sent it carries an **ARCHIVE** section listing what may bear on the task in each archive: `archive/` for retired code, with `archive/src/2026-08-09-rud-route/` holding the retired route's 72 files and `dev/ARCHIVE.md` describing modules retired before it; `archive/dev/TASKS-archived.md` for what each of 265 earlier dispatches FOUND; `archive/dev/JOURNAL-archived.md` for WHY; and `archive/dev/DECISIONS-archived.md` for the rulings that route ran on. **A return carries an ARCHIVE USED section** naming what it actually read and what it took from each item, at `file:line`. "I looked at the archive" is not a return, and a brief whose archive section is empty must say why. `dev/LESSONS.md` is NOT archived and still binds, cited the usual way through `scripts/rules.py`. **A port is priced against a fresh write, never assumed** (DD13), and P-l holds: a measured cure does not transfer by analogy. **ENFORCEMENT IS REVIEW ONLY.** Nothing mechanical reads a brief, so the orchestrator refuses a return whose ARCHIVE USED section is missing. A row that claimed a checker it does not have would be worse than this one. **THE LITERATURE HALF, added 2026-08-10 by the owner, and it is the same mechanism for a second corpus.** `dev/literature/` holds the digested mathematics: `digest.md` for the orthodox route, `j-hierarchy.md` for condensation and the stratification, `fine-structure.md`, `rudimentary-functions.md`, `devlin-errata.md` for the known errors in the primary text, `primary-sources.md` and `BIBLIOGRAPHY.md` for what was fetched and what it was consumed by, and `formalizations-landscape.md` for prior art. **A brief that dispatches mathematics carries a LITERATURE section naming what may bear on it, and a return carries a LITERATURE USED section** saying what it read, what it took, and, for anything it did not use, WHY NOT. **The why-not is the half that earns its keep:** a note saying a source is OCR-degraded, or covers the wrong chapter, or was superseded, is worth as much as one that supplies a lemma, and it stops the next agent paying the same reading twice. **WHY THIS WAS ADDED.** Every phase-1 brief so far cited the archive and none cited the literature, while `digest.md:513-518` had recorded a sourced GCH-in-L derivation, Devlin II.5 with Theorem 5.6, since 2026-08-03. The corpus was there and nobody was sent to it. **ENFORCEMENT, AND THE TWO HALVES ARE NOW IDENTICAL** (owner, 2026-08-10). `dispatch.py` REFUSES a brief that carries no ARCHIVE section, and refuses one that carries no LITERATURE section, **on every brief regardless of kind**. Each is satisfied by one honest line naming the corpus and saying nothing in it bears on the task, which is cheap to write and still forces the author to look. **WHY BOTH, when the archive half had never lapsed.** Measured 2026-08-10: twelve of twelve briefs and thirteen of thirteen returns carried their archive sections with no gate at all. That record argued for leaving it to review, and the owner ruled for alignment instead. The record makes the gate cheap rather than redundant: a rule already obeyed costs nothing to check, and two rules of the same shape enforced two different ways is a thing a reader has to explain to themselves. **WHY EVERY BRIEF AND NOT ONLY A BUILD, which is the correction that matters.** The literature half was first scoped to master-writing briefs, reasoning that a recon needs no mathematics. **That was wrong, and the test is the case that prompted the rule:** `[LJ-1.1]` is a recon, it wrote only a report, and it PLANNED THE ENTIRE GCH WING without citing a line of `dev/literature/`. The build-only scope would have exempted exactly the brief the rule exists for. **THIS BINDS THE CODEX PATH ONLY**, and the limit is stated rather than hidden. An in-harness dispatch does not pass through `dispatch.py`, and `[LJ-1.11]` proved the gap by going out short two mandatory rules. There the orchestrator applies DD18 by hand, and a return that arrives without both USED sections is sent back. |
| DD19 | Governance: one home per rule, goals registered before they start, and two guarded surfaces | **ONE HOME.** Every rule lives in exactly one canonical place, chosen by who enforces it, and a rule that no machine enforces must NAME its enforcement point: a gate, a brief section, a review step. A rule with no enforcement point is a wish. Nothing is canonical twice. **GOALS**, absorbed from DD18's old content: a ruling is a PLAN row and an episode is a JOURNAL entry; every dispatch is registered in the task index BEFORE it starts, one row per code, 200 characters, enforced by `scripts/check-task-index.py`; a ruling may be revised, and a revision is recorded rather than a row being rewritten. **TWO GUARDED SURFACES.** `AGENTS.md` takes no edit without the owner's ruling on the diff and a dated `AGENTS-diff-approved:` trailer, which `scripts/check-agents-guard.py` refuses to go without. `dev/glossary.toml` takes no entry chosen by an agent: a term it lacks goes through the two-agent pipeline, and the pipeline names its tiers: **arm 1 is codex**, which searches the literature for each rendering's provenance and marks every guess where the literature is silent, and **arm 2 is opus, adversarial**, which verifies the sources and attacks the collisions and PASSes or FAILs per term. A PASS lands the entry without the owner's review and the landing commit cites both; a FAIL, or a genuine fork, escalates that term and only that term. The owner's veto always stands. Absorbs the old DD18, DD20 and DD21. |
| DD22 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out; everything else inherits AGPL-3.0. Three buckets, declared centrally, with no in-file `SPDX-*` headers. `reuse lint` enforces it. |
| DD23 | **NO MATHEMATICAL PROSE until both trophies land. The prose phase comes AFTER.** | **Ruled 2026-08-09 by the owner.** Until `L ⊨ AC` and `L ⊨ GCH` are both proved on the two-tower bridge inside DD5's constraints, write NO mathematical prose: no chapter narrative, no trilingual exposition of the mathematics, no reader-facing explanation of a construction. Code and its own comments only. **The prose phase opens when the double trophy lands, and not before.** This is not a licence to write badly: DD11 still binds, and so does ASD-STE100 for every brief, report and message, which is working text rather than mathematical prose. **The reason is DD4.** Prose written against an architecture that reuse has not settled is prose written twice, and the retired route paid that bill. **What this does NOT suspend**: the marker grammar where prose already exists, `docs/`, and `dev/JOURNAL.md`, which is a record and not exposition. |
| DD24 | **THE QUALITY BAR IS SECONDS PER LINE, and on the internalization GCH wing it is the ONLY threshold.** | **Ruled 2026-08-09 by the owner.** Code written for `L ⊨ GCH` on the internalization route must reach the SAME quality as that route's delivered `L ⊨ AC` wing, and quality here means one measured thing: **the ratio of cold build seconds to in-fence lines.** The AC wing measured **0.007614 s per line** on 2026-08-09, 133.19 s over 17,492 lines, so the bar is a number rather than a judgment. **Why a RATIO**: a total can be met by writing less of a worse thing and a ratio cannot, so it says the content must be the same KIND of content. `dev/LESSONS.md` P-m measures why that matters: parameterized work runs about 0.010 to 0.013 s per line and instantiation about 0.22 to 0.297, a twentyfold spread no line count reveals. **THE WING CARRIES NO OTHER THRESHOLD**, absorbed from DD25: no line cap and no seconds cap, and the omission is deliberate. That wing exists to MEASURE what GCH costs, because the measurement sets DD5's benchmarks; a cap would make the measurement report the cap instead of the cost, and this project already paid for that when a projection was re-quoted as a measurement for nine dispatches. **The bar also governs DD5's own benchmark and the two-tower route**: a wing built at instantiation rates would set a seconds benchmark so loose that the new route could clear it while being worse, and a benchmark that is easy to beat measures nothing. **THE BASELINE BELONGS TO ONE TREE, and both tools refuse it on another** (owner, 2026-08-09). A seconds-per-line figure is not a constant: `[LJ-0.4]` compresses the tree by roughly 1,500 lines and moves BOTH terms, neither predictably, because a line lever is not a seconds lever (P-q). So `dev/ledger.toml` records `ac_baseline_lines` beside the figure, and `ledger.py --check` and `check-ratio.py` both REFUSE when standing has drifted from it, naming `[LJ-0.5]` as the re-measurement. Without that guard a stale bar reports exactly like a live one, which is C-28. **Enforced staged by `scripts/check-ratio.py`**, from the first GCH module onward, because a bar readable only at the end is read too late to act on. Read P-m, P-n, P-q and P-t before optimizing: P-q measured 315 lines removed buying 11.8 seconds, so a line lever is not a seconds lever, and P-t found a twentyeightfold spread inside ONE file, so the carrier never certifies the class. The formula does. |
| DD25 | **A NEGATIVE CODEX RETURN IS ADVERSARIALLY REVIEWED BY OPUS 5 AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ TOGETHER.** | **Ruled 2026-08-10 by the owner.** When a codex return's headline verdict is negative, the orchestrator dispatches an in-harness Opus 5 subagent at maximum effort to attack that return, before auditing it and before acting on it. **THE TRIGGER, stated so it cannot be argued away:** a refusal, a NO-GO, a RED gate, a stop taken as the deliverable, a refutation of the brief's premise, or a landed result that misses its band floor. If the verdict line would disappoint the person who wrote the brief, it is negative. **WHAT THE REVIEWER ATTACKS IS THE NEGATIVE, NOT THE TASK.** It is not a re-run and not a second attempt. The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed. **A review that AGREES is a real result** and costs one dispatch to buy confidence in a number the campaign is about to build on. **THEN BOTH ARE READ TOGETHER.** The orchestrator audits the codex return and the Opus review as one pair, and reports both to the owner, including where they disagree. Neither is accepted alone. **WHY, from measurement rather than caution:** four blocks refused on measurement in `[LJ-0.4]` and the orchestrator accepted all four. `[LJ-0.8]`, an adversarial review, then found a propagated sign error standing in five places and a refusal blamed on the wrong party. A negative return closes a line of work, so a wrong one is the most expensive kind of return there is, and it is the kind nobody re-checks. **THIS AMENDS DD17's TIER RULE.** DD17 requires the owner to name Opus per task, because a past override never carries forward. DD25 IS that naming, standing, for this one class. **IT DOES NOT CONTRADICT DD17's "a RED is never a trigger":** that clause forbids re-dispatching the TASK on a RED, and it still binds. DD25 dispatches a REVIEW of the RED, which is the opposite move. **THE HAND-APPLIED RULES.** An in-harness dispatch does not pass through `.claude/skills/codex-dispatch/dispatch.py`, so the DD4 and DD18 refusals do not fire; `[LJ-1.11]` went out short two mandatory rules through exactly this gap. The orchestrator writes DD4, ARCHIVE and LITERATURE into the review prompt by hand. **Enforcement:** the audit, and the PLAN section 11 row for a negative return must name its review's code. **No machine enforces the trigger today**, because reading a verdict as negative is a judgment; the honest enforcement is that the row is empty and visible. Operational form: `dev/ORCHESTRATION.md` section 1. |

| DD26 | **THE CATALOGS ARE NOT COUNTED. `src/Everything.lagda.md` and `src/Landmarks.lagda.md` are excluded from EVERY size figure, past and future.** | **Ruled 2026-08-10 by the owner.** Both are indexes rather than mathematics: one is the import catalog with its per-chapter prose, the other states the two trophies and imports what proves them. **The reason is DRIFT, and it is the owner's:** a catalog GROWS WITH THE PROJECT, so a threshold measured against a total containing one drifts further from the mathematics it is meant to bound, and drifts in the direction that flatters the tree. **It also collapsed a real discrepancy.** The AC side had TWO numbers under one name: the bucket, standing minus the declared wing, at 16,995; and DD24's own tree, the cold-build cone of `Landmarks`, at 16,916. The 79-line gap was exactly `Everything`, which no build of `Landmarks` compiles. Excluding both catalogs makes them ONE number, **16,897**, and a figure with one meaning cannot be quoted in the wrong place. **RETROSPECTIVE, by the owner's word:** the ruling re-bases figures already recorded, so `[LJ-0.4]`'s prerequisite is met at 16,897 rather than 16,995 and DD24's baseline is 0.007913 over 16,897 rather than 0.007904 over 16,916. **DD8's caliber is untouched:** non-blank lines inside ` ```agda ` fences, still. This ruling says which FILES that caliber runs over. **Enforced by `scripts/ledger.py`'s `UNCOUNTED` and `countable_masters()`**, which every size site now calls, and pinned by `scripts/tests/test_ratio_baseline.py` and `test_deletion_test.py`, whose assertion that Everything IS counted was flipped in the same commit. |
| DD27 | **THE HULL IS INDEXED BY A META TERM ALGEBRA, not by object-language formulas.** | **Ruled 2026-08-10 by the owner**, on a measured fork. `[LJ-1.3]` built the hull as `sett (Σ[ φ ∈ Formula ⟪X⟫ 1 ] Witnessed-small φ)`, so every membership certificate is an X-formula. That choice, not the mathematics, is what blocked condensation: the criterion at HULL parameters needs the order named inside the model, `relL α` sits at rank at least α while `Lset α` holds only rank below α, and the index type leaves no room to widen, because a hull-expressible order yields a hull-formula and the index demands an X-formula. **THE PRICES, and this is why it is a ruling and not a preference.** Keeping the index type costs **1.0 to 3.0k lines and 220 to 890 s, 17 to 23x DD24's bar** (`[LJ-1.16]`). Moving costs about **270 lines under 6 s**: 116 MEASURED by `[LJ-1.18]`'s probe at 0.0103 s/line, about 30 named follow-on, and about 120 for the counting priced by `[LJ-1.22]`. **THE COUNTING OBJECTION DIED ON MEASUREMENT.** `Code` needs the SAME cardinal law as `Formula K 1`, pairing at β, not a stronger one, so the fork neither cures nor worsens `[LJ-1.17]`'s square-law wall; the union over the naturals is internal to the constructor, since `wit` carries its arity. **DD4 IS THE REASON IT IS RIGHT AND NOT MERELY CHEAP.** The obstruction hits BOTH towers, so the blocked shape buys the definable well-order twice; the term algebra needs only a META well-order both towers already have, so it is template content bought once. `[LJ-0.7]` found the definable well-order appears on the whole GCH chain at exactly ONE place, Devlin's own proof of the hull. **WHAT IT REVISES:** `[LJ-1.3]`'s delivered hull, its index, and the statements over that index; it also RETIRES `[LJ-1.3]`'s booked residue piece one, 30 to 80 lines. **TWO CAVEATS STAND AND ARE NOT BURIED:** the 120-line and 2-second counting figures are ESTIMATES from same-class module rates, not measurements, and the mutual `enc`/`encs` termination is unchecked at that site, though the probe's `val`/`vals` passed the analogous shape. |
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

**THE TWO-CALIBER DISCIPLINE IS REVOKED** (owner, 2026-08-09, retiring DD7).
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

**TWO PIECES OF EVIDENCE THE RULING IS OWED, and the record on one of them
was wrong until `[LJ-1.149]` read it.** `[L3.32-T261]`'s probe on the S-tower
crossing **RAN**, on 2026-08-09: exit 0, one cold run of 1.50 s over 124 fresh
lines, at `agents/tasks/archive/L3-32-T261/ProbeT261.agda`, and it is the probe
`[T260]` specified and could not run. It measured that the GCH wing pays
neither `carried-sequence` nor `blockpowlim-instance`, the 4,238 to 5,218 that
`[L3.32-T257]` declared as its own weak point. **This paragraph and three
`dev/ledger.toml` notes said it never ran, from 2026-08-09 to 2026-08-13**,
because `[LJ-0.3]`'s closeout read the brief header rather than the report.
**WHAT IS STILL OWED IS DIFFERENT AND SMALLER:** one bounded op-clause priced
and multiplied by sixteen, which `[L3.32-T263]` left unmeasured, and a second
independent pass on `[T257]`'s line comparison, which is still one agent and
one pass. **`[LJ-2.0]` owns both** and gates `[LJ-2.5]`; `[LJ-2.3]` reads them
into the reuse map.

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
WHAT IT USED.** Ruled by the owner 2026-08-09 as a mechanism rather than an
encouragement. A brief carries an ARCHIVE section listing the archived code,
the archived task rows and the lessons that may bear on the task; a report
carries an ARCHIVE USED section naming what it actually read and what it took
from each. The retired route cost a year of measurement and the whole of it
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
| LJ-1.2 | Gate: probe the widest unmeasured term LJ-1.1 names | NO-GO, re-prices the wing | Step clause has no Delta-0 witness at ANY carrier. Crossing 5.0-5.1k, or 1.0-1.7k by the cone fork |
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
| LJ-1.154 | Carve the identity graph by separation, not by replacement | DISPATCHED | Separation is 2,500 to 1 cheaper. If it builds as well as composes, A5's 254 s was never necessary |
| LJ-1.155 | Is there a second dominant term, or is the wing intrinsically this expensive | DISPATCHED | LJ-1.145 found one and nobody looked for a second. This decides whether DD24 must be ruled |
| DD25-GAP | Orchestrator audit: DD25 was not followed | SEVEN TRIGGERS MISSED | LJ-1.55, 1.56, 1.59, 1.60, 1.61, 1.65, 1.66 all triggered and none was reviewed. I invented a MEASURED-class exemption DD25 does not grant |
| LJ-1.8 | Build: assemble L models GCH | planned | The measuring trophy. Needs LJ-1.7 |
| LJ-1.9 | Quality audit: the wing's ratio AND its net removable lines | planned | DD24's ratio, cold. PLUS an independent read of what did not need to be there: DD5 measure 3. Read P-m, P-q, P-t |
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
