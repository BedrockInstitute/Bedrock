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

## 0. Where the work stands (2026-08-09)

**REWRITTEN 2026-08-09 for the route change.** The text this replaces described
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
in-fence lines. The delivered internalization AC wing measures **0.007614
s/line**, from 133.19 s cold over 17,492 lines, and `scripts/check-ratio.py`
holds the GCH wing to it within a declared tolerance. A ratio is the right
single bar because a total can be met by writing less of a worse thing and a
ratio cannot: LESSONS P-m measured a twentyfold spread between content classes
that no line count reveals, and P-t measured a twentyeightfold spread inside
one file.

**What is delivered and standing.** `src/` is the internalization tree,
restored to match `main`: **75 masters, 17,492 non-blank in-fence lines,
133.19 s cold, exit 0**. It proves `L ⊨ ZF` and `L ⊨ ZFC` on the Def tower. The
tree is `--safe` and postulate-free, with LEM a module parameter rather than a
postulate (DD9). Quote `python3 scripts/ledger.py --brief` for standing, never
a number found in a paragraph.

**What is in flight.** `[LJ-0.1]` returned 30 defects and its repair is under
way. `[LJ-0.2]`, the sufficiency audit, is live. Phase 1 (`[LJ-1.1]` to
`[LJ-1.9]`) then proves GCH on the internalization route with NO prose, to
measure what a GCH wing costs. Phase 2 sets the benchmarks. Phase 3 builds the
two towers and the bridge and lands both trophies.

**Mathematical prose is FROZEN until both trophies land** (DD23). This is not
the retired check-cost freeze, which is closed. It is narrower and simpler: the
code goes first, the prose phase opens after.

**FOUR ARCHIVES, and surveying them is a brief section rather than a hope**
(DD19). `archive/` holds retired code, with `archive/rud-route/` holding the 72
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
- Bedrock removes even that postulate by parameterization (D2), making the
  whole tree `--safe`.

## 2. Source material survey (pointer)

The port-era survey of the source repository and its measured cost anatomy moved to [dev/memos/source-material-survey.md](memos/source-material-survey.md) ([L3.32-T113]). Its measurements remain a calibration anchor for pricing (§6.2) and for the simplification history (archived §10). Read it when a recon prices a lever or quotes a source-scale figure; the live plan is §0 and the goal registry is §11.

## 3. Ratified decisions
**The `DD` series, rebuilt 2026-08-09 on the two-tower bridge ruling and CONSOLIDATED the same day.** The owner ruled that the whole `D` series be archived and the list rebuilt, keeping only what does not contradict the new route and what is useful to it. **The retired `D` series lives in `archive/dev/DECISIONS-archived.md`, unedited**, and `scripts/check-rule-ids.py` resolves `D` citations against it, so every old citation still means what it meant. **A number is never reused, in either series.**

**Consolidated and revoked codes.** The first cut ran to 25 rows and the owner ruled it down under 20 by merging like with like. **DD3** merged into DD2, **DD6** into DD5, **DD10** into DD9 and DD11, **DD12** and **DD14** into DD13, **DD16** into DD15, **DD20** and **DD21** into DD19, **DD25** into DD24, and the old DD18 content into DD19, freeing DD18 for the archive-survey mechanism. **DD7 is REVOKED outright**, not merged: lines are no longer a hard constraint in their own right, so the two-caliber rule it carried is gone and a projection is now ONE best-effort figure with its basis named, which lives in DD8. These codes still resolve, so a commit message or brief that cites one is not broken. **No pure pointers.** Every row states its own minimum content; a rule you must open another file to read is a rule with a broken home, which DD19 forbids.

| # | Decision | Ruling |
|---|----------|--------|
| DD1 | The theorem, stated honestly | As in section 1: V=L ⊨ ZFC, relative consistency, relative to the host, and never an unqualified "Con(ZFC)". The endpoint is the SAME L satisfying GCH, stated internally, giving Con(ZF) → Con(ZFC + GCH) under the same relativization; "Con(GCH)" is likewise never claimed unqualified. |
| DD2 | **THE ENDPOINT IS RULED. THE ARCHITECTURE IS THE LEADING CANDIDATE, and it is ruled at `[LJ-2.5]` against measurement.** | **Ruled 2026-08-09 by the owner, and AMENDED the same day on `[LJ-0.3]`'s finding.** **WHAT IS RULED AND NOT REOPENABLE:** both trophies, `L ⊨ AC` and `L ⊨ GCH`, both stated in L, so no re-founding onto J is ordered; and where a bridge is built it delivers BOTH directions of the two-definition identification, never the one-way variant. **WHAT IS A CANDIDATE:** the two towers and the bridge, L plus J through rud. It is the leading architecture and the plan builds toward it. It is not yet the binding ruling. **WHY THE AMENDMENT.** The original row ruled the architecture on 2026-08-09, and `[LJ-0.3]` found the warrant self-contradictory: archived D26 held that a number alone may never put the route back on the table, and D39 changed the route on `[L3.32-T257]`'s figure, which `dev/ledger.toml` declares NOT YET CLEAR ENOUGH TO BIND the constraints that same figure set. **One pass by one agent cannot be too weak to set a threshold and strong enough to overturn a route.** The retrospective did NOT refute the architecture; it refuted the timing, and the owner adopted that. **SO THE RULING MOVES TO WHERE THE EVIDENCE IS**, `[LJ-2.5]`, after `[LJ-2.1]` measures the internalization double trophy, `[LJ-2.2]` writes both DD5 benchmarks in, and `[LJ-2.3]` delivers the reuse map that DD4's core constraint turns on. The candidate is confirmed, amended or replaced there, on measured evidence and not before. **A MEASUREMENT FOR `[LJ-2.5]`, recorded 2026-08-10 and NOT a re-opening.** `[LJ-1.2]` probed the Def tower's level-story certification and returned NO-GO: the step clause has no Delta-0 witness at ANY carrier, because the coded satisfaction leaves carry unbounded quantifiers. `[LJ-1.10]` traced that to **D-26 being paid**: a definable-power stage carries no generation data, so its level-hood must run through codes and satisfaction, and those leaves are unbounded. On the J tower the same story is structural with the Def-step collapsed to `⊤̇`, and its bounded clause layer is priced at 470 to 610 lines. **So the level-story certification is a few hundred lines on one tower and thousands on the other**, and that asymmetry is a fact about the architecture rather than about this wing. `[LJ-1.10]` states its own limits: the J tower is not free, its equivalence still needs fresh bounded clauses, and the hull, collapse and counting cost the same on both. **This is evidence for `[LJ-2.5]` to weigh, and nothing here re-opens the ruling early.** **WHAT THIS DOES NOT LICENSE.** Phases 1 and 2 are unchanged and are dispatched normally; a return may not re-table the ENDPOINT, which is ruled; and nobody re-opens the architecture question outside `[LJ-2.5]` on an argument rather than a measurement. Absorbs DD3. |
| DD4 | **MAXIMUM REUSE is the architecture's objective, and it is the same rule as WRITE IT GENERIC.** | **Ruled 2026-08-09 by the owner, as the route's CORE constraint, which is architectural and not arithmetic.** Follow the textbooks to the best route and architecture, and maximize the code the two proofs share. **The total is not to be pursued by splitting, re-bucketing, or any move that lowers reuse.** **THIS ROW HAS NO HARD METRIC, and that is the owner's decision, not an omission** (ruled 2026-08-09, when a sufficiency audit proposed a reuse checker). A shared-line count would be gamed the moment it gated anything: code can be moved into a shared module without either proof needing it there, and the number would rise while the architecture got worse. **So there is no threshold and no pass-or-fail, and there never will be.** **BUT IT DOES CARRY A REPORT, amended 2026-08-09 after `[LJ-0.3]` drew the distinction the first ruling missed.** Refusing the GATE is right; refusing the MEASUREMENT is one step too far, because a report cannot be gamed when nothing passes or fails on it, and the machinery already existed in `scripts/ledger.py`'s import closures. **`ledger.py --reuse` prints what the two proofs actually share**, in masters and in lines, with each closure's own total and the shared share of their union. It exits 0 whatever it finds, it is NOT in `make check`, and it refuses to compute while no GCH endpoint exists rather than inventing a number. **The report is evidence for a human, never a score to maximize:** a high share won by fattening the shared core is precisely the failure the no-gate ruling protects against, so it is read beside `[LJ-2.3]`'s reuse map and never instead of it. **THE COMPENSATING MECHANISM IS REPETITION, and it is the enforcement point this row names:** the principle is stated in EVERY brief this project sends, whatever the task kind, and every return says what it did about it. A rule with no meter has to be said out loud every time or it decays into a preference. **IT IS THE SAME RULE AS "WRITE IT GENERIC", absorbed here 2026-08-09 from archived D29 so it has one home.** Provenance: `dev/LESSONS.md` **P-h** is the measured law, twice on 2026-08-02, a walk taking set arguments as FUNCTION parameters ran past four minutes cold and never finished, and the same walk as a MODULE parameter with the arguments abstract dropped the file to about 13 s, then 30 s at the second site. Content written structure-generic at full strength makes every re-instantiation nearly free. **This campaign has paid for the converse twice:** a satisfaction cone whose 134 readings were written fixed to one carrier, and `[L3.32-T70]` mirroring at the class carrier what `[L3.32-T69]` had just written at the set carrier. Sharing between the two proofs is what generic writing BUYS; they are one discipline seen from two ends. **THE THREE MOMENTS, from D29, unchanged:** (1) a RECON brief asks out loud whether the content can be written once at a generic carrier and instantiated, and the report answers with a price for BOTH shapes, so a recon that returns only the fixed shape has not finished; (2) a BUILD brief states generic or fixed and why, and the default is generic; (3) the orchestrator asks it of the ROUTE's shape before any brief exists, because the cheapest generic decision is made before two chapters exist to unify. **THE ATTITUDE CLAUSE, the owner's own emphasis: keep a level head about the up-front cost.** Generic is more expensive on the first instance and cheaper from the second, so a stop-line is the standing temptation to write fixed and apologise later. **A stop-line is NEVER a reason to write fixed:** say so and stop for a re-price, rather than silently delivering the fixed shape inside the cap. **THE ONE MEASURED EXCEPTION is narrow and named**, `dev/LESSONS.md` P-r: a fold over a clause list costs about 3x the hand-written conjunction when its result type must be UNFOLDED by every consumer. That shape, and only that shape, is written out. **Enforcement:** the standing brief clause in `dev/ORCHESTRATION.md` section 3, which fires on every task kind; the route-planning clause in section 5; and the return audit in section 6, which rejects a build that chose fixed without saying so. Absorbs D29. |
| DD5 | **THE TWO QUANTITATIVE CONSTRAINTS are RELATIVE, and NEITHER BINDS until it is clear.** | **Ruled 2026-08-09 by the owner.** Both are taken at the DOUBLE-trophy endpoint and both are measured against the internalization route at ITS double-trophy endpoint. (1) LINES: this route's total must not exceed internalization's. (2) TIME: this route's total build time must not exceed internalization's. **A benchmark that is not clear is made clear first**, by the owner's own instruction, and today neither is. The line benchmark has one pass, `[T257]` at 25,485-28,258 naive, with a declared weak point worth 4,238-5,218, a fifth of the band, which can decide the constraint by itself. The time benchmark is half-built: the internalization AC wing measured 133.19 s over 17,492 lines on 2026-08-09, and its GCH half does not exist until `[LJ-1.8]`. **THE CALIBER**, absorbed from DD6: a size figure is the count of non-blank lines inside ` ```agda ` fences over git-tracked `*.lagda.md` under `src/`, the PRIMARY figure is the double-trophy endpoint, and `scripts/ledger.py --brief` is its only admissible source. The per-trophy split and the AC cap survive as DIAGNOSTICS. The deletion test survives UNCHANGED, because it is the structural test that keeps the accounting honest whichever figure binds. **THE COMPRESSION PREREQUISITE IS ~16.4k, NOT 16,000** (owner, 2026-08-10). The owner first set 16,000 as a prerequisite to phase 1. `[LJ-0.4]` refuted it, and the refutation was already on the record: `[L3.32-T205]` asked where the 16,000 floor came from and answered UNSUPPORTED, a survey's optimistic end never probed; `[L3.32-T208]` then MEASURED the seven levers at minus 620 to minus 860 against the survey's minus 755 to minus 1,486. The honest floor is 16.3k to 16.6k. **The shared-base foundation kit does not close the gap and moves the wrong way**, measured at plus 13 to plus 15 net, so it is judged on readability alone. The owner set the target at about 16.4k and ruled the phase proceeds. **The blocks land regardless of the total**, because `[LJ-0.4]`'s N1 to N4 and levers (c) to (f) are the DD4 move: they replace repeated fixed content with one generic frame, and the GCH wing's twelve clauses instantiate the same frames. What they make cheaper later outweighs the lines they remove today. **THE BENCHMARK IS SELF-SET, AND THAT IS A HOLE THIS ROW NAMES RATHER THAN CLOSES.** Found by `[LJ-0.3]` 2026-08-09 and not previously stated anywhere. **Phase 1 builds the internalization GCH wing, and `[LJ-2.1]` measures THAT WING to set the benchmark the two-tower route must then beat.** So this project writes its own examination paper. A long or wasteful wing sets a high benchmark, which the two-tower route then clears while being worse in absolute terms, and every threshold here would report a pass. **DD24 guards the wing's RATIO and nothing guards its TOTAL**, which is deliberate, because the wing exists to measure what GCH costs and a cap would make it report the cap. **DD24 IS NOT A DEFENCE HERE, and a first version of this row wrongly said it was.** `scripts/check-ratio.py` fails only when the aggregate is ABOVE the bar. Padding with cheap lines LOWERS seconds per line, so a padded wing passes DD24 more easily, not less. The ratio guards the wing's content CLASS and says nothing whatever about its SIZE, which is exactly the quantity that sets the line benchmark. **THREE MEASURES, and the first is the one that removes the incentive.** **(1) THE A-PRIORI CEILING.** `[LJ-1.1]` owes one best-effort projection with its basis, recorded BEFORE anything is built and before anyone could gain from inflating it. **The line benchmark is then the SMALLER of that projection and the measurement.** Building fat cannot raise the bar; building tight still lowers it. **(2) THE BUILDERS ARE NOT TOLD they are setting a bar.** A phase-1 build brief says write this as the deliverable, as tight as if it shipped, and does NOT say the result becomes the number phase 3 must beat. Naming an incentive creates it. **(3) `[LJ-1.9]` REPORTS NET REMOVABLE LINES**, from an independent reader asking what did not need to be there, and `[LJ-2.1]` records measured, projected and removable side by side. **The owner's judgment is the backstop, not the primary guard:** `[LJ-2.2]` does not flip the flags until it is on the record. A benchmark nobody questioned is not a measurement, it is a number the project chose for itself. **ENFORCEMENT, per measure, and stated as it really is.** Measure 1 is MECHANICAL: `dev/ledger.toml` carries `lines_apriori`, and `ledger.py --check` refuses a binding line benchmark that has no a-priori projection, or one larger than it. The gate is silent while `lines_state` reads unbound, so it costs nothing through phase 1 and fires on the day the number starts to matter. Measure 3 is HALF mechanical: `lines_removable` has a field, so the figure has a home and its absence is visible, but nothing checks that the reader was independent. **Measure 2 is REVIEW ONLY and says so**: nothing can read a brief, so the clause in `dev/ORCHESTRATION.md` section 3 and the return audit are all there is. A row that claimed a checker it does not have would be worse than this one. |
| DD8 | Every block is gated before it is funded, and an estimate is ONE best-effort number | Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work. A green gate narrows the band and lowers its top. **A build brief that cannot name its widest unmeasured term, and the probe that measures it, is not ready to send.** Nobody commits a probe. **THE TWO-CALIBER RULE IS REVOKED** (owner, 2026-08-09, retiring DD7). Lines are no longer a hard constraint in their own right, so a projection is stated ONCE, as a best-effort figure, with its basis named: probe, delivered comparable, or survey. **Say which**, because the basis is what a reader needs and the second decimal never was. An overage is still recorded plainly and worked down where real compression exists. |
| DD9 | Classical boundary, and generated proof | No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter; the whole tree is `--safe`. The archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree. A materially worse performance projection escalates to the owner. **GENERATED PROOF**, absorbed from DD10: a macro or reflection layer is admissible only where it is cheaper to READ than what it replaces, never merely cheaper to write, and `dev/STYLE-agda.md` names the forbidden constructs that `lint-agda.py` enforces. |
| DD11 | Code and prose craft | **NAMING**: a name says what the thing IS, not how it was built; an implicit nobody can infer is dissolved; a name with zero or one consumer is inlined. **PROSE**: no em dash in any language, CJK full-width sentence punctuation with half-width parentheses and `「」` quotes, English only inside ` ```agda ` fences, one master `.lagda.md` per module with the `<!--en--> <!--zh--> <!--ja-->` marker grammar. `scripts/lint-prose.py` and `weave-i18n.py` enforce most of this and `dev/STYLE-i18n.md` is the canonical statement. Absorbs DD10's craft half. |
| DD13 | Retirement is planned from the rewrite side, sunk cost decides nothing, and nothing is deleted | A consumer does not prove that a chapter must stay. **First price the ideal form of the content, written fresh today. Then compare.** "We already paid for it" never decides the question, in either direction, and DD2 is itself an instance: the route changed after a year of work. DD4 now asks the same question of every existing chapter, since content that cannot be shared may be cheaper rewritten than adapted. **ARCHIVE, NEVER DELETE**, absorbed from DD14: retired code goes to `archive/` at the repository root, outside `src/`, so every gate is blind to it by structure; archived files are frozen and nothing imports across the boundary; `dev/ARCHIVE.md` records what each module is, why it left, where it was last green, what it did right from measurement rather than praise, and what would make it worth a second look. This also governs `archive/dev/DECISIONS-archived.md`, `archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`. Absorbs DD12 and DD14. |
| DD15 | Measurement discipline: re-measure at every return, and never in the foreground | The ledger is re-measured at every return that could move it, and no standing figure is ever quoted from a paragraph. **A full cold typecheck runs in the BACKGROUND, never in the foreground**, absorbed from DD16: it costs minutes to tens of minutes and must not block a session. DD5's time constraint makes the measurement more load-bearing, not less, so the protocol is fixed: interface cache moved aside, single process, quiet machine, `/usr/bin/time -p`, and the figure recorded with its protocol beside it. Absorbs DD16. |
| DD17 | **The standing dispatch order: slots stay full until BOTH trophies are proved inside both constraints, and every dispatch is codex unless a named exception applies** | Amended 2026-08-09 from an AC-only terminus. An idle agent slot is a defect: a slot stays empty only when a real block stops every remaining task, and an audit is not a reason to leave one idle. **THE TIER, restored 2026-08-09 after the D37 consolidation dropped it.** **Codex is the default for every dispatch.** An in-harness Opus subagent is admissible in exactly two cases: the owner names it for THAT task, because a past override never carries forward; or the orchestrator judges the task very-very-heavy, meaning whole-campaign synthesis or wall-class mathematics beyond measured scale. Ordinary recons, probes, audits, reviews, polish passes and implementation batches are codex work. Enforcement is the brief header: `tier: codex (default)` needs no justification, `tier: opus` must name its exception, and **if that sentence will not write, the tier is codex**. **THE EMERGENCY BREAKTHROUGH TIER.** When a codex return does NOT do its task well AND the point is a critical breakthrough, the orchestrator may re-dispatch to Fable 5 at maximum effort without asking. BOTH conditions bind and the second is the scarce one: a critical breakthrough is a point where the loop cannot advance, so a gate whose verdict blocks the next funded build, a wall no measured cure passes, or a refutation that would re-price the route. Ordinary slowness or a task worth redoing at the same tier is NOT one. **A stop, a refutation and a RED are GOOD returns and never a trigger**; this campaign's most valuable results came back as REDs. Each use names its trigger in the brief, records the escalation in the task index row, and reports what the higher tier found that the first return missed, including when the answer is nothing. Operational form: `dev/ORCHESTRATION.md` sections 1 and 2. |
| DD18 | **THE ARCHIVE AND LITERATURE SURVEYS are sections of the brief and of the return, not a hope.** | **Ruled 2026-08-09 by the owner as a MECHANISM.** Before a brief is sent it carries an **ARCHIVE** section listing what may bear on the task in each archive: `archive/` for retired code, with `archive/rud-route/` holding the retired route's 72 files and `dev/ARCHIVE.md` describing modules retired before it; `archive/dev/TASKS-archived.md` for what each of 265 earlier dispatches FOUND; `archive/dev/JOURNAL-archived.md` for WHY; and `archive/dev/DECISIONS-archived.md` for the rulings that route ran on. **A return carries an ARCHIVE USED section** naming what it actually read and what it took from each item, at `file:line`. "I looked at the archive" is not a return, and a brief whose archive section is empty must say why. `dev/LESSONS.md` is NOT archived and still binds, cited the usual way through `scripts/rules.py`. **A port is priced against a fresh write, never assumed** (DD13), and P-l holds: a measured cure does not transfer by analogy. **ENFORCEMENT IS REVIEW ONLY.** Nothing mechanical reads a brief, so the orchestrator refuses a return whose ARCHIVE USED section is missing. A row that claimed a checker it does not have would be worse than this one. **THE LITERATURE HALF, added 2026-08-10 by the owner, and it is the same mechanism for a second corpus.** `dev/literature/` holds the digested mathematics: `digest.md` for the orthodox route, `j-hierarchy.md` for condensation and the stratification, `fine-structure.md`, `rudimentary-functions.md`, `devlin-errata.md` for the known errors in the primary text, `primary-sources.md` and `BIBLIOGRAPHY.md` for what was fetched and what it was consumed by, and `formalizations-landscape.md` for prior art. **A brief that dispatches mathematics carries a LITERATURE section naming what may bear on it, and a return carries a LITERATURE USED section** saying what it read, what it took, and, for anything it did not use, WHY NOT. **The why-not is the half that earns its keep:** a note saying a source is OCR-degraded, or covers the wrong chapter, or was superseded, is worth as much as one that supplies a lemma, and it stops the next agent paying the same reading twice. **WHY THIS WAS ADDED.** Every phase-1 brief so far cited the archive and none cited the literature, while `digest.md:513-518` had recorded a sourced GCH-in-L derivation, Devlin II.5 with Theorem 5.6, since 2026-08-03. The corpus was there and nobody was sent to it. **ENFORCEMENT, AND THE TWO HALVES ARE NOW IDENTICAL** (owner, 2026-08-10). `dispatch.py` REFUSES a brief that carries no ARCHIVE section, and refuses one that carries no LITERATURE section, **on every brief regardless of kind**. Each is satisfied by one honest line naming the corpus and saying nothing in it bears on the task, which is cheap to write and still forces the author to look. **WHY BOTH, when the archive half had never lapsed.** Measured 2026-08-10: twelve of twelve briefs and thirteen of thirteen returns carried their archive sections with no gate at all. That record argued for leaving it to review, and the owner ruled for alignment instead. The record makes the gate cheap rather than redundant: a rule already obeyed costs nothing to check, and two rules of the same shape enforced two different ways is a thing a reader has to explain to themselves. **WHY EVERY BRIEF AND NOT ONLY A BUILD, which is the correction that matters.** The literature half was first scoped to master-writing briefs, reasoning that a recon needs no mathematics. **That was wrong, and the test is the case that prompted the rule:** `[LJ-1.1]` is a recon, it wrote only a report, and it PLANNED THE ENTIRE GCH WING without citing a line of `dev/literature/`. The build-only scope would have exempted exactly the brief the rule exists for. **THIS BINDS THE CODEX PATH ONLY**, and the limit is stated rather than hidden. An in-harness dispatch does not pass through `dispatch.py`, and `[LJ-1.11]` proved the gap by going out short two mandatory rules. There the orchestrator applies DD18 by hand, and a return that arrives without both USED sections is sent back. |
| DD19 | Governance: one home per rule, goals registered before they start, and two guarded surfaces | **ONE HOME.** Every rule lives in exactly one canonical place, chosen by who enforces it, and a rule that no machine enforces must NAME its enforcement point: a gate, a brief section, a review step. A rule with no enforcement point is a wish. Nothing is canonical twice. **GOALS**, absorbed from DD18's old content: a ruling is a PLAN row and an episode is a JOURNAL entry; every dispatch is registered in the task index BEFORE it starts, one row per code, 200 characters, enforced by `scripts/check-task-index.py`; a ruling may be revised, and a revision is recorded rather than a row being rewritten. **TWO GUARDED SURFACES.** `AGENTS.md` takes no edit without the owner's ruling on the diff and a dated `AGENTS-diff-approved:` trailer, which `scripts/check-agents-guard.py` refuses to go without. `dev/glossary.toml` takes no entry chosen by an agent: a term it lacks goes through the two-agent pipeline, and the pipeline names its tiers: **arm 1 is codex**, which searches the literature for each rendering's provenance and marks every guess where the literature is silent, and **arm 2 is opus, adversarial**, which verifies the sources and attacks the collisions and PASSes or FAILs per term. A PASS lands the entry without the owner's review and the landing commit cites both; a FAIL, or a genuine fork, escalates that term and only that term. The owner's veto always stands. Absorbs the old DD18, DD20 and DD21. |
| DD22 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out; everything else inherits AGPL-3.0. Three buckets, declared centrally, with no in-file `SPDX-*` headers. `reuse lint` enforces it. |
| DD23 | **NO MATHEMATICAL PROSE until both trophies land. The prose phase comes AFTER.** | **Ruled 2026-08-09 by the owner.** Until `L ⊨ AC` and `L ⊨ GCH` are both proved on the two-tower bridge inside DD5's constraints, write NO mathematical prose: no chapter narrative, no trilingual exposition of the mathematics, no reader-facing explanation of a construction. Code and its own comments only. **The prose phase opens when the double trophy lands, and not before.** This is not a licence to write badly: DD11 still binds, and so does ASD-STE100 for every brief, report and message, which is working text rather than mathematical prose. **The reason is DD4.** Prose written against an architecture that reuse has not settled is prose written twice, and the retired route paid that bill. **What this does NOT suspend**: the marker grammar where prose already exists, `docs/`, and `dev/JOURNAL.md`, which is a record and not exposition. |
| DD24 | **THE QUALITY BAR IS SECONDS PER LINE, and on the internalization GCH wing it is the ONLY threshold.** | **Ruled 2026-08-09 by the owner.** Code written for `L ⊨ GCH` on the internalization route must reach the SAME quality as that route's delivered `L ⊨ AC` wing, and quality here means one measured thing: **the ratio of cold build seconds to in-fence lines.** The AC wing measured **0.007614 s per line** on 2026-08-09, 133.19 s over 17,492 lines, so the bar is a number rather than a judgment. **Why a RATIO**: a total can be met by writing less of a worse thing and a ratio cannot, so it says the content must be the same KIND of content. `dev/LESSONS.md` P-m measures why that matters: parameterized work runs about 0.010 to 0.013 s per line and instantiation about 0.22 to 0.297, a twentyfold spread no line count reveals. **THE WING CARRIES NO OTHER THRESHOLD**, absorbed from DD25: no line cap and no seconds cap, and the omission is deliberate. That wing exists to MEASURE what GCH costs, because the measurement sets DD5's benchmarks; a cap would make the measurement report the cap instead of the cost, and this project already paid for that when a projection was re-quoted as a measurement for nine dispatches. **The bar also governs DD5's own benchmark and the two-tower route**: a wing built at instantiation rates would set a seconds benchmark so loose that the new route could clear it while being worse, and a benchmark that is easy to beat measures nothing. **THE BASELINE BELONGS TO ONE TREE, and both tools refuse it on another** (owner, 2026-08-09). A seconds-per-line figure is not a constant: `[LJ-0.4]` compresses the tree by roughly 1,500 lines and moves BOTH terms, neither predictably, because a line lever is not a seconds lever (P-q). So `dev/ledger.toml` records `ac_baseline_lines` beside the figure, and `ledger.py --check` and `check-ratio.py` both REFUSE when standing has drifted from it, naming `[LJ-0.5]` as the re-measurement. Without that guard a stale bar reports exactly like a live one, which is C-28. **Enforced staged by `scripts/check-ratio.py`**, from the first GCH module onward, because a bar readable only at the end is read too late to act on. Read P-m, P-n, P-q and P-t before optimizing: P-q measured 315 lines removed buying 11.8 seconds, so a line lever is not a seconds lever, and P-t found a twentyeightfold spread inside ONE file, so the carrier never certifies the class. The formula does. |

## 4. Target skeleton (OWED a re-derivation for DD2)

The D5 target skeleton, its port-era diagram and the rename ledger moved to [dev/memos/target-skeleton-d5.md](memos/target-skeleton-d5.md). What stays binding from D5: the part level (Base, FOL, ZF, V, L, Landmarks) is fixed, below-part layout is provisional until the [L3.10] re-layering, and the authorities for what `src/` contains are `src/README.md` (the master symbol table) and `src/Everything.lagda.md` (the reading catalog), not this section. Read the memo when a rename's history or the port-era layout is needed.

## 5. Working mechanisms (pointer)

The mechanisms this section carried moved to their enforcers ([L3.32-T113]): the LEM parameterization convention is `dev/STYLE-agda.md` section 1 (the ruling is DD9 in §3); the two-catalog doctrine and the named-hypothesis debt form are in `dev/STYLE-agda.md`; probes and gates are `AGENTS.md` and `dev/LESSONS.md` D-1; orchestration is `dev/ORCHESTRATION.md`. The port-era mechanism history (the Frontier record, its re-cuts, construction order) moved to [dev/memos/working-mechanisms.md](memos/working-mechanisms.md); the Frontier's deletion is recorded in the struck D8 row of `archive/dev/DECISIONS-archived.md` and in rows L2.4 and L4.0 of `archive/dev/STATUS-archived.md`.

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

The T1-T6 tension register and its relief valves moved to [dev/memos/process-tensions.md](memos/process-tensions.md). Archived D11's mechanisms are in `archive/dev/DECISIONS-archived.md`; the live relief valves are the L0 standing track (§6.0) and the L4.1 harmonization (§11). Note that `DD11` is a DIFFERENT rule, code and prose craft: the D and DD numbers do not correspond.

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
| L3.32 | The L-trophy build (the ruled configuration) | **CLOSED 2026-08-09** when the route changed. The fourth switch: the Def tower kept the trophy, the wing rode a fresh-generic Sigma-1 face, and the rud-route code is now in `archive/rud-route/` |
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

The dispatched tasks on the two-tower bridge route, one row per code.

**The code is `LJ-<phase>.<step>`** and the phase is the hierarchy the owner
asked for: **1** is the internalization GCH wing, **2** is quantifying DD5's
benchmarks from it AND RULING THE ARCHITECTURE on them, and **3** is the
double trophy on whatever phase 2 rules. A phase is a barrier: phase 2 cannot
start before phase 1 delivers, because it measures what phase 1 built, and
phase 3's constraints are the numbers phase 2 sets.

**TWO PIECES OF EVIDENCE THE RULING IS OWED, and both are archived rather
than lost.** `[L3.32-T261]`'s probe on the S-tower crossing was QUEUED for an
Agda slot and never ran, and `[L3.32-T257]`'s line comparison carries a
declared weak point worth 4,238 to 5,218, about a fifth of its band. The
economics of the architecture rest on both. `[LJ-2.3]` surveys them under DD18
and says whether either must be re-run before `[LJ-2.5]` can rule.

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
| LJ-0.4 | Compress the internalization AC tree toward about 16.4k | RULED, ready to execute | 16,000 refuted by T205 and T208. Owner set ~16.4k 2026-08-10. Recon done, 8 disjoint blocks |
| LJ-0.4c | Compression block C: the Unique and Sound clause frames | STOPPED by the orchestrator, reverted | It gutted Sound to 7 lines and Unique to 11, moving 1,354 into a new module for a net of -59 |
| LJ-0.4e | Compression blocks E and G: traversal share, lex kit | REFUSED BOTH on measurement | E nets +19 against -60 to -120, G about -49 against -40 to -80. Kits built, priced, reverted |
| LJ-0.4b | Compression blocks B, D, F, H | planned | -380 to -730 together. Disjoint by file per C-25. B is the largest left after C |
| LJ-0.4a | Compression block A: the dead names, and 𝒟ₒ→isL | DELIVERED -240 | 48 names over 18 masters, 17,492 to 17,252. Kept 3 the plan rides and 5 Everything's prose names. 𝒟ₒ→isL refused |
| LJ-0.6 | Restore the V.Presentation shim the src/ restore deleted | DONE | +19 in-fence, 76 masters. Cold 132.87 s, exit 0. Unblocks the archived Collapse and Hull ports |
| LJ-0.5 | RE-MEASURE the DD24 seconds-per-line baseline, once per block | STANDING TASK | Now 132.87 s over 17,271 = 0.007693. Block A's 240 lines bought -0.50 s: compression WORSENS the ratio |
| LJ-1.1 | Recon: the GCH route on the internalization tower | RETURNED | Wing 8.0-10.8k, centre 9.4k. Widest term is the Levy crossing; probe specified. Corrects 7 of the LJ-1.x rows |
| LJ-1.2 | Gate: probe the widest unmeasured term LJ-1.1 names | NO-GO, re-prices the wing | Step clause has no Delta-0 witness at ANY carrier. Crossing 5.0-5.1k, or 1.0-1.7k by the cone fork |
| LJ-1.10 | RE-PRICE the crossing after LJ-1.2's NO-GO | RETURNED, a THIRD route | Neither candidate. Port the archived structural story: its Def-step is ⊤̇, so no code or table bound enters |
| LJ-1.11 | ADVERSARIAL review of LJ-1 against the literature route | dispatched | tier: fable 5, owner-named. LJ-1 predates DD18's literature half. Deviations need threshold AND DD reasons |
| LJ-1.3 | Build: the Skolem hull, a least-witness search over the order | DELIVERED 343 lines | Ported from 241 archived. 0.0070 s/line, 0.91x the bar. Does NOT use σ₁-up: LJ-1.5 does |
| LJ-1.4 | Build: the Mostowski collapse | DELIVERED 239 lines | Ported from the archive's 181, plus Devlin 5.2(ii) which the archive lacked. Carrier-generic. Cold tree 133.39 s, exit 0 |
| LJ-0.7 | Digest Devlin II.5 into the literature: the condensation lemma and GCH in L | planned | GATES LJ-1.5. digest.md:513 says II.5 is in hand but the derivation is NOT in the corpus |
| LJ-1.5 | Build: the condensation lemma, via the archived structural story | planned | LJ-1.10's route C. NOT the delivered description: LJ-1.2 refuted certifying that directly |
| LJ-1.6 | Build: cardinality of a stage, |L a| = |a| for infinite a | planned | ARCHIVE FIRST: archive/rud-route holds L/Cardinal*.lagda.md and FOL/Count.lagda.md. Parallel to LJ-1.3 to LJ-1.5 |
| LJ-1.7 | Build: every subset of a stage appears early | planned | Condensation plus cardinality. Needs LJ-1.5 and LJ-1.6 |
| LJ-1.8 | Build: assemble L models GCH | planned | The measuring trophy. Needs LJ-1.7 |
| LJ-1.9 | Quality audit: the wing's ratio AND its net removable lines | planned | DD24's ratio, cold. PLUS an independent read of what did not need to be there: DD5 measure 3. Read P-m, P-q, P-t |
| LJ-2.0 | Re-price the owed evidence: T257's weak point and T261's probe | planned | Does NOT block phase 1. Gates LJ-2.5 only, done when needed. ARCHIVE: T257, T259, T260, T261 |
| LJ-2.1 | MEASURE the internalization double trophy, lines and cold seconds | planned | Records measured, LJ-1.1's projection and LJ-1.9's removable together. Line benchmark is the SMALLER. C-12 |
| LJ-2.2 | Re-arm the thresholds, rebuild [[remaining]] and [[owed]] | planned | OWNER JUDGES the wing a fair paper BEFORE the flags flip (DD5). Four stale flags to clear |
| LJ-2.3 | Recon: the reuse map and the architecture that MAXIMIZES sharing | planned | DD4 decided here. Supersedes LJ-3.1. Delivers section 4's skeleton. Quote ledger.py --reuse |
| LJ-2.4 | Adversarial review of LJ-2.3's reuse map | planned | The critic is never the author. Supersedes LJ-3.2. A failing reuse claim sends LJ-2.3 back before the ruling |
| LJ-2.5 | THE ARCHITECTURE RULING (owner), on measured evidence | planned | DD2's candidate confirmed, amended or replaced. Needs LJ-2.0, 2.1, 2.2 and 2.4. Nothing in phase 3 starts first |
| LJ-3.1 | Recon: the two-tower architecture for MAXIMUM shared code | SUPERSEDED | Moved ahead of the architecture ruling as LJ-2.3 (DD2, amended 2026-08-09). Rule 3: new code, old row kept |
| LJ-3.2 | Adversarial review of LJ-3.1's reuse map | SUPERSEDED | Moved ahead of the architecture ruling as LJ-2.4. Rule 3: a re-stated goal takes a new code and the old row points at it |
| LJ-3.3 | Gate: probe the widest unmeasured term in the ruled architecture | planned | DD8, and it needs LJ-2.5's ruling first. Both constraints are relative, so an ungated term risks the endpoint |
| LJ-3.4 | Build: the J tower through rud | planned | ARCHIVE FIRST: the rud route delivered sixteen operations and a Story layer. Price port against fresh write per module |
| LJ-3.5 | Build: the two-directional bridge, L to J and J to L | planned | DD2 keeps BOTH directions. ARCHIVE: archive/rud-route/src/L/Rud/Bridge.lagda.md |
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
