# PLAN: the construction registry (V=L ⊨ ZFC, then GCH)

Bedrock's goal registry. It opened in July 2026 as the plan for one milestone,
re-landing the `fol-reification` result (V=L ⊨ ZFC) as textbook-grade literate
Agda; the campaign has since grown past that milestone, and the registry grew
with it. Developer doc, English only, not translated. Work is managed by the
goal codes of §6; the MASTER status table is §11.

**Read §0 first.** It states where the work stands today in one screen.
Everything after it is either standing legislation (§3, §6.0, §7) or history:
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

## 0. Where the work stands (2026-08-04)

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

**What is in flight.** `[L3.32]` wave 1 (the R4 corrective stop DELIVERED; the
face probe, the choice re-home probe, the retirement design recon and the W7
scoping RETURNED) and the foundation kit batch. Wave 2 builds the face chapter,
then W2, then W3 and W5 in parallel, then the bridge, the re-home, the
retirement surgery and W7.

**The ledger.** Standing after the ruled retirements is about 12.2 to 12.5k
non-blank in-fence lines; the naive endpoint projection is about 16.7 to 22.6k
against the owner's 25k line, with the calibrated projection failing that line
in every route examined (a route-invariant fact, driven by W7's greenfield and
the unprobed statement layers). Line calibers and the two-caliber discipline
are defined in §6.2.

**The narrative frame.** §6.1's `[L6]` declares the terminus: set-theoretic
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

## 1. The theorem, stated honestly (D1)

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

## 2. Source material survey (condensed)

*Port-era history, kept for its measurements.* This section surveys the source
repository as it stood in July 2026 and prices the port that opened this
registry. Its cost anatomy (§2.1) is still cited as a calibration anchor; its
scope statements describe the original milestone, not the current campaign
(§0).

Facts an implementing agent needs before touching the port:

- **Scale:** 172 literate modules, about 70.7k lines. Of these, `L/` holds 142
  modules and 66.5k lines (94%). The `--safe` core (Prelude, Truth, FOL,
  Reification, ZF, Models/HITV, Examples) is only about 4k lines and is
  already clean.
- **Root module:** `src/L/ModelZFCFinal.lagda.md` defines `L⊨ZFC : ZFCModel`
  (alias `Con-AC`). The ZF axiom fields live in `src/ZF/Model.lagda.md`
  (records `ZFModel`, `ZFCModel`); separation and replacement consume the
  deeply embedded `Formula`, which is where the reification framework is
  load-bearing.
- **Difficulty concentration:** the bulk of `L/` is the well-order `<L` and
  the L-recursion, reified as Δ₀ graph-certificate clusters (`Cmp*`, `Depth*`,
  `Order*`, `Trace*`, `Coh*`), plus internal satisfaction (`Sat*`, `Tarski*`)
  and coding (`Code*`, `Formula*`). These clusters are the L3 reduction-review
  targets.
- **Prose:** Chinese research-log style throughout (milestone provenance,
  probe numbers, performance archaeology). It is **construction intelligence
  for the porting agent, not translation input** (D6).
- **Performance engineering:** the source carries a documented playbook of
  conversion-blowup countermeasures (opaque seals, explicit implicit
  arguments, Π-parameterized assumption bundles); see
  `../fol-reification/docs/WORKLOG.md` §5. After the upstream M2.7
  optimization, the full lem-cone cold check runs in about 8.5 minutes at
  `-j4` with per-module heap caps (down from 157 minutes). The build machinery
  is portable; its trust model is codified as constraints in §7.
- **Goal management:** the source runs an append-only route-tree register
  (`../fol-reification/docs/ROUTE-TREE.md`) with dotted-decimal goal codes.
  Bedrock adopts a lightened version of the same discipline (D9, rules in
  §6.0).

### 2.1 Cost anatomy (measured 2026-07-25)

Where the source's mass actually sits, measured by attributing every module to
the `isZFCModel` field whose proof term reaches it. Method: non-blank lines
inside ` ```agda ` fences (prose excluded); transitive dependency closure from
each field's filling term; module granularity, except the six assembly modules
(`L.ModelAC`, `L.ModelACSep`, `L.ModelACNum`, `L.Condensation`, `L.ModelZFC`,
`L.ModelZFCFinal`), which are split per definition. The whole `L⊨ZFC` cone is
150 modules and 48,260 code lines; the other 22 modules (2,521 lines) are
probes and unwired experiments, which the consumption audit drops at port time.

Field names below are Bedrock's (§4 ledger), source names in parentheses where
they differ. "Body" is the code that literally fills the field, "cone" includes
all shared dependencies, "own" is code reachable from this field alone.

| `isZFCModel` field | body | cone | own |
|---|---:|---:|---:|
| `extensional` | 13 | 2,279 | 13 |
| `regularity` (`foundation`) | 7 | 2,273 | 7 |
| `hasEmpty` | 20 | 2,286 | 0 |
| `hasPair` | 48 | 2,314 | 0 |
| `hasUnion` | 65 | 2,331 | 0 |
| `hasSeparation` (`hasSep`) | 87 | 4,924 | 0 |
| `hasReplacement` (`hasRepl`) | 167 | 5,004 | 0 |
| `hasPower` | 33 | 3,038 | 149 |
| `numeral` | 54 | 2,791 | 0 |
| `numeral-zero` (`num0`) | 3 | 2,819 | 3 |
| `numeral-suc` (`numS`) | 18 | 2,834 | 18 |
| `hasInfinity` | 21 | 2,812 | 21 |
| `hasChoice` | 68 | 47,839 | **42,354** |

Read as a partition, the twelve ZF fields own 211 lines between them. Their
real cost is three shared blocks: the framework and carrier trunk (2,266
lines), the Δ₀ engine with the full-formula reflection machinery (2,571
lines), and the numeral chain (392 lines). Everything else is `hasChoice`:
42,354 lines, 88% of the cone, of which 42,258 sit in 106 modules that no other
field touches.

That mass is not one proof. It is 8 to 10 hand-built instantiations of a single
pipeline (step function to Δ₀ graph to "the graph is a set of L" to
certificate to soundness), once each for comparison, depth, the order itself,
satisfaction, traces, coherence, sequence codes, and the closure families.
Clone measurement over the twin families, after normalizing names:

| module pair (renaming-normalized) | similarity |
|---|---:|
| `CmpCertMatrix` / `DepthCertMatrix` | 86% |
| `CmpCodeCarrier` / `DepthCodeCarrier` | 67% |
| `CmpGraphInL` / `DepthGraphInL` | 60% |
| `CmpGraphInLFinal` / `DepthGraphInLFinal` | 50% |
| `CmpSound` / `DepthSound` | 8% |
| `OrderGraph` / `CmpGraph` | 4% |

So the scaffolding repeats and the soundness segments do not: the mathematics
genuinely differs per instance, but the harness around it is written out once
per instance. The reason is structural: the source has no general theorem
saying a recursively defined function is internalizable in L, so every
function builds its own. Density counts corroborate: 27.9 formula-syntax
tokens and 8.3 Δ₀ witness tokens per 100 lines, 3,963 explicitly spelled
implicit arguments and 139 `opaque` seals (the M2.7 performance tax), and 53%
of all lines sitting inside `where` blocks.

Projected reduction, by lever, each with the goal code that executes it and the
register entry that tracks it:

| Lever | Headroom | Code | Candidate |
|---|---|---|---|
| General internalization theorem | to roughly 8k to 12k total | `[L3.0]` | S5 |
| `reify!` macro industrialization | 4k to 6k | `[L3.2]` | S6 |
| Scaffolding parameterization | 3k to 5k | `[L3.4]` | S3 |
| Transition-layer sweep | 2k to 3k | `[L3.1]` | S9 |
| Transport and cast solver | 1k to 2k, high risk | `[L3.9]` | S7 |
| Dispatch-grid generation | 1k to 1.5k, source lines only | `[L3.8]` | S8 |

The five syntactic levers together are 25% to 40%, and every one of them trades
against cold-check time. The general theorem is the only lever that reaches
further; it is also the only lever that is research rather than refactoring.
D12 rules on which to take, §6.1 orders their execution.

> **Correction (2026-07-25, `[L3.0.3]`).** The 8k to 12k figure above is the
> ceiling of a **three-theorem programme**, not the yield of `[L3.0]`. The
> probe measured the pipelines directly: the constant-table theorem covers
> 13,518 of the 42,258 lines, `Order*` (11,386 with its trace machinery) needs
> a separate stage-indexed theorem, and `Sat*` / `Tarski*` / `Coh*` (10,706)
> fit only by halves. On tier 1 alone the honest projection is 42.3k to about
> 36k. The route survives; the probe also found a second abstraction worth as
> much as the theorem (a per-tag clause bundle). Full tier table and evidence:
> [memos/L3.0.3-subsumption-probe.md](memos/L3.0.3-subsumption-probe.md) §5
> and §6.

## 3. Ratified decisions

| # | Decision | Ruling |
|---|----------|--------|
| D1 | Statement of the result | As in §1: V=L ⊨ ZFC, relative consistency, relative to the host. Never unqualified "Con(ZFC)". **Extended 2026-08-03 with the campaign's endpoint**: the same L satisfies GCH, stated internally, yielding Con(ZF) → Con(ZFC + GCH) under the same relativization; "Con(GCH)" is likewise never claimed unqualified. |
| D2 | Classical boundary | **In force, and D20 was shaped around it: the archive lives outside `src/` precisely so this claim stays literally true of the whole checked tree.** No `postulate` anywhere. LEM (and any classical/choice principle) is an explicit parameter; the whole tree is `--safe`. Gated by the L0.2 performance spike; a materially worse projection (over 1.5x the M2.7 full-cone baseline) escalates back to the owner. Documented fallback if re-ruled: one postulate module with an explicit safe boundary. |
| D3 | Technical lemma layer | **SUCCEEDED IN PRACTICE 2026-08-04 by D16 and D21's mechanisms**, which do the same job with measurement instead of per-cluster review: ideal-form pricing alongside the continuation, probe-gated levers, the two-caliber discipline, and a whole-tree polish phase with exports frozen. The original ruling stands as history and its intent is unchanged: L3 starts with a **reduction review** per cluster:
| D4 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out (the owner authors both repositories). No in-file SPDX headers. Prose cites Rech (2020) and the source repository where warranted. |
| D5 | Skeleton | The previously reserved `src/` namespaces are void. The redesigned skeleton in §4 replaces them; `src/README.md` is rewritten in L1. Below the part level the skeleton is **provisional** (D11, tension T2). **Amended 2026-08-04**: §4's diagram is the port-era record, not the live tree; the authorities for what `src/` contains today are `src/README.md` (the master symbol table) and `src/Everything.lagda.md` (the reading catalog). The part level remains as fixed here: D20's archive lives at the repository root, OUTSIDE `src/`, precisely so that retiring code adds no part and disturbs no gate. |
| D6 | Prose | Full rewrite for beginners, English first, then Chinese (Japanese pre-supported). Source research prose is never translated; it serves the porter only. |
| D7 | Naming hygiene | No iteration-numbered or provenance-flavored names survive the port. The §4 mapping table is the rename ledger; extend it as porting proceeds. |
| D8 | Construction order | **SPENT 2026-07-31**: the Frontier is empty and deleted since `[L2.4]` and the root is unconditional, so the mechanism this decision installed has done its work. Original ruling: root-first via the Frontier record (§5), the statement of the theorem typechecks from day one, details land last. Reading order on the site remains foundations-first, and that half still binds. |
| D9 | Goal management | Work is managed by route-tree goal codes rooted at **L**: L0 to L8 as registered so far, sub-goals Lx.0 onward; the range is open at the top and grows by registration, not by amendment. Coding rules in §6.0. Commits and docs carry the code in brackets, for example `[L1.4]`. |
| D10 | Build performance | The build constraints of §7 are binding from the first ported module: single-invocation trusted gate, parallelism outside the trust base, tracked cold-check budget, per-module heap caps. Cold-check regressions are defects. |
| D11 | Revisability | The plan legislates for known unknowns explicitly: legislation may be added mid-course (standing L0 track), the skeleton below the part level may be re-cut after L3, Frontier fields may be re-cut, and a whole-book harmonization pass runs at L4. Mechanisms in §8. **Amended 2026-08-04 by D21**: the harmonization still runs at L4, but L4 is no longer next-after-L3 in time. It is gated behind `[L8.2]`, the consolidation report, so the order is endpoint, then `[L7]` archival, then `[L8]` consolidation and its gate, then `[L4]` prose. |
| D12 | L3 reduction strategy | **Outcome 2026-07-26 (`[L3.0.2]`): the decision was right, the analysis was wrong.** The lever was not a large internalization theorem (it is 96 lines) but general-formula comprehension, delivered at `[L2.2]`; the projected 65%-at-3x is now measured-and-projected at 7x to 14x. Original ruling, 2026-07-25: **take the big lever first** (goal `[L3.0]`), under an explicit paper-level gate and pre-agreed kill criteria (`[L3.0.3]`, `[L3.0.1]`); schedule ruling, same day: `[L3.0.3]` opens **before** L2. |
| D13 | Macros and generated proof | **Ruled 2026-07-27 by the owner.** Opacity is **not** an objection. **The single veto is conversion blowup.** A macro or reification route is judged by exactly two measured questions: is it smaller, and does it keep `src/` inside the §7.5 and §7.6 budgets. Supersedes the exposition argument recorded against `[L3.2]`, which is withdrawn. |
| D14 | Retiring a chapter in waiting | **SUPERSEDED 2026-08-04 by D17 (the trigger) and D20 (the disposal), on the owner's ruling.** Its passive trigger under-fired: a chapter with any surviving consumer never became *in waiting*, however dead its content, which is exactly how a 1,989-line chapter survived on a survivor-consumes warrant. D17 replaces the trigger with an active one (price the ideal-form rewrite, then retire wholesale) and D20 replaces deletion with archival. The warrant discipline this decision installed carries forward into the archive registry: a kept chapter still needs a named open goal and a dated expiry. Original ruling, 2026-07-27, kept as history: A chapter is *in waiting* when nothing outside its own namespace imports it (`Everything` never counts). Such a chapter is **retired** (files deleted, `Everything` entries dropped, the commit hash recorded in §11, plus one line saying what would bring it back) when **both**: no **open** goal names it in §6.1, and either a goal that did name it has closed without using it, or no goal ever named it. It is **kept** only under a **written warrant**: a named open goal *and* a dated expiry. Warrants live in §11 and expire whether or not anyone looks. **Trigger:** at every goal closure, list the chapters in waiting and check their warrants. |
| D15 | The AC route | **SUPERSEDED IN ROUTE CONTENT 2026-08-02 by `[L3.30]` and finally by D18**; what survives is its branch plan, which D20 completes (the old `main` becomes the archive, the working branch is promoted). Original ruling, 2026-07-31, by the owner: option C of `dev/memos/L3.28-ac-route.md` is adopted**, on the memo's numbers (ZF-only cone 4,180 lines, AC-only radius 13,217, the swap surface one import list) and on three same-day probes, all PASS (memo §9). `Def` keeps its satisfaction definition and every ZF-cone statement keeps its meaning; the internal tower and the internal well-order rebuild over a binder-free operations calculus; the satisfaction-internalization chapters retire at the cut-over. Execution is the two-step branch plan: build C on `godel-route` with both developments coexisting, judge the pedagogy side by side before deleting, promote on success; old `main` becomes the internalization archive with a wrap-up and a tag. Executes as `[L3.29]`, which carries the milestones and tripwires; the global stop is a landing projection above 11k at any milestone (since amended by the tripwire rulings, §11). **Pivot 2026-08-01: option B of `dev/memos/L3.29-b-pivot.md` is adopted for the build on this branch**, kinded closure tower with the stratified producer order, alongside the delivered route, final measurement then a fresh ruling before retirement.**2026-08-02: the architecture question is reopened as `[L3.30]` (rud re-architecture, exploratory) under the future-extensibility lens; the B build is suspended after its final batch; no retirement of any route occurs until the `[L3.30]` ruling.** |
| D16 | Sunk cost is not decisive | **Ruled 2026-08-04 by the owner, standing.** Route decisions and re-cuts ignore sunk cost; it is reference only. Routes under comparison are priced as FROM-ZERO rebuilds on current experience (the あるべき姿 form) ALONGSIDE their continuation forms, and both are presented for the ruling. Overlap between an ideal form and the standing tree is a discount to report, never an argument to make. The corollary the owner endorsed: **asset durability equals genericity**; what generalizes is promoted into shared foundation, what stays fixed to one carrier awaits retirement. Evidence that produced the rule: the Matching detour (four batches priced links of a chain whose root was classically false) and the monomorphic satisfaction cone (its 134 readings would re-instantiate free at any carrier had they been written structure-generic; the second-carrier tax is sunk form made visible). |
| D17 | Retirement is planned from the rewrite side | **Ruled 2026-08-04 by the owner, at EQUAL standing with D16.** A partial retirement scoped to keep a surviving consumer working is the wrong shape by default. First price what the ideal-form version of the needed content costs written fresh today, then retire the old chapter WHOLESALE. Any finding of the form "X must stay because Y consumes it" is INCOMPLETE until the ideal-form rewrite of what Y actually needs has been priced, and the pair (keep-cost versus rewrite-cost-plus-wholesale-retirement) goes to the owner. D-19 of `dev/LESSONS.md` prices PORTS and must not be quoted at a rewrite question. First application, same day: a 1,989-line chapter kept on a survivor-consumes warrant converted to a 0.65-1.25k rewrite, and the sweep it triggered found a second dead cone of about 1,076 lines. **Absorbing D14's role (2026-08-04): this decision now carries the retirement TRIGGER as well.** The trigger is active, not passive: at every goal closure, and at every ruling that changes what the tree consumes, ask of each chapter whether the ideal-form version of the content its consumers actually need is cheaper than the chapter; if it is, the chapter is scheduled for rewrite-and-archive. A chapter with surviving consumers is NOT thereby safe, which is the precise failure D14's passive trigger had. Disposal is D20's archive, never deletion. |
| D18 | The trophy configuration | **Ruled 2026-08-04 by the owner on the measured comparison (`_build/l3.31-lt-report.md`).** The trophy stays on the Def tower; there is no re-founding onto the rud/J tower. The wing rides a fresh-generic Sigma-1 face; the reindexed bridge lands at wing tail as a corollary; choice re-homes through it; the internalization cone, the choice tree and the coded cluster retire. The deciding fact was that keeping the trophy on L is a WASH against re-founding at the naive caliber, so the tie broke on the non-line dimensions (steady-state weight, parallelizability, shippability, and the fine-structure literature's J-native form arriving only at the horizon). Executes as `[L3.32]`. |
| D19 | The bridge is two-directional | **Ruled 2026-08-04 by the owner.** The bridge delivers BOTH directions of the two-definition identification; the one-way variant (mechanizing `isL → isJ` and demoting `isJ → isL` to a recorded classical fact) is rejected **on the theorem's value, not on its cost already paid**: a bridge that runs one way is a different and weaker theorem, and the two-definition identification is what the book claims and what the community discussion valued. D16 forbids "we already paid for it" as a deciding reason and that reason is not used here; the delivered proof's existence is a discount, not an argument. Consequence recorded at the time: the step-into-L content stays in the tree, which under D17 means it is rewritten in ideal form rather than kept at its delivered size. |
| D20 | The archive regime, and the endpoint promotion | **Ruled 2026-08-04 by the owner; amended the same day on the owner's two rulings: the regime takes effect IMMEDIATELY (it supersedes D14's deletion from now on, not only at the endpoint), and the archive lives OUTSIDE `src/`.** **(A) THE ARCHIVE REGIME, in force now.** Retired code is archived, never deleted. The archive is a top-level `archive/` directory at the repository root, holding each retired module at its ORIGINAL path (`archive/src/L/Coding/Sequence.lagda.md`), so provenance is self-evident and `git log --follow` keeps working. Being outside `src/` makes every exclusion STRUCTURAL rather than configured: the Agda gate is `agda src/Everything.lagda.md` and never reaches it, the include path does not contain it, the linters scan `src/` and skip it for free, the site builds from `src/` and never publishes it, and **D2 stays literally true of the whole checked tree**, which is why the archive is not in `src/`. The archive is **not required to typecheck, not required to be green, and a red archive is not a defect**; its modules keep their original imports even where those no longer resolve. Two disciplines keep it from rotting into a half-maintained second tree: **archived files are FROZEN** (never edited in place; a revival copies out, it does not edit in), and **nothing may import across the boundary in either direction**. Licensing is preserved, not changed by the move: `REUSE.toml` gains an `archive/**` carve-out matching the archived content's original license, and `reuse lint` continues to cover it, since REUSE is a repository-wide scan and coverage there is free. The archive carries its own `README.md` stating all of the above. **(B) THE REGISTRY.** `dev/ARCHIVE.md` records, per archived module: what it is, WHY it was archived (the ruling and its date), the commit at which it was last GREEN (this is what makes it usable later), its measured size, and the CONDITION under which it would be worth consulting again. Pre-regime deletions (the chapters deleted under D14 before this ruling) get registry entries pointing at their deletion commits, without file restoration; git history is their archive. **A revival condition that becomes provably moot may be closed and its files then genuinely deleted, recorded in the registry** so the archive cannot become a landfill. **(C) THE ENDPOINT PROMOTION.** When the endpoint (`L ⊨ ZFC ∧ L ⊨ GCH`) is reached, the old `main` is archived and tagged and the working branch becomes `main`, the same day, before any archival tidying, so that what the world sees is the delivered book. **Rationale.** The campaign retires more code than it keeps, and the retired code is the record of routes that were tried and priced. Deleting it destroys evidence a future reader or a future route may want; keeping it inside the gated tree taxes every build forever. The archive is the third option: preserved, unwired, ungated, indexed, and out of the way. The infrastructure (`archive/`, its README, the registry, the REUSE carve-out) is created at the FIRST archival, which is `[L3.32]`'s retirement surgery, not deferred to the endpoint. Endpoint execution is `[L7]`. |
| D21 | The consolidation phase, and the gate before prose | **Ruled 2026-08-04 by the owner, binding on what follows D20.** After the archival protocol completes, the tree gets a consolidation phase BEFORE any whole-book prose work: (1) a foundation refactor at the scale and character of the 2026-08-04 foundation audit and kit batch, re-run against the post-archival tree (audit first, priced candidates with named consumers and stop-lines, then one batch); (2) a line-by-line polish pass over the WHOLE tree, not a sample; (3) **a report to the owner, which is a GATE: the prose polish phase does not open until the owner has read it and ruled**, and the owner will add further code-shaping work at that point. The sequencing consequence is recorded explicitly: `[L4.1]`'s whole-book harmonization and everything downstream of it wait behind this gate, so the registry's L4 rows are not next-after-L3 in time. Rationale: prose written against code that is about to be reshaped is prose written twice, and the campaign has already measured how much a late reshape moves (the polish batches ran at -7.2 percent and -1.9 percent, and the foundation audit found compression that no prose pass could have anticipated). Executes as `[L8]`. |
| D22 | Every block is gated before it is funded | **Ruled 2026-08-04 by the owner, standing, in response to W7's fourth consecutive up-price.** From now on **no block is built at the 3x class without first trying to measure it**: every remaining block carries a paired D-1 probe, run BEFORE or alongside the build, aimed at that block's widest unmeasured term, and the block is funded at the band the probe leaves rather than at the band the survey guessed. The rule exists because this campaign has measured, repeatedly, that up-corrections land on survey-class terms and down-corrections on probe-reachable ones; the probe is therefore not caution but arithmetic, since each green gate moves its term from 3x to about 1.3x and narrows the band's TOP, which is the edge that touches the owner's line. Evidence that produced it: W7 re-priced upward four times in one day (a re-scope, a red gate, an itemization, and a delivered chapter that reduced its gap instead of closing it), while the one term that was probed in the same window, the shape-count, landed INSIDE its band at about 200 measured lines instead of on top of it. Corollary for dispatch: a build brief that cannot name its block's widest term and the probe that would measure it is not ready to be sent. |
| D23 | An idle agent slot is a defect | **Ruled 2026-08-05 by the owner, standing.** Whenever a sub-agent slot is free, the orchestrator CHECKS for parallelizable work and fills it. A slot stays empty only when every remaining task is genuinely blocked, and "blocked" means something specific: waiting on an owner ruling at a fork, waiting on a sibling's territory, waiting on a measurement whose absence makes the work unfundable under D22, or barred by the concurrency and heap ceilings of LESSONS C-12. **Auditing a return is not a reason to leave slots idle**, which is the error that produced this ruling: three slots sat empty through an audit that needed none of them. The check is cheap and belongs at every return: name what is unblocked, name what blocks the rest, and dispatch into the free slots before writing the report. |
| D24 | Every rule has one home, chosen by its enforcer | **Ruled 2026-08-05 by the owner, whose diagnosis was that some disciplines lived in documents and some in the orchestrator's memory, so a rule's address was unpredictable and its execution depended on one party remembering.** The scheme, whose purpose is EXECUTION rather than tidiness: **a rule lives where its enforcer is, and a rule that is not machine-enforced must name its enforcement point.** Term renderings live in `dev/glossary.toml` (a checker enforces them); code and prose style in the two style documents (linters); licensing in `REUSE.toml` (`reuse lint`); measured engineering law in `dev/LESSONS.md` (briefs point at it); project rulings here in section 3 (the orchestrator and the briefs); what every contributing agent must know in `AGENTS.md` (loaded at session start); and **dispatch, slots, briefs and audits in the NEW `dev/ORCHESTRATION.md`**, which is where the orchestration rules now live instead of in session memory where the owner could neither read nor amend them. `AGENTS.md` carries the index table so any rule can be found by kind. **Nothing is canonical in two places**; where a document restates another's rule it says which is canonical. Session memory keeps exactly two things: owner-private context that must never reach a public file, and the private REASONS and episodes behind a repo rule, each memory marked as a pointer to its canonical text. A rule with no enforcement point is a wish, and adding one here requires naming where it fires. |
| D25 | An owner instruction is executed or explicitly deferred | **Ruled 2026-08-05 by the owner after the orchestrator dropped one.** A message from the owner often carries more than one instruction, and the SECOND is the one that gets lost, especially when the first opens a topic interesting enough to absorb the turn. On 2026-08-05 a single message carried a terminology ruling and a dispatch instruction; the ruling was executed, the dispatch was dropped, and the owner had to ask three times before it was noticed. **Enforcement point, recorded in `dev/ORCHESTRATION.md` section 6: before writing the closing report of any turn, re-read the owner's last message and account for every instruction in it as done, dispatched, or deferred with a stated reason.** The same section also corrects a rule that was wrong as written: `AGENTS.md`'s never-commit-never-push rule binds DISPATCHED agents; the orchestrator commits after auditing and gating, and nobody pushes without the owner's word. |

## 4. Target skeleton (D5)

Top-level parts mirror the book's parts. The part level (Base, FOL, ZF, V, L,
Landmarks) is fixed; **cluster-internal layout is provisional until the L3.10
re-layering review** (tension T2), and file splits inside a cluster are
finalized at port time under the STYLE-agda rules (L0.0).

**Reading this section today.** The diagram below is the ratified D5 skeleton
as designed for the port, and it is kept as that record. The tree has since
grown past it and is about to shrink back past it: `L/Rud/` (the rudimentary
function engine and its tower) is a whole cluster the diagram predates, and
under D18 the satisfaction-internalization cone, the choice tree, the Goedel
trees and the coded cluster retire. **For what the tree contains right now, the
authorities are `src/README.md` (the master symbol table) and
`src/Everything.lagda.md` (the reading catalog), not this diagram.** The rename
ledger below it stays append-only and remains accurate as history.

```
src/
├─ Everything.lagda.md       aggregator; import order = reading order; site landing page
├─ Landmarks.lagda.md        milestone theorems restated, with pointers into the text
├─ Base/                     Part 0: host-language groundwork
│   ├─ Prelude               cubical re-exports, global conventions
│   ├─ Truth                 truth values (hProp toolkit; see S1 in §10)
│   └─ Classical             LEM as a parameter interface and its consequences; no postulate
├─ FOL/                      Part 1: first-order logic as an object of study
│   ├─ Syntax                Formula (12 constructors, incl. Δ₀ bounded quantifiers)
│   ├─ Structure             ZFStructure: carrier, equality, membership; ↾, environments
│   ├─ Semantics             Tarski satisfaction by structural recursion (holds by refl)
│   ├─ LevyHierarchy         the Levy hierarchy as inductive witnesses
│   ├─ Absoluteness          transitive classes; Δ₀ absolute, Σ₁ up, Π₁ down
│   ├─ Manipulation/         syntax manipulation, zero trunk consumers, reads at the tail
│   │   (Relabelling: the constant-domain kit; Renaming; Relativize)
│   └─ Reification/          host predicate ↔ object formula, with adequacy certificates
│       (Base, Combinators, Certified; the rest deferred, see ledger)
├─ ZF.lagda.md               Part 2: what a ZF(C) model is: isZFModel / isZFCModel records
│                            (single chapter; Encoding deferred, Coding returns under ZF/ at L2)
├─ V/                        Part 3: the cumulative hierarchy realizes ZF(C)
│   ├─ Hierarchy             the HIT V and its ZF structure 𝒮ᵥ
│   ├─ Smallness             the resizing interface
│   ├─ Coding, Satisfaction
│   └─ Model                 V ⊨ ZF; with set choice, V ⊨ ZFC
└─ L/                        Part 4: the constructible universe (the capstone)
    ├─ Constructible         isL as an inductive predicate
    ├─ Model                 ★ root: L ⊨ ZFC (LEM-parameterized; the Frontier is deleted, §11)
    ├─ Ordinal/, Hierarchy/  ordinals, L-stages
    ├─ Definability/         the Def operator
    ├─ Recursion/            the internalization theorem for L-recursion (L.Recursion)
    ├─ Coding/               formula and sequence coding
    ├─ Axioms/               per-axiom chapters: Basic, Separation, Replacement, Infinity, Power
    ├─ Condensation/         condensation and the power-set bound
    ├─ WellOrder/            the global well-order <L
    └─ Choice/               the choice set in L
```

Rationale, briefly: `Base/` collects everything that is about the host rather
than the mathematics, so the remaining parts read as book parts. Reification
nests under `FOL/` because it is logic machinery, not a peer subject of V and
L. The source's `Models/HITV` becomes `V/` because in a textbook V is a
subject, not "a model instance". `Landmarks` is the trophy case and gives
stable statement anchors.

Rename ledger (append-only; extend as porting proceeds; a re-cut after L3 adds
new rows rather than editing old ones):

| Source (fol-reification) | Bedrock | Notes |
|---|---|---|
| `Prelude`, `Truth`, `Classical` | `Base.Prelude`, `Base.Truth`, `Base.Classical` | `Classical` loses its postulate (D2); `LEM` stated per level, dividends take it explicitly; `lem→smallΩ` returns `Lift Bool ≃ hProp ℓ` directly (the source's Σ-packaging happens at the V-side `smallΩ` field, `[L1.5]`) |
| `Classical.lem→VResizing` | lands in `V/` with `[L1.5]` | re-layered: the V-side redemption belongs to Part 3; `Base.Classical` keeps `lem→smallΩ` / `lem→resize` |
| `Prelude._^_` | `FOL.Structure`, with `[L1.2]` | just-in-time (STYLE-agda §2): environments are assignments into a carrier, and the parameterized `FOL.Semantics` module cannot host a generic definition |
| `Prelude.absurd` | dropped (owner ruling, 2026-07-17) | the library's `Empty.rec*` serves: `embed = mapFo Empty.rec*`, and `embed-⊨` names it in its statement |
| `ZF.Structure.Transitive` | lands with `[L1.3]` (owner ruling, 2026-07-17) | just-in-time: its first consumer is the absoluteness chapter; deferred out of `FOL.Structure` |
| `FOL.Syntax.Closed` | `ParamFree` (owner ruling, 2026-07-17) | "closed" collides with closed formula = sentence; the standard set-theoretic name is parameter-free (constants are how parameters enter); zh 无参 |
| `FOL.Syntax.Sentence` | dropped (owner question, 2026-07-17) | zero consumers in the entire source development; where closed-ness matters the index says it (`ParamFree 0`), and the concept stays as prose |
| `FOL.Syntax` / `FOL.Semantics` / `FOL.Rename` | `FOL.Syntax` / `FOL.Semantics` / `FOL.Renaming` | |
| `Reification.{Base, Combinators, Graded, Absoluteness, Relativize}` | `FOL.Reification.*` | `[L1.3]`; `Absoluteness` restructured: unparameterized top + `Transitive` + inner `module Single`; downstream instantiates `Absoluteness.Single` |
| `Reification.Absoluteness2` | deferred (zero code consumers) | its route was superseded by the source's RAW reflection breakthrough; revisit at `[L2.2]` only if the reflection engine wants it |
| `Reification.Graph` | deferred to `[L2.2]` | sole consumer is `L.ModelACSep`; on landing, its private renaming copy is replaced by `FOL.Renaming` |
| `Reification.Characterization` | deferred (zero consumers) | `charac→/←` unconsumed; `RepPred` and `toFormula` deferred with it |
| `Reification.Universe` | deferred (zero consumers) | the Code universe scaffolded a coding layer that was built via parameter-free formulas instead |
| `Reification.Ceiling` | dropped as code | zero consumers; the compactness-ceiling argument becomes prose in the `ZF.Model` chapter (`[L1.4]`), where it explains why strong axioms are model fields |
| `Reification.Tactic` | deferred (zero consumers) | the source's entire L development hand-builds its representations |
| `Reification.Base.{ClassOf, Definable}` | deferred | parameterized definable classes; land with the geology part |
| `ZF.Structure` | `FOL.Structure` | re-cut `[L1.2]`: the bare {∈,≐}-structure is model-theory material and must be read before `FOL.Semantics`, which consumes it as a module parameter; `ZF/` keeps the axioms (`Model`) |
| `ZF.Model` | same name | |
| `Models.HITV.{Smallness, ZF, Def, Coding, Sat, Instance}` | `V.{Smallness, Model, Definability, Coding, Satisfaction}` | `Instance` folds into `V.Model`; `V.Hierarchy` introduces the HIT |
| `Examples.HITV` | folds into `V.Hierarchy` | the structure instance is part of the chapter |
| `L.Constructible` (`isL'`) | `L.Constructible` (`isL`) | primes dropped (D7) |
| `L.ModelZFCFinal`, `L.ModelZFC`, `L.ModelAC*` | `L.Model` + `L.Axioms.*` | |
| `L.{Hierarchy*, Stage*, Lset*, Rank*, OrdLadder}` | `L.Hierarchy.*` | |
| `L.{Ordinal, OrdinalLinear}` | `L.Ordinal.*` | |
| `L.{Def*, DefEnv, Defstep, Delta0Local}` | `L.Definability.*` | |
| `L.{Sat*, Tarski*, Realize, Reflect*}` | `L.Satisfaction.*` | |
| `L.{Code*, Formula*, VarCoding, SeqChar}` | `L.Coding.*` | |
| `L.{FFST*, Canon*, SatSetInL, SeqSetInL}` | `L.Closure.*` | |
| `L.{Condensation, PowerBound, CondReduce}` | `L.Condensation.*`, feeding `L.Axioms.Power` | |
| `L.{ConstructibleOrder, WellOrder2}` | `L.WellOrder.*` | |
| `L.{Cmp*, Depth*, Order*, Trace*, Coh*}` | `L.Recursion` + per-function instances | D12, 2026-07-25; delivered as `L.Recursion` and its instances |
| `L.{ChoiceSetInL2, Choice*}` | `L.Choice.*` | |
| `ZF.Model.foundation` | `regularity` | `[L1.4]`: aligns with the glossary's canonical term for the axiom; one axiom, one name |
| `ZF.Model.{hasSep, hasRepl, sep, num0, numS}` | `hasSeparation`, `hasReplacement`, `separate`, `numeral-zero`, `numeral-suc` | `[L1.4]`: registered-abbreviation rule (STYLE-agda §3); `Sep`/`Repl`/`num` are unregistered |
| `ZF.Model.ℕ̄` | `isNumeral` | `[L1.4]`: no invented symbols (STYLE-agda §0); the bar had no tradition to lean on |
| `ZF.Model.contrFromExt` | `setOf-unique` | `[L1.4]`: theorem names are kebab phrases; `Contr`/`Ext` unregistered |
| `ZF.Model.iter` | deferred to `[L1.5]` | just-in-time: zero consumers in this chapter; first consumer is the V-side chain assembly (`numeral = iterate ∅ _⁺` with two `refl` equations); rename to `iterate` on landing |
| `ZF.Encoding` | deferred (zero consumers) | `Class`/`Encoding` are consumed by nothing outside `Everything` in the source; the class concept appears as prose in `ZF.Model`; revisit if a consumer lands |
| `ZF.Coding` | deferred to `[L2.x]` | all consumers are the L-side coding stack (`L.{VarCoding, SubBridge, SatCert*, Defstep, CodeOrder, OrderGraph}`) and `V.Coding` |
| `Models.HITV.ZF.{extensionalV, foundationV}` | `V.Hierarchy.{extensionalV, regularityV}` | `[L1.5]`: structural facts of the HIT itself, re-homed to the chapter that introduces it; `foundationV` renamed per the regularity row |
| `Models.HITV.ZF.sepΔ₀` | `V.Smallness.separateΔ₀` | `[L1.5]`: the smallness chapter's capstone; `sepFromSmall`→`separateFromSmall` (abbreviation rule) |
| `Models.HITV.Smallness.{small-⋀, small-⋁, InnerSmall}` | deferred to `[L2.x]` | sole consumer is the Def operator (`Models.HITV.Def`), itself deferred |
| `Models.HITV.{Def, Sat, Coding}` | deferred to `[L2.x]` | consumers are the L definability/coding stack; the `sucV` lemmas `∈sucV-elim` (from `L.Ordinal`) and `∈sucV-inl`/`self∈sucV` (from `Models.HITV.Coding`) are re-homed to `V.Model` for the numeral pinning |
| `Models.HITV.ZF.NumeralSpec` | inlined as `V.Model.numeralV≡#` | `[L1.5]`: the field-form `numeral` (L1.4 row) removed the parameterization's purpose; `iter` (deferred at L1.4) is dropped entirely, `numeralV` is direct recursion |
| `Models.HITV.Instance.{fullSep, replImage, con!}` | `separateFull`, `replaceImage`, `one` | `[L1.5]`: abbreviation rule; `con!` was local and stays local |
| `V.Model.SetChoice` | `Base.Choice.SetChoice` | `[L1.9]`: re-homed and level-indexed (LEM-style packaging) so Diaconescu can be applied at two levels; owner ruling 2026-07-18: reads in Part 0, right after `Base.Classical` (the boundary's second interface) |
| `FOL.Reification.{Graded, Absoluteness, Relativize}` | `FOL.{Graded, Absoluteness, Relativize}` | owner ruling 2026-07-18: certificate, absoluteness, and relativization theory is FOL material parallel to `Renaming`; only the representation framework keeps the `Reification` namespace |
| `FOL.Reification.Graded.Certified`, `FOL.Reification.Absoluteness.Single.{Inner, transfer}` | `FOL.Reification.Certified` | extracted so `FOL.Graded` and `FOL.Absoluteness` genuinely do not inherit the representation line (they no longer import it); the framework's graded tier, zero consumers, closes the catalog |
| `ZF.Model` | `ZF` | owner ruling 2026-07-18: a one-module namespace read abrupt; the chapter is the part; `ZF.Coding` will nest under it when it returns at `[L2.x]` |
| `V.Definability` | `L.Definability` | owner ruling 2026-07-18: the Def operator is the L-construction step, matching the fixed skeleton's `L/Definability`; reading position unchanged (head of Part 4) |
| `TruthAlg`, `hPropAlg` | `TruthAlgebra`, `hPropAlgebra` | owner ruling 2026-07-18: `Alg` reads as "algorithm" and was an unregistered abbreviation (STYLE-agda §3); D7 naming hygiene, repo-wide mechanical rename |
| `V.Model.{VResizing, lem→VResizing}` | `Base.Classical.{Resizing, lem→Resizing}` | owner ruling 2026-07-18: the record is pure universe-level policy, the `V` was consumer-naming; promoted to the assumption-interface pattern D2/STYLE §1 always anticipated for resizing, level-indexed like `LEM`, minted beside the dividends it bundles |
| `Base.Classical.{Resizing (record), lem→Resizing, lem→resize, lem→smallΩ}` | `Impredicativity`, `lem→impredicativity`, `lem→resizing : … → Resizing ℓ`, `lem→hPropSmallness : … → HPropSmallness ℓ` | owner ruling 2026-07-18: the two instruments get named types (`Resizing` = the function type, `HPropSmallness` = the Σ), the packing is renamed for what it is, impredicativity |
| `V.Model.{V⊨ZF, VZFC.V⊨ZFC, V⊨ZFC-fromChoice}` | `VModel.V⊨ZF-impredicative`, (deleted), `V⊨ZFC` | owner ruling 2026-07-18: headline names carry the classical reading (`V⊨ZF` from LEM, `V⊨ZFC` from choice alone via Diaconescu); the exact-price form wears its hypothesis as a suffix; the two-hypothesis ZFC form is retired |
| `ZF.{ZFModel, ZFCModel}` | `isZFModel`, `isZFCModel` | owner ruling 2026-07-18: the records are predicates on a structure, and the names now read as such (`isZFModel 𝒮` = "𝒮 is a ZF model"), matching the library's is-prefix convention |
| landmark hypotheses `∀ {ℓ'} → LEM ℓ'` / `∀ {ℓ'} → SetChoice ℓ'` | single instances `LEM (ℓ-suc ℓ)` / `SetChoice (ℓ-suc ℓ)` | owner ruling 2026-07-18: both interfaces transfer downward (`lowerLEM`, `lowerSetChoice`, by lifting), so one instance at the model's truth level suffices; `lem→impredicativity` tightened likewise, and `L.Model`'s telescope takes `LEM (ℓ-suc ℓ)` |
| `FOL.Syntax.{mapTm, mapFo, ParamFree, embed}`, `FOL.Semantics.{⟦⟧-map, ⊨-map, embed-⊨}`, `FOL.Graded.{mapΔ₀, mapΣₙ, mapΠₙ}` | `FOL.Relabelling` | owner ruling 2026-07-18: the constant-domain toolkit has zero trunk consumers and gathers into one tail chapter, three altitudes (syntax, meaning, certificates); zh rendering re-cut: relabelling = 常量改名 and renaming = 改名 (the pair named by its objects) |
| `FOL.{Relabelling, Renaming, Relativize}` | `FOL.Manipulation.{Relabelling, Renaming, Relativize}` | owner ruling 2026-07-18: the three syntax-manipulation chapters cluster under one sub-namespace, mirroring `FOL.Reification`; reading order unchanged (the tail's tools section) |
| `FOL.Graded` | `FOL.LevyHierarchy` | owner ruling 2026-07-18: the term graded certificates (分级证书) collided with the adequacy certificates, so the Levy data are **witnesses** (见证) and the word certificate is reserved for adequacy; the zh rendering keeps the surname in Latin, giving Levy 层级 (with 列维 in the avoid list) |
| `Classical.lem→VResizing` | `V.Model.lem→VResizing` | `[L1.5]`: as planned in the L1.1 row; consumes `Base.Classical.{lem→resize, lem→smallΩ}` |
| `Models.HITV.Smallness.{small-⋀, small-⋁, InnerSmall}` | un-deferred into `V.Smallness` | `[L1.6]`: their consumer `Def` un-deferred; supersedes the L1.5 deferral row |
| `Models.HITV.Def` | `V.Definability` | `[L1.6]`: un-deferred (first consumer is `L.Constructible`); `abs-defSet` + `module Abs` deferred to `[L2.x]` (condensation-side); `DemoEmpty` and `ι-fst` dropped |
| `L.Rank.{_∈ᵗ_, ∈-induction, ∈-induction-compute}` | `V.Hierarchy.{∈-induction, ∈-induction-compute}` | `[L1.6]`: regularity's dividend, re-homed to the chapter that proves regularity; `_∈ᵗ_` already lives in `FOL.Structure`; `rank` and the rest of `L.Rank` at `[L2.x]` |
| `L.Ordinal.{IsOrd, isPropIsOrd}` | `L.Constructible` | `[L1.6]`: just-in-time, the class `isL` needs only the predicate; the rest of `L.Ordinal` at `[L2.x]` |
| `L.Hierarchy.{isTransV, isPropIsTransV, ∅/𝒟/⋃/∪/setUnion-trans, isLayer, layer-trans}` | `L.Constructible` | `[L1.6]`: folded into the one chapter; member-form `isL`, `layer∈L`, `layer⊆L`, `L-trans`, `L-directed`, `Lₙ`/`Lω` deferred to `[L2.x]` |
| `L.Constructible.{isL', isL'-trans}` | `isL`, `isL-trans` | `[L1.6]`: primes dropped per D7 (the Lset-form predicate IS the book's `isL`); `Lset` gains an `opaque` seal (conversion-blowup countermeasure, measured: `L.Frontier` 5 min → 1 s); `Lset-mono`, `Lset⊆𝒟ₒ`, `𝒟ₒ-inv`, `𝒟ₒ-intro`, `Lset→isL'`, `isL'→isL` deferred to `[L2.x]` |
| `FOL.Manipulation.Relabelling.ParamFree` | dropped (owner ruling, 2026-07-19) | like `Sentence`, the concept keeps its prose name (parameter-free formulas and zh 无参公式) but no code name: the type `Formula (⊥* {ℓ}) n` says it whole, and the two use sites (`embed`, `embed-⊨`) spell it out |
| `module V.Hierarchy where` + per-def `∀ {ℓ}` | `module V.Hierarchy {ℓ : Level} where` | owner ruling 2026-07-19, after an implicit-level audit: every one of the 15 downstream `𝒮ᵥ {ℓ}` pins sat inside an already-`{ℓ}`-parameterized chapter, so the level moves to the module telescope, L-side style; consumers import applied (`open import V.Hierarchy {ℓ}`) and use `𝒮ᵥ`, `∈-induction`, `regularityV` bare; `Landmarks` alone imports unapplied and keeps its explicit pins |
| `hPropAlgebra : ∀ {ℓ} → …` | `hPropAlgebra : ∀ ℓ → …` | owner ruling 2026-07-19, same audit: the implicit was never once inferred (every code use pinned it with braces), so the level becomes an honest explicit argument; ~25 use sites now read `hPropAlgebra ℓ` / `hPropAlgebra (ℓ-suc ℓ)` |
| `FOL.Structure.pathStructure` | dropped (owner ruling, 2026-07-19) | consumption audit found exactly one consumer (`𝒮ᵥ`; `𝒮ʟ` goes through `↾`), so the convenience constructor dissolves: `V.Hierarchy` writes the four-field record literal in place, and the structure chapter's propositional-side promise now points at the hierarchy chapter |
| bare witness/见证 as a standalone noun | anchored compounds only (owner ruling, 2026-07-19) | 见证 read like a coined proper name but nothing in the code bears it; the licensed forms are anchored compounds only, the Δ₀ witness with its zh mirror Δ₀ 见证 and the Lévy 见证 and 小性见证 analogues; verbal and anaphoric uses stay; ~17 prose sites re-anchored, and the leftover graded/分级 wording in `V.Smallness` retired with them |
| `FOL.Structure._∈ᵗ_` (anonymous module, prefix-applied `_∈ᵗ_ 𝒮 y x`) | `module hPropStructure {ℓ} (𝒮 : …)` with `open ZFStructure 𝒮 public` + `_∈ᵗ_` | owner ruling 2026-07-19: call sites should read `y ∈ᵗ x` after opening the structure; the record itself cannot host `∈ᵗ` (it is generic over the truth algebra, `Ω` abstract, no `⟨_⟩`), so the propositional side gets a named opening module that re-exports the fields; consumers swap `open ZFStructure` for `open hPropStructure` (ZF, V.Hierarchy, L.Constructible, L.Model) and `Transitive` opens it in a `where` |
| prefix application of mixfix operators | banned, STYLE §6 rule (owner ruling, 2026-07-19) | the `_∈ᵗ_ 𝒮 y x` episode generalized: operators are opened and written infix, two coexisting instances get `renaming` marks; repo sweep found the last offenders in `FOL.Manipulation.Relabelling` (`At._⊨_ ι γ φ` and `At.⟦_⟧` in `⟦⟧-map`/`⊨-map`/`embed-⊨`), now inner modules over `(f , ι)` with `_⊨∘_`/`⟦_⟧∘` and `_⊨∅_`; review-enforced (regex cannot tell application from operator-as-value) |
| `⟨ M x ⟩` (class applied to a point) | `x ∈ᶜ M` (owner ruling, 2026-07-19) | the library's `Cubical.Foundations.Powerset._∈_` re-exported through the Prelude hub, renamed `_∈ᶜ_` so the plain `_∈_` (the HIT membership in `V.Hierarchy`/`L.Model`) never clashes; class sites swept (`↾` carrier, `Transitive`, `SM` twice, `InnerSmall`, `DefOf.e/ι`, `accL`, `isContrΣ-fromCenter`); plain-hProp projections `⟨ P ⟩` are untouched |
| `FOL.Structure` | `FOL.ZFStructure` (owner ruling, 2026-07-19) | the chapter defines `ZFStructure` and its retinue, and the file now says so; all 15 importers follow |
| `ZF` (top-level chapter) | `FOL.ZFModel` (owner ruling, 2026-07-19) | the model specification is first-order logic's business, so the chapter joins `FOL/` beside `ZFStructure`; reading order unchanged (Part 2 between Absoluteness and V.Hierarchy); `V.Model`, `L.Frontier`, `L.Model`, `Landmarks`, and the catalog follow |
| `FOL.Absoluteness.Transitive` | `FOL.ZFStructure.Transitive` (owner ruling, 2026-07-19) | transitive classes are structure-side vocabulary (the definition needs only `∈ᵗ`/`∈ᶜ`), minted beside the memberships; `L.Definability`, `L.Constructible`, and `Certified` import from the new home, and `Certified` keeps only `module Single` from Absoluteness |
| `FOL.Structure._^_` | `FOL.Semantics._^_` (owner ruling, 2026-07-19) | environments belong to evaluation; the definition now sits inside the parameterized semantics module, so consumers take `_^_` from their applied instance (`open SemV`, `open Sem`, the `using` list of an applied import) and `Single` re-exports it for `Transfer` |
| `V.Smallness.isSmall` + `Base.Classical.{Resizing, HPropSmallness, Impredicativity}` | `Base.Impredicativity` (new chapter, owner ruling 2026-07-19) | `isSmall` moves to Part 0 so `Resizing ℓ` reads as "every `P : hProp (ℓ-suc ℓ)` is small"; the owner does not want `V.Smallness` to depend on the classical chapter, so the size vocabulary gets its own chapter between Truth and Classical, interfaces only; Classical keeps `LEM`, `lowerLEM`, and the three `lem→` redemptions (`resizeDec` restated over `isSmall`) |
| identity lambdas (`ι x = x`, `λ m → m`, `λ (x : S) → x`) | `id`, minted in `Base.Prelude` (owner ruling, 2026-07-20) | cubical has only the explicit-argument `idfun`, so per owner instruction the hub defines the book's one home-grown function; the seven canonical-interpretation sites (`ZFModel`, `V.Smallness` twice, `V.Model`, `L.Frontier`, `Absoluteness.Single`, `Certified.Transfer`) now read `open At id`-style |
| `module At {ℓc} {K} (ι : K → S)` | `module At {ℓc} (K : Type ℓc) (ι : K → S)` (owner ruling, 2026-07-20) | the constant domain is the load-bearing datum of an interpretation and every open now names it (`open At S id`, `SemV.At SM fst`, `open At (⊥* {ℓe}) …`), retiring the `{K = …}` pins at `Renaming` and `Single` |
| `L.{Cmp*, Depth*}` + `FFST*` / `L.{Order*, Trace*, Canon*, Env*}` / `L.{Sat*, Tarski*, Coh*}` | `L.Recursion` instances / staged/partial variants as once planned | `[L3.0.3]`, 2026-07-25: refined the row above into three tiers; the tier boundaries dissolved with `L.Recursion`, and the staged and partial variants were abandoned (L3.12, L3.13) |
| `L.Ordinal.{∅-ord, suc-ord, setUnion-ord, boundingOrd}` | `L.Ordinal` (new chapter) | `[L2.0]`: un-deferred from the L1.6 row that kept only `IsOrd`. Consumption-pruned to what the closure axioms need; `mem-ord`, the numeral and ω lemmas, `A∉A` and `ord-antisym` stay deferred to `[L2.1]` and later. **`L.OrdinalLinear` is not ported and may never be**: its `ord-tri` was the source's route to pairing, and `boundingOrd` replaces it constructively |
| `L.Constructible.{Lset-mono, 𝒟ₒ-intro, Lset⊆𝒟ₒ, Lset→isL}` | same names, back in `L.Constructible` | `[L2.0]`: un-deferred from the L1.6 deferral row, which named them for exactly this moment; `𝒟ₒ-inv` and `isL'→isL` stay deferred |
| `L.ModelAC.{extensional', foundation', hasEmpty', hasPair', hasUnion', con!, mere→isContr, isL'-directed, 𝒟ₒ→isL', ∅ₗ}` | `L.Axioms.Basic.{extensionalL, regularityL, hasEmptyL, hasPairL, hasUnionL, uniqueL, mere→uniqueL, isL-directed, 𝒟ₒ→isL, ∅ʟ}` | `[L2.0]`: the source's basic-axiom block becomes the first axiom chapter. `extensionalL` and `regularityL` **move here from `L.Model`** (they were proven there at `[L1.7]`): the uniqueness of every existence field flows from extensionality, so the chapter that needs it must own it, and `L.Model` becomes a pure assembly chapter |
| `L.ModelACNum.{pairₗ, unionₗ, sucₗ, pairₗ-fst, unionₗ-fst, suc-proj, numₗ, num-fst}`, `L.ModelZFC.{num0L, numSL}` | `L.Axioms.Infinity.{pairʟ, unionʟ, sucʟ, pairʟ-fst, unionʟ-fst, sucʟ-fst, numeralL, numeralL-fst, numeralL-zero, numeralL-suc}` | `[L2.1]`: the numeral chain becomes the second axiom chapter. Suffix convention settled here: `ʟ` marks an **object** of L (`∅ʟ`, `pairʟ`, mirroring `𝒮ʟ`), `-L` marks the L-instance of a **named model field** (`numeralL`, `hasEmptyL`), which is why the two coexist. `L.ModelACNum.{NumeralSpecL', ℕ̄ₗ, ω-specₗ', hasInfinityₗ'}` and all of `L.ModelACInfinity` wait for the collection step |
| `L.Ordinal.{mem-ord, A∉A, numeral-ord, #∈ω, numeral-mem, ω-mem-ord, ω-ord}` | `L.Ordinal.{mem-ord, ∈-irrefl, numeral-ord, #∈ω, numeral-mem, ω-mem-ord, ω-ord}` | `[L2.1]`: un-deferred as the collection step reaches them. `A∉A` renamed `∈-irrefl` (a theorem name is a kebab phrase, not a formula); `ord-antisym` stays deferred (no consumer), and it is asymmetry rather than antisymmetry if it ever lands |
| `L.Rank.{rank, rank-compute, rank-ord, rank-fix}` | `L.Rank` (new chapter) | `[L2.1]`: `_∈ᵗ_`, `∈-induction` and `∈-induction-compute` already live in `FOL.ZFStructure` / `V.Hierarchy` from `[L1.6]`, so the chapter is just the rank theory; `rank-mono` deferred (no consumer yet) |
| `L.OrdinalLinear.{⊆ᵇ, ⊆ᵇ-prop, extByBig, ¬sub→wit, ord-tri}` | `L.Ordinal.Linear.{_⊆ᵇ_, ⊆ᵇ-prop, ext-⊆ᵇ, ¬⊆ᵇ→witness, ord-tri}` | `[L2.1]`: **the first Bedrock chapter to take a `lem` parameter**, packaged per the L1.9 ruling as a single instance `LEM (ℓ-suc ℓ)` rather than the source's postulate. `extByBig`/`¬sub→wit` renamed to kebab phrases naming what they do |
| `L.FormulaBound.{BoundedTm, BoundedFo, BoundedTm-mono, BoundedFo-mono}` | `FOL.Manipulation.Bounding` (new chapter) | `[L3.0.4]`: minimal prerequisite for the theorem statement. Re-homed from `L/` to `FOL.Manipulation`, where it belongs by subject: it is relabelling when the map is only partial, and the source module is already pure syntax with no `Lset`/`defSet`/V dependency. `Relabel` (`liftFo`, `liftFo-correct`, `Δ₀-liftFo`) stays deferred to `[L2.2]`, where its consumer lands |
| `L.ChoiceSetInL.metaφ⟹isL'` | `L.Axioms.Basic.defSet→isL` | `[L3.0.4]`: the probe's checklist item 4. The source buries the closure engine in the choice chapter though the whole closure tower uses it; in Bedrock it is two lines over `[L2.0]` (`𝒟ₒ→isL` after `𝒟ₒ-intro`) and sits with the axioms that first exhibit the pattern |
| `Models.HITV.Def.Refine.{abs-defSet, module Abs}` | `L.Definability.Refine.{abs-defSet, module Abs}` | `[L2.1]`: un-deferred from the `[L1.6]` row that parked it as condensation-side; its first consumer is the ordinal formula of the collection step. Landing it executes the reading-order re-cut `[L1.4]` promised for `[L2.x]`: `FOL.Manipulation.{Relabelling, Bounding}` move from the tail to the Part 4 doorstep, since `L.Definability` is now their first consumer. `Renaming` and `Relativize` stay at the tail, still unconsumed |
| `L.{OrdLset, RankLset, OrdLsetSuc, OrdinalFormula}` | `L.Ordinal.Stages` (one chapter) | `[L2.1]`: four source modules merge, since they are one theorem read two ways (`ord∈Lset→∈` and `ord∈Lset-suc`) plus its two comparison lemmas and the Δ₀ predicate. `sucβ∈or≡` → `suc∈or≡`, `φ_ord` → `φ-ord` (kebab, no underscore). The source's per-branch helper discipline is kept verbatim and narrated: the conclusions are heavy membership types and inlining them in a case split normalizes them per branch |
| `L.ModelACInfinity.{ω∈L', ωₗ'}`, `L.ModelACNum.{ℕ̄ₗ, ω-specₗ', hasInfinityₗ'}` | `L.Axioms.Infinity.{ω∈L, ωʟ, isNumeralL, ω-specL, hasInfinityL}` | `[L2.1]`: the collection step joins the chain chapter rather than getting its own, and the chapter gains the `lem` parameter for it. `ℕ̄` → `isNumeralL` per the `[L1.4]` ruling that retired the invented bar |
| `ZF.Coding` | `FOL.Coding` | `[L3.3]`: un-deferred as L3 phase B opens. Namespace by subject, `FOL/`: it codes the object language into a structure, and it is generic over that structure (an injective pairing and an injection of the naturals, as module parameters), so it belongs beside `FOL.ZFStructure` rather than under the model chapter. **`⌜⌝-inj` is dropped by consumption audit** (`[L3.1]`, S9). **A consumer demanded it, 2026-07-27** (`[L3.0.1]`'s satisfaction table), and it returns as `[L3.22]`, not as `[L3.9]` work: that pointer named the wrong goal, and `[L3.9]` is abandoned with "a future need returns as a new code" |
| `Models.HITV.Coding` | `V.Coding` | `[L3.3]`: un-deferred; discharges `FOL.Coding`'s two parameters (`#-inj` through monotonicity and irreflexivity, `pr-inj` through the classification specifications). Its `A∉A` is dropped, superseded by `V.Hierarchy.∈-irrefl` |
| `L.Ordinal.∈-irrefl` | `V.Hierarchy.∈-irrefl` | `[L3.3]`: re-homed one chapter earlier, to the chapter that proves regularity, following the `[L1.6]` precedent for `∈-induction`. `V.Coding` needs it and must read before `L/`, so the L-side home was an inversion waiting to happen |
| `L.ConstructibleOrder.{SWO, IsLeast, isPropLeastOf, leastOf, Tri}` | `L.WellOrder.Base` | `[L3.14]`: un-deferred at owner request, ahead of `[L2.2]` which is its first consumer. `Tri` is re-minted here as a general three-way datatype (the source imports it from `FormulaOrder`, which is instance data and stays deferred). **The `lem` parameter moves from the module to `leastOf` alone**: the bundle and the uniqueness of least elements are constructive, so charging the whole chapter classically would have overstated the price. `ΣSWO` and the pullback stay deferred to `[L2.4]`, where the order they build is defined |
| `L.SatCertBase.{ClosedΣ, FixedFormulaSetΣ, FFSΣterm, codeΣ-mem, sgl-char, pair-char, prChar-fwd, prChar-bwd, sglAt, sglConAt, pairAt, pairConAt, prAt, tagAt}` | `L.Coding.Base` with `FixedFormulaSetΣ` → `allCodes`, `FFSΣterm` → `allCodesTerm`, `codeΣ-mem` → `code∈allCodes` | `[L3.14]`: the Δ₀ readers, the substrate 68 source modules consume. Names lose the provenance flavour (`FixedFormulaSetΣ` was arity-Σ bookkeeping, not a concept). The source's own lesson is kept as narration: the auxiliary predicates `SglOf`/`PairOf` are written in the shape the readers' satisfaction unfolds to, which is what makes each adequacy lemma one line instead of a second proof |
| `L.SatCertEnv.{envF, envV, envF-spec, lookupF-spec, memPairAt, sucAt, envA, consF, seqSet}` | `L.Coding.Environment.{env, envOf, env-spec, lookup-spec, memPairAt, sucAt, envIn, cons, seqSet}` | `[L3.14]`: the environment layer. The `F`/`V`/`A` suffixes were argument-shape bookkeeping rather than concepts and are dropped; `lookup-spec` keeps its name because functionality of the graph is the chapter's point |
| `L.SatCertLen.{∈#-elim, #∈#-elim}` | `L.Ordinal` | `[L3.14]`: the members of a numeral are exactly the smaller numerals. Re-homed from the certificate base to the ordinal chapter, where the numerals are introduced and the companion `numeral-mem` already lives; the source keeps it with its consumer. `mkFin`/`toℕ-mkFin` are **not** ported, having no consumer until `lenAt` lands |
| `L.SatCertLen.{FixedFormulaSetT, codeT-mem, FFSTterm, pairInAt, tagPairAt}` | `L.Coding.Tagged.{taggedCodes, taggedCode-mem, taggedCodesTerm, pairInAt, tagPairAt}` | `[L3.14]`: the arity-tagged code set and the binary-constructor shape matcher. Split out of `SatCertLen` because it is self-contained; the length guard is the rest of that source module and lands separately. `L.Coding.Base`'s singleton and pair membership lemmas were made public here, since `tagPairAt`'s backward direction has to exhibit the Kuratowski intermediates |
| `L.SatCertLen.{lenAt, lenAt-intro, lenAt-len, mkFin, toℕ-mkFin}` | `L.Coding.Length` | `[L3.14]`: the length guard, the rest of `SatCertLen` after the tagged-code half. `mkFin`/`toℕ-mkFin` return here, having been dropped by the sweep one goal earlier when `∈#-elim` moved to `L.Ordinal` without them; they are private to this chapter, which is their only consumer |
| `L.SatCertCons.{shiftPairAt, consAt}` | `L.Coding.Environment` | `[L3.14]`: environment extension, re-homed to the environment chapter whose `sucAt` they consume. `consAt`'s adequacy is stated against the encoded environment, which is the form the certificates hold |
| `L.SatCertCons.tripleInT` | `L.Coding.Entry` | `[L3.14]`: the certificate-entry form. **The source module is split by subject**: `tripleInT` is about how a certificate records an entry, while `shiftPairAt` and `consAt` are environment extension and belong with `L.Coding.Environment`, whose `sucAt` they consume. The source keeps all three together because they were built in one session |
| `L.Stage` | same name | `[L2.2]`: the earliest-stage function. `isLeastSt`/`Least`/`leastBelow`/`theLeast` become `isEarliest`/`Earliest`/`earliestBelow`/`theEarliest`, since "least" was ambiguous against `L.WellOrder.Base`'s `IsLeast` for an arbitrary predicate; here the order is fixed and the content is "earliest stage". `lem` is a module parameter per D2, replacing the source's `Classical` import |
| `L.FormulaBound.Relabel` | `FOL.Manipulation.Bounding.Relabel` | `[L2.2]`: the deferral recorded at `[L3.0.4]` is discharged; the module joins the chapter that defines the certificate it consumes. The source's `V` parameter is renamed `W`, since `V` is the hierarchy everywhere else in Bedrock and the parameter is an arbitrary common codomain |
| `L.ModelAC.{ReplQ, module SepAt}` | `L.Axioms.Separation.{ReplImage, module AtStage}` | `[L2.2]`: the Δ₀ separation and replacement engine. `φLeg`/`φKey`/`defKey` become `satBridge`/`carveSat`/`carveSatAnd`, `sealedDefSet` becomes `carve`, `sepBuild`/`replBuild` become `separateAt`/`replaceAt`, and `⊨transp` becomes `⊨-transport`: the source's names record how the proof was assembled, the new ones what each step says. The `opaque` seal on the carved set is kept and narrated |
| `Reification.Tactic` | revisited by S6 (§10) | 2026-07-25: the "deferred (zero consumers)" row above stands for the port itself, but the macro is the second-largest measured lever (4k to 6k); if S6 is taken up, the deferral is reversed under the goal code that takes it |

## 5. Working mechanisms (D2, D8)

**The Frontier record.** Root-first construction without postulates: `L.Frontier`
held one record whose fields were the *statements* of the not-yet-ported lemmas,
and the root theorem was proven from it. The record was the cut across the
dependency tree: each ported branch deleted its fields, the field list was the
live progress board, and `make check` stayed green at every commit. **The
Frontier is empty and deleted since `[L2.4]` (2026-07-31)**: `L.Model` takes
only `(lem : LEM (ℓ-suc ℓ))` and `L⊨ZFC` is unconditional in substance.

**Frontier re-cuts were normal (D11).** A field was not a contract with the
source's interface: when an L3 reduction changed the natural statement of a
lemma, the field was replaced (a *re-cut*), provided the root still typechecked
and `make check` stayed green. Re-cuts were recorded in the §11 field count.

**LEM as a parameter.** `Base.Classical` states the interface and derives its
consequences; the packaging validated by the L0.2 spike is
`LEM : ∀ ℓ → Type (ℓ-suc ℓ)` with classical-cone modules taking
`(lem : ∀ {ℓ} → LEM ℓ)` in their telescopes (STYLE-agda §1). The entire tree,
`Everything` included, is `--safe`.

**Reading order versus structure order** (owner ruling, 2026-07-18): the book
keeps two catalogs. The **reading catalog** is `Everything.lagda.md`, the
landing page: import order = reading order, hand-maintained. The **structure
catalog** is the namespace tree, derived automatically and never
hand-maintained. Namespace membership is decided by subject, reading position
by first consumption; the two are independent.

**Construction order versus reading order.** These are deliberately different.
The build proceeds root-first (the Frontier shrank over time); the book reads
foundations-first (`Base → FOL → ZF → V → L → Landmarks`, fixed by the
`Everything` import order). Neither order constrains the other.

**The named hypothesis, and its limit** (standing since `[L3.31]`). When a
chapter cannot discharge an obligation, the obligation is stated as a named
module hypothesis and the chapter ships conditional on it, with the hypothesis
recorded in §11. This kept the tree green through a long campaign. Its limit
was learned expensively: **a named hypothesis has no defence when the
hypothesis is false**, so the truth of a residue's target is now priced before
its proof, at the chain's ROOT, against the in-repo corpus (LESSONS D-10, and
the risk row in §9).

**Probes and gates** (standing since `[L3.30]`, sharpened 2026-08-04). Before
heavy or hard-to-reverse work, the load-bearing assumption is verified cheaply:
a D-1 probe builds the smallest decisive miniature, reports GO or NO-GO with a
price extrapolation, and is thrown away. A probe prices only OUR departures
(what the Cubical HIT setting costs us), never feasibility the literature or
the delivered tree already settles. Since 2026-08-04 every wide unprobed
component is expected to name its gate at estimate time (§6.2), and a stop
report is a full deliverable: the two most valuable results of this campaign
were a refutation and a stop.

**Orchestration.** Batches are written by delegated agents against pinned
briefs, archived in `_build/briefs/`; the orchestrator audits every return
(report, then code, then an independent typecheck and the linters), wires
`Everything.lagda.md` (agents never touch it), and commits with the goal code.
Agents never commit and never push. Concurrency and heap caps are governed by
LESSONS C-12.

## 6. Route tree (D9)

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
   cluster, a spike, a review, a piece of legislation). Individual lemmas and
   modules are artifacts hanging under a code, not codes themselves.
5. **Status vocabulary:** PLANNED, ACTIVE, DONE, PARKED (viable but shelved,
   revivable), SUPERSEDED (points to successor), ABANDONED (with reason).
   Status changes are dated and updated in place; history lives in git.
6. **Bookkeeping:** register a code in §11 *before* starting the work; update
   the §11 row in the same commit that changes a goal's status. New codes
   discovered mid-work are registered immediately, not backfilled.

### 6.1 The tree

**[L0] Legislation (standing track; never closes, see T1).** The initial set
L0.0 to L0.2 gates L1; later L0.x items are opened whenever porting uncovers an
un-legislated situation. Gate for L1: L0.0 to L0.3 DONE and approved by the
owner.

- **[L0.0]** `dev/STYLE-agda.md`, initial edition: OPTIONS policy
  (`--cubical --safe --guardedness` everywhere), assumption policy (D2;
  Frontier as the only debt form while it existed), naming rules (D7), the
  notation table, record-versus-data and universe-polymorphism conventions,
  annotation rules for performance idioms (each `opaque` seal or
  explicitly-spelled implicit carries a marker comment), and the master chapter
  template. Rules may be marked **provisional** (T1) and hardened later.
  **DONE 2026-07-16.**
- **[L0.1]** First glossary batch in `dev/glossary.toml`: constructible
  universe, cumulative hierarchy, condensation, absoluteness, reification,
  adequacy, relative consistency, well-order, and companions. **DONE
  2026-07-16.**
- **[L0.2]** LEM parameterization spike (gates D2): parameterize one or two
  representative heavy `L` modules over LEM, measure cold-check time against
  the source baseline, project the full-cone cost, record the verdict in §11.
  **DONE 2026-07-16, verdict green** (details in §11).
- **[L0.3]** `scripts/lint-agda.py`: a code-side linter for the masters, wired
  into `make check` and the pre-commit hook. Flagship check: **import
  necessity**; companions: the exact OPTIONS header, the using-list discipline,
  and the forbidden-construct ban (postulate, TERMINATING pragmas, holes).
  **DONE 2026-07-16.**
- **[L0.4]** Two-catalog doctrine (owner ruling, 2026-07-18): legislate the
  reading-catalog / structure-catalog split of §5. **DONE 2026-07-18.**
- **[L0.5]** Register `Ord` as an abbreviation in `STYLE-agda` §3 (opened
  2026-07-25 during `[L2.0]`). **DONE 2026-07-25.**
- **[L0.6+]** Reserved for mid-course legislation, opened as discovered.

**[L1] Root and trunk skeleton.** All L1 ports carry full textbook prose (en +
zh). Gate for L2: `make check` green; the owner reads the trunk end to end as a
book and signs off the tone. `[L3.0.3]`, the paper-level probe of the L3 big
lever, opens at this same boundary and runs alongside L2; it is
source-reading only, so it neither blocks nor is blocked by this gate.

- **[L1.0]** Lay the §4 skeleton, rewrite `src/README.md`, add
  `-WnoUnsupportedIndexedMatch` to `bedrock.agda-lib`, pin the source commit in
  §11. **DONE 2026-07-16.**
- **[L1.1]** Port `Base/` (Prelude, Truth, Classical-as-interface). **DONE
  2026-07-16.**
- **[L1.2]** Port `FOL/` core (Syntax, Semantics, Renaming). **DONE 2026-07-17.**
- **[L1.3]** Port `FOL/Reification/`. **DONE 2026-07-18.**
- **[L1.4]** Port `ZF/` (Model; Encoding/Coding as needed), fold in the Ceiling
  prose (compactness explains why strong axioms are model fields), and execute
  the **reading-order re-cut** (owner ruling, 2026-07-18): Part 1 slims to
  Syntax, Structure, Semantics; the reification chapters move to read right
  after `ZF.Model`; `Renaming` and `Relativize` move to the Part 4 doorstep at
  `[L2.x]`. Namespaces stay `FOL.*`; only reading order and ToC placement move.
  **DONE 2026-07-18.**
- **[L1.5]** Port `V/` (Hierarchy with the structure instance, Smallness,
  Definability, Coding, Satisfaction, Model). **DONE 2026-07-18.**
- **[L1.6]** Port `L.Constructible` (isL and the minimal machinery to define
  `𝒮ʟ`). **DONE 2026-07-18.**
- **[L1.7]** Write `L.Frontier` and the root `L.Model` statement. **DONE
  2026-07-18** (Frontier: 11 fields).
- **[L1.8]** Create `Landmarks`; set the `Everything` reading order. **DONE
  2026-07-18** (owner rulings: Landmarks reads **first**; the zero-consumer
  chapters read **last**; reification namespace re-cut the same day).
- **[L1.9]** Diaconescu and the single-hypothesis ZFC instance (owner ruling,
  2026-07-18): `Base.Choice` (`SetChoice` level-indexed like `LEM`;
  `choice→lem` via set quotients and effectivity), `V.Model.V⊨ZFC-fromChoice`,
  and a fourth landmark. The "two independent assumptions" prose is corrected
  to the one-way statement: LEM does not prove choice; choice proves LEM
  levelwise, but `SetChoice ℓ` cannot reach `LEM (ℓ-suc ℓ)`. **DONE
  2026-07-18.**

**[L2] The axiom branches, in pedagogical order.** Each branch descends until
it hits a technical cluster flagged for reduction review. Per-branch exit:
check green, prose complete (en + zh), glossary updated, the branch's Frontier
fields deleted or explicitly re-cut.

- **[L2.0]** Basic axioms (extensionality, foundation, empty, pair, union);
  source `L.ModelAC`. The warm-up. **DONE 2026-07-25** (Frontier 11 → 8; no
  `lem`, the whole goal is constructive).
- **[L2.1]** Infinity; source `L.ModelACNum`, `L.ModelACInfinity`, the numeral
  chain. **DONE 2026-07-25** (Frontier 8 → 4; the chain is constructive, the
  collection step is not: it needs `ω ∈ L`, hence `ord∈Lset-suc`, hence
  trichotomy).
- **[L2.2]** Separation and Replacement; source `L.ModelACSep`,
  `L.ModelACReduce`, the reflection engine. The methodological core: this is
  where reification pays off and gets its full narrative. **DONE 2026-07-25**
  (Frontier 4 → 2; six source chapters became three; `ReflectN` never becomes a
  chapter).
- **[L2.3]** Power via Condensation; source `L.Condensation`, `L.CondReduce`,
  `L.PowerBound`. **Re-scoped 2026-07-27 to "Power by bounding the
  constructible subsets"; DONE 2026-07-27** (79 lines of Agda against the
  source's ≈185 across three chapters; Condensation is not used; Frontier 2 →
  1; LEM (ℓ-suc ℓ) alone).
- **[L2.4]** Well-order and Choice trunk; source `L.ConstructibleOrder`,
  `L.WellOrder2`, `L.ChoiceSetInL2`. **DONE 2026-07-31** (Frontier empty and
  deleted; the global order is not needed and was struck; about 5,900 lines
  across thirteen chapters against an audit band of 1,900 to 3,150; details in
  §11).

**[L3] The technical layer, big lever first (D12), then reduction-first (D3).**
Each measured reduction lever of §2.1 carries its own code. Execution runs in
four phases; the sequence below is authoritative, the numbers are not (§6.0
rule 2).

> **A, design** (before and during L2): `[L3.0.3]` subsumption probe, **before
> L2** (delivered 2026-07-25) → `[L3.0.4]` theorem statement and clause-bundle
> design, after `[L2.2]`.
>
> **B, substrate**: `[L3.1]` sweep (standing from here on) → `[L3.2]` `reify!`
> → `[L3.3]` coding cluster.
>
> **C, machinery** (re-evaluated 2026-07-25 after `[L2.2]`): `[L3.0.5]` finite
> families → `[L3.11]` clause bundle → `[L3.0.1]` tier-1 proof of concept →
> `[L3.0.2]` verdict → green: `[L3.12]` and `[L3.13]` / red: `[L3.4]`. The
> grounds for the re-evaluation: stage 7 is `[L3.0.5]` and `[L3.2]` leaves the
> critical path; `[L3.11]`'s de-risk was paid by accident in `[L2.2]`
> (`L.ReflectFo`'s twelve-clause `Answers` tree checks in about two seconds);
> and `[L3.0.4]` §3's `reads : List (Σ[ t ∈ S ] ⟨ isL t ⟩)` carries the exact
> `L.Axioms.Full` hazard, certificates sealed where built.
>
> **D, ports**: `[L3.5]` `[L3.6]` `[L3.7]`, as instantiations on a green
> verdict → `[L3.10]` re-layering. `[L3.8]` and `[L3.9]` are opportunistic.

**Schedule change (owner ruling, 2026-07-25): phase B opens before `[L2.2]`.**
L2 is suspended after `[L2.1]` and L3's substrate starts now; `[L2.2]` to
`[L2.4]` resume afterwards. Verified before adopting: the coding cluster's
dependency cone reaches none of `L.ModelACSep`, `L.Reflect*`,
`L.Condensation` or `L.ChoiceSetInL2`; the cone is 44 modules, of which 17 and
about 4.9k lines are unported, and its one surprise is `L.ConstructibleOrder`,
which is the strict well-order vocabulary both branches need.

**Why all of phase C precedes any cluster port.** The measured tier boundaries
cut *across* the cluster boundaries, so porting a cluster before knowing which
of its members are theorem instances would re-create the T5 problem the probe
was run to avoid.

Two cautions on reading the sequence. The `L3.x` numbers ran in execution order
when the branch was renumbered on 2026-07-25 under the §6.0 rule 3 carve-out
(map in §11), but the carve-out is spent, so goals registered since take the
next free number and execute in the middle: read the phases, not the digits.

- **[L3.0]** **Internalization theorem for L-recursion (the big lever, D12;
  S5).** Target statement, working form: from a *step specification* (a tag
  alphabet, a Δ₀ clause matrix over coded arguments, and a well-founded
  measure) derive (i) that the induced recursion's trace is a set of L, (ii) a
  certificate relation sound and complete against the meta-level recursion,
  and (iii) uniqueness of the certified value. **DONE 2026-07-28 without
  exception**: the theorem delivered at 99 lines (`L.Recursion`), verdict
  green; the instance half (satisfaction) closed the same day. Record in §11.
  - **[L3.0.0]** SUPERSEDED 2026-07-25 by `[L3.0.3]` and `[L3.0.4]`. Never
    started; no content lost.
  - **[L3.0.3]** **Subsumption probe, source-reading only, opens before L2.**
    Does one step specification subsume `Cmp*` and `Depth*`? Deliverables: the
    fits table and a **required-interface checklist**. **This is where the
    cheap kill signal lives.** Owner gate. **DONE 2026-07-25, verdict amber.**
  - **[L3.0.4]** **Theorem statement in Bedrock's idiom.** Prerequisite:
    `[L2.2]`. Deliverables: the specification signature, a projected line
    budget, and the list of §4 chapters it would displace. Owner gate. **DONE
    2026-07-25.**
  - **[L3.0.5]** **Finite families at a stage.** DONE 2026-07-25. `finSetL`:
    a finite family of members of `Lset σ` is a set of `L`, by finite
    disjunction. 60 lines.
  - **[L3.0.1]** **Proof of concept (tier 1, the constant-table theorem).**
    Run the reference instance and the theorem in one loop, then `Cmp` as the
    stress case. Measure lines and cold-check per §7. **Kill criteria, agreed
    in advance:** the theorem fails to reach two instances; or an instance is
    not materially smaller than the source pipeline; or §7.6's budget is
    breached and the WORKLOG §5 playbook does not clear it. **DONE 2026-07-28**
    (re-pointed 2026-07-26 to satisfaction as the instance; kill criteria
    applied to instances only).
  - **[L3.0.2]** **Verdict and rollout ruling.** Green: `[L3.12]`/`[L3.13]`
    open and `[L3.5]`-`[L3.7]` are re-stated as instantiation goals. Red:
    `[L3.12]`/`[L3.13]` stay closed and `[L3.4]` opens. **DONE 2026-07-26,
    green** (memo `memos/L3.0.2-verdict.md`).

  Scheduling and safety: `[L3.0.3]` opened ahead of L2 because it is the only
  research-risk item on the critical path; the Frontier is what makes a
  research gamble affordable, and a red verdict costs the attempt and nothing
  else. One risk the split does not remove: a memo written before any axiom
  branch has been ported in Bedrock is written by a porter still fluent mainly
  in the source's idiom, which is the D6 failure mode; `[L3.0.3]` is scoped to
  survive it.

- **[L3.1]** **Transition-layer sweep (S9), standing.** Ahead of each cluster
  port, run the consumption audit over that cluster and drop what the source's
  own later strata superseded. Measured headroom 2k to 3k. Success criterion:
  every cluster memo opens with a drop list naming each dropped module and the
  audit finding that justifies it. Standing goal, no single completion date; it
  closes with `[L3.10]`. **Drop list EXECUTED 2026-07-29: −529 Agda lines**
  (§11).
- **[L3.2]** **`reify!` industrialization (S6). CLOSED, REJECTED 2026-07-27 on
  measurement** (§11). DORMANT re-open trigger recorded in §11.
- **[L3.3]** SUPERSEDED 2026-07-25 by `[L3.14]`, after a consumption
  re-measurement (§11). The goal was scoped as the source's whole `Code*` /
  `Formula*` / `VarCoding` / `SeqChar` cluster, about 4.9k lines; measuring
  consumers showed that only the Δ₀ code readers are substrate.
- **[L3.14]** **Coding substrate: the Δ₀ code readers.** Source `SatCertBase`
  (68 consumers), `SatCertEnv` (44), `SatCertLen` (46), `SatCertCons` (13);
  about 910 lines. **DONE 2026-07-25** (seven chapters; §11).
- **[L3.11]** **Per-tag clause bundle (S10).** Registered 2026-07-25 on the
  probe's finding that the twelve tags are traversed **five times per
  instance**. Deliverable: a `ClauseBundle` record. **ABANDONED 2026-07-27 on
  a measurement** (§11).
- **[L3.12]** **Stage-indexed internalization theorem (S11), tier 2.**
  Registered 2026-07-25; covers `Order*`, `Trace*`, `Canon*`, `Env*`, 11,386
  lines. Gate: green `[L3.0.2]`. **ABANDONED 2026-07-27** (§11).
- **[L3.13]** **Partial-certificate variant (S12), tier 3.** Registered
  2026-07-25 for `Sat*` / `Tarski*` / `Coh*` (10,706 lines). Gate: green
  `[L3.0.2]`. **ABANDONED 2026-07-27** (§11).
- **[L3.4]** **Scaffolding parameterization (S3), conditional.** Fallback
  consolidation. Gate: opens only on a red `[L3.0.2]`. **ABANDONED 2026-07-27**
  (the condition is impossible, not unmet).
- **[L3.5]** Satisfaction cluster (source `Sat*`, `Tarski*`, `Realize`,
  `Reflect*` remnants). **DISSOLVED as a cluster 2026-07-27** (§11).
- **[L3.6]** Closure cluster (source `FFST*`, `Canon*`, `SatSetInL`,
  `SeqSetInL`). **DISSOLVED 2026-07-27** (§11).
- **[L3.7]** Well-order certificate cluster (source `Cmp*`, `Depth*`,
  `Order*`, `Trace*`, `Coh*`); the largest at 42.3k source lines (§2.1).
  **CLOSED, SCOPE RE-ATTRIBUTED 2026-07-28** (§11).
- **[L3.8]** **Dispatch-grid generation (S8), opportunistic.** **ABANDONED
  2026-07-27, premise spent** (§11).
- **[L3.9]** **Transport and cast solver (S7), lowest priority.** Spike first,
  roll out only on evidence. A failed shape check closes the goal ABANDONED.
  **ABANDONED 2026-07-27** (§11).
- **[L3.10]** Post-reduction **re-layering review** of the whole `L/` subtree
  (T2). **PLANNED.** Boundary against `[L3.28]` ruled 2026-07-31: split by
  **purpose, not by file**; `[L3.28]` owns quantity, `[L3.10]` owns
  arrangement that serves no compression; `[L3.28]` runs first. `[L3.1]`
  closes with this row.

**[L4] Convergence.** Runs after `[L3.32]`'s wing, bridge and retirement
surgery land, on the tree that survives them.

- **[L4.0]** Empty the Frontier, delete `L.Frontier`, drop the parameter; the
  unconditional `L⊨ZFC` lands. **DONE in substance** by `[L2.4]`: the Frontier
  is empty and deleted and the root is unconditional. The row stays as the
  record of a goal delivered under another code.
- **[L4.1]** Whole-book **harmonization pass** (T4): re-read end to end, fix
  foreshadowing and cross-references, run the zh/ja cross-check for term drift,
  reconcile prose with the `[L3.32]` interface changes. **PLANNED, and GATED
  BEHIND `[L8.2]` by D21**: this is the prose phase, and it does not open until
  the owner has ruled on the consolidation report. Its
  scope has grown with the campaign: the retirement surgery deletes whole
  chapters, so the pass now includes re-reading the book's spine for the
  chapters that vanish and for the corrected identification story (`Matching`
  is recorded as false, and the delivered direction is `isJ → isL`).
- **[L4.2]** Update `Landmarks`, the README trio, and the Charter status;
  retrospective. **PLANNED.** The Charter status line must state the endpoint
  as `L ⊨ ZFC ∧ L ⊨ GCH`, not the AC-only waypoint.
- **[L4.3]** ~~Seed a GCH successor plan~~ **ABSORBED 2026-08-03.** The GCH
  endpoint moved INTO the active campaign (§0), so no successor document is
  seeded and this row closes. The narrative beyond GCH is `[L6]`, not a
  successor to this file.

**[L5] Build and site infrastructure (parallel workstream, not a sequential
phase).** Must be in place before L2 scale-up; constraints in §7 apply from the
first ported module regardless.

- **[L5.0]** Port the build machinery: dependency-manifest generator, parallel
  per-module checking, per-module heap caps, shared config; wire into `make
  check` per the §7 trust model. **PLANNED.**
- **[L5.1]** Split `make check` into a fast gate (changed cone) and a full
  gate. **PLANNED** (the three named gate defects belong here, §11).
- **[L5.2]** CI strategy: affected cone on PRs, full check nightly, `.agdai`
  interface caching. **PLANNED.**
- **[L5.3]** Site pipeline load test at about 200 pages. **PLANNED.**

**[L6] The narrative master plan (owner-ordered 2026-08-04: the "L5+" outline;
the meeting at bedrock).** The book's title concept is its terminus, declared
here as the standing narrative frame under which all later milestones and all
asset valuations execute.

- **The arc.** The AC/GCH trophy is not a warm-up: it is the construction of
  the future bedrock object. Set-theoretic geology and inner model theory are
  one mountain seen from two faces, and the book walks from the first face to
  the meeting point: geology supplies the equivalence structure and its
  invariants over the generic multiverse (grounds, the mantle, the bedrock);
  inner model theory supplies the canonical representatives (the normal
  forms). The meeting theorems all share one sentence shape: the abstract
  invariant, computed, EQUALS the canonical object.
- **The meeting map, three levels.** Level 1, in this book's reach: **"L is a
  bedrock"**, the second trophy: L has no proper ground (constructibility is
  absolute between transitive class models with the same ordinals, so a
  ground W of L satisfies L = L-of-W contained in W contained in L), hence
  the mantle of every set-generic extension of L is L. Its ingredients are
  exactly: the trophy's L; the GCH wing's W2 + W5 (the uniform level formula
  and condensation, double-consumed as the absoluteness kit); the forcing
  entry over the HIT V (names, evaluation, genericity); the geology
  definitions with Laver-Woodin ground-model definability (whose technical
  core, the approximation and cover properties, is the first appearance of
  inner-model-style arguments inside geology). Level 2, mid-range: the
  invariants dictionary: forcing-invariance of the mantle, the Ground Axiom,
  and HOD as the second dig. Level 3, the far horizon, named and not
  planned: Usuba's bedrock theorem (strongly compact implies the mantle is a
  ground), the HOD dichotomy, and the Varsovian program (the mantle of a
  canonical mouse is again fine-structural): every time geology's invariant
  is computed in a canonical situation, the answer speaks fine structure,
  which is the rud trunk's deep legacy.
- **The phase spine.** Phase 1: the trophy, under whichever fork ruling the
  owner issues; the fork table is read with the added criterion of what
  feeds W2/W5 and the forcing-facing satisfaction machinery. Phase 2: the
  forcing entry ticket over the HIT V (the `[GLp]` POC prices it). Phase 3:
  the geology kit (grounds, Laver-Woodin, the mantle, invariance). Phase 4:
  the meeting theorem "L is a bedrock" as the second trophy. The far horizon
  stays named in prose and out of the budget.
- **The asset re-coloring rule.** From this section on, every asset is
  valued against BOTH trophies, not one: the internalization cone's future
  is the forcing semantics (the forcing relation's definability is a
  satisfaction-internalization problem in a new costume); the rud trunk's
  future is condensation/GCH now and fine structure at the horizon; W2/W5
  are double-consumed. The owner-ordered re-valuation of all standing assets
  under this frame executes when `[GLp]` returns, followed by the balanced
  route candidates (long-term economics of the frame against short-term
  economics of the trophy).
- **The novelty claim.** Per the L3.30 formalization landscape sweep,
  set-theoretic geology exists in no major proof assistant's library; the
  claim is re-verified at Phase 3 kickoff before being printed anywhere
  public.

**[L7] The endpoint promotion and the archive's completion (D20).** The
archive REGIME is in force now and its infrastructure is built at the first
archival, under `[L3.32]`; what waits for the endpoint is the promotion and the
final sweep.

- **[L7.0]** Archive `main` and promote the working branch. The current `main`
  (the internalization archive) is tagged and archived; the branch carrying the
  delivered endpoint becomes `main`. Done the same day the endpoint lands,
  before any tidying, so what the world sees is the delivered book. **PLANNED.**
- **[L7.1]** The final archival sweep: every chapter retired during the
  campaign that has not yet moved is moved, and the pre-regime deletions are
  entered in the registry against their deletion commits. **PLANNED.**
- **[L7.2]** Verify the exclusions end to end on the finished tree: the Agda
  gate, both linters, the marker and glossary checkers and the site build must
  all be structurally blind to `archive/`, and `reuse lint` must still cover it.
  A red archive at this point is not a defect; an archive that any gate TRIES to
  check is. **PLANNED.**
- **[L7.3]** Final pass on `archive/README.md`: the constraints in full, what a
  reader should expect (code that was correct when written, against interfaces
  that have since moved), and how to revive a module (copy out, never edit in
  place). **PLANNED.**
- **[L7.4]** Final pass on `dev/ARCHIVE.md`: every entry carries what it is, why
  it was archived with the ruling and date, its last-green commit, its measured
  size, and its revival condition; entries whose condition is already moot are
  closed. **PLANNED.**

**[L8] Consolidation, and the gate before prose (D21).** Opens when `[L7]`
closes. Nothing in `[L4]` runs before `[L8.2]` has been ruled.

- **[L8.0]** The foundation refactor, at `[L3.32-T8]`'s scale and character,
  re-run against the post-archival tree: an audit that prices candidates in
  both calibers with a named future consumer and a stop-line each, a rejected
  list with reasons, then one batch executing what the owner accepts. The
  post-archival tree is a different subject from today's: the retirements will
  have removed most of the consumers whose existence justified parts of the
  base, so candidates rejected in 2026-08-04 may qualify then and must be
  re-examined rather than inherited. **PLANNED.**
- **[L8.1]** A line-by-line polish pass over the **whole** tree, not a sample.
  Exports frozen, the law book binding, the measured polish classes as the
  starting catalog, and per-file before-and-after measurement. The two polish
  batches this campaign ran are the rate anchors, and their residues (the named
  perf hotspots that survived them) are inputs, not leftovers. **PLANNED.**
- **[L8.2]** **THE GATE.** Report to the owner: what the refactor changed, what
  the polish measured, what the tree now weighs, and what remains. The prose
  polish phase does not open until the owner has ruled on this report, and the
  owner will add further code-shaping work at that point. Nothing downstream
  may be started in anticipation. **PLANNED.**

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

## 7. Build constraints (D10, binding)

Imported from the source's Makefile trust model (`../fol-reification/Makefile`,
WORKLOG §8.1) and adapted to Bedrock's rules:

1. **The trusted gate is one invocation.** `agda src/Everything.lagda.md`
   remains the single certificate: one call, obviously correct, never
   parallelized. Since Bedrock's whole tree is `--safe` and `Everything`
   imports all of it, this one invocation is the entire trust base.
2. **Parallelism is a warm-up layer, outside the trust base.** The parallel
   per-module build exists only to populate `.agdai` interfaces fast; the
   `Everything` invocation then revalidates hashes cheaply. Make's dependency
   edges are scheduling hints: a wrong edge can cause wasted work or a false
   red, never a false green.
3. **The one false-green mode is audited away.** A module missing from
   `Everything`'s import list is unchecked by the gate. An audit script
   asserts, on every check, that the import closure of `Everything` equals the
   set of `src/**/*.lagda.md` files.
4. **The dependency manifest is generated, never committed.** `gen-deps` runs
   in under a second, so the manifest is regenerated into `_build/` on every
   check and consumed from there.
5. **Cold-check wall-clock is a tracked budget.** Baseline numbers are recorded
   in §11 at every gate. Working ceiling: full cold check at or under **15
   minutes at `-j4`** on the reference machine (upstream proves the same
   mathematics fits in about 8.5). A merge that breaches the ceiling is
   blocked until triaged.
6. **Per-module discipline.** Per-module heap caps (the source settled on
   `-M6g`; revisit against measurements). A module exceeding roughly **120
   seconds** cold or its heap cap is a conversion blowup: triage with the
   source's WORKLOG §5 playbook before merging, and annotate any surviving
   countermeasure per the L0.0 rules.
7. **Serial fallback stays available.** A serial full-check target (single
   process, wide heap cap) is kept for dispute arbitration and for reproducing
   races, as in the source.
8. **Reference machine and `-jN` defaults are documented in the build
   config**, so budget numbers are comparable across time.

## 8. Process tensions and their resolutions (D11)

Known internal tensions in the L0 to L5 plan, each with its designed relief
valve. The common principle: **the plan legislates the mechanism of change,
not the impossibility of change.**

- **T1: Legislation is partly hindsight.** Some style rules can only be
  discovered by porting. Relief: L0 is a standing track; STYLE-agda rules may
  be marked *provisional*; a porter hitting an un-legislated situation opens a
  new L0.x item (or asks the owner) rather than improvising silently.
- **T2: Skeleton finality versus post-reduction insight.** Relief: only the
  part level of §4 is fixed; everything below is provisional until the
  dedicated L3.10 re-layering review; renames land as appended ledger rows.
- **T3: Pedagogical order versus dependency order.** Relief: the Frontier
  mechanism (§5) decouples them; a branch was portable the moment its cut was
  stated.
- **T4: Early prose versus whole-book coherence.** Relief: per-merge prose must
  be complete and correct, but foreshadowing and cross-references may be
  deferred; the L4.1 harmonization pass sweeps the whole book.
- **T5: L3 reduction versus already-narrated interfaces.** Relief: every L3
  memo carries an impact list on ported chapters; Frontier re-cuts (§5) are
  the sanctioned mechanism; prose residue is caught by L4.1.
- **T6: Performance scaffolding versus readability.** Relief: countermeasures
  stay in the code, annotated per L0.0 so narration can skip them; §7 budgets
  decide when a countermeasure is load-bearing (measure, do not guess).

## 9. Risks and mitigations

| Risk | Mitigation |
|---|---|
| LEM parameterization regresses check-time badly | L0.2 spike gates D2 before any mass port; documented fallback exists but needs a new owner ruling. |
| Conversion blowups resurface during rename/refactor | §7 budgets and per-module discipline; the source WORKLOG §5 playbook is the triage reference; countermeasures stay annotated and visible; the measured laws are in `dev/LESSONS.md`. |
| CI wall-clock grows past budget | §7 ceiling plus L5.1/L5.2 split gates and nightly full check; upstream M2.7 numbers bound the worst case. |
| Translation debt accumulates | A master merges only with en + zh complete (enforced by the marker checker); ja stays pre-supported. |
| Simplification scope creep | §10 register: every simplification candidate gets its own verify-then-decide entry; the default is a faithful port. |
| The thin endpoint margin closes | The naive projection passes the owner's 25k line, but the pass depends on new spend staying inside its band. Every gate that tightens the TOP of a band is margin work, not luxury (§0); the W7 cardinal gate and the two retirement gates run before the chapters they price. |
| Census-class terms re-price upward | The measured pattern of this campaign: down-corrections land on terms a probe can reach, up-corrections land on terms only a census could reach. Mitigation is the standing probe discipline (LESSONS D-1, D-6, D-10): every wide unprobed term gets its D-1 gate designed with the estimate and run before funding. |
| A residue's target turns out to be false | Happened once, expensively (the per-level identification, classically false and refuted in the literature). Mitigation now standing: the chain ROOT is truth-checked against the in-repo corpus before any link is priced (LESSONS D-10, appended 2026-08-03), and a delegated corpus dossier is mandatory for any residue stated as a named classical lemma. |
| Geology is funded before its sources are in hand | The in-repo corpus contains zero geology sources (`_build/l3.31-glprobe-report.md`). Fetching Fuchs-Hamkins-Reitz, Usuba and Laver/Woodin is a mandatory gate before any geology funding, alongside the mantle size-wall design recon. |
| Statement drift toward unqualified "Con(ZFC)" | D1 fixes the framing; the root chapter and Landmarks are the canonical wording; glossary pins the translated terms. |
| Process drift (ad-hoc naming, unregistered work) | §6.0 rules: no work without a code, no backfilled registration; §11 updated in the same commit as the status change. |

## 10. Candidate simplification register

Each entry needs its own cheap verification and owner decision before
deviating; an accepted candidate is executed under the goal code of the cluster
it affects. S1 to S12 are the port-era register (the default there was a
faithful port of the source). S13 onward are the current era's, where the
default is instead D16's: price the ideal form alongside the standing one. The
foundation-layer candidates below come from the 2026-08-04 audit
(`_build/l3.32-t6-report.md`), which priced each with three numbers: what the
rewrite costs, what it compresses immediately, and what it saves the
CONTINUATION, each with a named future consumer.

| # | Candidate | Verification needed | Status |
|---|-----------|---------------------|--------|
| S1 | Specialize the truth-algebra abstraction (`TruthAlg`) to plain hProp | Check whether any non-hProp instance is load-bearing in the source | verified 2026-07-16: **rejected**. The record is a law-free operation signature, definitionally transparent on `hPropAlg` (record ι), and is the designed seam for the forcing-stage Boolean instance; only one instance exists today, but the Charter targets forcing. Ported faithfully in `[L1.1]`. |
| S2 | Merge `Absoluteness2` into `Absoluteness` | Diff the two modules' roles | resolved 2026-07-18: **deferred entirely** instead of merged; `Absoluteness2` has zero code consumers (its route superseded by the source's RAW reflection breakthrough). Ledger row added. |
| S3 | Unify the five graph-certificate families under shared combinators | Executes as `[L3.4]` | resolved 2026-07-25: **conditional fallback behind S5.** The §2.1 measurement puts shared combinators at 3k to 5k and shows the families diverge precisely where the mathematics is (soundness segments overlap 4% to 9% after renaming, scaffolding 50% to 86%). Opens only on a red `[L3.0.2]`; a green verdict absorbs it (it did: `[L3.4]` ABANDONED 2026-07-27). |
| S4 | Fold `ZF.Encoding` / `ZF.Coding` into their consumers | Map their import sites | open |
| S5 | General internalization theorem for L-recursion | Executes as `[L3.0]`: paper-level subsumption of `Cmp*` and `Depth*` first, then a two-instance proof of concept with kill criteria | **adopted as the primary route** (D12, 2026-07-25); delivered as `L.Recursion` at 99 lines; verdict green 2026-07-26, instance half done 2026-07-28. |
| S6 | Industrialize the source's `reify!` macro over the L-side formula groups | Executes as `[L3.2]` | **closed, rejected 2026-07-27 on measurement** (§11): net +9 lines over the two modules rated best, +25% to +33% on `L.Coding.Model`; both D13 tests fail; re-open trigger: a congruence family written by hand a third time with no combinator available, or the traversal-dense share passing 20%. |
| S7 | Tactic-generated transport and cast steps | Executes as `[L3.9]`, spike first | open, lowest priority, as registered; the goal `[L3.9]` itself is ABANDONED 2026-07-27 (Bedrock has 456 `subst`/`cong`/`transport` sites, not 3,300; a future need returns as a new code). |
| S8 | Generate the mechanical dispatch grids instead of writing their clauses | Executes as `[L3.8]` | open as registered; the goal is ABANDONED 2026-07-27 (premise spent: the grids the lever was for are gone or unneeded). |
| S9 | Drop the source's superseded transition layers ahead of each cluster port | Executes as `[L3.1]`, standing | open; 2k to 3k. Executed 2026-07-29: −529 lines (§11). |
| S10 | Declare each of the twelve tags once instead of five times | Executes as `[L3.11]` | registered 2026-07-25; **abandoned 2026-07-27 on a measurement**: the only instance answered no, the clauses factor through two shared frames. |
| S11 | Stage-indexed internalization theorem for transfinite recursions | Executes as `[L3.12]` | registered 2026-07-25; **abandoned 2026-07-27**: the complexity boundary dissolved. |
| S12 | Partial-certificate variant for the non-constant tables | Executes as `[L3.13]` | registered 2026-07-25; **abandoned 2026-07-27**: its subject was retired by the `[L3.0.1]` design change. |
| S13 | Publicize the eight `V.Coding` pair helpers (delete `private`) | none needed beyond a grep for re-derivations by the FACT (C-14) | **ACCEPTED 2026-08-04, executing under `[L3.32-T8]`.** Cost 1 line, blast radius zero, deletes a measured third copy and saves 8 to 16 lines in every future pair-consuming consumer (forcing names, geology). |
| S14 | A `defSet` computation table in `L.Definability`, replacing four `defSet≡` proofs in `L/Axioms/Basic` | its own D-1 gate: the table plus the four re-derivations must stay under 57 lines (60 percent of the 94 replaced), and no entry may need resizing or LEM | **ACCEPTED 2026-08-04, executing under `[L3.32-T8]`.** Write about 50, compress 25 to 40 now, save 50 to 110 in the continuation (the axiom re-points, the face's adequacy, W7's formula count, geology's class carriers). The one structural rewrite in the audit with probe support. |
| S15 | A `V.Presentation` kit (`member`, `fiber`, injectivity, the membership conversion) | the kit must stay under 30 lines and every re-derivation must drop to two lines or fewer, with no change to any existing transport direction | **ACCEPTED 2026-08-04, executing under `[L3.32-T8]`.** Write about 20, compress 20 to 35 now (about 25 inline fiber sites become one-liners), save 40 to 60 later (W5's bounding, W7's hull, geology's carriers). |
| S16 | An axiom-frame kit in `FOL.ZFModel` (the description-elimination equation and uniqueness aliases) | the two named re-derivations must shrink from 14 lines to six or fewer | **ACCEPTED 2026-08-04, executing under `[L3.32-T8]`.** Write about 20, compress 20 to 35 now, save 20 to 50 later. |
| S17 | A syntax-walk calculus (`FOL.Fold`: the formula algebra plus one generic fusion lemma), ADDITIVE only | its D-1 gate: three delivered walk-plus-correctness pairs re-expressed as instances inside 60 probe lines, with definitional behaviour unchanged on a concrete sample | **GATED 2026-08-04, probe running under `[L3.32-T8]`.** Zero immediate compression by design, but the largest continuation number in the audit: 450 to 1,050 lines, aimed at the forcing era's satisfaction recursion collapsing to one algebra. The in-place retrofit of the five existing manipulation modules is REJECTED (26 masters of blast radius, load-bearing reduction behaviour, and a measured counter-instance where a stored decomposition walled at 12 GB while the inline form ran in one second). |
| S18 | Collapse `FOL.Coding`'s double encoding into one tag-and-payload decomposition | its D-1 gate: the injectivity lemma must not cost more than its current 35 lines, and no export may change name or behaviour | **ACCEPTED BUT DEFERRED 2026-08-04 by owner ruling: it waits behind the wing.** Write about 40, compress 50 to 70, but blast radius 2 and its second master consumer retires under D18, so the standing continuation value is thin. The audit rates it the weakest accepted candidate and notes that dropping it loses nothing. |

## 11. MASTER status table (live)

One row per goal code; update the row in the same commit that changes the
status (§6.0 rule 6). Bookkeeping lines follow the table.

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
| L3.32 | The L-trophy build (the ruled configuration) | **RULED AND ACTIVE 2026-08-04** by D18. The Def tower keeps the trophy; the wing rides a fresh-generic Sigma-1 face; the reindexed bridge lands at wing tail as a corollary; choice re-homes through it; the internalization cone, the choice tree, the Goedel trees and the coded cluster retire. Wave 1 (the R4 corrective stop, the face probe, the choice re-home probe, the retirement design recon, the W7 scoping) has returned; wave 2 builds the face chapter, then W2, then W3 and W5 in parallel, then the bridge, the re-home, the retirement surgery and W7. **THE TASK REGISTER (`[L3.32-T1]` onward; T9 to T12 were BACKFILLED 2026-08-04 in breach of the section 6.0 rule that registration precedes work, and the breach is recorded here rather than tidied away):** T1 the R4 corrective stop, DELIVERED and committed; T2 the fresh-generic face probe, GO on both arms; T3 the choice re-home probe, GO; T4 the retirement design recon, which found the retirement only partial and provoked D17; T5 the W7 scoping, which re-priced W7 up and designed its gate; T6 the foundation audit, six candidates priced and eight rejected; T7 the wholesale-retirement recon under D17, which converted the provoking case and found the Realize cone; T8 the foundation kit batch (S13 to S16 plus S17's gate), RUNNING; **T9 the W7 cardinal gate, RETURNED RED, and the red is the useful answer** (`_build/l3.32-t9-report.md`, probe orchestrator-reverified green, zero postulates): **T1 the count is GREEN on the mathematics** (the exact-shape injection from a carrier's unary formulas into a shape-plus-tuple sum exists constructively at the delivered syntax, with decode and reconstruction, so D-10's target-truth question is answered YES) **but costs 448 lines by itself, over the gate's whole 400-line stop-line**: T5's "the count runs on the delivered formula type" is confirmed as true and refuted as free. **T2 the product bound WALLS**, and it walls in D-10's named killer class: the kappa-times-omega core reduces honestly to the ORDINAL PAIRING theorem, for which the tree has no raw material at all (no ordinal arithmetic, no order-type or rank theory; the absence was grep-verified by the orchestrator, whose only hit was the probe itself). The probe proves the conditional core, so the missing piece is exactly the pairing chapter, priced at 250-400 lines against a named delivered comparable. **T3 the payoff is RED as a consequence and adds a piece T5 never itemized**: a shape-count, an injection from constant-free formulas of each arity into the carrier's index, which is a natural-number-valued code where every coding in the tree is set-valued. **BAND CONSEQUENCE, in T5's own terms: the cardinal row re-prices to 0.75-1.30k naive and W7 calibrated to roughly 3.90-7.35k**, and the count's formulation needs bijection and initial-ordinal theory rather than the surjection theory, which enlarges the definitional layer further. One conversion wall was hit and cured by stating the count generically, which is the I-4 family's own prescription and left the statement stronger than the target; **THE LEDGER AFTER THE WHOLE TASK SET, recomputed from the LT baseline with every delta shown (2026-08-04): standing 11,254** (12,737 plus D19's 1,989 for keeping the step-into-L content, minus the same 1,989 when D17 converted it to a rewrite, minus 1,289 for the Realize cone as T11 measured it, minus 141 for the DefInJ and SatTable re-type, minus 67 for the Base re-home, plus 14 for the foundation kit), **new spend 6.49-13.11k naive** (LT's 4.51-10.11 plus 0.45-0.70 for W7's cardinal row, 0.08-0.20 for W3, 1.20-1.70 for the fresh step-into-L chapter, and 0.25-0.40 for the newly-named ordinal pairing chapter), **so the endpoint is 17.74-24.36k naive, still inside the owner's 25k line with 0.64k of margin at the pessimistic corner.** The conversions D17 forced bought back more than D19 cost, and W7 and W3's rises ate part of it. **THE OPEN QUESTION SUBMITTED TO THE OWNER: W7 has now re-priced up twice with its remaining pieces unprobed, and T9's red named a new self-contained entity, the ordinal pairing chapter, which the cardinal chapter cannot proceed without.** **OWNER RULED 2026-08-04: option B, build the pairing chapter now with the scope gate riding alongside.** Registered BEFORE dispatch this time: **`[T16]`** the ordinal pairing chapter, real code under `L/Ordinal/`, 250-400 estimated against the delivered `L.Ordinal.Stages` at 241, delivering the injective pairing on an infinite ordinal's index that T9's product bound reduced to and that cardinal arithmetic will consume again in the geology and fine-structure eras; **`[T17]`** the shape-count probe, the piece T9 found un-itemized (constant-free formulas of each arity injecting into the index, a natural-number-valued code where every coding in this tree is set-valued), so that it cannot become W7's third up-price; **`[T18]`** the scope gate, read-only: what cardinal vocabulary does the internal GCH sentence MINIMALLY need, and in particular whether its direction is servable by the surjection form alone, which would let the bijection and initial-ordinal theory defer to the geology era. The orchestrator's recommendation as submitted: B with C as its gate, and A rejected because this campaign's measured pattern is that up-corrections land on survey-class terms and W7 is currently survey-class throughout. **`[T18]` RETURNED AND REFUTED THE SCOPING HOPE (2026-08-04, `_build/l3.32-t18-report.md`): the surjection-only branch is dead and NO W7 row shrinks.** The bijection and initial-ordinal layer is forced, not deferrable: the collapse chain and the below-the-successor step are bijection-shaped, and the count's own statement needs the relation-form predicates. W7 stands at 1.35-2.60k naive (the cardinal row rising again to 0.80-1.45k as the definitional layer is itemized rather than left vague) and 3.90-7.35k calibrated. **But the gate paid for itself in two other currencies.** First, it CONFIRMS option B independently of T9: the pairing theorem is consumed by the tower-induction's limit case at the successor cardinal AND again by fine structure's own level-cardinality theorem, so it is substrate rather than a W7 expense. Second, it delivers TWO BINDING FORMULATION RULINGS for the cardinal chapter, each of which prevents a rebuild: **(a) define equinumerosity as the existence of a BIJECTION, not as injections both ways**, since the latter turns every equality into a per-consumer Cantor-Bernstein obligation and drags the general theorem into W7 anyway; **(b) build the predicates GENERALLY (equinumerosity, cardinal, successor cardinal, as formulas with their certificates) rather than as GCH-specific shims**, because fine structure's own cardinal notion and geology's internal cardinality function are EXTENSIONS of exactly these, so the layer is reused rather than rewritten. What genuinely defers is named: the aleph sequence, the cardinality function, general Cantor-Bernstein, general cardinal arithmetic, and cofinality. **The trap avoided is stated plainly: a surjection-only or raw-injection cardinality would have forced every later consumer to re-derive the bijection and initial-ordinal facts from scratch, which is the rebuild D16 exists to prevent.** **`[T17]` RETURNED GO (2026-08-04, `_build/l3.32-t17-report.md`, probe orchestrator-reverified green, zero postulates, LEM-free): the shape-count is a SUBROUTINE, not a chapter.** D-10's question is answered true at the delivered syntax (the formula and term types are plain inductive families and the constant domain is empty, so each arity's constant-free formulas form a finite-branching tree over a finite index and are countable), and the proof transplants the tree's own codes-determine-formulas machinery from sets to naturals. The only genuinely new raw material is an injective pairing on the naturals at about 25 lines, which this tree never shipped because its own pairing is the set-theoretic one. It delivers exactly the signature the cardinal payoff consumes, composed with the delivered numerals' injection, typechecked in file. **So W7's third up-price is now MEASURED at about 200 lines, inside T9's re-priced band rather than on top of it, and the cardinal row's dominant remaining wall is unchanged: the ordinal pairing chapter.** One development failure, cured: an I-4-family unification trap where a defined pairing's implicit arguments would not solve, which the delivered set pairing dodges only because it is abstract. **`[T16]` DELIVERED THE CHAPTER AND REDUCED THE GAP RATHER THAN CLOSING IT (2026-08-04, committed `76994a2`, orchestrator-reverified green, 369 lines, no postulate and no partial recursion):** the canonical well-ordering of a product is built with all four laws certified, and the order-type collapse is proved BIJECTIVE rather than merely injective, which is the hard half. **But the pairing the cardinal step consumes is delivered CONDITIONAL on one named bound, the square law (an infinite ordinal's product is equinumerous with it), whose textbook proof runs through ordinal arithmetic this tree does not have; the chapter states it as a hypothesis rather than postulating it and prices it at 300-460 naive / 500-950 calibrated.** So the pairing's true cost is 669-829 naive against the 250-400 the gate estimated, which is **W7's FOURTH consecutive up-price** (T5's re-scope, T9's red, T18's itemization, and now this). **THE LEDGER AT THE END OF THE TASK SET: standing 11,254, new spend 6.96-13.69k, endpoint 18.21-24.94k naive, centre about 21.6k, and the margin at the pessimistic corner is 0.06k, which is to say the corner now touches the owner's 25k line.** The corner requires every term to land at its top at once, and the centre is comfortable; but this campaign's measured pattern is that up-corrections land on survey-class terms, and W7 remains survey-class in its remaining pieces. Recorded for the owner as a decision point rather than resolved by the orchestrator. **OWNER RULED 2026-08-04: gate every block from here, which is now D22.** The remaining blocks and their paired gates, registered before dispatch: **`[T19]`** W3's own gate, already designed by T14, run before the order chapters are funded; **`[T20]`** the level formula as the FACE'S FIRST REAL INSTANTIATION, which doubles as the measurement of the face chapter's batch 2 (if one instantiation is cheap the other two are, and if it is not, the wing's largest row is wrong today); **`[T21]`** the square law's decisive core, the ordinal-arithmetic lemma the pairing chapter left named, since it is now the cardinal row's dominant wall and has consumers in both later eras. Each is a probe, each is aimed at its block's widest unmeasured term, and each reports what its block should be funded at. **`[T20]` RETURNED GO, AND D22 PAID ON ITS FIRST APPLICATION** (2026-08-04, `_build/l3.32-t20-report.md`, probe orchestrator-reverified green, zero postulates, LEM-free): the face's four-entry telescope is filled at the REAL tower, with all three adequacies carrying real content and the consumer's two-way read-off obtained. The measurement that matters is the split: **111 per-consumer lines against a ONE-TIME 197-line shared kit** (the pair atoms with their decodes and the component recovery, written once generic in the carrier and reused by all three consumers), so the face's genericity is not just cheap to write but cheap to CONSUME. The Def-step entry collapses to a 17-line theorem at the real tower. **FUNDING, measured rather than surveyed: W2's row at 150-250 naive (about 195-410 calibrated), the L cone's missing pair engine at 193 lines charged ONCE across all consumers, and the face chapter's batch 2 at about 650-950 naive (845-1,490 calibrated)** against the census's W1-fresh 1,185-2,300, which the measurement now places at its floor rather than its middle. One I-5 wall was hit and cured: a completed range-decode branch with an inferred truncation type ran past five minutes, and the named typed version checks in about five seconds, the same cure then applied preemptively to its sibling. **`[T21]` RETURNED WITH A CHEAPER ROUTE AND A DEARER PRICE** (2026-08-04, `_build/l3.32-t21-report.md`, probe orchestrator-reverified green, zero postulates): D-10 was answered in the direction the brief asked for, not the textbook one. The route this tree can carry is the INITIAL-SEGMENT route, which needs **no ordinal arithmetic at all**, rather than the textbook's addition and multiplication as set recursions with a doubling lemma, none of which exist here. Its decisive step is measured green: the containment, the descent (the collapse is equinumerous with its initial segment, whose surjective half runs through the delivered least-witness machinery, which absorbs a truncated union membership into a proposition-valued goal), the collapse-boundedness by well-founded recursion, and the composition yielding the pairing chapter's exact bound. **The successor case disappears entirely**, since the reduction to the initial ordinal lands on a limit. **But the price rises: the order core ALONE measures 308 lines against T16's 300-460 estimate for the whole theorem, so the square law funds at 480-610 naive (centre about 545) / 0.9-1.2k calibrated**, with its remaining pieces named and separately priced (the initial-ordinal layer, the finite base, the wrapper and transfer). Two walls recorded: the truncation wall on the naive descent, cured by the least-witness pattern the re-home probe established, and the membership-heavy union steps at the opaque seal, which run about four times the pairing chapter's per-line cost and are reported rather than cured. **`[T19]` RETURNED RED, WITH THE MECHANISM MEASURED RATHER THAN GUESSED** (2026-08-04, `_build/l3.32-t19-report.md`, probe orchestrator-reverified green): the order formula's CONTENT is real and the statement layer it would consume checks instantly, but **every materializing step is a wall**: forming a member's index at the concrete tower's presentation exhausts an 8 GB heap, the key-shape case analysis normalizes the least-element search and hangs even with a trivial body at BOTH the concrete and the abstract carrier, and comparison types carrying a concrete ordinal hang. The recorded P-d class was never even reached, because the satisfaction cannot be stated; these are the other P-series class, the one the retiring cone's seals exist for, which is the clearest possible evidence that W3's cost is a DESIGN problem (sealing discipline) rather than a line-count problem. The order-as-an-element target is red structurally, and T14's own P2 fork is CONFIRMED to fire. **No row moves to the cheaper class, so W3 funds at 1.1-2.7k naive / 3.3-7.9k calibrated.** **THE LEDGER AFTER ALL THREE GATES: standing 11,254, new spend 7.22-14.24k, endpoint 18.48-25.49k naive with the centre at 21.99k. The pessimistic corner now BREACHES the owner's 25k line by 0.49k.** The three gates moved money in three directions, which is exactly what D22 was ruled to produce: the face's batch 2 fell from a surveyed 1,185-2,300 to a measured 650-950, the square law rose from 300-460 to 480-610, and W3 rose from 480-950 to 1.1-2.7k. The centre remains comfortably inside the line; the corner does not, and W3's red says the way to recover it is a design pass on the order's sealing rather than more lines. **OWNER RULED 2026-08-04: run that design pass. `[T22]` registered and dispatched**, a sealing DESIGN probe rather than a build: T19's three walled shapes reproduced exactly and attacked with the law book's named cures (the variable-level restricted-carrier statement for the heap event, the written-type helper and the birth-site seal with opaque-unfolding reads and the proposition-valued absorption for the case analysis, and the variable-ordinal restatement for the comparison types), each arm measured before and after rather than reported as a verdict word, with a 240 second per-arm abort. The arm that decides everything is the second, because it hangs at the ABSTRACT carrier too and therefore is not an instantiation artifact: if it is curable, W3's cost is a design problem and the pessimistic corner returns inside the line; if it is not, the corner's breach is real and the question becomes scope or the line itself. **`[T22]` RETURNED: ALL THREE ARMS BROKEN, AND THE HONEST READING IS THAT THE RISK FELL WHILE THE PRICE DID NOT** (2026-08-04, `_build/l3.32-t22-report.md`, probe orchestrator-reverified green). Arm 2, the one that decided it, reproduced exactly (60 second aborts at BOTH carriers, resident memory climbing through 8 GB and reaching 10.5 GB on a longer run) and then broke under all three named cures at about 0.9 seconds each, a factor of sixty: the abstract hang was the case construction RE-ELABORATING the least-element search in every branch, not the search itself. Arms 1 and 3 did not reproduce at all under pinned implicits and warm caches, so T19's heap event was an elaboration-context artifact rather than a statement property, which is itself a lesson now filed. **But the funding barely moves: naive stays at 1.1-2.7k and calibrated falls only from 3.3-7.9k to about 3.2-7.8k, because only the clause-content statement layer reclassifies while the leastness content, the family table and the confirmed rider all stand.** So the endpoint's naive band is unchanged at 18.48-25.49k, centre 21.99k, **and the pessimistic corner still breaches the owner's line by 0.49k**. What changed is the KIND of risk, not the amount of money: W3 is now a build with a measured first-formulation prescription (never case on a transparent least-witness term, seal consumer aliases at their birth site with unfolding reads beside them, state at the small index with presentation implicits pinned, take ordinals as variables, re-home truncated searches into proposition-valued goals, write every branch type reaching a comparison or a search) rather than a wall of unknown depth. **The orchestrator's reading for the owner: the corner is a PROJECTION whose top is still made of survey-class terms, and the D22 measurements so far have moved such terms in both directions with the single largest move being downward (the face's batch 2, from a surveyed 1,185-2,300 to a measured 650-950). Continuing to gate is therefore the cheapest way to find out whether the corner is real, and no scope or line decision is forced today.** **OWNER RULED 2026-08-04: continue gating the remaining survey-class terms. Registered before dispatch: `[T23]` the bridge's non-face rows (the closed-form index tower, the reshaped induction's successor clause, and the limit assembly, measured as a DELTA against the delivered reduction rather than as an absolute); `[T24]` the choice re-home's carve half, the residual `[T3]` named and did not build, which is the only part keeping that leg at the coarse class; `[T25]` the bridge's successor hypothesis re-stated on the fresh face, never measured, and carrying a second question that decides whether the coded cluster's retirement is clean: does the re-stated object still need the coded machinery for anything, or do the face and the unconditional switch supply it. **TWO BUILDS DISPATCHED ALONGSIDE THEM, both funded because their gates passed (D22): `[T26]` the shared pair kit, the one-time 197-line half of the face's batch 2 that all three consumers charge once, built before any consumer so none of them pays it twice; `[T27]` the count layer, productionizing the two green probes (the count with its decode and reconstruction, and the shape-count with the natural-number pairing this tree never had) as the cardinal chapter's combinatorial first block, under T18's binding design rulings. A THIRD build is queued for the orchestrator rather than dispatched: the Realize cone's retirement, which T11 measured green at 1,289 lines and which is the first real application of the archive regime, is held until `[T23]` clears, because stripping the switch chapter under a probe that reads its consumers would break that probe's typechecks. **`[T25]` RETURNED RED ON THE ASSUMPTION IT WAS SENT TO TEST, WHICH IS THE GATE WORKING** (2026-08-04, `_build/l3.32-t25-report.md`, probe orchestrator-reverified green): the re-stated successor hypothesis is NOT supplied by the fresh face plus the unconditional switch. Two mechanized reasons: the face's slice is BOUNDED IN ITS CARRIER, so the initial-segment story cannot reach the definable power's membership at the next level, which is precisely the instance this campaign already refuted; and an exact covering needs a CODE SET AS A MEMBER, which the face cannot build (defining the code as the definable set is circular) and which only the coded machinery supplies. **So the coded cluster's retirement is NOT clean: the 3,761-line figure shrinks to 2,382 (the step-into-L chapter and the base block), while CodeSet and CodePred, 1,379 lines, STAY while the successor step consumes the code set as a member.** The interface itself is cheap and measured (52 lines, funding 50-70 naive, inside its booking); it is the WITNESSES that stay survey-class, at 0.40-0.80k naive and unmoved to the cheaper class, now joined by the newly surfaced covering term. **LEDGER: standing rises to 12,633 and the endpoint to 19.85-26.87k naive, centre 23.36k, with the pessimistic corner 1.87k over the owner's line.** The corner was being carried by the clean retirement, which is exactly what this gate was sent to test. **THE ORCHESTRATOR'S NEXT MOVE UNDER D17, not yet dispatched: a keep of 1,379 lines justified by a survivor consuming them is the shape D17 forbids taking at face value, so the ideal-form price of the code-set-as-a-member must be measured before the keep is accepted; T25 named the widest unmeasured term for exactly this, the relation's membership at the one-block index.** **OWNER CORRECTION 2026-08-04, and it was a discipline correction, not a preference: the orchestrator surfaced the keep as a fork to be ruled and asked whether to measure it, when D17 already answers it. If a module cannot retire cleanly, the move is to REWRITE it from actual need and retire the old code wholesale; measuring whether to keep is not the question. `[T28]` dispatched accordingly, as a BUILD rather than a survey: the minimal fresh supplier of what the successor step consumes, standing on the delivered engine, so the 1,379 lines retire whole.** Its thesis, to be tested by building rather than argued: the incumbent is large because it proves the code set's membership at EVERY arity over a two-limit telescope, while the successor step needs it at ONE index, which is a limit by construction, at the arity its consumer actually uses; the key that makes this possible is the kernel's own finding that at a limit index the codes are ALREADY members. Stop-line 500 lines, with the honest alternative named in the brief: if the fresh module cannot supply the consumer inside it, the incumbent's size is justified and the keep genuinely wins. **`[T28]` RETURNED WITH THE THESIS REFUTED BY THE BUILD, WHICH IS D17 WORKING RATHER THAN FAILING** (2026-08-04, `_build/l3.32-t28-report.md`): writing the minimal supplier from the consumer's actual need showed the need IS the incumbent's core, not a sliver of it. The obligation is three items (the code map, the covering set with both membership directions, and the set's membership at the corrected index); the fresh module delivers the first two and the containment outright in 167 green lines, and reduces the third to one named residue **which is exactly the object the incumbent's own chapter spends itself supplying**. Measured section by section, the arity and two-limit generality the fresh module drops accounts for at most 30-45 of the incumbent's 1,186 lines, since the telescope is never cased on and the twelve clauses are identical at one arity; the rest is the object-language predicate, needed identically at one arity and one index. **So the honest fresh supplier is about 1,305-1,320 lines against the incumbent's 1,379, roughly two and a half times the stop-line, and the answer is KEEP: justified by content, not by inertia.** The 167 built lines are NOT committed to the tree, since they restate at one arity what the kept chapter proves at every arity; they are preserved at `_build/templates/CodeSetBlock.lagda.md` as the template for the SatTable re-typing, whose target shape they state precisely, and they go when that re-typing lands. **The ledger therefore stands where T25 left it: standing 12,633, endpoint 19.85-26.87k naive, centre 23.36k, the corner 1.87k over the line.** **`[T24]` RETURNED RED-THEN-CORRECTED, AND ITS D-10 CATCH MATTERS MORE THAN ITS PRICE** (2026-08-04, `_build/l3.32-t24-report.md`, probe orchestrator-reverified green): the residue `[T3]` recorded, a J-side carve BY A DESCRIPTION NAMING THE ORDER, is FALSE at the intended generality, because the delivered order is explicitly external (the chapter says so in its own prose, orchestrator-verified at Order:1014) and its internal reading is precisely W3, which T19 and T22 found red-then-cured but not cheap. The census's claim that no coded reader was needed was true of the pair reader and false of the NAMING. The corrected target is green: the carve runs through the unconditional switch in one line and the counting in 38, about 130 lines in all, with the bridge step and the description as module hypotheses. **Funding: the measured halves sit at the LOW end of T3's band (about 0.18-0.24k naive), but the description, which is the row's dominant share, is undelivered W3 content, so the leg does not move fully to the cheaper class; it becomes a leg that CONSUMES W3's delivery rather than an independent cost.** One wall of exactly T19's class was hit twice and cured the same way, by a consumer-side seal mirroring the retiring cone's own, which is the third independent confirmation that the order's cost is a sealing-discipline problem. **`[T23]` RETURNED GO, AND THE RESHAPE IS A DELTA THAT SHRINKS THE REDUCTION** (2026-08-04, `_build/l3.32-t23-report.md`, probe orchestrator-reverified green): the closed-form index tower is 141 lines including the two facts the induction needs of it (every level of it is a limit, unconditionally, and its successor is the extension of its predecessor), and **the successor clause is a SIX-LINE composition** of the corrected block theorem with the delivered level equation. The whole reshaped induction, with its limit clause stated and left as permitted, is 48 lines against the delivered reduction's own 137: **the reshape is 0.35 times the thing it replaces, not an addition to it.** Funding: the bridge's non-face rows now fund at 0.54-1.45k naive (centre 1.00k) and 1.12-2.96k calibrated, with the index tower and the induction skeleton moving to the measured class while the limit-case assembly, the re-type and the consumers' tower-specific clauses do not, so **the calibrated top falls from about 4.1k to about 3.0k while the naive total barely moves**, which is the two-caliber discipline doing exactly what it is for. **D-8 fired and was fixed inside the run**: the tower's first monotonicity target is false in the subset order, and the ordinal-conditioned kit that replaces it, 26 lines, is a hidden term the recon never priced. One consolation with real value: the square law is now a NAMED bounded item with a delivered comparable rather than an unknown, and the ordinal arithmetic it needs has consumers beyond it in both the fine-structure and geology eras, so it is substrate on the same argument that justified the pairing chapter itself. **T10 the StepInL ideal-form gate, RETURNED NO-GO ON THE BAND BUT THE REWRITE DECISION SURVIVES AT A CORRECTED PRICE** (`_build/l3.32-t10-report.md`, probe orchestrator-reverified green, no walls): measured on the delivered frames, an arm costs 31 to 35 non-blank lines both directions, which is 0.82 to 0.92 times the chapter's own 38 and nothing like the twelve T7 hoped for; the instantiation frame is 45 to 79, at the LOW end of T7's own 50-to-100 estimate and far under its 200-line red line. Since T7's red criterion is not met the verdict does NOT flip to keeping, but the price moves: **the fresh chapter is 1.2 to 1.7k naive (centre about 1.45k), not 0.65 to 1.25k**, so rewriting still beats keeping 1,989 lines by about 0.28 to 0.79k rather than T7's claimed 0.73 to 1.34k, and the naive 25k line still passes with about 0.45k of margin. Six hypotheses were audited and THREE were refuted: `prAt′` is not delivered in `FOL.Syntax` but PRIVATE in `Describe` (orchestrator-verified at Describe:153), an arm is not about twelve lines, and the adequacy layer does not delete to 140-340 but lands at 640-800. D-10 again did the decisive work: the gate's own transcribed target was FALSE (the environment order carved the pair the wrong way round) and the corrected target, the chapter's own convention, is what was measured. Named as required before the chapter is funded: per-operation probes for the remaining shaped operations and for the values half; **T11 the Realize-strip compile gate, RETURNED RED-THEN-GREEN, and the correction IMPROVES the ledger** (`_build/l3.32-t11-report.md`): the cut as T7 specified it does NOT compile, because retained `Switch` spec code still consumes the stripped import (`∃ₚ`, an export of `L.Rud.Realize`, is used by `unionSpec` and a same-class residue in `prodSpec`, `memSpec`, `condSpec`, `memWit`, `eqWit`, `chSepSpec`, `eqSepSpec`); all three consumers failed at exit 42. The CORRECTED cut adds that 211-line notation-and-spec layer, which has no consumer outside the stripped region either, and then `Switch`, `Bridge` and `SatTable` all typecheck GREEN. **So the dead weight is 789 (Realize) plus 500 (Switch: the six Realize-dependent modules at 287 plus the spec layer at 211) = 1,289 code lines, 213 more than T7's arithmetic sum, and `Descr`/`Hops` are confirmed Realize-free as the analysis claimed.** The working tree was restored byte for byte from a scratch copy (SHA-256 identical, no git used) and re-verified green; the orchestrator confirmed the restore and the RED cause at source. The GREEN of the corrected cut is agent-measured and will be re-verified by the orchestrator at execution, when the cut is actually made; **`[T35]` RETURNED, AND ITS HEADLINE IS A SELF-CORRECTION THAT MATTERS MORE THAN ITS BUILD** (2026-08-05, `_build/l3.32-t35-report.md`; Bridge, SatTable and StepInL all orchestrator-reverified green): the index tower lands at 165 lines and the reshaped induction closes its successor clause end to end as T23's six-line composition, with the limit clause stated and left as the first named residue. **But the survivor investigation found that the direction this campaign had been calling unconditionally delivered was not**: `bridge-isJ→isL`'s proof ran through `p4`'s limit-membership, which used the per-level identification, whose own proof used the residue that had already been refuted. The theorem is true and is now RE-PROVED free of the identification, with its limit membership carried as the second named residue beside the induction's own; and **the class-level `bridge-isL→isJ` is now genuinely delivered from the reshaped induction**, which is what D19 ruled for. `SatTable`'s landing can now close structurally, since `Reduce`'s interface no longer exposes the refuted residue. One environment datum recorded honestly: the new chapter cold-checks in about fifteen minutes against the baseline's forty-eight seconds and re-checks warm in about 1.5 seconds, diagnosed as cold elaboration under heavy conversions rather than a wall. **The lesson is filed against D-10 in its sharpest form: a refutation is not complete until the consumers of the refuted object have been walked, because a target's falsity does not announce itself to the theorems whose proofs pass through it.** **`[T43]` RETURNED: THE OBSTRUCTION IS ON THE CRITICAL PATH, AND THE WAY PAST IT IS NOT TO CLIMB IT** (2026-08-05, `_build/l3.32-t43-report.md`): the GCH conclusion forces a call at the successor cardinal, and the tower induction cannot be restricted to initial ordinals, so the owner's option 2 is answered NO on its face. But the report's value is the alternative it measured: **restate the counting's bounds in TRUNCATED form**, since every consumer goal in the chain is a proposition and the truncation is therefore free on the consumer side, and the order core's own induction hypothesis can be consumed truncated because every elimination of it inside the core lands in the empty type. The honest extraction is then not needed at all. The other routes were priced and rejected on evidence: a choice principle implies excluded middle and would cost the tree's postulate-free claim, and there is no counting route that avoids the product, since the count's own upper bound contains the square law (the honest syntax injection of a pair of members into unary formulas IS the square law at that cardinality). `[T47]` dispatched to build the truncated layer, ADDITIVELY, since a sibling is reading the chapter. **T13 the archive infrastructure, DELIVERED and committed (`d063709`)**: `archive/` with its README, `dev/ARCHIVE.md` as the registry, and a REUSE carve-out preserving archived content's original license. Its finding corrects an orchestrator assumption: moving the archive out of `src/` did NOT make every exclusion structural, because four scripts discover inputs through `git ls-files` (repository-wide) or through the pre-commit hook's explicit staged paths, and those needed real filters; only the Agda gate, the include path and the site build were blind by construction. Verified not by reading but by a POISON PILL: a file violating every gate at once was placed in the archive, `make check` passed over it and `reuse lint` covered it at full compliance, and the test is recorded in the registry to be repeated whenever a gate's file discovery changes. **T14 the W3 recon, DELIVERED (`_build/l3.32-t14-report.md`): the internal order re-prices UP to 480-950 naive / 1,505-2,946 calibrated** against the 400-750 estimate, and the rise is fully attributed: the source recon's own rows summed above its band, one sub-item (the initial-segment facts) had been dropped from its decomposition entirely, and the successor clause carries the recorded direction-pair discipline rather than an artifact. The calibrated move is SMALLER than the naive one because T2's GO reclassifies the packaging sublayer to 1.3x, which is the two-caliber discipline visibly paying. Its adversarial-honesty item names the most likely remaining underprice: the paired satisfaction face for the order-as-a-set-of-pairs, priced separately as its gate's fork, whose red outcome adds a 0.4-0.8k prerequisite. Nothing in the retiring 6,050-line cone serves the wing's order except the shape of what NOT to build: that cone's successor-clause wall class is W3's first stop-line. **T12 the geology corpus fetch, DELIVERED (`dev/literature/geology.md`, 694 lines, all five questions answered with citations) after two failed attempts and a session resume**: attempt 1 died with zero output having researched for its whole budget, attempt 2 wrote the skeleton and died with every section empty, and the resume of attempt 2's own session carried its research forward and filled the file. The failure minted LESSONS C-22 (a dispatched agent writes its deliverable incrementally, never at the end). Its two load-bearing findings: the second trophy is not a located standalone theorem but its components are (Reitz proves L satisfies the Ground Axiom; the FHR authors state on the record that the mantle of L[G] is L; the derivation from Reitz plus Jech 13.16(ii) is two lines), and the mantle's universe-size wall the GLp POC measured is exactly what the ground-model definability theorem buys off, so it is priced literature-side rather than invented. **The retirement surgery ARCHIVES rather than deletes** (D20, in force from 2026-08-04) and builds the archive infrastructure on its first use. Standing and endpoint figures are in section 0. Execution record, with the wave-by-wave measurements: `dev/JOURNAL.md`. |
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

### Bookkeeping

The dated records (spike verdicts, landed-batch records, tripwire changes,
retirement hashes) have moved to `dev/JOURNAL.md`, section *Dated records*,
together with the execution narratives of the large goal rows. This section
stays as the pointer so the registry's structure is unchanged: a fact that is
a RULING belongs in a row above; a fact that is an EPISODE belongs in the
journal; a fact that is a LAW belongs in `dev/LESSONS.md`.
