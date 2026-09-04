# The route tree (archived from dev/PLAN.md section 6.1)

> **STATUS: SUPERSEDED.** The one-row-per-goal statuses are live in dev/PLAN.md section 11 (MASTER status table and task index); the coding rules are dev/PLAN.md section 6.0. **Section 6.2 is now caliber and the single best-effort projection, and it REVOKED the two-caliber discipline this header used to name** (owner 2026-08-09, retiring DD7). DD8 carries the replacement rule. Read this memo when a goal's full statement, its gates, or the L3 execution phases are needed. **The L3 route is itself retired**, and the live route is the two-tower bridge (dev/PLAN.md DD2), so read this memo as a record of the earlier route. Moved out of dev/PLAN.md by [L3.32-T113] because it updates rarely.

---

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
