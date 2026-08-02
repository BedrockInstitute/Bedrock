# PLAN: porting L ⊨ ZFC from fol-reification

The construction plan for Bedrock's first milestone: re-landing the
`fol-reification` result (V=L ⊨ ZFC, hence Con(ZF) → Con(ZFC)) as
textbook-grade literate Agda in this repository. Developer doc, English only,
not translated. Decisions recorded here were ratified by the owner on
2026-07-16 and are binding until the owner revises them. Work is managed by the
goal codes of §6; the MASTER status table is §11.

**This file is the goal-history registry.** Every row records what was ruled,
when, and with what outcome, in compact form, and points to where the substance
lives. The measured lessons (performance laws, conversion rules, termination
traps, inference traps, design doctrines) have moved to `dev/LESSONS.md`. The
evidentiary basis of the route pivot (the B ruling) lives in
`dev/memos/L3.29-b-pivot.md`; the AC-route survey and probes live in
`dev/memos/L3.28-ac-route.md`. A row's opening word is its status; status
changes go at the front of the row.

- **Source repository:** `choukh/fol-reification`, local sibling checkout at
  `../fol-reification`. Reference pin at planning time: commit `8b190d5`
  (2026-07-16, M2.7 build-optimization landed; the Con(AC) mathematical
  milestone itself dates to 2026-07-14). Re-pin the exact source commit in §11
  when L1 porting starts.
- **Toolchain parity:** both repos use Agda 2.8.0 + cubical 0.9; all source
  modules are `--cubical --guardedness`. No toolchain migration is needed.

## 1. The theorem, stated honestly (D1)

What the source proves, and what Bedrock will claim, is:

> In Cubical Agda (the host), the constructible sub-universe L of the HIT
> cumulative hierarchy V is a ZFC model: `L⊨ZFC : isZFCModel 𝒮ʟ` where `𝒮ʟ`
> is `𝒮ᵥ` restricted to the inductive constructibility predicate. Semantically
> this yields the **relative** consistency Con(ZF) → Con(ZFC), relative to the
> host theory (Cubical Agda with universes, informally about ZFC plus an
> inaccessible).

The unqualified claim "Con(ZFC)" is never made, in code names, prose, or
marketing. The root chapter opens with exactly this framing (this matches the
Charter's position that rigor is independent of metatheoretic strength).

Assumption budget of the source proof, to be preserved or improved:

- The `--safe` framework core (FOL, Reification, ZF interface, HIT-V model) is
  zero-postulate, machine-enforced by `--safe`.
- The L development rides **exactly one postulate**, excluded middle
  (`Classical.lem`). No holes, no `TERMINATING`, no `--allow-unsolved-metas`
  anywhere in the source `src/`.
- Bedrock removes even that postulate by parameterization (D2), making the
  whole tree `--safe`.

## 2. Source material survey (condensed)

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
| D1 | Statement of the result | As in §1: V=L ⊨ ZFC, relative consistency, relative to the host. Never unqualified "Con(ZFC)". |
| D2 | Classical boundary | No `postulate` anywhere. LEM (and any classical/choice principle) is an explicit parameter; the whole tree is `--safe`. Gated by the L0.2 performance spike; a materially worse projection (over 1.5x the M2.7 full-cone baseline) escalates back to the owner. Documented fallback if re-ruled: one postulate module with an explicit safe boundary. |
| D3 | Technical lemma layer | L3 starts with a **reduction review** per cluster: first try to shrink the code substantially and re-layer it so the narration flows end to end. Only if a cluster resists reduction may its exposition be tersened, per cluster, with explicit owner sign-off. |
| D4 | Licensing | Ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out (the owner authors both repositories). No in-file SPDX headers. Prose cites Rech (2020) and the source repository where warranted. |
| D5 | Skeleton | The previously reserved `src/` namespaces are void. The redesigned skeleton in §4 replaces them; `src/README.md` is rewritten in L1. Below the part level the skeleton is **provisional** (D11, tension T2). |
| D6 | Prose | Full rewrite for beginners, English first, then Chinese (Japanese pre-supported). Source research prose is never translated; it serves the porter only. |
| D7 | Naming hygiene | No iteration-numbered or provenance-flavored names survive the port. The §4 mapping table is the rename ledger; extend it as porting proceeds. |
| D8 | Construction order | Root-first via the Frontier record (§5): the statement of the theorem typechecks from day one, details land last. Reading order on the site remains foundations-first. |
| D9 | Goal management | Work is managed by route-tree goal codes rooted at **L**: L0 to L5, sub-goals Lx.0 onward. Coding rules in §6.0. Commits and docs carry the code in brackets, for example `[L1.4]`. |
| D10 | Build performance | The build constraints of §7 are binding from the first ported module: single-invocation trusted gate, parallelism outside the trust base, tracked cold-check budget, per-module heap caps. Cold-check regressions are defects. |
| D11 | Revisability | The plan legislates for known unknowns explicitly: legislation may be added mid-course (standing L0 track), the skeleton below the part level may be re-cut after L3, Frontier fields may be re-cut, and a whole-book harmonization pass runs at L4. Mechanisms in §8. |
| D12 | L3 reduction strategy | **Outcome 2026-07-26 (`[L3.0.2]`): the decision was right, the analysis was wrong.** The lever was not a large internalization theorem (it is 96 lines) but general-formula comprehension, delivered at `[L2.2]`; the projected 65%-at-3x is now measured-and-projected at 7x to 14x. Original ruling, 2026-07-25: **take the big lever first** (goal `[L3.0]`), under an explicit paper-level gate and pre-agreed kill criteria (`[L3.0.3]`, `[L3.0.1]`); schedule ruling, same day: `[L3.0.3]` opens **before** L2. |
| D13 | Macros and generated proof | **Ruled 2026-07-27 by the owner.** Opacity is **not** an objection. **The single veto is conversion blowup.** A macro or reification route is judged by exactly two measured questions: is it smaller, and does it keep `src/` inside the §7.5 and §7.6 budgets. Supersedes the exposition argument recorded against `[L3.2]`, which is withdrawn. |
| D14 | Retiring a chapter in waiting | **Ruled 2026-07-27.** A chapter is *in waiting* when nothing outside its own namespace imports it (`Everything` never counts). Such a chapter is **retired** (files deleted, `Everything` entries dropped, the commit hash recorded in §11, plus one line saying what would bring it back) when **both**: no **open** goal names it in §6.1, and either a goal that did name it has closed without using it, or no goal ever named it. It is **kept** only under a **written warrant**: a named open goal *and* a dated expiry. Warrants live in §11 and expire whether or not anyone looks. **Trigger:** at every goal closure, list the chapters in waiting and check their warrants. |
| D15 | The AC route | **Ruled 2026-07-31 by the owner: option C of `dev/memos/L3.28-ac-route.md` is adopted**, on the memo's numbers (ZF-only cone 4,180 lines, AC-only radius 13,217, the swap surface one import list) and on three same-day probes, all PASS (memo §9). `Def` keeps its satisfaction definition and every ZF-cone statement keeps its meaning; the internal tower and the internal well-order rebuild over a binder-free operations calculus; the satisfaction-internalization chapters retire at the cut-over. Execution is the two-step branch plan: build C on `godel-route` with both developments coexisting, judge the pedagogy side by side before deleting, promote on success; old `main` becomes the internalization archive with a wrap-up and a tag. Executes as `[L3.29]`, which carries the milestones and tripwires; the global stop is a landing projection above 11k at any milestone (since amended by the tripwire rulings, §11). **Pivot 2026-08-01: option B of `dev/memos/L3.29-b-pivot.md` is adopted for the build on this branch**, kinded closure tower with the stratified producer order, alongside the delivered route, final measurement then a fresh ruling before retirement.**2026-08-02: the architecture question is reopened as `[L3.30]` (rud re-architecture, exploratory) under the future-extensibility lens; the B build is suspended after its final batch; no retirement of any route occurs until the `[L3.30]` ruling.** |

## 4. Target skeleton (D5)

Top-level parts mirror the book's parts. The part level (Base, FOL, ZF, V, L,
Landmarks) is fixed; **cluster-internal layout is provisional until the L3.10
re-layering review** (tension T2), and file splits inside a cluster are
finalized at port time under the STYLE-agda rules (L0.0).

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
| `FOL.Syntax.{mapTm, mapFo, ParamFree, embed}`, `FOL.Semantics.{⟦⟧-map, ⊨-map, embed-⊨}`, `FOL.Graded.{mapΔ₀, mapΣₙ, mapΠₙ}` | `FOL.Relabelling` | owner ruling 2026-07-18: the constant-domain toolkit has zero trunk consumers and gathers into one tail chapter, three altitudes (syntax, meaning, certificates); zh rendering re-cut: relabelling = 常量变换 and renaming = 变量变换 (the pair named by its objects) |
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

## 6. Route tree (D9)

### 6.0 Coding rules (lightened from the source's ROUTE-TREE §0)

1. **Code form** = `L<goal>.<subgoal>…`, dotted decimal, rooted at L0 to L5.
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

**[L4] Convergence.**

- **[L4.0]** Empty the Frontier, delete `L.Frontier`, drop the parameter; the
  unconditional `L⊨ZFC` lands. **PLANNED** (superseded in substance by
  `[L2.4]`'s delivery: the Frontier is already empty and deleted).
- **[L4.1]** Whole-book **harmonization pass** (T4): re-read end to end, fix
  foreshadowing and cross-references, run the zh/ja cross-check for term drift,
  reconcile prose with any L3 interface changes. **PLANNED.**
- **[L4.2]** Update `Landmarks`, the README trio, and the Charter status;
  retrospective. **PLANNED.**
- **[L4.3]** Seed the next-milestone plan (L ⊨ GCH, per the Charter) as a
  successor to this document. **PLANNED.**

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
| The internalization theorem does not converge (D12) | `[L3.0.3]` ran paper-level before L2; `[L3.0.1]` carried kill criteria agreed in advance; the Frontier kept the tree green, so a red verdict cost the attempt alone. |
| The generic abstraction resurrects conversion blowups | Abstract parameters over large formulas are the source playbook's own worst case (WORKLOG §5 case 16: one implicit `{φ}` cost 74 minutes and was fixed by one explicit argument). The theorem's parameters are spelled explicitly and `opaque`-sealed; §7.6 polices every instance. |
| The B build's open risks materialize | `dev/memos/L3.29-b-pivot.md` §6 lists the priced-but-unmeasured items; each lands behind the route's probe discipline with its abort criteria fixed in advance. |
| Statement drift toward unqualified "Con(ZFC)" | D1 fixes the framing; the root chapter and Landmarks are the canonical wording; glossary pins the translated terms. |
| Process drift (ad-hoc naming, unregistered work) | §6.0 rules: no work without a code, no backfilled registration; §11 updated in the same commit as the status change. |

## 10. Candidate simplification register

Default is a faithful port; each entry here needs its own cheap verification
and owner decision before deviating. Add entries as they are discovered; record
verdicts. An accepted candidate is executed under the goal code of the cluster
it affects.

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
| L3.29 | AC by the operations calculus (route C); now B on top | **REGISTERED AND ACTIVE 2026-07-31, executing D15 on the `godel-route` branch; old `main` is frozen except critical fixes until promotion.** Route C milestones and tripwire history: **M1** (operations + closure step, target 600-850, stop above 1,000 or 60 s); **M2 DONE 2026-08-01**: normal-form over graph-coded tuples, about 900 lines across three chapters against the 750 projection, laws P-d/P-e paid along the way; **M3 meta half DONE 2026-08-01**: `L.Godel.Terms` delivered (195 lines, 1.7 s) with `termDef≡Def` on top, the Def-equivalence; **M4 DONE 2026-08-01**: `L.Godel.InL` 1,604 (14.8 s), `L.Godel.Codes` 199, `L.Godel.Definable` 1,143, `L.Godel.Table` 1,343 (13 s, 43 lines over its own 1,300 stop line), laws P-f and the named-continuation medicine paid; **TRIPWIRE ACCOUNTING 2026-08-01**: Gödel part 5,936 vs the 2,700-4,900 bucket, whole tree 25,858, landing projection ≈13.5k-14.5k over the 11k tripwire; **RULED (option 3)**: bounded continuation, tripwire temporarily re-set to a measured landing above **14k**; the 9.5k-10.5k band acknowledged unreachable, honest revised aim ≈12.5k-13.5k. **M5 order re-cut RULED IN**: Step spine survives with one import swapped, Naming rebuilt (N1 `L.WellOrder.Tree` 279 lines 1.1 s with the two termination lessons; N2 `L.Godel.Name` 258 lines 1.3 s via a left inverse; N3 the swap lands as a **parallel scaffold** `L.Godel.Step`, 362 lines, old cluster untouched); **(d) IS COMPLETE 2026-08-01** after the junk-table problem was walked end to end (certificate formula `CertAt` with the honesty induction; Tower closes at 1,723 code lines, ~90 s cold cone). **THE RULED MEASUREMENT 2026-08-01**: whole tree 28,580; dying gross 14,245; surviving basis ≈15,280; pre-compression ≈15,850-16,450; post-compression ≈15,000-15,700. **THE TRIPWIRE (above 14k) FIRES; RULED (option 1)**: measurement accepted, tripwire re-set to a measured landing above **16.5k**, build continues into M5's internal side; the count premium is the certificate architecture and the order internal side's real price, bought for second-class builds and the binder-free architecture; the compression pass remains banked. **M5-INTERNAL DESIGN RULED 2026-08-01** after the collector recon: (i) the name order is RE-CUT to a skeleton/parameter split (slating `L.WellOrder.Tree` for retirement at M7), (ii) the collector is REBUILT LEAN, (iii) the 16.5k tripwire reads POST-COMPRESSION at final delivery, central estimate 15.5-16.0k in-line. Batches: M5a (meta re-cut), M5b (Cond supplier), M5c (lean collector), M5d (Bound assembly). **M5a LANDED, committed `9539088`**: the name-order re-cut to skeleton and parameters, `L.WellOrder.Base` + `L.Godel.Name`, **retired by the B pivot** (lessons: P-g and the graft entry in `dev/LESSONS.md`). **THE B PIVOT, RULED 2026-08-01**: the audits (compression, cone, deep-levers) priced the delivered route at 13.1-13.7k; the closure fork's cut probe returned NO-GO-with-salvage and the order probe returned GO with candidate 1 (the stratified producer order); **option B is adopted**, the kinded closure tower with the stratified producer order, built alongside the delivered route on this branch; pointer: **`dev/memos/L3.29-b-pivot.md`**. **CURRENT STATE: B development active on this branch; the delivered route coexists untouched; a final measurement and then a fresh ruling precede any retirement.** Milestones M6/M7 as originally registered: M6 `Transversal` re-pointed, `L⊨ZFC` green with both developments coexisting, owner reads the new Part for the pedagogy verdict before anything is deleted; M7 the internalization chapters retire, final measurement against the band (superseded by the B ruling's fresh-ruling clause). After promotion, step two of D15: the archive wrap-up on the old `main` (role-explaining README banner in English and Chinese, a tag on the last full-internalization commit, toolchain pinned Agda 2.8.0 + cubical 0.9)**B BATCH LEDGER (all codex-delegated, orchestrator-audited)**: B1 the closure chapter opens, satisfaction-set lemmas + the singleton family (`5cd66e2`); B2 the deferrals close, reverse pinning by direct path lambdas + the full extension equation + singletonsAt/singletonsL (`97bb716`); B3 the kinded levels, the invariant, terms-to-levels, the cut theorem (`6e12593`); B4a the layer described, eighteen direction-paired readers + the prefix-table description (`7b6d799`); B4b+B4c the two over-description guards (values at positive arities; extension at arity one, caught by the mandated meta-match table) and the PINNING THEOREM at full strength (`810d9cd`); B4d five of nine tag-image constructibility lemmas, module-parameterization law found (uncommitted, riding with B4e); B4e the remaining images + stepL + sliceL, RUNNING as the FINAL B batch, harvest-only. Also in this row: the owner-directed detail-quality passes over codex-written chapters (Tower `da5a09c` + `e57f2b5`, net −34 lines, named adequacy readers, InL-style Fin abbreviations; quality bar = the hand-written internalization standard; prose deliberately left thin). **SUSPENDED 2026-08-02**: the owner-directed future-extensibility review (GCH, fine structure, geology wings; completion-state-blind) reopened the architecture question; no further B batches; every route's code stays in place until the `[L3.30]` ruling. |
| L3.30 | The rud re-architecture (exploratory) | **REGISTERED 2026-08-02 by owner direction. EXPLORATORY: no production code is written and none retired until the ruling.** The question, posed completion-state-blind: the ideal architecture for the book's future, meaning the trophy, then GCH (`[L4.3]`), then the fine-structure wing (diamond, square, covering, core models) and the geology/HOD wing. The orchestrator's analysis on record: every route decomposes into a hierarchy engine plus an internal verification layer, and all the measured cost lives in the second; the ideal trunk is Jensen's rudimentary functions (untyped small basis, S/J-hierarchy one operation per step, no arity slices and no certificates, junk excluded by extensional determination) with `Def` keeping its satisfaction face and the equivalence a named theorem, so the motivation and the machine are both taught and the classical L-versus-J switch happens at a theorem; the internalization line's durable asset is a small vocabulary-generic set-model satisfaction module for the wings; fine structure is rud-native; Paulson's Isabelle/ZF record independently documents the satisfaction-internalization pain, and GCH-in-L appears unformalized in the major systems (both to be verified by D1). Trunk-to-trophy estimated 4.5-6.5k BEFORE the probe-price-times-3 calibration this project measured. **PREPARATORY TASK REGISTER (parallel codex agents, orchestrator as gatekeeper, all 2026-08-02):** `[L3.30-L1]` literature collection, codex workspace-write with network, deliverables `dev/literature/{rudimentary-functions,j-hierarchy,devlin-errata,formalizations,BIBLIOGRAPHY}.md` with per-claim source citations and a no-memory rule, report `_build/l1-report.md`, RUNNING; `[L3.30-S1]` salvage inventory over the three built routes, codex read-only, deliverable `_build/rud-salvage.md` (four bins with file:line evidence, measured sizes, the LESSONS bindings), RUNNING; `[L3.30-D1]` the digestion document pinning the orthodox contemporary form, codex `deepseek-v4-pro` draft under orchestrator audit, deliverable `dev/literature/digest.md`, must answer the Q1-Q7 checklist of the raw sweep (the exact basis function by function; S-versus-J stratification and where condensation lives; the comprehension theorem's shape; the canonical well-order; rud_A; the Devlin error classes as a do-not-repeat list; the formalization landscape including whether GCH-in-L is virgin territory). **D1 DELIVERED 2026-08-02, orchestrator-authored directly by owner redirection (`92d3fd7`)**: Q1-Q7 pinned with rulings on all six UNVERIFIED marks (Paulson's GCH ruled not mechanized on artifact evidence), the SZ-versus-Mathias basis fork laid out for the memo, the verbatim match between SZ's canonical well-order and the order probe's candidate 1 recorded, the owner's note reconciled point by point with four flagged discrepancies (the Gandy-Jensen "Gödel operations" attribution OPEN; the S-step formula shape, SZ's form wins; the operation count 9-or-10 versus SZ's 16; the master-code reduction unextracted), nine open items with settling actions; the codex parallel draft remains RUNNING and will be reconciled into the delivered digest on return; `[L3.30-M]` the design memo `dev/memos/L3.30-rud-route.md`, orchestrator-authored, consuming D1 and S1: the architecture, the salvage plan, the build order, the probe checklist, the calibrated budget, PENDING D1. The owner recorded an independent exploration note as reference input, **dev/literature/owner-notes-rud.md** (the Gandy-Jensen canonicity, the rud family disambiguation with the S-hierarchy as the pivot for uniform Sigma-1 definability, the master-code dividend for formalization, the geology verdict that rud offers no leverage there and the syntax burden lives in forcing itself, and the two Cubical-specific pitfalls); D1 must reconcile against it, with primary sources winning any disagreement. **Ruling gate: the owner rules adoption on `[L3.30-M]`; the B4e walk-transparency datum enters `dev/LESSONS.md` regardless; nothing retires before the ruling.** |
| L4 | Convergence | PLANNED |
| L4.0 | Empty Frontier, unconditional root | PLANNED (the Frontier is already empty and deleted; the unconditional root is delivered) |
| L4.1 | Whole-book harmonization pass | PLANNED |
| L4.2 | Landmarks/README/Charter updates | PLANNED |
| L4.3 | Seed the GCH successor plan | PLANNED |
| L5 | Build and site infrastructure | PLANNED |
| L5.0 | Build machinery port | PLANNED |
| L5.1 | make check split | PLANNED (the three named gate defects belong here: the two linters that skip untracked files, the glossary avoid-list keying off markers, and the missing end-of-file check) |
| L5.2 | CI strategy | PLANNED |
| L5.3 | Site pipeline load test | PLANNED |

### Bookkeeping (dated records)

Each dated record preserves the registry facts: dates, rulings, tripwire
changes, landed-batch records (chapter names, headline line counts, check
times). The substance (measured laws, design narratives) lives in
`dev/LESSONS.md` and the memos; where a lesson is involved, the entry names its
`dev/LESSONS.md` ID.

- **LEM spike verdict [L0.2], 2026-07-16: green.** Method: two copies of the
  source `src/` in a scratch area; the vertical slice `Classical →
  L.OrdinalLinear → L.Stage → L.ConstructibleOrder → L.WellOrder → L.ModelAC`
  was rewritten with `LEM : ∀ ℓ → Type (ℓ-suc ℓ)` in a new `--safe` interface
  module, the postulate deleted, `Classical` parameterized and upgraded to
  `--safe`, the five consumers taking `(lem : ∀ {ℓ} → LEM ℓ)` telescopes.
  Everything compiles. Cold-check cost, same machine: slice total 43.3 s →
  44.2 s (+1.9%); worst stable per-module delta about +5% (`L.ModelAC` 3.72 →
  3.90 s); `L.WellOrder` 31.3 → 32.4 s (+3%). Far inside the 1.5x gate: **D2
  stands, no fallback needed.** Residual risk: the deep certificate clusters
  were not exercised; §7 budgets police them.
- **Source commit pin [L1.0], 2026-07-16:** `8b190d50feb0` (the tree as of the
  M2.7 build optimization; the Con(AC) mathematical content is unchanged since
  `527f13b`, 2026-07-14). All L1-L3 porting reads the source at this commit;
  advancing the pin is an explicit `[L0.x]` decision. (The
  `-WnoUnsupportedIndexedMatch` flag turned out to be present in
  `bedrock.agda-lib` from the start.)
- **Coding re-measurement [L3.3] → [L3.14], 2026-07-25:** consumers of each
  remaining module in the pinned source. **Substrate** (stays): `SatCertBase`
  197/68, `SatCertLen` 259/46, `SatCertEnv` 135/44, `SatCertCons` 319/13; 910
  lines total. **Instance data** (moves out): `CodeOrder` 1,277 (all 20
  consumers `Cmp*`/`Depth*`/`Order*`/`WellOrder2`), `CodeSeqCert*` 757
  (`FFST*`/`Cmp*`/`Depth*`), `SeqChar` 422 (tier-2 trace), `FormulaOrder` 361,
  `VarCoding` 385 (one consumer, `TarskiSat`). `ConstructibleOrder` 137 is
  well-order vocabulary for `[L2.2]` and tier 2. `[L3.3]` shrinks by 78%; the
  displaced 3.3k is relocated to `[L3.5]`/`[L3.6]`/`[L3.7]`. Two smaller
  findings: checklist item 2 (readers parameterized over de Bruijn position)
  is already satisfied upstream; `[L3.2]`'s macro cannot touch the
  characterization lemmas, which are set-theoretic mathematics.
- **Classical-cone finding [L2.0], 2026-07-25:** the basic axioms need **no**
  classical logic. The source proves pairing by ordinal trichotomy
  (`L.OrdinalLinear.ord-tri`); Bedrock's `boundingOrd` supplies a *common
  stage* constructively. `L.Ordinal` and `L.Axioms.Basic` are plain `--safe`
  with no `lem`. **First re-examination [L2.1]:** the numeral chain is
  constructive too, but the collection step is not: `hasInfinityL` needs `ω ∈
  L`, hence `ord∈Lset-suc`, hence ordinal trichotomy, which the source's probe
  P8-3 judged constructively unprovable. The L side's classical cone begins at
  the collection step. **Second re-examination [L2.2]:** reflection does not
  need the well-ordering of `L`: take the least **stage** that holds a witness
  instead of the stage of the least witness, and `pickWitness` becomes a
  truncated statement. `[L2.2]` drops about 600 lines and gains no assumption;
  `L.Stage`'s descent is now `leastOrd`; `bound2` moved from
  `L.Axioms.Separation` to `L.Ordinal`; `ReflectN` does not exist as a chapter
  (the engine is written once at `k` parameters with an explicit-gap reach
  lemma). `[L2.2]` is about 1,000 source lines lighter before `ReflectFo`.
- **Theorem statement [L3.0.4], 2026-07-25:** memo delivered, awaiting owner
  gate. The prerequisite was narrower than PLAN assumed: only `BoundedFo` and
  the closure engine, so `[L2.2]`'s reflection interface is consumed by the
  theorem's *proof*, not its statement. Both prerequisites ported in this
  goal: `FOL.Manipulation.Bounding` and `L.Axioms.Basic.defSet→isL`. Budget:
  tier 1 at 3.0k to 4.5k against 13,518. Stages 4 and 8 of the eight-stage
  pipeline are already Bedrock theorems (`boundingOrd`/`Lset-mono`,
  `defSet→isL`).
- **Subsumption probe verdict [L3.0.3], 2026-07-25: amber.** One step
  specification subsumes `Cmp*` and `Depth*`; `FFST*` is already a third
  instance. (a) the harness is 4,673 lines written three times, so the
  theorem's own yield is about 2.9k, not 8k to 12k; (b) the larger recoverable
  block is per-tag clause work (twelve tags traversed five times per
  instance), which wants a `ClauseBundle`. Classification: `Order*` does not
  fit (stage-indexed theorem); `Sat*`/`Tarski*`/`Coh*` fit by halves
  (certificate yes, constant table no); the closure tower needs no theorem.
  The memo's §8 checklist is binding input for `[L2.2]` and `[L3.3]`. Goals
  registered from this verdict, same day: `[L3.11]`, `[L3.12]`, `[L3.13]`.
- **L3.0.0 split (§6.0 rule 3, standard re-split), 2026-07-25:** owner ruling;
  the source-facing half runs before L2, the Bedrock-idiom half after `[L2.2]`.
  `[L3.0.1]` and `[L3.0.2]` cannot move: the proof of concept needs the coding
  substrate.
- **L3 renumbering (§6.0 rule 3 carve-out), 2026-07-25:** map, old to new:
  theorem `L3.5` → **`L3.0`** (sub-goals `L3.5.0/.1/.2` → `L3.0.0/.1/.2`),
  sweep `L3.6` → **`L3.1`**, `reify!` `L3.7` → **`L3.2`**, coding cluster
  `L3.0` → **`L3.3`**, scaffolding `L3.8` → **`L3.4`**, satisfaction `L3.1` →
  **`L3.5`**, closure `L3.2` → **`L3.6`**, certificates `L3.3` → **`L3.7`**,
  dispatch grids `L3.9` → **`L3.8`**, cast solver `L3.10` → **`L3.9`**,
  re-layering `L3.4` → **`L3.10`**. The carve-out is spent; L3 codes are
  immutable again.
- **Source cost anatomy (§2.1), 2026-07-25:** cone 150 modules, 48,260 code
  lines; `hasChoice` owns 42,354 (88%), `hasPower` 149, the other eleven
  fields 62 between them; shared blocks 2,266/2,571/392; scaffolding 50% to
  86% identical, soundness 4% to 9%.
- **Cold-check baseline (§7.5), re-measured 2026-07-26 at `[L3.16]`:**
  whole tree, 51 modules, 5,519 Agda lines: 18.5 s serial, about 2% of the
  budget. **This per-module list was WRONG and corrected 2026-07-27**: it was
  produced by piping `--profile=modules` through `sort -rn`, and Agda prints a
  thousands separator, so every module at or above 1,000 ms sorted as though it
  were under ten (C-2 in `dev/LESSONS.md`). Real worst module: `L.Axioms.Basic`
  at 7,142 ms, 36% of the whole tree; tree 20.0 s; `L.Coding.Model` 1,632.
  The budgets still hold with room. The line worth keeping: `L.Axioms.Full`
  checks in 259 ms, and before its constructibility certificate was sealed it
  did not finish in 600 s: one `opaque` worth a factor of at least 2,300
  (rule 2, R-29).
- **Frontier field count:** **1** after `[L2.3]` (opened at 11 on `[L1.7]`;
  `[L2.0]` deleted `hasEmptyL`, `hasPairL`, `hasUnionL`; `[L2.1]` deleted the
  numeral chain's three and then `hasInfinityL`; `[L2.2]` deleted
  `hasSeparationL` and `hasReplacementL` together; `[L2.3]` deleted
  `hasPowerL`). Remaining after that: choice alone. **`[L2.4]` deleted the last
  field and the record itself, 2026-07-31.**
- **Conversion-blowup finding [L2.2], the sharpest so far:** `L.Axioms.Full`
  did not finish in ten minutes, from **one proof term**: the constant is the
  stage as an element of the model, and an element of the model is a pair of a
  set with its constructibility certificate, which unfolds through
  `DefOf.defSet⊤≡A`. Sealing the certificate alone (`opaque isL-Lset`) took
  the chapter from over 600 s to **1.4 s**; sealing the reflected ordinal was
  tried first and did nothing. The shape generalizes: when a restricted
  structure's elements appear as constants of the object language, seal the
  membership certificate where the element is built, not the element (R-29).
- **Internalization finding [L3.0.1], 2026-07-26:** the internalization
  theorem is **52 lines of Agda** (`L.Recursion`), against the projected 1,400
  to 2,000 and the source's 13,518 for tier 1. It is a wrapper around
  `hasReplacementL`: `[L2.2]` paid for general-formula comprehension once and
  for all, so a recursion whose graph is expressible has its table in `L` and
  the table is the replacement image. Consequences: the theorem half is done;
  `[L3.11]` loses two of five fields and is re-scoped to conditional; `[L3.12]`
  and `[L3.13]` are to be re-examined; `[L3.0.5]` stands honestly (superseded
  as stage 7's prerequisite but survives as a general lemma). What the
  instances still owe: `smallDom`, twelve lines in `L.Recursion`, discharges
  the index-set obligation for every instance at once, so no instance ever has
  to internalize its own syntax as a set; the only remaining obligation (b) is
  the graph written in the object language and proved single-valued.
  `isL-Lset`/`LsetS` re-homed from `L.ReflectFo` to `L.Axioms.Basic`.
- **Interface completion and fillability probe [L3.0.1], 2026-07-26:** the
  first cut asked for single-valuedness, which is the wrong thing to ask; the
  form to fill is now `Definition` (domain, function, defining formula, two
  adequacy directions). Fillability probed with the singleton map `x ↦ {x}`:
  **35 lines**, chapter checks in about a second. It establishes the frame is
  inhabitable; it does not measure `Depth`/`Cmp`.
- **Verdict measurement [L3.0.2], 2026-07-26:** source `hasChoice` cone
  (48,229 lines, 142 modules) classified by reason-the-code-exists:
  **satisfaction 16,400 (34%)**, recursion tables 12,019 (24%), order and
  choice 11,929 (24%), reflection and model assembly 3,517 (7%), other 2,669,
  coding substrate 1,695. Measured ratios: reflection 2,283 → 721 (3.2x),
  coding substrate 2,638 → 1,065 (2.5x), internalization harness 4,673 → 96
  (49x); whole covered buckets 5,212 → 3,409 (1.53x). Per-clause unit about
  65 lines (from `L.ReflectFo`). **D12 named the wrong lever**: the real lever
  was general-formula comprehension, paid at `[L2.2]`. Projection for the
  remaining 43,017 lines: 3,000 to 6,400; the `L` side lands at 6,500 to
  10,000 total against 3,361 already written, a 7x to 14x compression. Weakest
  row: order and choice.
- **Where the lever points next [L3.0.2 follow-up], 2026-07-26:** satisfaction
  is not merely the largest bucket, it is the bottom of the other two (the
  order's graph mentions a definable enumeration of `Def(A)`). `Depth*` is a
  termination measure Agda does not need; `Cmp` is a decidable comparison on
  `Formula`. Of the remaining 43k, one third is irreducible mathematics under
  another third, and the last third is bookkeeping for a language weaker than
  Agda. The coding substrate is not on the right base (`Formula (V ℓ) n` vs
  `Formula S n`; the bridge is `Relabel.liftFo`); the Δ₀ witnesses are dead
  weight for this purpose; the substrate is usable, not free, and not to be
  extended.
- **[L3.15] registered 2026-07-26; delivered same day at 34 lines.** Re-base
  the coding readers onto `S`: `L.Absoluteness` instantiates `Relabel` once at
  the bound "constructible" and composes four already-proved steps; no
  induction of its own. `BoundedFo InL` is free for constant-free readers; the
  identity relabelling in the last step is needed (`⊨-map` at `f = id`).
  Standing limit: the bridge is Δ₀ only; write unbounded predicates directly.
  Do not port further Δ₀ readers.
- **Reconnaissance and adjudication [L3.0.1], 2026-07-26:** the `[L3.0.2]`
  finding's operative content holds, its stated mechanism is false. The real
  mechanism is **witness-locality** (R-28): a graph may not describe an object
  by asserting the existence of that very object; pinned at
  `L.Recursion.witnessInModel`. Design change: slot = recursion index, table
  over it = value; no `∃̇C ∃̇S` wrapper. `[L3.0.5]`'s `finSetL` is load-bearing.
  Revised estimate for the bucket: 1,200 to 1,850.
- **Steps 1 and 2 delivered [L3.0.1], 2026-07-26:** `L.Coding.Model` (183) and
  `L.Coding.InL` (43) at the time. Two roads, both kept: constant-free readers
  are quoted through `[L3.15]`; readers naming a numeral are written fresh
  (one unbounded existential, unbounded is free now). The unscoped obligation
  (the ambient environment set) was half retired: `envIsFinSet` is `refl` (an
  environment is a finite set on the nose), and `seqSet` already collects
  sequences at every length; what remains is the characterization.
- **Step 3 opened, 2026-07-26:** two frames carry the twelve clauses (`extAt`,
  `binClauseAt`). A mis-count was caught and corrected: a three-frame grouping
  was wrong, the truth is **two frames, twelve relations**; and a fatal shape
  defect: `taggedCodes` carries arity on the outside and both frames read only
  one layer, making the clause vacuous at every arity but one (C-4). Fixed by
  reading the key in two layers.
- **Twelve-clause audit, 2026-07-26:** six lenses, 14 proposed, 11 confirmed, 6
  distinct defects after de-duplication, two of them fatal. Every de Bruijn
  index was correct. Fatal 1: `envOverAt` described a proper class (nine of
  twelve clauses vacuously true; fixed by a fourth conjunct pinning members to
  pairs). Fatal 2: the universal clause's outer guard was `⇒̇` where every
  other clause has `∧̇` (one token, unsatisfiable rather than wrong).
  Assumption-bill defect: implication was material, taken constructively (no
  `lem` added). Two scope defects in the bounded quantifiers (both ranged over
  the bound alone; fixed to range over the carrier and guard by the bound). A
  prose sentence stating an invariant hid fatal 2 (C-3). Unstated constraints
  listed for later chapters.
- **[L3.2] re-evaluation, 2026-07-27: downgrade.** (a) The headroom shrank
  about twentyfold in translation: 8k to 10k of hand-built material in the
  source is 338 lines here, or 827 lines, 14% of `src/`, counting every
  traversal-dense module. (b) Ordinary abstraction has already done the job
  five times (`Ladder`, `Definition`, `extAt`, the clause frames, `L.ReflectFo`'s
  box combinators). (c) Bedrock pays costs the source did not (exposition,
  generated terms, `FOL.Reification` at zero consumers for nine goals). Status
  DORMANT with a measurable re-open trigger.
- **Structural correction [L2.1 revisited], 2026-07-26:** the chapter that
  provides numerals as constants (`isL (# k)`) was split: `L.Axioms.Numerals`
  (constructive: the model's pairing, union, successor, the projection
  equations, `numeralL`) and `L.Axioms.Infinity` (classical: `ω∈L` and the
  collection step, and nothing else). `L.Coding.Model` stays `lem`-free. Watch
  for, but do not build first, a generic "definable step gives a definable
  recursion" lemma (the `Ladder` lesson: the interface is discovered from a
  real consumer).
- **Route audit to `hasChoiceL` [L3.20 follow-up], 2026-07-27:** five claims
  adversarially checked; two refuted (the rank-descent claim; the
  uniform-relation claim). Corrected: `hasChoiceL` is the transversal form
  (`L.Frontier.ChoiceStatement`), and the equivalence of forms is unbuilt
  model-internal mathematics; `isL` is definability, so a transversal has to be
  exhibited by a formula. `[L3.17]` is a characterization debt, not a blocker.
  Route table (dependency order): 1 `[L3.17]` (80-150, delivered 229), 2
  `[L3.0.1]` steps 4-7 (500-1,000, delivered 2,186: `Sat` 179, `Table` 248,
  `Sound` 801, `Unique` 630, `Slot` 187, `Graph` 67, `Satisfaction` 74), 3
  `[L3.21]` (100-250), 4 `Def` internalized at a stage (150-300), 5 `[L3.19]`
  (200-400), 6 `[L2.4]` `<L` (600-1,500, lowest confidence), 7 `hasChoiceL`
  (60-150, high). Total 1,700 to 3,750. Row 2 is the largest single miss this
  plan has recorded; the mechanism is that the twelve clauses are one statement
  written twice. The one question that now matters most: does the
  least-fixed-point idiom transfer to satisfaction?
- **Design ruling for satisfaction's `funct` [L3.0.1], 2026-07-27:** the
  coherence lemma wins; the least-fixed-point rescue does not transfer
  (satisfaction's clauses are equations, not closure conditions, so "least"
  has nothing to quantify over). The graph: twelve clauses conjoined, guarded
  by `closedAt C`, `x ∈ C`, and `domAt T C` (load-bearing); `svAt T` is not
  wanted. Estimate moves to 1,375 to 1,970. `⌜⌝`-injectivity returns as
  `[L3.22]`. `Sat` must be defined on `Formula S n`, not `Formula K n`. The
  blowup hazard was measured: the predictor is induction count times truncation
  elimination, not formula size (R-27).
- **Defect in delivered `[L3.16]` code, found 2026-07-27:** `tmValAt` reads one
  tag of two (constants pinned to the empty set under `extAt`); four clauses
  affected. Fixed the same day at 26 lines: the reader gains the constant
  disjunct and a characterization in both directions (C-5). The prose sentence
  that justified the one-case reader stopped being true at `[L3.18]` (C-3).
- **The build order's letters retire into codes, 2026-07-27:** U0-U7 mapped to
  owners. U0 `[L3.16]` DONE (the `tmValAt` repair). U1 `[L3.17]` DONE at 228
  lines, 1.8 s (`envSet` reads both ways). U2 `[L3.16]` DONE at 241 lines
  (chapter 836 → 1,077, 5.3 s; five of twelve clauses had no reader in either
  direction). U3 `[L3.0.1]` DONE at 74 lines, 1.2 s (`L.Coding.Sat`; splitting
  `cond` from `Sat` made it small). U4a `[L3.22]`. U4b `[L3.0.1]` DONE at 149
  lines (`L.Coding.Table` 125 + `L.Coding.InL` 24): the module application at
  the model did not finish in ten minutes until `pairʟ`/`unionʟ`/`sucʟ`/
  `numeralL` and their projections went into one `opaque` block in
  `L.Axioms.Numerals` (about a third of a second after; rule 2, module
  application is a conversion site). U5a `[L3.0.1]` DONE at 21 lines (the
  device already existed and only had to be exported). U5b `[L3.0.1]` DONE
  (`L.Coding.Sound` 801; the two atoms hit a conversion wall, cured by
  flattening the nesting into readings at a variable environment; one defect
  found by attempting the verification). U6 `[L3.0.1]` DONE (`L.Coding.Unique`
  630; the `⊥̇` case walled until stated with the formula recovered from the
  key rather than substituted into it). U7 `[L3.0.1]` DONE (`L.Coding.Graph`
  67, `L.Coding.Satisfaction` 74, `L.Coding.Slot` 187). The route to
  `hasChoiceL` is **eight codes**: `[L3.16]` residue, `[L3.17]`, `[L3.22]`,
  `[L3.0.1]`, `[L3.21]`, `[L3.19]`, `[L2.4]`, with `[L3.20]` closed behind
  them.
- **Post-`[L3.0.1]` inventory, 2026-07-28:** `src/` is **9,659** non-blank
  lines inside agda fences, 62 files (`L` 7,764, `FOL` 984, `V` 614, `Base`
  213, the rest 84). The `[L3.0.1]` cone alone is 4,142, 43% of the
  development. What is left in L3 is two codes (`[L3.21]`, `[L3.19]`).
  Projection: remainder 2,125 to 5,465, retirement −529, so `src/` finishes at
  11,255 to 14,595, mid about 12,900 (2.9x to 3.8x compression). **`[L3.0.2]`'s
  "L side 6,500 to 10,000" is superseded**: the `L` side is 7,764 today.
  Retirement, all verified by importer count: `L.Coding.Entry` 78, `Tagged`
  98, `Length` 158, `Recursion` 62, and the closed `FOL.Reification` namespace
  133: **529 lines**. `L.Coding.Closed` (163) is held as a plausible `[L3.21]`
  input. Three risks in order: the `<ʟ` stratification (risk 1, goes to
  2,500-3,500 if it does not close), `[L3.23]`'s overturn, and `[L3.21]`'s
  decode shape. Four bookkeeping defects found and fixed in the same pass.
  Next: `[L3.21]`, decode first, behind a probe of 60 lines or less.
- **`[L3.21]` decode, 2026-07-28:** a fifth wall, 2,237 s to 1.5 s, and neither
  seal nor variable restatement was involved. Bisection: the scaffolding alone
  is 2.4 s; the entire cost is the equation that says the produced formula's
  code is the code that was peeled. **The cause is that the frame's constructor
  is a variable**; the fix is to hand the frame the constructor's coding
  equation as a hypothesis and pass `refl` at the twelve concrete call sites
  (rule 5). Verified by perturbation rather than by reading: eleven deliberate
  corruptions, every one rejected (C-6). One overclaim corrected: a closed and
  shaped set is not always the key of a formula; the arity component needs a
  condition, and the set owes it, not the predicate.
- **`[L3.21]` delivered, 2026-07-28:** 670 non-blank lines in four chapters
  (`Descent` 44, `Shape` 334, `Recover` 190, `CodeSet` 102), 692 measured
  across the tree, whole `L` tree cold in 57 s; 2.8x to 7x over the 100-250
  estimate. The predicate's first conjunct (the arity) is the whole finding.
  What is NOT closed: the constants are unconfined, so `Codes A` is caught
  between two statements; `[L3.19]` cannot read `Def A` off it until the
  constants conjunct lands (`[L3.24]`).
- **L3 re-inventory, 2026-07-28 evening:** `src/` is **10,351** non-blank agda
  lines across 66 files, up 692 on the morning. Remainder 3,110 to 8,100,
  point estimate 6,200; final `src/` 12,930 to 17,920, point about 16,000.
  Retirement is 529 and not one line more; `L.Coding.Closed` comes off the
  retirement list. Six status conflicts found, the first four fixed. `[L3.24]`,
  `[L3.25]` and `[L3.26]` registered (the fourth, fifth and sixth time the
  unowned-prerequisite failure mode was caught; `[L3.24]` the first found
  inside a goal already declared done). Next: `[L3.24]`, behind a probe of 60
  lines or fewer.
- **Rule 6 has a boundary, found by `[L3.26]`, 2026-07-28:** the grep of
  unfold sites called four goals ([L3.24] three, [L3.25] two, [L3.26] zero
  across eleven outside consumers), all landing at or under estimate; but
  `[L3.26]` walled at 482 s inside its own proof. Rule 6 predicts what a change
  costs its consumers, and says nothing about what the theorem costs to prove
  (rule 6 in `dev/LESSONS.md`).
- **`[L3.23]` delivered, 2026-07-28:** `L.Coding.Uniform` 124 lines,
  `FOL.Manipulation.Relabelling` +20, `L.Coding.Bridge` −14, net **+131**,
  against the row's 240 to 610 and the probe's 40 to 70. The registered
  overturn did not fire: `Table`, `Slot`, `Sound` (801) and `Unique` (630)
  have **zero edited lines**, because the graph binds its table and its index
  set existentially. The only genuinely new mathematics was the bridge between
  two codings; `codeBridge` finally has a consumer; `mapFo` functoriality
  belongs in the relabelling chapter and is now there. Finding one sharpens
  rule 1 (R-30): the split between rules 1 and 2 is where the expensive
  construction lands, not proof-versus-type. Finding two: `AllCodes-closed`
  has no consumer and the prose claimed it did; corrected in both files and
  both languages (C-3).
- **A gap in the gate, found 2026-07-28:** `lint-prose.py` and
  `check-glossary.py` discover their inputs through `git ls-files`, so a new
  untracked file is silently skipped by those two stages. The fix belongs to
  `[L5.1]`; until then, run both linters explicitly on any new file before
  trusting a green gate (C-8).
- **`[L3.19]` route audit, 2026-07-29:** three independent designs, judged,
  then one probe; no code written. The ruling: take the sequence-
  characterization design, amended by the third design's scope cut. The
  powerset has to be written at a variable carrier and the hierarchy cannot
  stay external; internal `isL`, `L ⊨ V=L`, an object-language ordinal
  predicate, a big-union reader, and a `Recursion` instance for the hierarchy
  are all dropped, each verified unconsumed. Decomposition and estimate: 775
  to 1,385, point about 1,050, split 405 to 735 to `[L3.27]` and 370 to 650
  here, six chapters with build order C0, probe, C1-C6. **THE FORK, for the
  owner**: the code-set layer of the last two days (about 900 lines) was built
  on the warrant that `[L3.19]` reads the definable powerset off it; three
  independent designs and the judge agree that it does not. Options: (i)
  accept the layer as built ahead of demand; (ii) generalize the predicate and
  the graph in place; (iii) retire the unconsumed top. **The judge recommends
  (ii).** `AllCodes-closed` is bound to the same fork.
- **The owner ruled the `[L3.19]` fork on 2026-07-29: option (ii), generalize
  in place.** The satisfaction graph and the code predicate take the carrier as
  a **slot**; `Codes` and `AllCodes` are re-derived on top; exactly one code
  characterization. `AllCodes-closed` is retired with it. Safety property to
  check rather than assert: every fixed-carrier form must be re-derived at its
  existing type, so no delivered statement becomes weaker; if `Sound` or
  `Unique` acquires an edit, that is the signal to stop and re-measure.
- **C0 and the in-place generalization landed, 2026-07-29:** `L.Axioms.Basic`
  +26 agda lines (`Lset-suc`, `isL-𝒟ₒ`, `𝒟ₒS`), `L.Coding.Graph` 67 to 99,
  `L.Coding.CodeSet` 201 to 186, `L.Coding.Uniform` and `Everything` prose
  only. Whole tree cold 80 s, worst single file 20 s, `make check` green. The
  safety property held: every pre-change type came back by `refl`; the only
  type that changed is `twelveAt`, which became arity-generic. The generalized
  predicate needs one existential fewer. One defect fixed: `Lset-suc` was
  delivered with a dead `IsOrd σ` hypothesis. A simplification found and
  deliberately not taken: `𝒟ₒ→isL` collapses to two lines but belongs to
  `[L3.10]`'s re-layering.
- **`[L3.27]` complete, 2026-07-29:** `L.Coding.Powerset` 400 lines,
  `L.Coding.CodeSet` 186 to 200, `L.Coding.Uniform` 124 to 126; about **480
  net** against 405 to 735. `src/` is now 11,378 lines. Powerset cold 27.8 s,
  whole tree cold 105 to 120 s. The description was verified positively at an
  arbitrary ordinal; the side condition is load-bearing; a closed
  object-language sentence in which the carrier is bound by a quantifier and
  named nowhere was derived. **RULE 8**: a `PT.rec` over an object-language
  existential must name its payload type (payload left to inference over 140 s,
  written out 2.1 s). Two corrections to what the brief told the implementer
  (CodeSet's public readers; rule 2 predicted but did not fire on the
  introduction half). Watch item for `[L5.1]`: whole-tree cold doubled while
  four chapters were added.
- **`[L3.19]` COMPLETE, 2026-07-29:** `L.Coding.Sequence` 135 lines,
  `L.Hierarchy` 354, plus assembly: **+490** against the re-scoped 370 to 650.
  `src/` is **11,872** lines. Worst module 24.8 s; whole tree cold 127.5 s.
  `Lset-only` and `Lset-defines` are two implications between the graph and
  the meta `Lset`, with ordinality the only hypothesis on either side; `hierL`
  is sealed where it is built. All three design rulings held against the
  delivered code; non-vacuity was settled at concrete ordinals. **RULE 9**,
  which arrived by correcting rule 8's own chapter: the cost is not the alias,
  it is the reduction of the sentence once its slots are concrete; the sentence
  as a parameter with its own equation and `refl` at the one call site is
  23.5 s (alias everywhere 108 s, fully concrete 586 s). Rule 5 generalizes
  off constructors onto sentences. `L.Coding.Sequence`'s prose is corrected in
  both languages.
- **L3 status, re-confirmed row by row 2026-07-29:** 36 L3 rows read; closed
  33, open 3 (`[L3]` the container, `[L3.1]` standing, `[L3.10]` planned).
  The critical path through L3 is clear and `[L2.4]` opens; L3 does not close.
  Five rows carried a stale opening word until today. The pattern: **a row's
  opening word is what a reader takes, and appending a DONE record to the end
  of a long row does not change it** (C-7).
- **`[L2.4]` route audit, 2026-07-29:** three designs judged, one probe green,
  no goal code written. The registered risk is settled: the STEP is a
  comparison and the stratification closes (the trigger never fires); the
  FAMILY is a recursion and is now templated and measured (`Sequence` 135 +
  `Hierarchy` 354 = 490). The global order is not needed and should be struck:
  nothing on the route states a relation on all of `L`; `Cmp`, `FormulaOrder`,
  `CodeOrder`, the general `ΣSWO` and every global order law are **NOT
  NEEDED**; parameters enter as an environment rather than by substitution.
  This is the first demand the every-arity code set has had: the route
  consumes `AllCodes`, not `Codes`. Estimate 1,900 to 3,150, point about 2,400,
  in eight chapters. Probe green at 80 lines and 1.2 s: pure codes are
  hereditarily finite; the limit stage is closed under Kuratowski pairing and
  contains every numeral. **RULE 10**: a case split on ordinal trichotomy whose
  branches conclude in a membership hProp must be a named helper with its
  conclusion written down, never a `with` (did not finish in 90 s, killed at
  693 s and 13 GB inline; 2 s named; 45x). A blocker to budget: stage-bounded
  pairing must be lifted from a `where` block to a named public lemma (about
  30 lines). **THE FORK, for the owner**: how to well-order the hereditarily
  finite base. (i) Prove the finite stages finite and well-order them by
  min-difference: 250 to 450, no second recursion, one extra guarded branch,
  but it introduces a finiteness vocabulary the repository does not have at
  all (no `isFinSet`, `Discrete` or `Dec` in `src/`). (ii) Internalize a
  well-order on constant-free syntax as a constant: 550 to 900, uniform, but a
  second internalized recursion. **The judge recommends (i).**
- **The owner ruled the `[L2.4]` fork on 2026-07-29: option (i), the finite
  base by finiteness.** No second internalized recursion; the internal step
  gains one branch guarded by membership in the limit stage. The route buys a
  finiteness vocabulary the repository has none of; the discipline is to take
  the least that discharges the obligation and not import a general theory. If
  the chapter finds itself proving general facts about finite types, that is
  the signal that option (ii) was the cheaper buy after all.
- **`[L2.4]` C0 and C1 landed, 2026-07-29:** `L.Choice.Stage` 155 against 80
  to 150, `L.Choice.Finite` **619** against 250 to 450, plus 17 lines lifted
  in `L.Axioms.Basic` and 5 elsewhere. `src/` is 12,134. Worst module 8.5 s,
  whole tree cold 126 s. The finiteness is real and computes (the actual
  cardinalities of the first six stages derived by `refl`: 0, 1, 2, 4, 16,
  65536; a deliberate wrong number was rejected). The well-order is real by a
  decisive test: instantiating the search at the naturals under the reversed
  order derives falsity from the cover. The vocabulary stayed bounded as the
  ruling required. The measurement the owner asked to hear: the min-difference
  order is the expensive half (about 150 net lines more than a first-occurrence
  pullback), and what the 150 buys is **canonicity**; recorded rather than
  acted on, because the ruling said min-difference and C4 will answer whether
  the later chapters need canonicity. A fresh instance of law 2: naming a
  module application in a TYPE re-does it (`L.Axioms.Basic` +10.3 s, 8.2 to
  18.5; alias in the type costs zero; R-25).
- **`[L2.4]` C2 and C3 landed, 2026-07-30:** `FOL.Manipulation.Parameters`
  179 against 200 to 330, `L.Choice.Name` 410 against 250 to 400. `src/` is
  12,725. The occurrence trick makes decidable equality unnecessary: constants
  are counted and collected by OCCURRENCE, left to right; the parameter block
  sits AFTER the variables, so all four binders cost nothing and capture is
  impossible by construction. C3's order is three keys compared directly; all
  four well-order fields landed. **RULES 11, 12 and 13**, one accident seen
  three ways (in `dev/LESSONS.md`). Three renderings chosen by meaning and
  surfaced, not committed (abstraction of parameters, occurrence, chapter
  placement); the chapter did NOT mint a word for a parameter-free formula
  (already 无参 in the glossary).
- **`[L2.4]` C4 landed, 2026-07-30:** `L.Choice.Step` 348 against 250 to 400,
  cold 3.1 s. `src/` is 13,074. End extension came out as a PATH, not an
  implication (thirteen lines of path induction plus one). Well-foundedness is
  inherited honestly at both levels, checked by breaking each. **A MEASURED
  REDUNDANCY for the owner to rule**: the finite branch is logically surplus
  (the name branch in both cases compiles; an `opaque` seal is an equally good
  normalization barrier at the same cost), about twenty lines plus the
  chapter's one direct spend of the excluded middle; the design argument for
  keeping it (the book should not carry two unrelated well-orders of the limit
  stage) is a coherence claim the chapter never proves. Recommendation:
  delete the finite branch and the claim together. Not executed (owner's
  call). One coinage surfaced and not registered: `birth`.
- **The surplus branch is deleted, 2026-07-30, by owner ruling:**
  `L.Choice.Step` 348 to 331 and cold 3.1 s to 1.7 s; the seal is not merely as
  good a barrier as the stuck guard, it is a **faster** one. Gone with the
  branch: the inclusion transfer, the successor lemma for the limit stage, the
  finite chapter's order from the import list, and the chapter's one direct
  spend of the excluded middle. **`birth stage` registered as 诞生阶段 /
  誕生段階.** A rule the author broke and the gate caught: the Chinese written
  for this correction used two em dashes; rewritten with a colon (C-9 in the
  author's own words: the author of the rule is not exempt).
- **`[L2.4]` C5 landed, 2026-07-30:** `L.Choice.Internal` 700 lines against
  450 to 750, cold 9.5 s, whole tree 132.6 s. `src/` is 13,758. Both adequacy
  halves for the order landed; the min-difference formula was not needed.
  **THE AUDIT'S AMENDMENT 2 IS WRONG AS STATED**: membership in the limit
  stage is necessary and not sufficient; without more the description
  **collapses** (at a key that is nobody's code, one may take the index set to
  be that key alone, whereupon closedness and all twelve clauses hold
  vacuously). The repair is a code-set slot with the key required to lie in
  it. **A RESIDUAL GAP, which C6 must not assume away**: "the code lies in the
  limit stage" implies its constants lie there, not that it has none, so the
  least internal name of a set need not be its least meta name; the repair is
  a second code-set slot at the **empty alphabet**. **RULES 14 and 15** (in
  `dev/LESSONS.md`). A measurement recorded so a later chapter does not spend
  hours rediscovering it: the order at a CONCRETE pair of names is not
  derivable at all (probes killed at 90 and 100 seconds; law 11).
- **`[L2.4]` C6 landed, 2026-07-30:** `L.Choice.Internal` gained about 130
  lines for the faithfulness repair; `L.Choice.Table` is 459 new. `src/` is
  14,347. **The faithfulness repair is right and it is inert**: its three
  lemmas have zero use sites, and replacing the conjunct by a tautology leaves
  the rest of the chapter typechecking, so the gap the previous chapter named
  still stands. The table is a FRAME, not a theorem. **THE DEBT WAS
  UNDERSTATED IN FOUR PLACES**: it is three obligations, not one: the step
  condition must describe the order family at every ordinal, and that family
  is birth-primary; so filling it needs the step's adequacy, the birth stage
  described in the object language (nothing describes yet), and the code set
  at a carrier that moves with the birth. A defect no linter catches: two
  lines of tool-call scaffolding after the final marker would have been woven
  into every language; deleted (C-8). Revised remaining scope: about 3,800 to
  4,300 against the audit's 1,900 to 3,150. One surplus surfaced and kept: the
  limit-stage conjunct is derivable from the constant-freeness one, kept until
  retired on purpose.
- **`[L2.4]` faithfulness, 2026-07-30:** `L.Choice.Faithful` 525 lines, cold
  3.5 s. `src/` is 14,861. (b), the birth stage described, is CLOSED both ways:
  the description never says "the successor of b", it says the birth by the
  carve characterization; first use of object-language negation anywhere in
  `src/`, and it costs nothing. (c), the code set at a moving carrier, is
  CLOSED and it is an INSTANTIATION, not a construction. (a), the step's own
  adequacy, is NOT attempted and is parameterized honestly. The new conditions
  are load-bearing, checked the same way yesterday's inertness was caught:
  eight perturbations rejected. **FOUR MORE LAWS**: law 14 was mis-stated
  (seal the pair carrying the constructibility proof: 178 s to 2.0 s; again
  past 400 s against 3.5 s); an environment must be spelled out, never
  abbreviated (207 s vs 2.84 s, 73x); law 10 generalizes off trichotomy onto
  any split into a satisfaction (300 s vs 3.46 s); a description read at
  constants must be sealed where it is built (163 s and 160 s vs 3.5 s); the
  stage must arrive as a term, not a slot (two binders 163 s, one binder 3 s).
  All in `dev/LESSONS.md`.
- **`[L2.4]` obligation (a), 2026-07-30:** `L.Choice.Adequate` 658 lines,
  whole tree cold 154 s. `src/` is 15,435. The table is still conditional.
  Three findings: (1) no chapter builds the limit-stage order as an element of
  `L`, and until one does the step's adequacy cannot be applied at any
  concrete carrier (a chapter of its own); (2) the other relation slot is
  already discharged; (3) a shape mismatch in the parameter, not a meaning
  mismatch (four slots offered, seven wanted). **RULE 20**: `L.Choice.Name`'s
  `denote-table` cannot be discharged at all (restating its own type and
  filling it with itself does not finish in 400 s, while each of its two
  factors checks in 2.4 s; with the result type inferred the same substitution
  is 2.4 s, with it written down it never returns). The last link of piece 6
  is blocked in a DELIVERED module, not here. Delivered on `[L2.4]`: about
  3,640 lines across nine chapters; the audit's band was 1,900 to 3,150 and
  the goal has passed it while still owing a chapter. The overrun's cause is
  now precisely stated: the audit priced the internal side as one adequacy,
  delivery found three, and this chapter found a fourth.
- **`[L2.4]` the limit order, 2026-07-30:** `L.Choice.Limit` 458 lines.
  `src/` is 15,894. Three pieces unconditional; the fourth (the
  earliest-disagreement family) is another recursion in its own right, and the
  probe returned AMBER on SCOPE rather than on feasibility, estimated 400 to
  650. Law 1 measured again at 82x at a new place: the level inlined at its six
  sites cost 144.55 s; arriving as a variable with its defining equation,
  1.76 s. Two things worth keeping that are not laws: the first universal
  quantifier used anywhere under `src/L/` appears here and is free; and the
  second key's description needs no equation between levels because the
  disjunction binds a different number of levels in each disjunct. `[L2.4]`
  stands at about 4,100 lines across ten chapters.
- **`[L2.4]` the earliest-disagreement family, 2026-07-31:** `L.Choice.Before`
  1,110 lines against 400 to 650, cold 4.6 s, whole tree 156 to 172 s.
  `src/` is 17,005. `L.Choice.Limit.Described` is instantiated and the limit
  order is UNCONDITIONAL. **A NINETY-NINE FOLD WALL**: building the family did
  not finish (killed past 400 s); the template's parameter-carrying-its-own-
  equation remedy alone brought it to 376 s; sealed where built, each reading
  in its own unfolding block: 376 s to 3.79 s. The parameter remedy and the
  seal are not alternatives (R-26). Three economies worth keeping: the
  approximation below a numeral is finite; the predecessor of a numeral is its
  membership-maximal member; one description serves two consumers. **THE
  FORK, the last one on this goal**: `L.Choice.Faithful`'s step parameter is
  still not discharged, and the obstruction is structural: the two chapters
  each hold what the other needs, one stage apart; closing it is a re-cut of
  where the step adequacy is supplied. Not taken. A gate defect found by a
  positive control: the glossary checker's avoid-list keys off the language
  markers, so a forbidden rendering outside any marker is silently not a
  violation (C-8). `[L2.4]` stands at about 5,200 lines across eleven
  chapters.
- **`[L2.4]` the re-cut, 2026-07-31:** THE FORK'S PREMISE DID NOT HOLD; the
  change is about 40 lines rather than a restructure. The step parameter
  already hypothesised the carrier side; what blocked the instantiation was
  the SPELLING of the table's four readings (stated at the constructed set,
  they were circular at the top level). Restated at "whatever realizes the
  class", the circularity is gone. The two ends now meet, shown by machine: a
  probe supplies all six arguments of the step adequacy at a stage; a second
  probe checks the step chapter's new readings apply to that same stage. The
  safety property held completely: every delivered statement comes back
  accepted at its old spelled-out type, definitionally; one statement changed
  and it is a WEAKENING of a frame's hypothesis. The table is still
  conditional; what remains is assembly with no new idea. **Two more laws**:
  a property of a computed least name must BE the well-order chapter's
  least-element predicate at an exported family, never a re-spelling of it
  (16 s vs nothing; R-22); the TYPE a frame concludes in must be sealed where
  it is built (unsealed it did not finish past 200 s, sealed the chapter is
  7 s; R-21). Pre-existing drift fixed in passing: the step chapter's recap
  still described the deleted second branch.
- **`[L2.4]` IS DONE, 2026-07-31. THE FRONTIER IS EMPTY AND DELETED.**
  `L.Choice.Order` 424 and `L.Choice.Transversal` 232 close the chain.
  `src/L/Frontier.lagda.md` is gone, and `L.Model` now reads `module L.Model
  {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where L⊨ZFC : isZFCModel; L⊨ZFC = record
  { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }`. **The constructible universe
  models ZFC, with the excluded middle as the only assumption besides the
  universe level.** Verified personally rather than from a report: the module
  takes no frontier parameter, and a scan of every `agda` fence in `src/`
  finds no `postulate`, no interaction hole, no `TERMINATING`, no
  `primTrustMe` and no weakened option pragma anywhere. `make check` green.
  The transversal typechecked on the first try, the only chapter on this goal
  that did; its route is the one the audit settled. `L.WellOrder.Base` finally
  has its consumer. **One more law, measured at the assembly**: the TYPE a
  frame concludes in must be sealed where it is built (R-21; the same
  application at variable slots is free, a defined constant already blocks the
  runaway, and `opaque` is the robust form). Knock-on repairs from the
  deletion: the Agda linter's message, the dependency map's legend, the style
  guide, the source README and the landmarks lose their references to the
  frontier. Final accounting for the goal: about 5,900 lines across thirteen
  chapters, against an audit band of 1,900 to 3,150; the cause, stated once:
  the audit priced the internal side as one adequacy; delivery found three,
  then a fourth, and the last of them was a whole recursion.
- **`[L3.28]` the compression pass, full record, 2026-07-31:** registered by
  owner request, runs before `[L4]`; about **quantity, not correctness**.
  Twenty-two conversion laws were measured during this layer, and most of them
  did not exist when the earliest chapters were written (`L.Coding.Sound` 801
  and `L.Coding.Unique` 630 predate rules 5, 9, 14, 16 and 20 entirely). Three
  concrete candidates were in hand: (1) `𝒟ₒ→isL` 18 lines to 2, blocked only
  by file order; (2) `L.Choice.Finite`'s min-difference order, about 150 lines
  more than the first-occurrence pullback, buying canonicity; (3)
  `L.Coding.Satisfaction` (74), the per-formula instance `L.Coding.Uniform`
  supersedes. Method: measure before estimating; **no compression lands
  without a before-and-after measurement, and no delivered statement may
  weaken**, checked by re-spelling the pre-change types and demanding them
  back. **Candidate (3) DONE 2026-07-31, by deletion**: a whole-tree import
  sweep found exactly two modules no other module imports (`Landmarks`, the
  entrance, zero-consumer by design, and `L.Coding.Satisfaction`); the fork
  closed on `Uniform`'s own recorded evidence; deletion is cascade-clean,
  **−127 file lines, −74 Agda lines**, plus the three dangling references
  repaired. **SCOPE WIDENED 2026-07-31 by owner request**: the pass now covers
  all of `src/`, with a best-effort target of `src/` under 10,000 Agda lines.
  **SURVEYED the same day, whole tree**: baseline after candidate (3) is
  **17,492 non-blank Agda lines** in 37,271 file lines across 75 masters.
  First finding, negative in a load-bearing way: there is no module-level dead
  weight (the import cone of `Landmarks` reaches all 74 non-index masters).
  The lever table, conservative to optimistic: (a) dead names −150 to −400,
  (b) verbatim-repeat extraction in `Sound`/`Unique` about −90, (c) an
  ∃ⁿ-with-∧ frame combinator −120 to −300, (d) frame retrofit of the pre-law
  chapters −200 to −341, (e) one generic fold for `FOL/Manipulation` −120 to
  −200, (f) the recursion-assembly triplication −130 to −200 at the
  conservative cut only, (g) sealed-constant dedupe DECLINED (module-
  application hazard). **Candidate (2) is STRUCK**: canonicity has a consumer
  (`L.Choice.Before`), and the pullback prices to net +60 to +360, a loss.
  **The arithmetic**: (a) through (f) sum to **−755 conservative, −1,486
  optimistic**, so the tree lands between **16.0k and 16.7k** and the 10k
  best-effort target is not reachable by compression of the current
  architecture. **SUPERSEDED IN PART the same day**: the widened target turned
  out to ask one question, how `L ⊨ AC` is proved; cutting the single edge
  `L.Model → L.Choice.Transversal` splits the tree into a ZF-only cone of
  **4,180** lines and an AC-only radius of **13,217 (75.6%)**; option C prices
  to **8.3k to 10.5k**; the fork and its pricing live in
  **`dev/memos/L3.28-ac-route.md`**. While unruled, levers (b), (c), (d), (f)
  were GATED; (a) proceeded restricted to the ZF cone, (e) on the ZF-cone
  `Manipulation` chapters, candidate (1) proceeded. **RESOLVED 2026-07-31: the
  ruling is C (D15)**, and the gate dissolves rather than lifts; levers (b),
  (c), (d), (f) retire with the chapters they would have compressed; the 10k
  target transfers to `[L3.29]`'s landing measurement, tightened band 9.5k to
  10.5k. This row closes when `[L3.29]` lands or aborts.
- **`[L3.29]` the B pivot's evidentiary basis, 2026-08-01:** five reports in
  `_build/` (about 1,800 lines total) documented the route's measured state
  and the two probes; their content is condensed and preserved in
  **`dev/memos/L3.29-b-pivot.md`** (the audits' verdicts with their key tables,
  the four junk cases, the stratified producer order, the A-versus-B table,
  the B work plan's price tables, and the open risks). The M5a report's
  Surprises 1 supplied law **P-g** and the graft entry in `dev/LESSONS.md`.
