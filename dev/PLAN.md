# PLAN: porting L ⊨ ZFC from fol-reification

The construction plan for Bedrock's first milestone: re-landing the `fol-reification`
result (V=L ⊨ ZFC, hence Con(ZF) → Con(ZFC)) as textbook-grade literate Agda in this
repository. This is a developer doc (English only, not translated). Decisions recorded
here were ratified by the owner on 2026-07-16 and are binding until the owner revises
them. Work is managed by the goal codes of §6; the MASTER status table is §11.

- **Source repository:** `choukh/fol-reification`, local sibling checkout at
  `../fol-reification`. Reference pin at planning time: commit `8b190d5` (2026-07-16,
  M2.7 build-optimization landed; the Con(AC) mathematical milestone itself dates to
  2026-07-14). Re-pin the exact source commit in §11 when L1 porting starts.
- **Toolchain parity:** both repos use Agda 2.8.0 + cubical 0.9; all source modules are
  `--cubical --guardedness`. No toolchain migration is needed.

## 1. The theorem, stated honestly (D1)

What the source proves, and what Bedrock will claim, is:

> In Cubical Agda (the host), the constructible sub-universe L of the HIT cumulative
> hierarchy V is a ZFC model: `L⊨ZFC : isZFCModel 𝒮ʟ` where `𝒮ʟ` is `𝒮ᵥ` restricted to
> the inductive constructibility predicate. Semantically this yields the **relative**
> consistency Con(ZF) → Con(ZFC), relative to the host theory (Cubical Agda with
> universes, informally about ZFC plus an inaccessible).

The unqualified claim "Con(ZFC)" is never made, in code names, prose, or marketing.
The root chapter opens with exactly this framing: what a model is, what "relative to
the host" means, and why the host's strength is the declared, auditable price (this
matches the Charter's position that rigor is independent of metatheoretic strength).

Assumption budget of the source proof, to be preserved or improved:

- The `--safe` framework core (FOL, Reification, ZF interface, HIT-V model) is
  zero-postulate, machine-enforced by `--safe`.
- The L development rides **exactly one postulate**, excluded middle
  (`Classical.lem : (P : hProp ℓ) → ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩)`). No holes, no `TERMINATING`,
  no `--allow-unsolved-metas` anywhere in the source `src/`.
- Bedrock removes even that postulate by parameterization (D2), making the whole tree
  `--safe`.

## 2. Source material survey (condensed)

Facts an implementing agent needs before touching the port:

- **Scale:** 172 literate modules, about 70.7k lines. Of these, `L/` holds 142 modules
  and 66.5k lines (94%). The `--safe` core (Prelude, Truth, FOL, Reification, ZF,
  Models/HITV, Examples) is only about 4k lines and is already clean.
- **Root module:** `src/L/ModelZFCFinal.lagda.md` defines `L⊨ZFC : ZFCModel` (alias
  `Con-AC`). The ZF axiom fields live in `src/ZF/Model.lagda.md` (records `ZFModel`,
  `ZFCModel`); separation and replacement consume the deeply embedded `Formula`, which
  is where the reification framework is load-bearing.
- **Difficulty concentration:** the bulk of `L/` is the well-order `<L` and the
  L-recursion, reified as Δ₀ graph-certificate clusters (`Cmp*`, `Depth*`, `Order*`,
  `Trace*`, `Coh*`), plus internal satisfaction (`Sat*`, `Tarski*`) and coding
  (`Code*`, `Formula*`). These clusters are the L3 reduction-review targets.
- **Prose:** Chinese research-log style throughout (milestone provenance, probe
  numbers, performance archaeology). It is **construction intelligence for the
  porting agent, not translation input** (D6).
- **Performance engineering:** the source carries a documented playbook of
  conversion-blowup countermeasures (opaque seals, explicit implicit arguments,
  Π-parameterized assumption bundles); see `../fol-reification/docs/WORKLOG.md` §5.
  After the upstream M2.7 optimization, the full lem-cone cold check runs in about
  8.5 minutes at `-j4` with per-module heap caps (down from 157 minutes). The build
  machinery (`tools/gen-deps.py`, `config.mk`, generated `deps.mk`,
  `tools/audit-targets.py`) is portable; its trust model is codified as constraints
  in §7.
- **Goal management:** the source runs an append-only route-tree register
  (`../fol-reification/docs/ROUTE-TREE.md`) with dotted-decimal goal codes. Bedrock
  adopts a lightened version of the same discipline (D9, rules in §6.0).

### 2.1 Cost anatomy (measured 2026-07-25)

Where the source's mass actually sits, measured by attributing every module to the
`isZFCModel` field whose proof term reaches it. Method: non-blank lines inside
` ```agda ` fences (prose excluded, so these numbers are smaller than the 70.7k above);
transitive dependency closure from each field's filling term; module granularity, except
the six assembly modules (`L.ModelAC`, `L.ModelACSep`, `L.ModelACNum`, `L.Condensation`,
`L.ModelZFC`, `L.ModelZFCFinal`), which are split per definition so that the small fields
are not swallowed by the module hosting five of them. The whole `L⊨ZFC` cone is 150
modules and 48,260 code lines; the other 22 modules (2,521 lines) are probes and unwired
experiments, which the consumption audit drops at port time anyway.

Field names below are Bedrock's (§4 ledger), source names in parentheses where they
differ. "Body" is the code that literally fills the field, "cone" includes all shared
dependencies (so the column does not add up), "own" is code reachable from this field
alone.

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

Read as a partition, the twelve ZF fields own 211 lines between them. Their real cost is
three shared blocks: the framework and carrier trunk (2,266 lines, reached by all
thirteen), the Δ₀ engine with the full-formula reflection machinery (2,571 lines, serving
separation, replacement, power and choice), and the numeral chain (392 lines, serving the
four infinity-side fields). Everything else is `hasChoice`: 42,354 lines, 88% of the
cone, of which 42,258 sit in 106 modules that no other field touches.

That mass is not one proof. It is 8 to 10 hand-built instantiations of a single pipeline
(step function to Δ₀ graph to "the graph is a set of L" to certificate to soundness),
once each for comparison, depth, the order itself, satisfaction, traces, coherence,
sequence codes, and the closure families. Clone measurement over the twin families, after
normalizing names, gives the shape of it:

| module pair (renaming-normalized) | similarity |
|---|---:|
| `CmpCertMatrix` / `DepthCertMatrix` | 86% |
| `CmpCodeCarrier` / `DepthCodeCarrier` | 67% |
| `CmpGraphInL` / `DepthGraphInL` | 60% |
| `CmpGraphInLFinal` / `DepthGraphInLFinal` | 50% |
| `CmpSound` / `DepthSound` | 8% |
| `OrderGraph` / `CmpGraph` | 4% |

So the scaffolding repeats and the soundness segments do not: the mathematics genuinely
differs per instance, but the harness around it is written out once per instance. The
reason is structural. The source has no counterpart of the layer textbooks carry as
rudimentary functions and Σ-recursion absoluteness, that is, no general theorem saying a
recursively defined function is internalizable in L. Every function builds its own.
Density counts corroborate the picture: 27.9 formula-syntax tokens and 8.3 Δ₀ witness
tokens per 100 lines, 3,963 explicitly spelled implicit arguments and 139 `opaque` seals
(the M2.7 performance tax), and 53% of all lines sitting inside `where` blocks.

Projected reduction, by lever, each with the goal code that executes it and the register
entry that tracks it:

| Lever | Headroom | Code | Candidate |
|---|---|---|---|
| General internalization theorem | to roughly 8k to 12k total | `[L3.0]` | S5 |
| `reify!` macro industrialization | 4k to 6k | `[L3.2]` | S6 |
| Scaffolding parameterization | 3k to 5k | `[L3.4]` | S3 |
| Transition-layer sweep | 2k to 3k | `[L3.1]` | S9 |
| Transport and cast solver | 1k to 2k, high risk | `[L3.9]` | S7 |
| Dispatch-grid generation | 1k to 1.5k, source lines only | `[L3.8]` | S8 |

The five syntactic levers together are 25% to 40%, and every one of them trades against
cold-check time. The general theorem is the only lever that reaches further: it would
collapse the 8 to 10 pipelines into one theorem plus small instances, putting the
certificate mass in the 8k to 12k range. It is also the only lever that is research
rather than refactoring. D12 rules on which to take, §6.1 orders their execution.

> **Correction (2026-07-25, `[L3.0.3]`).** The 8k to 12k figure above is the ceiling of
> a **three-theorem programme**, not the yield of `[L3.0]`. The probe measured the
> pipelines directly and found that the constant-table theorem covers 13,518 of the
> 42,258 lines, that `Order*` (11,386 with its trace machinery) needs a separate
> stage-indexed theorem, and that `Sat*` / `Tarski*` / `Coh*` (10,706) fit only by
> halves. On tier 1 alone the honest projection is 42.3k to about 36k. The route
> survives, and the probe also found a second abstraction worth as much as the theorem
> (a per-tag clause bundle). Full tier table and evidence:
> [memos/L3.0.3-subsumption-probe.md](memos/L3.0.3-subsumption-probe.md) §5 and §6.

## 3. Ratified decisions

| # | Decision | Ruling (owner, 2026-07-16) |
|---|----------|----------------------------|
| D1 | Statement of the result | As in §1: V=L ⊨ ZFC, relative consistency, relative to the host. Never unqualified "Con(ZFC)". |
| D2 | Classical boundary | No `postulate` anywhere. LEM (and any classical/choice principle) is an explicit parameter; the whole tree is `--safe`. Gated by the L0.2 performance spike; a materially worse projection (rule of thumb: over 1.5x the M2.7 full-cone baseline) escalates back to the owner before proceeding. Documented fallback if re-ruled: one postulate module with an explicit safe boundary. |
| D3 | Technical lemma layer | L3 starts with a **reduction review** per cluster: first try to shrink the code substantially and re-layer it so the narration flows end to end, with no long stretches of dry material. Only if a cluster resists reduction may its exposition be tersened, per cluster, with explicit owner sign-off. |
| D4 | Licensing | Confirmed: ported code enters `src/` under CC BY-NC-SA 4.0 via the existing `REUSE.toml` carve-out (the owner authors both repositories). No in-file SPDX headers. Prose cites Rech (2020) and the source repository where the mathematics warrants it. |
| D5 | Skeleton | The previously reserved `src/` namespaces are void. The redesigned skeleton in §4 replaces them; `src/README.md` is rewritten in L1. Below the part level the skeleton is **provisional** (D11, tension T2). |
| D6 | Prose | Full rewrite for beginners, English first, then Chinese (Japanese pre-supported). Source research prose is never translated; it serves the porter only. |
| D7 | Naming hygiene | No iteration-numbered or provenance-flavored names survive the port (`WellOrder2`, `ChoiceSetInL2`, `ModelZFCFinal`, `Absoluteness2`, primed predicates). The §4 mapping table is the rename ledger; extend it as porting proceeds. |
| D8 | Construction order | Root-first via the Frontier record (§5): the statement of the theorem typechecks from day one, details land last. Reading order on the site remains foundations-first; the `Everything` import order is the reading order. |
| D9 | Goal management | Work is managed by route-tree goal codes in the style of the source's ROUTE-TREE register, rooted at the letter **L**: top-level goals L0 to L5, sub-goals Lx.0 onward. Coding rules in §6.0. Commits and docs touching planned work carry the code in brackets, for example `[L1.4]`. |
| D10 | Build performance | The build constraints of §7 are binding from the first ported module: single-invocation trusted gate, parallelism outside the trust base, tracked cold-check budget, per-module heap caps. Cold-check regressions are defects, not background noise. |
| D11 | Revisability | The plan legislates for known unknowns explicitly: legislation may be added mid-course (standing L0 track), the skeleton below the part level may be re-cut after L3, Frontier fields may be re-cut, and a whole-book harmonization pass runs at L4. Mechanisms in §8. |
| D12 | L3 reduction strategy | **Outcome 2026-07-26 (`[L3.0.2]`): the decision was right, the analysis was wrong.** The lever was not a large internalization theorem (it is 96 lines) but general-formula comprehension, delivered at `[L2.2]`; the projected 65%-at-3x is now measured-and-projected at 7x to 14x. Original ruling, 2026-07-25: **take the big lever first.** Before the certificate clusters are reduced one by one, attempt a general **internalization theorem for L-recursion** (goal `[L3.0]`). Grounds: the §2.1 measurement shows the certificate mass is 8 to 10 hand-built instantiations of one pipeline, repeating because the source has no rudimentary-function / Σ-recursion absoluteness layer; the syntactic levers cap out at 25% to 40%, the theorem reaches roughly 65%. This is research, not refactoring, so it runs under an explicit paper-level gate and pre-agreed kill criteria (`[L3.0.3]`, `[L3.0.1]`), and D3's per-cluster reduction review stands as the route for whatever the theorem does not absorb. Schedule ruling, same day: the paper-level probe `[L3.0.3]` opens **before** L2, so the route's cheap kill signal arrives before the axiom branches commit to a Frontier cut at the certificate boundary. |
| D13 | Macros and generated proof | **Ruled 2026-07-27 by the owner.** Opacity is **not** an objection: avoiding macro black boxes is not a project aim. Explain the macro's own logic, cut the code volume, and the reader's burden goes *down*, closer to real mathematical practice. **The single veto is conversion blowup.** So a macro or reification route is judged by exactly two measured questions: is it smaller, and does it keep `src/` inside the §7.5 and §7.6 budgets. If both, pursue it actively. Supersedes the exposition argument that had been recorded against `[L3.2]`, which is withdrawn. |
| D14 | Retiring a chapter in waiting | **Ruled 2026-07-27.** A chapter is *in waiting* when nothing outside its own namespace imports it (`Everything` never counts; it imports everything). Such a chapter is **retired** (files deleted, `Everything` entries dropped, the commit hash recorded in §11 so it is recoverable, plus one line saying what would bring it back) when **both**: no **open** goal names it in §6.1, and either a goal that did name it has closed without using it, or no goal ever named it. It is **kept** only under a **written warrant**: a named open goal *and* a dated expiry, the goal at whose closure the question is asked again. Warrants live in §11 and expire whether or not anyone looks. **Trigger:** at every goal closure, list the chapters in waiting and check their warrants; it is one grep. Rationale: this book is read, so a chapter with no consumer costs a reader's attention, not just disk; and `FOL.Reification` sat at zero consumers for nine goals precisely because nothing ever forced the question. |

## 4. Target skeleton (D5)

Top-level parts mirror the book's parts. The part level (Base, FOL, ZF, V, L,
Landmarks) is fixed; **cluster-internal layout is provisional until the L3.10
re-layering review** (tension T2), and file splits inside a cluster are finalized at
port time under the STYLE-agda rules (L0.0).

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
    ├─ Frontier              TEMPORARY: the assumption record = the un-ported cut (§5)
    ├─ Model                 ★ root: L ⊨ ZFC (Frontier-parameterized until L4)
    ├─ Ordinal/, Hierarchy/  ordinals, L-stages
    ├─ Definability/         the Def operator
    ├─ Recursion/            PENDING [L3.0]: the internalization theorem for
    │                        L-recursion; the clusters below become its instances
    ├─ Satisfaction/         internal Tarski truth in L
    ├─ Coding/               formula and sequence coding
    ├─ Closure/              "x is in L" closure lemmas
    ├─ Axioms/               per-axiom chapters: Basic, Separation, Replacement, Infinity, Power
    ├─ Condensation/         condensation and the power-set bound
    ├─ WellOrder/            the global well-order <L; Certificates/ pending L3.7 (§10 S3)
    └─ Choice/               the choice set in L
```

Rationale, briefly: `Base/` collects everything that is about the host rather than the
mathematics, so the remaining parts read as book parts. Reification nests under `FOL/`
because it is logic machinery, not a peer subject of V and L. The source's
`Models/HITV` becomes `V/` because in a textbook V is a subject, not "a model
instance". `Landmarks` is the trophy case and gives stable statement anchors.

Rename ledger (append-only; extend as porting proceeds; a re-cut after L3 adds new
rows rather than editing old ones):

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
| `L.{Cmp*, Depth*, Order*, Trace*, Coh*}` | `L.WellOrder.Certificates.*` | layout decided by the L3.7 reduction review |
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
| `L.{Cmp*, Depth*, Order*, Trace*, Coh*}` | `L.Recursion` + per-function instances, pending `[L3.0]` | D12, 2026-07-25: conditional successor to the `L.WellOrder.Certificates.*` row above. On a green `[L3.0.2]` verdict the theorem takes the working name `L.Recursion` and reads before the clusters that instantiate it; each source pipeline becomes a short instance chapter under the cluster that owns its mathematics. On a red verdict this row is void and the `Certificates.*` row governs |
| `L.{Cmp*, Depth*}` + `FFST*` / `L.{Order*, Trace*, Canon*, Env*}` / `L.{Sat*, Tarski*, Coh*}` | `L.Recursion` instances / `L.Recursion.Staged` instances, pending `[L3.12]` / `L.Recursion.Partial` instances, pending `[L3.13]` | `[L3.0.3]`, 2026-07-25: refines the row above, which lumped all five families under one theorem. The probe measured three tiers with different homes, and the tier boundaries cut across the `[L3.5]` to `[L3.7]` cluster boundaries (`Canon*` is a closure-cluster module belonging to the staged tier), so the final layout is an `[L3.10]` question |
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
| `ZF.Coding` | `FOL.Coding` | `[L3.3]`: un-deferred as L3 phase B opens. Namespace by subject, `FOL/`: it codes the object language into a structure, and it is generic over that structure (an injective pairing and an injection of the naturals, as module parameters), so it belongs beside `FOL.ZFStructure` rather than under the model chapter. Reads at the Part 4 doorstep with `Relabelling` and `Bounding`. **`⌜⌝-inj` is dropped by consumption audit** (`[L3.1]`, S9): it is the 12-by-12 grid of §10's S8, 132 of whose 144 clauses carry no mathematics, and the `Codes` relation with `codes-canon` is what every consumer was designed around. It returns only if a consumer demands it. **A consumer demanded it, 2026-07-27** (`[L3.0.1]`'s satisfaction table), and it returns as `[L3.22]`, not as `[L3.9]` work: that pointer named the wrong goal, and `[L3.9]` is abandoned with "a future need returns as a new code" |
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
holds one record whose fields are the *statements* of the not-yet-ported lemmas, and
the root theorem is proven from it:

```agda
record Frontier ℓ : Type (ℓ-suc ℓ) where
  field
    sep-in-L : ...    -- statement of the separation lemma, etc.

module L.Model {ℓ} (lem : LEM (ℓ-suc ℓ)) (F : Frontier ℓ) where
  L⊨ZFC : isZFCModel 𝒮ʟ
```

The record is the cut across the dependency tree: each ported branch deletes its
fields, the field list is the live progress board, and `make check` stays green at
every commit. When the record is empty, `L.Frontier` is deleted, the parameter is
dropped, and the unconditional theorem stands (L4). Frontier fields are the **only**
sanctioned form of "not proven yet"; holes and postulates never appear.

**Frontier re-cuts are normal (D11).** A field is not a contract with the source's
interface: when an L3 reduction changes the natural statement of a lemma, the field is
replaced (a *re-cut*), provided the root still typechecks and `make check` stays
green. Re-cuts are recorded in the §11 field count and, when they affect already
ported chapters, in the affected cluster's L3 memo (tension T5).

**LEM as a parameter.** `Base.Classical` states the interface and derives its
consequences; the packaging validated by the L0.2 spike is
`LEM : ∀ ℓ → Type (ℓ-suc ℓ)` with classical-cone modules taking
`(lem : ∀ {ℓ} → LEM ℓ)` in their telescopes (STYLE-agda §1). The entire tree,
`Everything` included, is `--safe`.

**Reading order versus structure order** (owner ruling, 2026-07-18): the book
keeps two catalogs. The **reading catalog** is `Everything.lagda.md`, the landing
page: import order = reading order, hand-maintained, and its sections are reading
units that need not coincide with namespaces, since a chapter reads where its
first consumer needs it. The **structure catalog** is the namespace tree, derived
automatically and never hand-maintained: the sidebar groups modules by namespace
(groups ordered by first appearance in `Everything`, members in reading order
restricted to the group), and chapter pages carry previous/next links along the
reading order. Namespace membership is decided by subject, reading position by
first consumption; the two are independent.

**Construction order versus reading order.** These are deliberately different. The
build proceeds root-first (Frontier shrinks over time); the book reads
foundations-first (`Base → FOL → ZF → V → L → Landmarks`, fixed by the `Everything`
import order). Neither order constrains the other.

## 6. Route tree (D9)

### 6.0 Coding rules (lightened from the source's ROUTE-TREE §0)

1. **Code form** = `L<goal>.<subgoal>…`, dotted decimal, rooted at L0 to L5. Always
   written in brackets in prose and commits (`[L2.3]`), which also keeps codes
   visually distinct from the `L/` module namespace and from `L⊨ZFC`.
2. **Codes are identity, not order.** Sibling numbers carry no temporal or priority
   meaning; scheduling lives in the status field and the gate conditions.
3. **Immutable and append-only.** A code, once assigned, is never renamed, deleted,
   reused, or renumbered. New work takes the next free number under its parent. A
   goal that gets re-stated or re-split gets a **new** code; the old one is marked
   SUPERSEDED with a pointer. **Carve-out (owner ruling, 2026-07-25):** a branch whose
   codes have *all* never left PLANNED, with no work committed against any of them,
   may be renumbered once by explicit owner ruling; the old-to-new map is recorded in
   §11 so earlier references stay traceable. Exercised once so far, for L3, on the day
   the reduction levers were registered.
4. **What gets a code:** a goal with its own success criterion (a chapter cluster, a
   spike, a review, a piece of legislation). Individual lemmas and modules are
   artifacts hanging under a code, not codes themselves.
5. **Status vocabulary:** PLANNED, ACTIVE, DONE, PARKED (viable but shelved,
   revivable), SUPERSEDED (points to successor), ABANDONED (with reason). Status
   changes are dated and updated in place; history lives in git.
6. **Bookkeeping:** register a code in §11 *before* starting the work; update the §11
   row in the same commit that changes a goal's status. New codes discovered
   mid-work are registered immediately, not backfilled.

### 6.1 The tree

**[L0] Legislation (standing track; never closes, see T1).**
The initial set L0.0 to L0.2 gates L1; later L0.x items are opened whenever porting
uncovers an un-legislated situation.

- **[L0.0]** `dev/STYLE-agda.md`, initial edition: OPTIONS policy (`--cubical --safe
  --guardedness` everywhere), assumption policy (D2; Frontier as the only debt form),
  module and lemma naming rules (D7), the notation table (dotted object-language
  operators, superscript families, semantic brackets), record-versus-data and
  universe-polymorphism conventions, annotation rules for performance idioms (each
  `opaque` seal or explicitly-spelled implicit carries a marker comment so narration
  can skip it), and the master chapter template (motivation, definitions, statement,
  proof, recap). Rules may be marked **provisional** (T1) and hardened later.
- **[L0.1]** First glossary batch in `dev/glossary.toml`: constructible universe,
  cumulative hierarchy, condensation, absoluteness, reification, adequacy, relative
  consistency, well-order, and companions.
- **[L0.2]** LEM parameterization spike (gates D2): parameterize one or two
  representative heavy `L` modules over LEM, measure cold-check time against the
  source baseline, project the full-cone cost, record the verdict in §11.
- **[L0.3]** `scripts/lint-agda.py`: a code-side linter for the masters, wired into
  `make check` and the pre-commit hook. Flagship check: **import necessity**, every
  name bound by a `using`/`renaming` clause must actually be used, so the import
  block is always necessary (sufficiency is the typechecker's job). Companions:
  the exact OPTIONS header, the using-list discipline for `open import`, and the
  forbidden-construct ban (postulate, TERMINATING pragmas, holes). `Everything` and
  the designated hub modules (`Base.Prelude`, `Base.Truth`) are exempt from the
  import checks by design; `-- lint-agda: keep` is the per-import escape hatch.
- **[L0.4]** Two-catalog doctrine (owner ruling, 2026-07-18): legislate the
  reading-catalog / structure-catalog split of §5 (`Everything` = hand-maintained
  reading order; sidebar = namespace tree derived from it, never hand-maintained;
  per-chapter previous/next links along the reading order). Implementation: the
  §5 paragraph, the `STYLE-agda` §2 note, the `src/README.md` Everything section,
  the `Everything` opening prose, and the renderer (sidebar tree + `chapnav`).
- **[L0.5]** Register `Ord` as an abbreviation in `STYLE-agda` §3 (opened 2026-07-25
  during `[L2.0]`). The predicate `IsOrd` shipped at `[L1.6]` and the ordinal chapter
  adds `∅-ord`, `suc-ord`, `setUnion-ord`, `boundingOrd`, so the short form is
  load-bearing across the L side while §3's registered list did not carry it. The
  alternative, spelling `ordinal` in every stage lemma, loses to tradition and to
  signature width.
- **[L0.6+]** Reserved for mid-course legislation, opened as discovered.

Gate for L1: L0.0 to L0.3 DONE and approved by the owner.

**[L1] Root and trunk skeleton.**

- **[L1.0]** Lay the §4 skeleton (replacing the old reserved namespaces), rewrite
  `src/README.md`, add `-WnoUnsupportedIndexedMatch` to `bedrock.agda-lib`, pin the
  source commit in §11.
- **[L1.1]** Port `Base/` (Prelude, Truth, Classical-as-interface).
- **[L1.2]** Port `FOL/` core (Syntax, Semantics, Renaming).
- **[L1.3]** Port `FOL/Reification/`.
- **[L1.4]** Port `ZF/` (Model; Encoding/Coding as needed), fold in the Ceiling
  prose (compactness explains why strong axioms are model fields), and execute the
  **reading-order re-cut** (owner ruling, 2026-07-18): Part 1 slims to Syntax,
  Structure, Semantics; the reification chapters (Base, Combinators, Graded,
  Absoluteness) move to read right after `ZF.Model`, their openings rewritten to
  point backward at the separation/replacement fields and to motivate with
  self-contained micro-examples instead of destination-naming; `Renaming` and
  `Relativize` move to the Part 4 doorstep at `[L2.x]`, before their first
  consumers. Namespaces stay `FOL.*`; only reading order and ToC placement move.
- **[L1.5]** Port `V/` (Hierarchy with the structure instance, Smallness,
  Definability, Coding, Satisfaction, Model).
- **[L1.6]** Port `L.Constructible` (isL and the minimal machinery to define `𝒮ʟ`).
- **[L1.7]** Write `L.Frontier` and the root `L.Model` statement.
- **[L1.8]** Create `Landmarks`; set the `Everything` reading order.
- **[L1.9]** Diaconescu and the single-hypothesis ZFC instance (owner ruling,
  2026-07-18): a `Base.Choice` chapter (`SetChoice` re-homed from `V.Model`,
  level-indexed like `LEM`; `choice→lem` mechanized via set quotients and
  effectivity), the corollary `V.Model.V⊨ZFC-fromChoice`, and a fourth
  landmark. The "two independent assumptions" prose is corrected to the one-way
  statement: LEM does not prove choice; choice proves LEM levelwise, but
  `SetChoice ℓ` cannot reach `LEM (ℓ-suc ℓ)`, so the fixed-level pair stays
  mutually non-implying and the two-parameter `V⊨ZFC` remains the finer
  accounting.

All L1 ports carry full textbook prose (en + zh). Gate for L2: `make check` green;
the owner reads the trunk end to end as a book and signs off the tone. `[L3.0.3]`, the
paper-level probe of the L3 big lever, opens at this same boundary and runs alongside
L2; it is source-reading only, so it neither blocks nor is blocked by this gate.

**[L2] The axiom branches, in pedagogical order.**
Each branch descends until it hits a technical cluster flagged for reduction review;
those cuts stay in the Frontier (T3). `[L2.4]` additionally waits on the `[L3.0.3]`
verdict before fixing its Frontier cut, so that the certificate-boundary cut is made in
the theorem's shape if the theorem is viable (T5 avoidance, D12 schedule ruling). Per-branch exit: check green, prose complete
(en + zh), glossary updated, the branch's Frontier fields deleted or explicitly
re-cut.

- **[L2.0]** Basic axioms (extensionality, foundation, empty, pair, union); source
  `L.ModelAC`. The warm-up.
- **[L2.1]** Infinity; source `L.ModelACNum`, `L.ModelACInfinity`, the numeral chain.
- **[L2.2]** Separation and Replacement; source `L.ModelACSep`, `L.ModelACReduce`,
  the reflection engine (`L.Reflect*`, `L.ReflectFo`, `L.StageBound`,
  `L.Delta0Local`). The methodological core: this is where reification pays off and
  gets its full narrative.
- **[L2.3]** Power via Condensation; source `L.Condensation`, `L.CondReduce`,
  `L.PowerBound`.
- **[L2.4]** Well-order and Choice trunk; source `L.ConstructibleOrder`,
  `L.WellOrder2`, `L.ChoiceSetInL2`, stopping at the certificate-cluster boundary.

**[L3] The technical layer, big lever first (D12), then reduction-first (D3).**
`[L3.0]` runs ahead of the cluster work and decides its shape: it attempts the general
internalization theorem, and only what the theorem does not absorb goes through the
per-cluster review. That review is unchanged: (1) a **reduction review memo** (what the
cluster does, why it is as large as it is, the consolidation plan, the projected size,
the layering design for the narration, and the **impact list** on already ported
chapters, T5); (2) owner gate on the memo; (3) port per the approved plan, measuring
check-time throughout (§7); (4) prose at full narrative quality by default, with the D3
per-cluster fallback only on explicit sign-off.

Each measured reduction lever of §2.1 carries its own code. Execution runs in four
phases; the sequence below is authoritative, the numbers are not (§6.0 rule 2).

> **A, design** (before and during L2): `[L3.0.3]` subsumption probe, **before L2**
> (delivered 2026-07-25) → `[L3.0.4]` theorem statement and clause-bundle design, after
> `[L2.2]`.
>
> **B, substrate**: `[L3.1]` sweep (standing from here on) → `[L3.2]` `reify!` →
> `[L3.3]` coding cluster.
>
> **C, machinery** (re-evaluated 2026-07-25 after `[L2.2]`, see the three grounds
> below): `[L3.0.5]` finite families → `[L3.11]` clause bundle → `[L3.0.1]` tier-1
> proof of concept → `[L3.0.2]` verdict → green: `[L3.12]` stage-indexed theorem and
> `[L3.13]` partial-certificate variant / red: `[L3.4]` scaffolding merge.
>
> **Grounds for the re-evaluation.** (a) `[L3.0.4]`'s stage table attributes stage 7 to
> `[L3.2]`; it does not belong there. What stage 7 needs is one lemma, "a finite family
> drawn from a stage is a set of `L`", about sixty lines by finite disjunction. It is now
> `[L3.0.5]`, done, and **`[L3.2]` leaves L3.0's critical path entirely**. (b) `[L3.11]`'s
> stated rationale was de-risk: the source's WORKLOG case 13 records a twelve-field record
> of formula-valued fields failing to typecheck at all, and a bundle that blows up predicts
> a theorem that blows up. **That de-risk has been paid, by accident, in `[L2.2]`**:
> `L.ReflectFo` carries a twelve-clause tree (`Answers`), its twelve-clause raise, and a
> twelve-clause recursion (`gstep`) returning a Σ-package of an ordinal with its witnesses,
> the same shape at the same width, checking in about two seconds. What remains of
> `[L3.11]` is line saving, not risk, so it no longer gates on caution: it gates because the
> proof of concept consumes it. (c) `[L3.0.4]` §3's `reads : List (Σ[ t ∈ S ] ⟨ isL t ⟩)`
> carries the exact hazard `[L2.2]` diagnosed at `L.Axioms.Full`: sets paired with
> constructibility certificates, used as **constants of the clauses' object language**.
> Those certificates must be sealed where they are built, or the theorem does not finish.
> Recorded as an amendment to the statement memo rather than a re-statement of it.
>
> **D, ports**: `[L3.5]` `[L3.6]` `[L3.7]`, as instantiations on a green verdict and as
> originally planned on a red one → `[L3.10]` re-layering. `[L3.8]` and `[L3.9]` are
> opportunistic and execute inside whichever goal first needs them.

**Schedule change (owner ruling, 2026-07-25): phase B opens before `[L2.2]`.** L2 is
suspended after `[L2.1]` and L3's substrate starts now; `[L2.2]` to `[L2.4]` resume
afterwards. Verified before adopting, by taking the dependency cone of the coding cluster
against the pinned source: it reaches **none** of `L.ModelACSep` (separation),
`L.Reflect*` (the reflection engine), `L.Condensation` (power) or `L.ChoiceSetInL2`
(choice). The cone is 44 modules, of which 17 and about 4.9k lines are unported, and its
one surprise is `L.ConstructibleOrder`, which is not L2 work at all but the strict
well-order vocabulary that both branches need. Consequence to keep in view: the Frontier
stays at four fields for the duration and `L.Model` keeps its parameter, which is the
device working as designed rather than a regression.

**Why all of phase C precedes any cluster port.** `[L3.0.3]` measured the tier
boundaries and they cut *across* the cluster boundaries: `Canon*` sits in `[L3.6]`'s
closure cluster but belongs to the stage-indexed tier, and `Coh*` sits with the
certificates but fits only by halves. Porting a cluster before knowing which of its
members are theorem instances would re-create exactly the T5 problem the probe was run
to avoid. So every piece of reduction machinery lands first, and the clusters are ported
against finished machinery.

Two cautions on reading the sequence. The `L3.x` numbers ran in execution order when the
branch was renumbered on 2026-07-25 under the §6.0 rule 3 carve-out (map in §11), but the
carve-out is spent, so goals registered since (`[L3.11]` to `[L3.13]`) take the next free
number and execute in the middle: read the phases, not the digits. And `[L3.0]`'s own
sub-goals have never been in order (`.3` and `.4` before `.1` and `.2`), which is rule 3
working as designed.

- **[L3.0]** **Internalization theorem for L-recursion (the big lever, D12; S5).** Target
  statement, working form: from a *step specification* (a tag alphabet, a Δ₀ clause
  matrix over coded arguments, and a well-founded measure) derive, once and for all,
  (i) that the induced recursion's trace is a set of L, (ii) a certificate relation
  sound and complete against the meta-level recursion, and (iii) uniqueness of the
  certified value. This is the layer the textbooks carry as rudimentary functions and
  Σ-recursion absoluteness; the source has no counterpart, which is why §2.1 finds the
  same pipeline written out 8 to 10 times.
  - **[L3.0.0]** SUPERSEDED 2026-07-25 by `[L3.0.3]` and `[L3.0.4]`. The single design
    memo was split once the schedule was audited: its source-facing half needs nothing
    from Bedrock and can run before L2, while its Bedrock-idiom half is blocked on
    vocabulary that `[L2.2]` fixes. Never started; no content lost.
  - **[L3.0.3]** **Subsumption probe, source-reading only, opens before L2.** Read the
    source at the pinned commit and answer one question: does a single step
    specification subsume `Cmp*` and `Depth*`? They are the closest twins (scaffolding
    overlap 50% to 86%) and they diverge exactly at soundness (8%), so the answer must
    take the soundness argument as instance data and absorb only the harness; a design
    that claims to absorb soundness is wrong. Then classify `Order*`, `Trace*`, `Coh*`,
    `Sat*` and the closure families as fits or does not fit, with the reason.
    Deliverables: that fits table, and a **required-interface checklist** naming the
    vocabulary the theorem will need, so `[L2.2]` and `[L3.3]` can be ported in the
    shape it wants (compare WORKLOG §5 case 12: codes must be an inductive relation,
    never raw values whose equalities force normalization). **This is where the cheap
    kill signal lives:** if no single shape subsumes even the twins, D12's route is red
    before L2 begins. Runs entirely against `../fol-reification`, touches no `src/`
    file, and cannot affect `make check`. Owner gate.
  - **[L3.0.4]** **Theorem statement in Bedrock's idiom.** Prerequisite: `[L2.2]`,
    which fixes `BoundedFo`, the reflection interface and the separation vocabulary the
    statement has to speak. Consumes `[L3.0.3]`'s fits table and checklist as input.
    Deliverables: the specification signature and the theorem stated over Bedrock's
    names, a projected line budget for the theorem and for one instance, and the list
    of §4 chapters it would displace. Per the probe's recommendations, the signature
    carries the per-tag `ClauseBundle` (whose construction is `[L3.11]`) and the `reads`
    field for instances that name an already-internalized table, and it does **not**
    discharge the cmp instance's `wcCert` hypothesis, which is a Frontier field.
    `Depth` is the reference instance and `Cmp` the stress instance; `FFST` is
    degenerate and will not exercise the signature. Gated before `[L3.3]` finishes.
    Owner gate.
  - **[L3.0.5]** **Finite families at a stage.** DONE 2026-07-25. `finSet`{.Agda},
    `finSet-in`/`finSet-out` and `FinOf.finSetL` in `L.Axioms.Basic`: a finite family
    of members of `Lset σ` is a set of `L`, by the finite disjunction of "equals this
    one" over the stage's index type. Registered on re-evaluation as stage 7's real
    prerequisite, correcting `[L3.0.4]` §4's attribution of it to `[L3.2]`. It
    generalizes the same chapter's hand-written pairing, which is its two-element case,
    and it is what places a recursion's table of values at one stage. 60 lines.
  - **[L3.0.1]** **Proof of concept (tier 1, the constant-table theorem).**
    Prerequisites, all now met or in hand: `[L3.14]`, the coding substrate (done),
    since certificates quantify over coded formulas and sequences; `[L3.0.5]`, stage 7's
    lemma (done); `liftFo`, stage 5, landed at `[L2.2]`; and `[L3.11]`, whose bundle is
    the specification's `clauses` field. **Run the reference instance and the theorem in
    one loop, not the theorem then the instance**: the `[L2.2]` lesson is that the right
    interface is discovered from a real consumer and guessed wrong in the abstract, which
    is how `Ladder` was found and how the source's `ReflectN` was avoided. Prove the theorem and re-derive `Depth` and `FFST` as instances,
    then `Cmp` as the stress case. Measure lines and cold-check per §7. **Kill
    criteria, agreed in advance:** the theorem fails to reach two instances; or an
    instance is not materially smaller than the source pipeline; or §7.6's per-module
    budget is breached and the WORKLOG §5 playbook does not clear it. Any one of them
    ends the attempt, and the result is written up either way.
  - **[L3.0.2]** **Verdict and rollout ruling.** Green: `[L3.12]` and `[L3.13]` open,
    `[L3.5]` to `[L3.7]` are re-stated as instantiation goals under new codes and the
    originals marked SUPERSEDED (§6.0 rule 3), and the theorem lands as `L.Recursion`
    per the §4 ledger row. Red: `[L3.12]` and `[L3.13]` stay closed (both build on tier
    1), `[L3.4]` opens, and `[L3.5]` to `[L3.7]` proceed exactly as originally planned
    with the S6 and S7 levers of §10 as the remaining reduction budget.

  Scheduling and safety: `[L3.0.3]` opens **now**, ahead of L2, because it is the only
  research-risk item on the critical path and its inputs (the pinned source, plus the
  `isL` / `Lset` / `Def` vocabulary already landed at `[L1.6]`) all exist; `[L3.0.4]`
  follows `[L2.2]` and gates before `[L3.3]` finishes; `[L3.0.1]` runs after `[L3.3]`
  and before `[L3.5]`. Running the probe ahead of `[L2.4]` is deliberate: that branch
  states its Frontier cut at the certificate-cluster boundary, and knowing the theorem's
  shape first lets the cut be made in that shape instead of being re-cut later under
  T5. The Frontier (§5) is what makes a research gamble affordable at all: the
  certificate cuts stay as fields for the duration, `make check` stays green throughout,
  and a red verdict costs the attempt and nothing else.

  One risk the split does not remove: a memo written before any axiom branch has been
  ported in Bedrock is written by a porter still fluent mainly in the source's idiom,
  which is the D6 failure mode (source research prose is porter intelligence, never
  translation input). `[L3.0.3]` is scoped to survive it, since a fits table and an
  interface checklist are findings about the source rather than Bedrock prose, and
  `[L3.0.4]` is what waits for the idiom to exist.

- **[L3.1]** **Transition-layer sweep (S9), standing.** The cheapest lever and the one
  that runs first, because every later lever operates on whatever survives it: ahead of
  each cluster port, run the consumption audit over that cluster and drop what the
  source's own later strata superseded (iteration remnants such as the `SatWitness` /
  `SatWitnessK4` pair, bridge modules such as `SubBridge` and `HierarchyBridge`, the
  `ProbeM1*` probes). Measured headroom 2k to 3k. Success criterion: every cluster memo
  opens with a drop list naming each dropped module and the audit finding that justifies
  it, so the reduction is visible rather than silent. Standing goal, no single
  completion date; it closes with `[L3.10]`.
- **[L3.2]** **`reify!` industrialization (S6). DORMANT, re-evaluated 2026-07-27 with
  measurements rather than inherited figures.** The goal was to extend the source's
  reflection macro (`FOL.Reification.{Base, Combinators, Certified}`, 133 lines, ported at
  `[L1.3]` and **still with zero consumers**) so it emits Δ₀ witnesses, `BoundedFo`
  witnesses and L-side environment slices, then to re-derive the hand-built formula /
  witness / adequacy triples from it.

  **The headroom did not survive translation.** The inherited figure, 4k to 6k saved
  against 8k to 10k of hand-built material, was measured on the source. Bedrock's whole
  equivalent is `FOL.Manipulation.{Relabelling, Renaming, Bounding, Relativize}` = **338
  lines**, and those four modules are almost entirely twelve-clause traversal. Counting
  every traversal-dense module in the book (those four plus `FOL.{Coding, Semantics,
  LevyHierarchy}`, `L.ReflectFo`, `L.Coding.InL`) gives **827 lines, 14% of `src/`**.

  **Probed 2026-07-27 under D13, and the answer is to adopt the framework, not to build a
  macro.** Two deliverables were rebuilt through `FOL.Reification.Combinators` and measured
  against their hand-written originals in `L.Coding.Model`:

  | deliverable | hand-written | reification | ratio |
  |---|---:|---:|---:|
  | `appAt` + adequacy (content-heavy) | 21 | 19 | 1.1x |
  | `svAt` + its two directions (pure congruence) | 27 | **10** | **2.7x** |

  The split is exactly where it should be. `appAt`'s work is `collapse`, the proof that a
  truncated existential over the model is plain membership, which needs `isL-trans`; no
  framework does mathematics, so nothing is saved. `svAt`'s work is de Bruijn bookkeeping
  and four substitutions through two helper lemmas; the framework builds it inside out in
  one expression and both helpers disappear.

  **The obstruction I assumed does not exist.** `RepP` is a pair, so a *quoted* reader
  injects as a leaf: `(prAtL … , prAtL-adequate …)` **is** a `RepP`, and the combinators
  build upward from it. Quoting and reification compose, so the hierarchy-side readers and
  the model-side predicates live in one calculus.

  **D13's veto does not fire.** Per-module profile: `Probe` 107 ms,
  `FOL.Reification.Combinators` 81 ms, `Base` 23 ms. No conversion cost at all.

  **Consequence for the goal's own name.** The probe used **no macro**. `RepΔ₀` already
  sits in `Certified`, which was one of the three extensions this goal proposed to add. So
  the ordering is: adopt the combinators for congruence-shaped predicates now, and treat
  `reify!` proper as a later question whose margin is smaller precisely because the
  combinators will already have taken the saving.

  **Ordinary abstraction has done part of the job**, five times: `Ladder`, `Definition`,
  `extAt`, `binClauseAt`/`unClauseAt`, and `L.ReflectFo`'s `Box`/`joinBox`/`addBox`, with
  16 combinator uses in `L.ReflectFo` and 40 in `L.Coding.Model`. That is evidence a
  combinator is often enough, not evidence a macro is unwanted.

  **D13 (owner ruling, 2026-07-27) governs this goal.** Opacity is **not** an objection:
  the project does not aim to avoid macro black boxes. Explain the macro's own logic, cut
  the code volume, and the reader's burden goes *down*, closer to real mathematical
  practice. **The one veto is conversion blowup.** So the test is exactly two questions,
  asked with measurements: does it shrink the code, and does it keep `src/` inside the §7.5
  and §7.6 budgets. If both, pursue it.

  An earlier version of this entry argued from exposition ("twelve `cong₂` clauses read as
  prose, a macro call is opaque"). **That argument is withdrawn under D13** and must not be
  reintroduced.

  **ATTEMPTED AND REJECTED ON MEASUREMENT, 2026-07-27, branch `l3.2-reification`.** The
  adoption was carried out for real: `retarget`/`retarget₀`/`predOf` added to the framework
  (step 1), `L.Coding.Base`'s hub reader `prAt` rebuilt through the certified combinators
  with its three public names kept as projections (step 2), and `L.Coding.Entry` rebuilt on
  top of it (step 3, the plan's own decisive test). Everything typechecks; `make check` is
  green on the branch. **Both of D13's tests fail.**

  **Not smaller.** `L.Coding.Entry` 78 → 56, a genuine 22-line saving, exactly the shape the
  audit predicted. `L.Coding.Base` 187 → **218**, a 31-line cost. Net over the two modules
  the plan rated best: **265 → 274, +9 lines.** And the hub cost is not deferred: 13 of the
  31 lines are the three reps' type signatures, which the framework never removes, and the
  step-6 shim deletion can recover only 3.

  The reason is the discriminating rule, applied where the plan had not applied it. The
  framework pays where an adequacy lemma already exists stating a nice predicate *and* two
  or more `subst` sites hang off it. `prAt-adequate` has **zero** `subst` sites: it was
  already a three-line `⇔toPath` over `prChar-fwd`/`prChar-bwd`. So the hub is the worst
  possible shape, and the hub is the one module that cannot be skipped.

  **And it degrades a budget for nothing.** `L.Coding.Model`, which was **not** converted,
  goes 1,720 ms on `main` to 2,144 / 2,186 / 2,211 / 2,291 ms across four cold runs on the
  branch, a consistent **+25% to +33%**; the tree goes 20.5 s to 21.1–21.8 s. That is not a
  conversion blowup in D13's sense, and the absolute figures stay far inside §7.5 and §7.6.
  But it trips the plan's own step-2 abort gate of 2.1 s, and paying it for a negative line
  delta is a bad trade on both axes. The cause is structural: `prAt` is now
  `prAt-rep q u v .fst`, so every downstream site that recognised it by its constructor tree
  reduces through the rep.

  **Would more consumers amortise it?** The plan projects `Tagged` −22 and `Length` −9. Even
  if both hold exactly, all four chapters land at about −22 lines against a permanent
  +25–33% on the largest coding module, and the two modules already measured came in 40
  lines worse than projected. The expected value is break-even at best.

  **Ruling: do not adopt.** The three source commits were **reverted in place** once the
  measurement was in; this entry is the deliverable. (A first version of this ruling said
  "the branch is the record and is not to be merged", which is wrong and is corrected the
  same day:
  the branch also carries `[L2.3]`, `[L3.18]` and `[L3.20]`, so it merges, and it is the
  rejected refactor that comes out rather than the branch.) What survives is the calibration, which is now measured
  rather than projected: a reification framework of this shape pays only where an adequacy
  proof carries multiple transports, and a hub whose adequacy is already direct will eat the
  savings of every leaf that quotes it.

  **What would change the answer.** Not a macro; `reify!` generates the same reps and would
  inherit the same hub cost. Only a different framework interface would: one where a rep's
  predicate need not be restated in a signature (the 13 lines), and where `translate` of a
  built rep is *definitionally* the hand-written formula in the eyes of downstream
  pattern-matching rather than merely propositionally equal (the 25–33%). Both are framework
  redesigns, not adoption work, and neither is scheduled.

- **Chapters in waiting, and their warrants (D14), first census 2026-07-27.** Scanned by
  the D14 rule: nothing outside the namespace imports it, `Everything` excluded.

  | in waiting | warrant: which open goal needs it | expires at |
  |---|---|---|
  | `FOL.Reification.{Base, Combinators, Certified}` | the one use `[L3.2]` did **not** test: a graph handed to `L.Recursion.Definition.graph`, which `hasReplacementL` consumes without ever matching on the formula, so the 25–33% cost that sank the coding-chapter adoption cannot arise there | `[L3.0.1]` |
  | `L.Coding.{Base, Entry, Tagged, Length, InL}` | `[L3.0.1]`, the satisfaction certificate | `[L3.0.1]` |
  | `L.Recursion` | `[L3.0.1]`, its instance half | `[L3.0.1]` |
  | `L.WellOrder.Base` | `[L2.4]` | `[L2.4]` |

  **So the answer to "can `FOL.Reification` be deleted now" is: not yet, and for exactly one
  more goal.** `[L3.2]` measured and rejected it for the coding chapters, where downstream
  code recognises a formula by its constructor tree. It did not measure the case where a
  built formula is handed straight to a comprehension field and nobody looks inside, which
  is what `[L3.0.1]` will do. At `[L3.0.1]`'s closure the warrant expires: if the graph was
  built by hand there too, the namespace is retired under D14 and the 133 lines go, with the
  hash recorded.

  **Process note, recorded because it cost real bookkeeping.** This exploration ran in a
  git branch while a second conversation worked the same worktree. Its `git add -A` swept a
  revert of mine into one of its commits, so `[L3.2]`'s backing-out is recorded inside
  `7428a23` rather than in a commit of its own. Nothing was lost and the tree stayed green,
  but two conversations must not share a worktree: give the second one its own, or serialise
  them.

  Note that most of `L.Coding` is also in waiting. That is not a smell: those chapters were
  written **for** `[L3.0.1]` and are days old. The warrant mechanism exists to tell that
  case apart from the one `FOL.Reification` was in, having had no dated expiry for nine
  goals.

  **Corrections on the record.** One turn before the re-evaluation I called `[L3.2]` "the
  real lever" on the twenty-nine traversals; that was said before measuring. And the
  re-evaluation cited `FOL.Reification`'s nine goals at zero consumers as "evidence about
  demand"; **that inference does not hold.** `RepP n P = Σ[ φ ] (∀ γ → (γ ⊨ φ) ≡ P γ)` is
  literally the shape of **11** adequacy lemmas hand-written in `L.Coding.Model` over two
  days without the framework being reached for, and `Certified.RepΔ₀` already supplies the
  Δ₀ witness that this goal listed as something the macro still had to add. Zero consumers
  measured discoverability, not fit.
- **[L3.3]** SUPERSEDED 2026-07-25 by `[L3.14]`, after a consumption re-measurement
  (§11). The goal was scoped as the source's whole `Code*` / `Formula*` / `VarCoding` /
  `SeqChar` cluster, about 4.9k lines; measuring consumers showed that only the Δ₀ code
  readers are substrate and the rest is instance data.
- **[L3.14]** **Coding substrate: the Δ₀ code readers.** What the theorem and every
  certificate actually consume: the set-theoretic characterizations of singleton, pair
  and Kuratowski pair, and the object-level readers `sglAt`, `pairAt`, `prAt`, `tagAt`,
  `unpairAt` with their adequacy lemmas, already parameterized over de Bruijn position
  in the source. Source `SatCertBase` (68 consumers), `SatCertEnv` (44), `SatCertLen`
  (46), `SatCertCons` (13); about 910 lines. `FOL.Coding` and `V.Coding` landed under
  `[L3.3]` and stand. Optional accelerator: roughly the formula-and-adequacy half of
  these chapters is what `[L3.2]`'s macro is for, so `[L3.2]` may be taken first; the
  characterization lemmas are set-theoretic mathematics and no macro generates them.
- **[L3.11]** **Per-tag clause bundle (S10).** Registered 2026-07-25 on the probe's
  finding that the twelve tags are traversed **five times per instance**: once for the
  clause formula, once for its Δ₀ witness, once for its bounding witness, once for
  soundness, once for witness satisfaction, spread across five modules. Deliverable: a
  `ClauseBundle` record carrying all five artifacts for one tag, plus the dispatcher
  that assembles a certificate from a twelve-element bundle family, so a tag is
  declared once. Measured target: 3,130 lines of per-tag work in `Cmp*` alone (the
  source's own WORKLOG case 19 calls 132 of one module's 144 clauses mathematically
  empty), and roughly 4.4k across tier 1. Runs **before** `[L3.0.1]`, for two reasons:
  it is the specification's `clauses` field, so the proof of concept consumes it; and
  it is the cheap de-risk for the expensive step, since a bundle that cannot be built
  without conversion blowup predicts a theorem that cannot either. Worth taking on a
  red `[L3.0.2]` as well, which is why it is its own goal and not a sub-goal of
  `[L3.0]`.
- **[L3.12]** **Stage-indexed internalization theorem (S11), tier 2.** Registered
  2026-07-25 on the probe's finding that `Order*` does **not** fit the constant-table
  theorem: `G_ord` is not a constant table, its certificate's env comparison reads the
  graph itself, the graph is ordinal-indexed and built by transfinite recursion, closure
  runs by ∈-induction with a successor/limit dispatch under LEM, and images come from
  `hasRepl` rather than finite `mkSett` tables. Target statement: a transfinite
  recursion whose step is internalizable yields an internalizable ordinal-indexed
  family. Covers `Order*`, `Trace*`, `Canon*`, `Env*`, 11,386 lines. **Gate: opens only
  on a green `[L3.0.2]`**, because tier 2 builds on tier 1 (the order certificate names
  `cmpGraphV` as a constant leaf). Same research discipline as `[L3.0]`, so it carries
  its own memo, proof of concept and verdict as sub-goals, with kill criteria fixed
  before code.
- **[L3.13]** **Partial-certificate variant (S12), tier 3.** Registered 2026-07-25 on
  the probe's finding that `Sat*`, `Tarski*` and `Coh*` (10,706 lines) fit by halves:
  they share the certificate, soundness, witness and closure stages, but not the
  constant table, because the total clause's only witness for `satSet` is `satSet`
  itself, which is circular. The source's own escape is a `(C,S)`-pair *partial*
  certificate carrying a downward-closed code set (`L.CohCert`). Deliverable: that
  partial certificate as a **variant of the tier-1 specification** rather than a third
  theorem, plus the classification of which of the three families it reaches. Gate:
  green `[L3.0.2]`; runs before `[L3.5]`, the cluster it serves.
- **[L3.4]** **Scaffolding parameterization (S3), conditional.** Fallback consolidation:
  merge the repeated pipeline harness (graph, in-L, in-L-final, certificate matrix, code
  carrier) into modules parameterized over a step specification, leaving each function a
  short instantiation. Measured headroom 3k to 5k, and measured ceiling: the twins share
  50% to 86% of their scaffolding but only 4% to 9% of their soundness, so this lever
  can only ever take the harness. **Gate: opens only on a red `[L3.0.2]`**, since a green
  verdict absorbs it entirely. Carries the same blowup discipline as `[L3.0]` (explicit
  implicits, `opaque` seals from the first commit).
- **[L3.5]** Satisfaction cluster (source `Sat*`, `Tarski*`, `Realize`, `Reflect*`
  remnants).
- **[L3.6]** Closure cluster (source `FFST*`, `Canon*`, `SatSetInL`, `SeqSetInL`).
- **[L3.7]** Well-order certificate cluster (source `Cmp*`, `Depth*`, `Order*`,
  `Trace*`, `Coh*`); the largest at 42.3k source lines (§2.1).
- **[L3.8]** **Dispatch-grid generation (S8), opportunistic.** Generate the mechanical
  coverage grids (the source's 12 by 12 tag dispatch in `CmpWitnessSat`, the
  `CodeOrder.triSameTag` layout) instead of writing out clauses whose bodies carry no
  mathematics. Measured headroom 1k to 1.5k of **source lines only**: the source's own
  fix moved those clauses to a cheaper codomain rather than deleting them, so check-time
  is unaffected and this lever buys readability, not speed. Naturally a byproduct of
  `[L3.2]`; executes inside whichever cluster goal first hits a grid, and is skipped
  outright if `[L3.0]` removes the grids.
- **[L3.9]** **Transport and cast solver (S7), lowest priority.** Spike first, roll out
  only on evidence: on one module, check whether generated `subst`/`cong` chains keep the
  playbook's safe shape (path operations sunk into top-level helpers over neutral
  endpoints) or the inlined shape that WORKLOG §5 cases 14, 15 and 18 had to undo. 3,300
  measured sites, 1k to 2k of headroom, and the highest risk-to-reward of the five. A
  failed shape check closes the goal ABANDONED with the measurement recorded; it is not
  retried per cluster.
- **[L3.10]** Post-reduction **re-layering review** of the whole `L/` subtree (T2):
  with all clusters landed, revisit the branch splits of §4, re-cut where the
  reduced code suggests a better decomposition, and append the renames to the §4
  ledger.

**[L4] Convergence.**

- **[L4.0]** Empty the Frontier, delete `L.Frontier`, drop the parameter; the
  unconditional `L⊨ZFC` lands.
- **[L4.1]** Whole-book **harmonization pass** (T4): re-read end to end, fix
  foreshadowing and cross-references, run the zh/ja cross-check for term drift,
  reconcile prose with any L3 interface changes.
- **[L4.2]** Update `Landmarks`, the README trio, and the Charter status;
  retrospective.
- **[L4.3]** Seed the next-milestone plan (L ⊨ GCH, per the Charter) as a successor
  to this document.

**[L5] Build and site infrastructure (parallel workstream, not a sequential phase).**
Must be in place before L2 scale-up; constraints in §7 apply from the first ported
module regardless.

- **[L5.0]** Port the build machinery: dependency-manifest generator, parallel
  per-module checking, per-module heap caps, shared config; wire into `make check`
  per the §7 trust model.
- **[L5.1]** Split `make check` into a fast gate (changed cone) and a full gate,
  keeping the existing prose/marker/glossary/reuse gates unchanged.
- **[L5.2]** CI strategy: affected cone on PRs, full check nightly, `.agdai`
  interface caching.
- **[L5.3]** Site pipeline load test at about 200 pages (render time, sidebar,
  per-page TOC).

## 7. Build constraints (D10, binding)

Imported from the source's Makefile trust model (`../fol-reification/Makefile`,
WORKLOG §8.1) and adapted to Bedrock's rules:

1. **The trusted gate is one invocation.** `agda src/Everything.lagda.md` remains the
   single certificate: one call, obviously correct, never parallelized. Since
   Bedrock's whole tree is `--safe` and `Everything` imports all of it, this one
   invocation is the entire trust base.
2. **Parallelism is a warm-up layer, outside the trust base.** The parallel
   per-module build exists only to populate `.agdai` interfaces fast; the `Everything`
   invocation then revalidates hashes cheaply. Make's dependency edges are scheduling
   hints: a wrong edge can cause wasted work or a false red, never a false green.
3. **The one false-green mode is audited away.** A module missing from `Everything`'s
   import list is unchecked by the gate. An audit script asserts, on every check,
   that the import closure of `Everything` equals the set of `src/**/*.lagda.md`
   files (the source's `audit-targets.py` pattern).
4. **The dependency manifest is generated, never committed.** `gen-deps` runs in
   under a second, so the manifest is regenerated into `_build/` on every check and
   consumed from there. This upholds Bedrock's no-generated-files rule; the source's
   committed-`deps.mk` pattern is deliberately not imported.
5. **Cold-check wall-clock is a tracked budget.** Baseline numbers are recorded in
   §11 at every gate. Working ceiling: full cold check at or under **15 minutes at
   `-j4`** on the reference machine (upstream proves the same mathematics fits in
   about 8.5). A merge that breaches the ceiling is blocked until triaged.
6. **Per-module discipline.** Per-module heap caps (the source settled on `-M6g`;
   revisit against measurements). A module exceeding roughly **120 seconds** cold or
   its heap cap is a conversion blowup: triage with the source's WORKLOG §5 playbook
   (16 to 20 case studies) before merging, and annotate any surviving countermeasure
   per the L0.0 rules.
7. **Serial fallback stays available.** A serial full-check target (single process,
   wide heap cap) is kept for dispute arbitration and for reproducing races, as in
   the source.
8. **Reference machine and `-jN` defaults are documented in the build config**, so
   budget numbers are comparable across time.

## 8. Process tensions and their resolutions (D11)

Known internal tensions in the L0 to L5 plan, each with its designed relief valve.
The common principle: **the plan legislates the mechanism of change, not the
impossibility of change.**

- **T1: Legislation is partly hindsight.** Some style rules can only be discovered by
  porting (which performance idioms recur, how certificate lemmas want to be named).
  Relief: L0 is a standing track; STYLE-agda rules may be marked *provisional*; a
  porter hitting an un-legislated situation opens a new L0.x item (or asks the owner)
  rather than improvising silently. Hardening a provisional rule may trigger a
  bounded cleanup sweep, scheduled as part of the same L0.x item.
- **T2: Skeleton finality versus post-reduction insight.** The best split of the `L/`
  branches may only be visible after L3 shrinks the clusters. Relief: only the part
  level of §4 is fixed; everything below is provisional until the dedicated L3.10
  re-layering review; renames land as appended ledger rows, and goal codes for
  superseded layouts are marked SUPERSEDED rather than rewritten.
- **T3: Pedagogical order versus dependency order.** L2's teaching order does not
  match the proof's dependency order. Relief: this is exactly what the Frontier
  mechanism (§5) decouples; a branch is portable the moment its cut is stated,
  regardless of what below it exists.
- **T4: Early prose versus whole-book coherence.** Trunk chapters are written before
  the chapters they should foreshadow exist. Relief: per-merge prose must be complete
  and correct, but foreshadowing and cross-references may be deferred; the L4.1
  harmonization pass sweeps the whole book once the shape is final.
- **T5: L3 reduction versus already-narrated interfaces.** Consolidating a cluster
  can change statements that L2 chapters already narrate. Relief: every L3 memo
  carries an impact list on ported chapters; Frontier re-cuts (§5) are the sanctioned
  mechanism; prose residue is caught by L4.1.
- **T6: Performance scaffolding versus readability.** Blowup countermeasures clutter
  a textbook; stripping them resurrects blowups. Relief: countermeasures stay in the
  code, annotated per L0.0 so narration can skip them; §7 budgets decide when a
  countermeasure is load-bearing (measure, do not guess).

## 9. Risks and mitigations

| Risk | Mitigation |
|---|---|
| LEM parameterization regresses check-time badly | L0.2 spike gates D2 before any mass port; documented fallback exists but needs a new owner ruling. |
| Conversion blowups resurface during rename/refactor | §7 budgets and per-module discipline; the source WORKLOG §5 playbook is the triage reference; countermeasures stay annotated and visible. |
| CI wall-clock grows past budget | §7 ceiling plus L5.1/L5.2 split gates and nightly full check; upstream M2.7 numbers bound the worst case. |
| Translation debt accumulates | A master merges only with en + zh complete (enforced by the marker checker); ja stays pre-supported. |
| Simplification scope creep | §10 register: every simplification candidate gets its own verify-then-decide entry; the default is a faithful port. |
| The internalization theorem does not converge (D12) | `[L3.0.3]` is paper-level, runs before L2 and gates before any code is written; `[L3.0.1]` carries kill criteria agreed in advance; the Frontier keeps the tree green for the whole attempt, so a red verdict costs the attempt alone and `[L3.5]` to `[L3.7]` resume as planned. |
| The generic abstraction resurrects conversion blowups | Abstract parameters over large formulas are the source playbook's own worst case (WORKLOG §5 case 16: one implicit `{φ}` cost 74 minutes on a single module and was fixed by one explicit argument). The theorem's parameters are spelled explicitly and `opaque`-sealed from the first commit, and §7.6 polices every instance; a blowup the playbook cannot clear is a kill criterion, not a puzzle to grind on. |
| Statement drift toward unqualified "Con(ZFC)" | D1 fixes the framing; the root chapter and Landmarks are the canonical wording; glossary pins the translated terms. |
| Process drift (ad-hoc naming, unregistered work) | §6.0 rules: no work without a code, no backfilled registration; §11 updated in the same commit as the status change. |

## 10. Candidate simplification register

Default is a faithful port; each entry here needs its own cheap verification and
owner decision before deviating. Add entries as they are discovered; record verdicts.
An accepted candidate is executed under the goal code of the cluster it affects.

| # | Candidate | Verification needed | Status |
|---|-----------|---------------------|--------|
| S1 | Specialize the truth-algebra abstraction (`TruthAlg`) to plain hProp | Check whether any non-hProp instance is load-bearing in the source | verified 2026-07-16: **rejected**. The record is a law-free operation signature, definitionally transparent on `hPropAlg` (record ι), and is the designed seam for the forcing-stage Boolean instance; only one instance exists today, but the Charter targets forcing. Ported faithfully in `[L1.1]`. |
| S2 | Merge `Absoluteness2` into `Absoluteness` | Diff the two modules' roles | resolved 2026-07-18: **deferred entirely** instead of merged; `Absoluteness2` has zero code consumers (its route superseded by the source's RAW reflection breakthrough). Ledger row added. |
| S3 | Unify the five graph-certificate families under shared combinators | Executes as `[L3.4]` | resolved 2026-07-25: **conditional fallback behind S5.** The §2.1 measurement puts shared combinators at 3k to 5k and shows the families diverge precisely where the mathematics is (soundness segments overlap 4% to 9% after renaming, scaffolding 50% to 86%), so this lever can only ever take the harness. Opens only on a red `[L3.0.2]`; a green verdict absorbs it. |
| S4 | Fold `ZF.Encoding` / `ZF.Coding` into their consumers | Map their import sites | open |
| S5 | General internalization theorem for L-recursion | Executes as `[L3.0]`: paper-level subsumption of `Cmp*` and `Depth*` first, then a two-instance proof of concept with kill criteria | **adopted as the primary route** (D12, 2026-07-25); projected to put the 42.3k certificate mass in the 8k to 12k range |
| S6 | Industrialize the source's `reify!` macro over the L-side formula groups | Executes as `[L3.2]`: extend it with Δ₀ witness output, `BoundedFo` witnesses and L-side environment slices, then re-derive one hand-built formula group and compare lines and check-time | open; projected 4k to 6k against roughly 8k to 10k of hand-built formula / witness / adequacy triples (density: 27.9 formula tokens per 100 lines). Independent of S5 and worth taking on either verdict; reverses the `Reification.Tactic` deferral row in §4 |
| S7 | Tactic-generated transport and cast steps | Executes as `[L3.9]`, spike first: on one module, check that generated terms keep the playbook's safe shape (top-level helpers, neutral endpoints) rather than the inlined shape that WORKLOG §5 cases 14, 15 and 18 had to undo | open, lowest priority; 3,300 measured `subst`/`cong` sites and 1k to 2k of headroom, but a naive tactic emits exactly the shape those fixes removed, so a failed shape check closes it ABANDONED rather than retrying per cluster |
| S8 | Generate the mechanical dispatch grids instead of writing their clauses | Executes as `[L3.8]`, opportunistically inside whichever cluster first hits a grid | open; 1k to 1.5k of **source lines only**. The source's own fix moved those clauses to a cheaper codomain rather than deleting them, so check-time is unaffected: this lever buys readability. Byproduct of S6; void if S5 removes the grids |
| S9 | Drop the source's superseded transition layers ahead of each cluster port | Executes as `[L3.1]`, standing: the consumption audit each port goal already runs, made explicit per cluster | open; 2k to 3k. Bedrock already does this informally (the "deferred (zero consumers)" rows of the §4 ledger); the candidate exists so the drop list is recorded in each cluster memo rather than happening silently |
| S10 | Declare each of the twelve tags once instead of five times | Executes as `[L3.11]`: a `ClauseBundle` carrying formula, Δ₀ witness, bounding witness, soundness and completeness per tag, plus the dispatcher | open, **registered from the `[L3.0.3]` measurement** (2026-07-25); roughly 4.4k across tier 1, of which 3,130 sits in `Cmp*`. Independent of S5's verdict and worth taking either way; also the cheap de-risk for S5's proof of concept |
| S11 | Stage-indexed internalization theorem for transfinite recursions | Executes as `[L3.12]`, memo first, same discipline as S5 | open, registered 2026-07-25; covers the 11,386 lines of `Order*` / `Trace*` / `Canon*` / `Env*` that the probe classified as not fitting the constant-table theorem. Gated on a green `[L3.0.2]`: tier 2 builds on tier 1 |
| S12 | Partial-certificate variant for the non-constant tables | Executes as `[L3.13]`: the `(C,S)`-pair certificate as a variant of the tier-1 specification | open, registered 2026-07-25; addresses the certificate half of `Sat*` / `Tarski*` / `Coh*` (10,706). Not a third theorem: the source already found the escape from the circularity, and this candidate is about stating it once |

## 11. MASTER status table (live)

One row per goal code; update the row in the same commit that changes the status
(§6.0 rule 6). Bookkeeping lines follow the table.

| Code | Goal | Status |
|---|---|---|
| L0 | Legislation (standing track) | ACTIVE (initial set gate cleared by owner 2026-07-16) |
| L0.0 | STYLE-agda.md initial edition | DONE 2026-07-16 |
| L0.1 | First glossary batch | DONE 2026-07-16 |
| L0.2 | LEM parameterization spike | DONE 2026-07-16, verdict green |
| L0.3 | Agda linter (import necessity) | DONE 2026-07-16 |
| L1 | Root and trunk skeleton | ACTIVE 2026-07-16 |
| L1.0 | Skeleton, src/README, agda-lib flag, source pin | DONE 2026-07-16 |
| L1.1 | Port Base/ | DONE 2026-07-16 |
| L1.2 | Port FOL/ core | DONE 2026-07-17 (four chapters: Syntax, Structure re-cut from ZF/, Semantics, Renaming) |
| L1.3 | Port FOL/Reification/ | DONE 2026-07-18 (five chapters, consumption-pruned; six deferrals in the ledger) |
| L1.4 | Port ZF/ | DONE 2026-07-18 (`ZF.Model` with the Ceiling compactness prose folded in; `Encoding`/`Coding` deferred by consumption audit; reading-order re-cut executed: reification reads after `ZF.Model`, `Renaming`/`Relativize` at the Part 4 doorstep) |
| L1.5 | Port V/ | DONE 2026-07-18 (`V.{Hierarchy, Smallness, Model}`; `Def`/`Sat`/`Coding` and `InnerSmall` deferred to `[L2.x]` by consumption audit; `V⊨ZF`/`V⊨ZFC` delivered) |
| L1.6 | Port L.Constructible | DONE 2026-07-18 (`V.Definability` un-deferred as prerequisite; `∈-induction` re-homed to `V.Hierarchy`; `InnerSmall` added to `V.Smallness`; `isL` is the Lset-form predicate, `𝒮ʟ` delivered) |
| L1.7 | Frontier + root L.Model | DONE 2026-07-18 (Frontier: 11 fields, the verbatim model-field statements at 𝒮ʟ; root proves extensional/regularity outright and assembles L⊨ZF/L⊨ZFC; field count is the progress meter) |
| L1.9 | Diaconescu + single-hypothesis V⊨ZFC | DONE 2026-07-18 (`Base.Choice` with `choice→lem`; `V⊨ZFC-fromChoice`; fourth landmark) |
| L1.8 | Landmarks + Everything order | DONE 2026-07-18 (Landmarks restates V⊨ZF, V⊨ZF-classical, V⊨ZFC, and the frontier-conditional L⊨ZFC; owner rulings 2026-07-18: Landmarks reads **first**; the zero-consumer chapters read **last**, after Part 4; re-cut same day: Reification namespace = {Base, Combinators, Certified} (the framework, in waiting), Graded/Absoluteness/Relativize re-homed to FOL as peers of Renaming and read inside Part 1 for FOL continuity; `ZF.Model`→`ZF`, `V.Definability`→`L.Definability`; reading order = Landmarks, Parts 0–4, tools-in-waiting, framework) |
| L0.4 | Two-catalog doctrine (reading vs structure) | DONE 2026-07-18 |
| L0.5 | Register `Ord` as an abbreviation (STYLE §3) | DONE 2026-07-25 (opened during L2.0; `IsOrd` had shipped at L1.6 unregistered) |
| L2 | Axiom branches | SUSPENDED 2026-07-25 after L2.1, by owner ruling: phase B of L3 runs first (§6.1). Resumes at L2.2 |
| L2.0 | Basic axioms | DONE 2026-07-25 (`L.Ordinal` + `L.Axioms.Basic` + `L.Constructible` additions; extensionality and regularity re-homed from `L.Model`; Frontier 11 fields → 8; no `lem`, the whole goal is constructive) |
| L2.1 | Infinity | DONE 2026-07-25 (`L.Axioms.Infinity` + `L.Ordinal.Stages`; Frontier 8 → 4). The chain is constructive, the collection step is not: it needs `ω ∈ L`, hence `ord∈Lset-suc`, hence trichotomy |
| L2.2 | Separation and Replacement | DONE 2026-07-25 (resumed after L3.14 closed). Landed: `L.Stage` (generalized to `leastOrd`), `Relabel` (into `FOL.Manipulation.Bounding`); `Relativize` was already ported at `[L1.4]`. Landed `L.Axioms.Separation`, complete: the Δ₀ engine, the parameter-bounding recursion, and `separateΔ₀`/`replaceΔ₀` unconditionally for the bounded fragment. Landed `L.Reflect` (Montague closure and single-∃ reflection at an arbitrary tuple of parameters, **without the well-ordering of `L`**, so `WellOrder`/`FormulaOrder`/`ΣSWO` leave this goal for `[L2.4]` and `ReflectN` never becomes a chapter), `L.ReflectFo` (structural induction over an arbitrary formula on a jointly built ladder), and `L.Axioms.Full` (both comprehension fields). **Frontier 4 fields → 2**; only the power set and choice remain. Six source chapters (`WellOrder`, `FormulaOrder`, `Reflect`, `ReflectN`, `ReflectFo`, `ModelACReduce`, `ModelACSep`) became three |
| L2.3 | Power by bounding the constructible subsets (re-scoped 2026-07-27 from "Power via Condensation") | **DONE 2026-07-27.** `L.Axioms.Power`, **79 lines of Agda**, against the source's ≈185 across three chapters. `𝒫V` from `V.Model`, its constructible members resized to a small index, their stages bounded by `boundingOrd`, and `hasSeparationL` carves the stage by "every member of this is a member of `a`", whose meaning is the model's own `⊆ˢ` **definitionally** (`subFo-is-⊆` is `refl`). The bound makes the membership conjunct automatic, so the two predicates agree pointwise. **Condensation is not used**: the axiom asks that the constructible subsets form a set, not that they appear early, and the condensation chapters belong to the GCH successor plan. Assumption bill unchanged: `LEM (ℓ-suc ℓ)` alone, since `lem→impredicativity` already packs both the resizing and the `hProp ℓ` smallness through `lowerLEM`. **Frontier 2 fields → 1** |
| L2.4 | Well-order and Choice trunk | PLANNED, deferred behind L3 phase B |
| L3 | Technical layer (big lever first, D12; renumbered 2026-07-25 into execution order) | ACTIVE 2026-07-27. Re-inventoried after the internalization finding: six goals closed as clutter created by that same finding, three new codes registered for unowned obligations, and the forward order re-cut (§11) |
| L3.0 | Internalization theorem for L-recursion (S5) | **DONE 2026-07-26** except `[L3.0.1]`'s instance half, re-pointed at satisfaction (verdict memo §4). Theorem delivered at 99 lines; verdict green |
| L3.0.0 | Design memo (single) | SUPERSEDED 2026-07-25 by L3.0.3 + L3.0.4; never started |
| L3.0.3 | Subsumption probe, source-reading only | DONE 2026-07-25, memo delivered; verdict amber (route alive, projection corrected) |
| L3.0.4 | Theorem statement in Bedrock's idiom | DONE 2026-07-25, memo delivered; prerequisite narrowed from all of L2.2 to `BoundedFo` + the closure engine. **Two amendments from the phase-C re-evaluation**: stage 7 is `[L3.0.5]`, not `[L3.2]`; and `reads`'s `isL` certificates must be sealed where built (the `L.Axioms.Full` hazard) |
| L3.0.5 | Finite families at a stage (stage 7) | DONE 2026-07-25 (`finSetL` in `L.Axioms.Basic`; registered on the phase-C re-evaluation, correcting the memo's attribution of stage 7 to L3.2) |
| L3.0.1 | Two-instance proof of concept | **RE-POINTED 2026-07-26** by the `[L3.0.2]` measurement: the instance to build is **satisfaction**, the largest bucket (34%) and the largest uncertainty at once, not `Depth`, which the same analysis expects to vanish (it is a termination measure and Agda needs none). **Theorem DONE 2026-07-26**: `L.Recursion` complete at 99 lines of Agda: `Recursion`/`Of` over `hasReplacementL`, `smallDom` discharging the domain generically, and `Definition`/`Image` reducing an instance's obligation to a defining formula and its adequacy. Fillability probed at 35 lines (singleton map, uncommitted). **Instance half ACTIVE, and it is being built under sibling codes, not here**: the reconnaissance's seven-step order splits into general-purpose object-language work, which is `[L3.15]` (the bridge) and `[L3.16]` (the object language over the model, steps 1 to 3, all twelve clauses written and audited), and satisfaction-specific work, which is steps 4 to 7 and stays here. The split follows §6.0 rule 4: the object language has its own success criterion and every later instance consumes it, so it is not a sub-goal of this one. **Remaining here**: `Depth` and `Cmp`, whose graphs talk about coded syntax, are what the kill criteria measure. **INSTANCE HALF DONE 2026-07-28.** Satisfaction is a `Recursion`: `L.Coding.Satisfaction` is 74 lines and checks in 9 s, the whole cone 4,034 lines across ten chapters, every one of them under 2 s. The route the reconnaissance drew held end to end, and the three things it did not predict are the ones worth recording. **(1) An environment is an interface.** Four theorems feed the graph's four hypotheses, and each was first stated at whatever vector its own chapter found convenient; the instance then needed them at one common vector. Two alignment commits moved the statements rather than transporting the proofs (`[L3.9]` is abandoned, and this is why it never came back): a chapter that will be applied inside a graph takes its environment's tail as a module parameter and puts the graph's own binders in front, so that supplying the witnesses makes the vectors literally equal. After that `funct` typechecked on the first attempt. **(2) The twelve clauses are stated twice, and both statements can be wrong the same way.** The bounded-quantifier clauses drew the bound variable from the value of the bounding term alone on the object-language side, which the clause-by-clause audit caught; the meta-level `Sat` had the identical defect, and nothing caught it until the uniqueness half was attempted against it. So the audit is necessary and not sufficient: the two sides are one statement written twice, and only the proof that relates them tests both. Both now carry the guard in their signatures. **(3) Five conversion walls, each over 600 s, each with a different cause**, and the four rules they produced are general enough to state: discharge an adequacy substitution at a *variable* argument, never at a concrete one; seal a construction with `opaque` at the site where it is built, and a **module application is such a site**; compute one side of a two-indexed case analysis from the tag rather than matching both (96 → 12, 144 → 12, 150–200 → 21); transport a *statement* rather than re-parameterizing its proof. The largest single win was `L.Axioms.Numerals`: one `opaque` block around four numerals and their projections took the `FOL.Coding` module application from over 600 s to 0.3 s |
| L3.0.2 | Verdict and rollout ruling | DONE 2026-07-26, memo [memos/L3.0.2-verdict.md](memos/L3.0.2-verdict.md). **Green, for a different reason than D12 expected.** The 43k remaining becomes a projected 3,000 to 6,400; the `L` side lands at 6,500 to 10,000 total, 3,361 already written. L3.5 to L3.7 proceed as instantiations; L3.4 does not open |
| L3.1 | Transition-layer sweep (S9) | ACTIVE 2026-07-25, standing: first drop recorded at `FOL.Coding` (`⌜⌝-inj`, the 132-clause off-diagonal grid, no consumer) |
| L3.2 | `reify!` industrialization (S6) | **ATTEMPTED AND REJECTED ON MEASUREMENT, 2026-07-27.** Re-opened on a probe, adopted for real through step 3 of its own build order, then backed out. `L.Coding.Entry` 78 → 56 (the framework does pay where an adequacy proof carries several transports) but the hub `L.Coding.Base` cost 187 → 218 to enable it: **net +9 over the two modules the plan rated best**, and `L.Coding.Model`, which was never converted, went +25% to +33% because `prAt` became a projection. Both of D13's tests fail. Source commits reverted; the measurement is the deliverable. A macro would not change this, since `reify!` generates the same reps and inherits the same hub cost. `FOL.Reification` keeps a D14 warrant to `[L3.0.1]` |
| L3.3 | Coding cluster (as originally scoped) | SUPERSEDED 2026-07-25 by L3.14; `FOL.Coding` and `V.Coding` landed under it and stand |
| L3.16 | The object language over the model | **DONE 2026-07-28** (was ACTIVE 2026-07-26). Both units are in: `U0` repaired `tmValAt`, `U2` wrote the introduction half of the twelve clauses. **Measured at close: `L.Coding.Model` 1,289, `L.Coding.InL` 330**, against the 647 and 52 this row quoted while it was open; the growth is later goals consuming the chapter, which is the tree's normal shape and not an overrun of this goal. Original scope follows. `L.Coding.Model` (647), `L.Coding.InL` (52). Renamed from "readers quoted in the model": the chapter also builds values (`prʟ`), writes the readers the bridge would charge too much for (`tagAtL`), and frames clauses. Contents: what "function" means (`prAtL`, `appAt`, `svAt`, `domAt`), environments (`valuesInAt`, `envOverAt`, `pairsInAt`), the two-layer key readers, `extAt` with the set operations, the two clause frames, `subValAt`/`subValSuccAt`, `consAtL`, `tmValAt`, and **all twelve clauses**. `L.Coding.InL`: every code, and every environment, is an element of `L`. **Two roads, both kept**: constant-free readers are quoted through `[L3.15]`; readers naming a numeral are written fresh, since quoting would thread a constructibility witness through the formula's whole shape while writing needs one unbounded existential, and unbounded is now free. Steps 1 to 3 of the `[L3.0.1]` build order, at 699 lines against its own 680 estimate. Audited clause by clause (§11); six defects found and fixed, two fatal |
| L3.15 | Re-base the coding readers onto `S` | **DONE 2026-07-26, and it is not a re-base.** `L.Absoluteness`, **34 lines**: one instantiation of `Relabel` at the bound "constructible", and a four-step transfer chain with no induction of its own. `[L3.14]`'s 1,065 lines are neither stranded nor rewritten; they stay on the hierarchy side and are quoted |
| L3.14 | Coding substrate: the Δ₀ code readers | DONE 2026-07-25. Seven chapters: `L.WellOrder.Base`, `FOL.Coding`, `V.Coding`, `L.Coding.{Base, Environment, Tagged, Length, Entry}`. The source's `SatCert*` split by subject rather than by session |
| L3.11 | Per-tag clause bundle (S10) | **ABANDONED 2026-07-27 on a measurement, not a projection.** Its re-scoped condition was "an instance shows it is wanted"; the only instance ever written answers **no**: `L.Coding.Model`'s twelve clauses factor through two shared frames plus `extAt`, not a per-tag record. Its original condition was to be the specification's `clauses` field, and `L.Recursion` has no such field. Superseded rationale follows. **RE-SCOPED to conditional 2026-07-25.** De-risk rationale spent (`L.ReflectFo` checks the twelve-clause shape); two of five fields removed by the internalization finding; and with the graph unconstrained there is no reason a clause must be a per-tag formula in a twelve-way grid. Do not build until an instance shows it is wanted |
| L3.12 | Stage-indexed theorem, tier 2 (S11) | **ABANDONED 2026-07-27.** Tier 2 existed because `Order*` sat outside tier 1's complexity boundary, and that boundary dissolved: `L.Recursion` imposes no complexity bound, no measure and no stage-locality, so an ordinal-indexed family is an ordinary instance. No staged variant is wanted. Re-open under a new code only if a concrete instance fails to fit |
| L3.13 | Partial-certificate variant, tier 3 (S12) | **ABANDONED 2026-07-27.** Its subject is the source's `(C,S)`-pair partial certificate, which the `[L3.0.1]` design change retired by name (slot as index, table as value; no `∃̇C ∃̇S` wrapper). Its registered rationale, that the total certificate is circular, was itself adjudicated false: the mechanism is witness-locality. Nothing is left for it to be a variant of |
| L3.4 | Scaffolding parameterization (S3) | **ABANDONED 2026-07-27.** Its gate is "opens only on a red `[L3.0.2]`", and that verdict returned **green**. The condition is not unmet, it is impossible |
| L3.5 | Satisfaction cluster | **DISSOLVED as a cluster 2026-07-27**, contradicted on four of its five named sources: `Reflect*` shipped at `[L2.2]`, `Tarski*` at `[L3.16]`, `Sat*InL`/`Stage`/`Slice` and `SatWitness*` dissolve. What survives is one `L.Recursion` `Definition`, which `[L3.0.1]` also claims; **the owner must rule which code owns it**. The genuine residue (`Realize` when parameters enter, `SeqChar` object-adequacy) moves to `[L3.19]` |
| L3.6 | Closure cluster | **DISSOLVED 2026-07-27.** Not one member survives as closure work: `FFST*` is what `L.Coding.InL.codeL` does in twelve lines with `finSetL`; `SeqSetInL` is superseded by `seqSet` plus `smallDom` and separation; `SatSetInL` dissolves into `L.Recursion.Of.table`; `Canon*` belongs to the well-order. The "closure engine" sense of the name shipped as `L.Axioms.Basic.defSet→isL`. Strike `L/Closure/` from §4 |
| L3.7 | Certificate cluster | PLANNED |
| L3.8 | Dispatch-grid generation (S8) | **ABANDONED 2026-07-27, premise spent.** Two goals have now walked the natural grid sites (`[L3.14]`, `[L3.16]`) and neither produced a grid: the Δ₀ obligations that forced them are gone, and the one real grid (`⌜⌝-inj`, 132 clauses) was dropped by consumption audit at `[L3.1]` |
| L3.9 | Transport and cast solver (S7) | **ABANDONED 2026-07-27** (the row carried two statuses at once). The inherited 3,300-site figure is source-side; Bedrock's whole `src/` has **456** `subst`/`cong`/`transport` sites, so the lever is an order of magnitude smaller than registered. Recorded so the goal cannot be re-argued from the source figure; a future need returns as a new code |
| L3.10 | Re-layering review of L/ | PLANNED |
| L3.17 | The ambient environment set exists | **DONE 2026-07-27 at 229 lines** (`src/L/Coding/EnvSet.lagda.md`, three importers), against the 60-to-120 estimate below: `envSet` reads both ways, `envSet-in` puts every environment over the carrier in it and `envSet-out` recovers the function whose graph a member is. **This row read PLANNED until 2026-07-28** while the unit table below recorded it DONE the day it landed; a code with two statuses corrupts every projection that reads either one, so the status lives here and the unit table defers to it. Original scope follows. PLANNED, **next after `[L2.3]`** (registered 2026-07-27). `L.Coding.Model` describes the set of environments at an arity and disowns its existence in both languages; `[L3.0.1]` never claimed it; PLAN's own bookkeeping calls it "a sub-unit of step 3" that the ≈340-line estimate did not include. **An unowned prerequisite is how a projected budget silently goes wrong**, so it gets a code. Also owes that a table's values are subsets of it. Est. 60 to 120 |
| L3.18 | The parameter alphabet (was "the parameter bridge") | **RULED 2026-07-27, and neither side of the fork wins.** The owner delegated the ruling with the principle "minimise code size, subject to no conversion blowup". **Take the third option: widen the satisfaction table's alphabet and move neither representation.** Keep `L.Definability` exactly as it is, parameters as constants, and let the table range over codes of `Formula ⟪ A ⟫ n`. ~**20 net code lines across two files, zero in `L.Definability` or any of its four consumers**, against Option 1's 275 to 320 and Option 2's that-plus-400-to-700 of consumer rewrite. **The fork was mis-framed and the row said so**: the two options are **nested, not alternatives**. `L.Axioms.Separation` feeds `Def` a formula carrying arbitrary constants, so a parameter-free `Def` would need the same constants-to-variables traversal at the identical type; Option 2 therefore *contains* Option 1 and adds consumer churn on top, and cannot win under any weighting. Why the third option is available at all: coded syntax **already** admits set constants (`⌜ con x ⌝ᵗ = mkTag 0 x`, and `c-con` is already a constructor of the coding relation), `L.Coding.Model` never mentions parameter-freeness anywhere in its 647 lines, and the clause frames never descend into a term code, so an arbitrary set payload is inert to the recursion. What the parameter-free split buys is an **absolute, stage-independent code set**, and the well-order does not want one: `<L` is stage-first by construction, and `allCodes`/`taggedCodes`/`ClosedΣ`/`pairInAt` have **zero mathematical consumers today**. Blowup risk **low**, one named hazard: generalized `codeL` puts members' `isL` certificates inside code certificates, exactly the `L.Axioms.Full` shape, contained by the same `opaque`-at-the-construction-site fix already timed at 600 s → 259 ms. **What would overturn it**: if `[L3.19]` needs an absolute code set to state internal definability, since the third option makes the alphabet stage-relative by design. Spike that before `[L3.19]`, not before this change. **First step taken the same day and the hazard did not materialize**: `codeTmL`/`codeL` generalized from `Formula (⊥* {ℓ}) n` to `Formula K n` with a constructibility hypothesis on the alphabet, the parameter-free case recovered as the instance at the empty type (`codeFreeL`), and the instantiation at `{K = ⟪ Lset σ ⟫}` with `Lset→isL` timed at **16 ms**. `L.Coding.InL` went 59 → 74 ms. **No seal needed**, against the `L.Axioms.Full` precedent that motivated the concern |
| L3.20 | Subformula closure, and the first measurement of the lever | ACTIVE 2026-07-27. The slot a recursion on codes is stated against, and **the cheapest honest test of `[L3.0.2]`'s biggest unknown**: `L.Recursion` buys its 99 lines by demanding `funct` of every client and supplying no measure, no stage-locality and no induction principle, and it has **zero importers**, so every downstream number rests on an unexercised field. The closure has the same recursion shape as satisfaction (value at a code from values at subcodes) with trivial values, so it isolates the cost of the `funct` frame from the cost of the content, at perhaps a third of satisfaction's size. Meta level delivered: `closure` and `closureL` in `L.Coding.InL`, twelve clauses each, on two new shapes (`sglL`, `cupL`); the chapter is 98 lines and checks in 123 ms. **First finding, and it is about the lever's interface rather than its cost.** `Definition` asks an instance for `fn : S → S`, a function on the whole model. A recursion over **coded** syntax cannot supply one without first deciding whether an arbitrary element is a code and recovering the syntax it encodes, which is a decoder the recursion never otherwise needs. Single-valuedness does not need it either: **contractibility is a proposition**, so an instance may decide by cases and take apart truncated witnesses on the way to proving it. `L.Recursion.mereFunct` records this in four lines, and every coded-syntax instance, satisfaction included, will fill `Recursion` through it rather than `Definition`. So `Definition` is the form for instances that have a total meta function, not the general one, and the chapter now says which is which. **Second finding, and it moves the definition rather than the cost.** The twelve clauses constrain a table only where a code *and its subcodes* carry entries, so a table with a **single entry** satisfies all twelve vacuously and no value is pinned. The clauses are therefore half a definition; the other half is a demand on the index set, that it contain the subcodes of everything in it. `L.Coding.Model.closedAt` is that half: the two frames with the table struck out, eight of the twelve constructors saying something (the two atoms carry term codes, the two constants a numeral, and none of the four has a subformula), four relations underneath divided the way the arities divide, each read back already composed with its frame. **+120 lines, typechecked first try, chapter at 3.3 s.** Alongside it `L.Coding.InL.closure-inv`: every element of a closure is the key of a formula, and that formula's own closure sits inside the one it came from, which is how an induction knows its hypothesis is available where it wants to apply it (+81 lines, chapter 2.4 s). **A conversion measurement worth keeping, and a new instance of the old rule.** The twelve cases of `closure-inv` first went through two combinators parameterized by an equation ``closure φ ≡ ⁅ key φ ⁆s ∪ …``, discharged by `refl` at each of the eight call sites: **it did not finish in ten minutes.** The same combinators parameterized by the two *inclusions* that equation induces, with no equation and no `subst`, check in **2.4 s**. So: a propositional equation between two set constructions is expensive to carry even when it is `refl`, and the maps it induces are free. **MEASURED 2026-07-27, and `L.Recursion` has an importer for the first time.** The instance sends each key in a formula's closure to the closure of the formula that key names. **The frame costs 62 lines**: `L.Coding.Recursion` is the graph (5), existence and uniqueness (25), the record (6) and the table (1). **The design finding that produced that number**: a graph may not say "the value is built from the values at the subcodes", because the object language has no table to hold subvalues until the theorem hands one back. It may say **"the value is the least set containing the key and closed under subcodes"**, and *least* is what makes it single-valued, so uniqueness is antisymmetry: one extensionality, no induction. Existence is the only induction. **Total for the end-to-end instance: +631 lines** over the state at `fea1112`. `L.Coding.Model` +189 (`closedAt`, and every frame and relation now reading both ways, since the set handed to a recursion must *satisfy* what the clauses eliminate); `L.Coding.InL` +208 (`closure-inv`, `key∈closure`, the singleton and binary-union helpers, and `byTag`); `L.Coding.Closed` 163 (closedness, then leastness); `L.Coding.Recursion` 62; `L.Recursion` +9 (`mereFunct`). **Of that, roughly 480 lines are apparatus every later instance inherits** (the object-language closedness predicate and its readers, the inversion, the tag matching, and closedness of the closure); `closureLeast` (about 78) and the instance itself do not carry over. **`byTag` is the piece worth naming**: matching twelve constructors against eight demands is twelve times eight written the obvious way, and is twelve written this way, because the demand is *computed* from the constructor tag (`Concl`, a type family over the tag) and the tag equation that pairing's injectivity yields carries the formula's case to it by `subst`. **What this does not measure, stated before the number is quoted**: satisfaction's values are not characterized by a least-fixed-point property, so its `funct` cannot use the antisymmetry shortcut and must pay for a coherence lemma (any two clause-satisfying tables with closed domains agree at a key) plus the twelve clause verifications. This instance measures the frame with the mathematics under it made as cheap as it can be made, and the chapter says so in both languages. Timings: `Closed` 6.5 s, `Recursion` 11.7 s |
| L3.19 | The L-hierarchy internalized | PLANNED (registered 2026-07-27). The internal definition of `L` off which the internal well-order is read, plus its adequacy against the meta hierarchy. The last mathematical content on the `hasChoiceL` chain, and named by no row before today. Est. 200 to 400. Also holds `[L3.5]`'s residue (`Realize` when parameters enter, `SeqChar` object-adequacy). Risk: `L.Absoluteness` is Δ₀ transfer with no induction of its own, so it will not cover a stage-recursive predicate; if a genuine absoluteness induction is needed here it is a chapter, not a lemma, and the likeliest place for the `L`-side budget to overrun |
| L4 | Convergence | PLANNED |
| L4.0 | Empty Frontier, unconditional root | PLANNED |
| L3.21 | The code set at a stage, in `L`, with an object predicate | **REGISTERED 2026-07-27** by the `[L3.20]` route audit, which found it unowned. `Def A = sett (Formula ⟪A⟫ 1) defSet` takes **syntax as its index type**; internalized, that index has to be a *set* carrying an object-language membership predicate. `[L3.18]` names the absolute version of this question and defers it ("spike before `[L3.19]`"); the **stage-relative** version was never asked, and `[L3.18]` made the alphabet stage-relative by design, so it is the version that actually arises. `L.Coding.InL`'s standing disclaimer ("the set of all codes is deliberately not proved to be one") is true today and is expected to stop being true exactly here. Route: `smallDom` for the domain, then `hasSeparationL` by "x is a code over `Lset σ`", for which `closedAt` plus a well-formedness predicate is the tool. **This is the same failure mode `[L3.17]` was registered to prevent**, caught the same way. Est. 100 to 250. **PROBE GREEN 2026-07-28, 55 lines, 1.4 s, uncommitted.** The question was the decode's induction handle, and it is not the one the route assumed. **`∈-induction` does not descend from a code to its parts**: a Kuratowski pair puts a part four membership steps down, not one, and the intermediate sets are not codes, so the motive cannot carry them. **The handle is rank.** `rank-mono` (rank is strictly monotone along membership) is `L.Rank`'s own `fromA` with the ordinality hypothesis dropped, 14 lines; four applications compose through the pair tower by ordinal transitivity; and the descent then runs `∈-induction` on **the rank** with motive `P r = (z) → rank z ≡ r → Wf z → Q z`, taking the code and the predicate as parameters. `Wf` and `Q` were left abstract in the probe and the argument never asks what they say, so the object-language predicate is free to be whatever `[L3.21]` writes. **It walled at 164 s and the wall is the goal's fourth measured kind.** The cost was entirely in the two chain lemmas, nothing in the descent. **Rule 1 does not fix it**: restating the four-step chain at variable arguments measured 162 s, indistinguishable. **Rule 2 does**: `rank` unfolds to an accessibility eliminator and had never been sealed, and one `opaque` block around `rank` and `rank-compute` took it to **1.4 s**, with the whole tree still cold-checking in 61 s. Committed on its own, since it is a repair to a chapter that predates all of this. **The general statement, and it is new**: rule 1 fixes conversion pressure a *proof* creates, by substitution; rule 2 fixes pressure a *type* creates, by a construction appearing in the goal. They are not interchangeable, and which one applies is decided by where the expensive term sits. **What the probe does not settle**: it takes `peel` as a hypothesis, so the object-language well-formedness predicate and its elimination are still unwritten, and that is where the remaining 200 to 420 lives |
| L3.22 | `⌜⌝`-injectivity at a fixed arity | **REGISTERED 2026-07-27**, the return of the obligation `[L3.1]` dropped by consumption audit, under a new code because §6.0 rule 3 forbids reviving an abandoned one. **The consumer is `[L3.0.1]`'s satisfaction table, and the demand is unavoidable**: the table is a *set*, so if two subformula occurrences share a key with different values it is genuinely multi-valued and **existence fails**, not merely its proof. Head-versus-tail collisions die to a rank argument; collisions between the two branches of `a ∧̇ b` do not. **Stated at `K = S`, not at an arbitrary alphabet**: under `[L3.18]` codes are taken of `mapFo f χ`, and for non-injective `f` the statement is simply false. Gate: a five-constructor spike, 25 cases, measuring whether the 20 off-diagonal `clash` cases reduce or whether `mkTag` being a function forces normalization of two nested pair values; **this is the one place left where the design can fail rather than merely cost more**. Red verdict routes through `Codes`/`codes-canon` instead, +150 to 250. Est. 150 to 200 plus a 60-to-90 spike. **DONE the same day at 100 lines, 1.2 s, and the spike was never run because the failure it was gating no longer exists.** The grid is avoidable: **the constructor is recoverable from the tag, and the tag is a number, so what a formula's constructor *is* can be computed from it.** One type family `Match` over the tag saying what having that tag looks like, one function `matches` producing it, and the tag equation that pairing's injectivity yields carries the second to the first by `subst`. Twelve clauses each and twelve for the case analysis, **in place of a hundred and forty-four**, and the hundred and thirty-two off-diagonal `clash` cases the gate was about **are not written at all**, so whether they would reduce is moot. Stated at the structure's own carrier, which is where `FOL.Coding` already lives, so the `[L3.18]` alphabet concern does not arise either. **This is the same move `L.Coding.InL.byTag` makes to match twelve constructors against eight demands**, and it is now stated in general in the chapter: when a case analysis is indexed by two things a tag already relates, compute one side from the tag instead of matching both |
| L3.23 | Satisfaction uniform in the carrier | **REGISTERED 2026-07-28** by the post-`[L3.0.1]` inventory, which found it unowned, the same failure mode that produced `[L3.17]` and `[L3.21]` and the third time an audit has caught it. `[L3.0.1]` delivers a table indexed by **one formula's** slot (`Recursion.dom = slot B φ`), and every downstream consumer wants the table over the **whole code set at a stage**: `[L3.21]` supplies that set, `[L3.19]` reads `Def` off it, `[L2.4]` compares codes in it. Nothing connects the two, and no row asks for the connection. **Priced low on a verified reading of the delivered code, not on optimism**: the carrier is already a slot everywhere it matters, so nothing has to be re-indexed. `twelveAt` conjoins clauses at `Bi : Fin 5`, a variable; `envSetAt` takes `bi : Fin k`; `Sat`, `Table`, `Slot`, `Sound` and `EnvSet` all take `B` as an Agda module parameter, which is already universally quantified; `keyʟ` is top-level and mentions no carrier. **The one pin is `var Bi ≐ con B` in `satGraph`**, and `L.Recursion` permits a graph to bind its table existentially provided the witness is in `L`, which it is, per carrier, by an Agda-level function of `B`. So what remains is the domain (the key set in place of `slot B φ`), its subcode-closure, and `funct` re-run through `[L3.21]`'s decode. Est. 150 to 350. **The overturn condition, and it is `[L3.0.1]`'s own unanswered question**: if the internal hierarchy's `funct` cannot discharge that existential because the domain or the well-formedness predicate needs the carrier as a *constant*, then `slot`/`satTable`/`total`/`inSlot` re-index at `(carrier, key)` and `Sound` (801) and `Unique` (630) pay a transport tax: **+400 to 900, on top**. Spike it inside `[L3.21]`, where the predicate is written, not after |
| L4.1 | Whole-book harmonization pass | PLANNED |
| L4.2 | Landmarks/README/Charter updates | PLANNED |
| L4.3 | Seed the GCH successor plan | PLANNED |
| L5 | Build and site infrastructure | PLANNED |
| L5.0 | Build machinery port | PLANNED |
| L5.1 | make check split | PLANNED |
| L5.2 | CI strategy | PLANNED |
| L5.3 | Site pipeline load test | PLANNED |

- **LEM spike verdict [L0.2]:** **green** (2026-07-16). Method: two copies of the
  source `src/` in a scratch area; the vertical slice `Classical → L.OrdinalLinear →
  L.Stage → L.ConstructibleOrder → L.WellOrder → L.ModelAC` was rewritten with
  `LEM : ∀ ℓ → Type (ℓ-suc ℓ)` in a new `--safe` interface module, the postulate
  deleted, `Classical` itself parameterized and upgraded to `--safe`, and the five
  consumers taking `(lem : ∀ {ℓ} → LEM ℓ)` telescopes with module application at
  import sites. Everything compiles (Setω-sorted telescope parameter included).
  Cold-check cost, same machine, `GHCRTS -A64m -I0 -M6g`: slice total 43.3 s →
  44.2 s (+1.9%); worst stable per-module delta about +5% (`L.ModelAC` 3.72 →
  3.90 s, median of 3); `L.WellOrder`, the historical blowup case, 31.3 → 32.4 s
  (+3%). Far inside the 1.5x gate: **D2 stands, no fallback needed.** Residual
  risk: the deep certificate clusters were not exercised; §7 budgets police them
  during L2/L3 porting.
- **Source commit pin for the port [L1.0]:** `8b190d50feb0` (2026-07-16, the tree as
  of the M2.7 build optimization; the Con(AC) mathematical content is unchanged since
  527f13b, 2026-07-14). All L1-L3 porting reads the source at this commit; advancing
  the pin is an explicit `[L0.x]` decision. (The `-WnoUnsupportedIndexedMatch` flag
  turned out to be present in `bedrock.agda-lib` from the start; no change needed.)
- **Coding re-measurement [L3.3] → [L3.14]:** 2026-07-25, before porting the remaining
  4.2k lines. Method: count consumers of each remaining module in the pinned source. The
  cut is stark. **Substrate** (universally consumed, stays): `SatCertBase` 197 lines /
  68 consumers, `SatCertLen` 259 / 46, `SatCertEnv` 135 / 44, `SatCertCons` 319 / 13;
  910 lines total. **Instance data** (consumed only by the certificate families, moves
  out): `CodeOrder` 1,277 lines whose 20 consumers are *all* `Cmp*` / `Depth*` /
  `Order*` / `WellOrder2`; `CodeSeqCert*` 757, consumed by `FFST*` / `Cmp*` / `Depth*`;
  `SeqChar` 422, all six consumers in the tier-2 trace machinery; `FormulaOrder` 361,
  same families as `CodeOrder`; `VarCoding` 385 with **one** consumer (`TarskiSat`).
  `ConstructibleOrder` 137 is well-order vocabulary for `[L2.2]` and tier 2, not for the
  theorem. So `[L3.3]` shrinks by 78%, and the displaced 3.3k is not deleted but
  **relocated**: per the `[L3.0.4]` memo those modules become `ClauseBundle` fields of
  their instances, so porting them now would mean porting them in the shape the theorem
  is meant to replace, then refactoring. They move to `[L3.5]` / `[L3.6]` / `[L3.7]` and
  are written once, after the theorem exists. Two smaller findings: checklist item 2's
  "parameterized over de Bruijn position from the start" is **already satisfied**
  upstream (the readers take `Fin n` arguments), so that refactor is free; and `[L3.2]`'s
  macro targets roughly the formula-and-adequacy half of the readers but cannot touch
  the characterization lemmas, which are set-theoretic mathematics.
- **Classical-cone finding [L2.0]:** the basic axioms of the constructible universe
  need **no** classical logic, against the source's shape. The source proves pairing
  by comparing the two stages with ordinal trichotomy (`L.OrdinalLinear.ord-tri`,
  which imports `Classical`), so the whole of `L.ModelAC` sits in the LEM cone and the
  `[L0.2]` spike duly parameterized it. But trichotomy is stronger than the proof
  needs: pairing wants a *common* stage, not a comparison, and `boundingOrd` supplies
  one constructively (`L.Ordinal` imports no classical chapter in either repository).
  So `L.Ordinal` and the coming `L.Axioms.Basic` are plain `--safe` with no `lem` in
  their telescopes, and the classical cone starts later than the source suggests.
  Re-examine the same question at each later axiom before importing a `lem` parameter.
  **First re-examination [L2.1], and the answer flips:** the numeral *chain* is
  constructive too (its projection equations ride on the constructive `isL-directed`,
  where the source's were classical only because trichotomy was), but the *collection*
  step is not. `hasInfinityL` needs `ω ∈ L`, hence `ord∈Lset-suc`, hence `rank-Lset` and
  `sucβ∈or≡`, and the latter is ordinal trichotomy, which the source's probe P8-3 judged
  constructively unprovable (it implies excluded middle). So the L side's classical cone
  begins at the collection step, three chapters later than the source's shape suggests.
  **Second re-examination [L2.2], and the cone shrinks again in a different direction:**
  reflection was expected to need the well-ordering of `L`, because the source picks its
  Montague witness with `leastOf <L` and therefore drags in `L.WellOrder` (244),
  `L.FormulaOrder` (361, already classified as instance data by `[L3.14]`) and
  `ΣSWO`/`pullSWO` (deferred to `[L2.4]`), roughly 600 lines. Grepping the source's
  `Reflect` shows `<L` is used in exactly one place, `decideStage`/`pickStage`, and only
  to name a canonical witness. But the construction never needs a canonical *element*:
  it needs a canonical *ordinal*, and the ordinals are already well-ordered by membership.
  So Bedrock takes the least **stage** that holds a witness instead of the stage of the
  least witness, by the descent already proved in `L.Stage`, and `pickWitness` becomes a
  truncated statement, which is all `closure` ever consumed. **The well-ordering of `L`
  moves entirely into `[L2.4]` with choice**, which is where it belongs; `[L2.2]` drops
  about 600 lines and gains no assumption. Two refactors fell out and were taken:
  `L.Stage`'s descent is now `leastOrd` over an arbitrary property of ordinals with the
  stage function as its first instance (the argument never inspected the property), and
  `L.Constructible` now states the tower's union structure as `Lset-in`/`Lset-out`, with
  `Lset-mono` a two-line corollary, replacing the three ad-hoc inversion helpers the
  source rebuilds inside `Reflect`. `bound2` moved from `L.Axioms.Separation` to
  `L.Ordinal`, where it is one of two consumers' shared ordinal theory.
  **Second saving in the same goal, taken immediately:** the source writes the
  single-parameter reflection and then re-derives it at a tuple of parameters in a
  separate chapter (`ReflectN`, 381), calling the second a "parallel re-derivation".
  Every step of the construction is indifferent to the number of parameters; the tuple
  is felt in exactly one place, locating it, where finitely many layers must be merged.
  Bedrock therefore writes the engine once at `k` parameters, with the merge done by an
  explicit-gap reach lemma (`βₙ n ∈ βₙ (suc (d + n))`, one `+-comm` to merge two) rather
  than an order relation on ℕ. `ReflectN` does not exist as a chapter here. Combined
  with the well-order finding, `[L2.2]` is about 1,000 source lines lighter before
  `ReflectFo` is reached.
- **Theorem statement [L3.0.4]:** delivered 2026-07-25 in
  [memos/L3.0.4-theorem-statement.md](memos/L3.0.4-theorem-statement.md), awaiting owner
  gate. **The prerequisite was narrower than PLAN assumed.** `[L2.2]` was made the gate on
  the reasoning that separation fixes the vocabulary; in fact the statement needs only
  `BoundedFo` and the closure engine, so `[L2.2]`'s reflection interface is consumed by
  the theorem's *proof*, not its statement. Both prerequisites were ported in this goal:
  `FOL.Manipulation.Bounding` (`BoundedFo`, `BoundedFo-mono`, pure syntax, `--safe`) and
  `L.Axioms.Basic.defSet→isL` (two lines composing `[L2.0]`'s `𝒟ₒ→isL` with
  `𝒟ₒ-intro`, and the re-homing the probe's checklist item 4 asked for). `[L3.0.1]` still
  waits on `[L3.3]`. Budget: tier 1 at 3.0k to 4.5k against 13,518, consistent with the
  probe's corrected projection. Notable confirmation: stages 4 and 8 of the eight-stage
  pipeline are **already Bedrock theorems** (`boundingOrd`/`Lset-mono` from `[L2.0]`,
  `defSet→isL`), so the constructive foundation laid there is the theorem's substrate and
  costs it no assumption.
- **Subsumption probe verdict [L3.0.3]:** **amber**, memo delivered 2026-07-25 in
  [memos/L3.0.3-subsumption-probe.md](memos/L3.0.3-subsumption-probe.md), awaiting owner
  gate. Central question answered **yes**: one step specification subsumes `Cmp*` and
  `Depth*`, and `FFST*` is already a third instance of the same eight-stage pipeline,
  which the source names as an engine and reuses piecewise without ever parameterizing.
  Every field of the proposed specification is fillable by both twins with none left
  over, and the four stages the clone measurement scored highest (86%, 67%, 60%, 50%)
  are exactly the four the theorem absorbs. Two findings against the plan as written:
  (a) the harness is 4,673 lines written three times, so the theorem's own yield is
  about 2.9k, not the 8k to 12k of §2.1, corrected there; (b) the larger recoverable
  block is per-tag clause work (12 tags traversed five times per instance), which wants
  a `ClauseBundle` in the specification signature and is worth roughly as much again.
  Classification: `Order*` does not fit and needs a second, stage-indexed theorem;
  `Sat*` / `Tarski*` / `Coh*` fit by halves (certificate yes, constant table no, since
  the total clause's only witness for `satSet` is circular); the closure tower needs no
  theorem at all. The memo's §8 checklist is binding input for `[L2.2]` and `[L3.3]`,
  most sharply: codes as an inductive relation, the closure-table kit generic over its
  index from day one, and `metaφ⟹isL'` re-homed out of the choice chapter.
  Goals registered from this verdict, same day: `[L3.11]` (S10, the clause bundle),
  `[L3.12]` (S11, the stage-indexed theorem for tier 2) and `[L3.13]` (S12, the
  partial-certificate variant for tier 3). Execution was re-phased at the same time so
  that **all** reduction machinery lands before any cluster port, since the measured
  tier boundaries cut across the cluster boundaries and porting a cluster first would
  re-create the T5 problem the probe was run to avoid. The `L3.x` digits no longer
  track execution order (the renumbering carve-out is spent); §6.1's phase list is the
  authority.
- **L3.0.0 split (§6.0 rule 3, standard re-split):** owner ruling 2026-07-25, after a
  schedule audit asked whether `[L3.0]` could start before L2. Finding: the memo's
  source-facing half (does one specification subsume `Cmp*` and `Depth*`, and what
  interface does the theorem need) depends on nothing but the pinned source, while its
  Bedrock-idiom half is blocked on `BoundedFo` and the reflection vocabulary that
  `[L2.2]` fixes; the trace-is-a-set and uniqueness statements are already sayable with
  the `isL` / `Lset` / `IsOrd` / `Def` vocabulary landed at `[L1.6]`, but the
  certificate relation is not. So `[L3.0.0]` is marked SUPERSEDED and replaced by
  `[L3.0.3]` (probe, before L2) and `[L3.0.4]` (statement, after `[L2.2]`), per rule 3's
  re-split clause rather than the spent renumbering carve-out. `[L3.0.1]` and `[L3.0.2]`
  were examined and **cannot** move: the proof of concept needs the coding substrate
  `[L3.3]`, which in turn needs `ZF.Coding` un-deferred.
- **L3 renumbering (§6.0 rule 3 carve-out):** owner ruling 2026-07-25, exercised while
  every L3 code was still PLANNED with no work committed against any of them, so that
  sibling numbers read in execution order. Map, old to new: theorem `L3.5` → **`L3.0`**
  (sub-goals `L3.5.0/.1/.2` → `L3.0.0/.1/.2`), sweep `L3.6` → **`L3.1`**, `reify!`
  `L3.7` → **`L3.2`**, coding cluster `L3.0` → **`L3.3`**, scaffolding `L3.8` →
  **`L3.4`**, satisfaction `L3.1` → **`L3.5`**, closure `L3.2` → **`L3.6`**,
  certificates `L3.3` → **`L3.7`**, dispatch grids `L3.9` → **`L3.8`**, cast solver
  `L3.10` → **`L3.9`**, re-layering `L3.4` → **`L3.10`**. No goal was retired, added, or
  changed in status by the renumbering; the carve-out is spent and L3 codes are
  immutable again from this point.
- **Source cost anatomy (§2.1):** measured 2026-07-25 against the pinned commit. Cone of
  `L⊨ZFC` = 150 modules, 48,260 code lines. Per-field attribution: `hasChoice` owns
  42,354 (88%), `hasPower` 149, the other eleven fields 62 between them; the shared
  blocks are the framework trunk 2,266, the Δ₀ engine plus reflection 2,571, the numeral
  chain 392. Clone measurement over the twin families: scaffolding 50% to 86% identical
  after renaming, soundness segments 4% to 9%. Verdict feeding D12: the certificate mass
  is 8 to 10 instantiations of one pipeline, and the missing abstraction is the
  rudimentary-function / Σ-recursion absoluteness layer. Reproduction: the attribution
  is a dependency-closure count over ` ```agda ` fences, re-runnable from the pinned
  source at any time.
- **Cold-check baseline (§7.5), re-measured 2026-07-26 at `[L3.16]`.** Whole tree,
  **51 modules, 5,519 Agda lines: 18.5 s serial** (not even `-j4`), against the §7.5
  working ceiling of 15 minutes at `-j4`. That is about **2%** of the budget.

  Per-module (`--profile=modules`), slowest first: `L.Rank` 670 ms, `L.Axioms.Separation`
  667, `L.Coding.Environment` 592, `L.Coding.Model` 417, `FOL.Coding` 372, `V.Model` 306,
  `L.Reflect` 296. Against the §7.6 per-module budget of ~120 s the worst module is at
  **0.6%**, so nothing is close, and there are still **zero** `-- perf:` markers in `src/`.

  **This per-module list is WRONG and was wrong when written; corrected 2026-07-27.** It
  was produced by piping `--profile=modules` through `sort -rn`, and Agda prints a thousands
  separator, so every module at or above 1,000 ms sorted as though it were under ten. The
  real worst module then and now is **`L.Axioms.Basic` at 7,142 ms**, ten times the figure
  reported, and `L.Coding.Model` was second at 1,632. Re-measured cold on the same machine
  2026-07-27: **tree 20.0 s**, `L.Axioms.Basic` 7,142, `L.Coding.Model` 1,632, `Miscellaneous`
  957, `L.Axioms.Separation` 719, `L.Rank` 687, `L.Coding.Environment` 631.

  The budgets still hold with room: 20.0 s against 15 minutes is 2%, and 7.1 s against ~120 s
  is 6%. But `L.Axioms.Basic` alone is **36% of the whole tree**, which is a fact the earlier
  entry hid, and it is the module to watch: `finSetL` and its `finDisj` induction landed
  there at `[L3.0.5]`. **Method note, since the error was in the measurement and not the
  mathematics: never sort Agda's profile output numerically without stripping the separator.**

  The line worth keeping: **`L.Axioms.Full` checks in 259 ms**, and before its
  constructibility certificate was sealed it did not finish in **600 s**. One `opaque` is
  worth a factor of at least 2,300 there, which is the sharpest number the conversion-blowup
  finding has produced and the reason it is stated as a rule rather than an anecdote.

  Caveat on any cross-repository reading of these numbers: Bedrock is not finished, so 18.5 s
  is not comparable to the source's ~8.5 minutes for the completed development. What the
  measurement does establish is headroom, and that the design has not been buying its line
  compression with check time.
- **Frontier field count:** **1** (opened at 11 on `[L1.7]`; `[L2.0]` deleted
  `hasEmptyL`, `hasPairL`, `hasUnionL`; `[L2.1]` deleted the numeral chain's three and
  then `hasInfinityL`; `[L2.2]` deleted `hasSeparationL` and `hasReplacementL` together;
  `[L2.3]` deleted `hasPowerL`). Remaining: **choice alone**. All twelve fields of
  `isZFModel` are theorems, so `L⊨ZF` is now unconditional in substance and the frontier
  carries only the extension.
- **Conversion-blowup finding [L2.2], the sharpest so far:** `L.Axioms.Full` did not
  finish in ten minutes, and the cause was **one proof term**. Relativization bounds
  quantifiers by a constant, the constant is the stage *as an element of the model*, and
  an element of the model is a pair of a set with its constructibility certificate. That
  certificate unfolds through `DefOf.defSet⊤≡A` into the definability and smallness
  machinery, and it rides inside every type that mentions the constant, which is every
  type in the chapter. Sealing the certificate alone (`opaque isL-Lset`, keeping the
  *first* component reducing, since "lies in the bound" and "lies in the stage" are the
  same statement only because it reduces) took the chapter from over 600 s to **1.4 s**.
  Sealing the reflected ordinal was tried first and did nothing: the ordinal was never
  the problem, the certificate travelling with it was. The shape generalizes: when a
  restricted structure's elements appear as *constants of the object language*, seal the
  membership certificate where the element is built, not the element.
- **Internalization finding [L3.0.1], and it ends the theorem half of the goal:** the
  internalization theorem is **52 lines of Agda** (`L.Recursion`), against `[L3.0.4]` §5's
  projected 1,400 to 2,000 and the source's 13,518 for tier 1. It is a wrapper around
  `hasReplacementL`. The reason the source needs its eight-stage pipeline is that its
  comprehension fields are **Δ₀-only**, so a recursion's table must be made definable
  *inside a stage*, where a formula does not mean what it means outside; hence
  absoluteness, hence a Δ₀ certificate, hence per-clause Δ₀ and bounding witnesses, a
  bounding ordinal, and a relabelling layer. `[L2.2]` paid for the general case once and
  for all: replacement in `L` holds for formulas of **any** complexity and is read at the
  class model. So a recursion whose graph is expressible at all has its table in `L`, the
  table **is** the replacement image, and stages 1 to 5, 7 and 8 of the memo's table have
  nothing left to discharge. There is no circularity: the per-index value is in `L` by
  pairing and the numerals, and collecting infinitely many of them is what replacement is
  for.

  Consequences across the tree, all of them contractions:
  - `[L3.0.1]`'s theorem half is **done**; what survives is the instance half, and the
    kill criteria now apply to instances only.
  - `[L3.11]` loses `ClauseBundle`'s `delta0` and `bounded`, two of five fields. More than
    that, its premise weakens: with the graph unconstrained there is no reason a clause
    must be a per-tag object-language formula in a twelve-way grid, so the bundle should
    not be built until an instance shows it is wanted. **Re-scoped to conditional.**
  - `[L3.12]` (tier 2) and `[L3.13]` (tier 3) were separated from tier 1 by exactly the
    complexity boundary that has now dissolved. Both are to be re-examined before opening;
    neither is claimed dead here.
  - `[L3.0.5]` stands, but honestly: `finSetL` was registered as stage 7's prerequisite
    and stage 7 no longer exists. It survives as a general lemma subsuming the chapter's
    hand-written pairing, which is worth its sixty lines, but it was superseded within
    the hour.

  **What the instances still owe, after the follow-up.** Obligation (a), the index set
  in `L`, looked like the next unit and turned out to be **generic**: an index set does
  not have to be *collected* into a set of `L`, only *contained* in one, and any small
  family of elements of `L` is contained in a single stage by the bounding lemma applied
  to their earliest stages, a stage being a set of `L`. That is `smallDom`, twelve lines
  in `L.Recursion`, and it discharges (a) for every instance at once. The recursion is
  then defined on more than its intended indices, which costs nothing: the graph is made
  total by a default value and the intended table is recovered by separation, now
  available for arbitrary formulas. **So no instance ever has to internalize its own
  syntax as a set.** What an instance supplies is that its indices are elements of `L`
  one at a time, which for coded syntax is pairing and the numerals.

  Obligation (b) stands and is now the only one: the graph must be written in the object
  language and proved single-valued. It is the instance's own mathematics and was never in
  scope for absorption (`[L3.0.4]` §7.1 said so). What has gone is the *second* job that
  used to ride along with it, of making that formula bounded and its constants
  stage-local, which was the larger of the two.

  Re-homing taken with it: `isL-Lset` and `LsetS` ("a stage is a set of `L`", with the
  certificate sealed) move from `L.ReflectFo` to `L.Axioms.Basic`, next to `𝒟ₒ→isL` and
  `defSet→isL`. They are constructive and now have three consumers.
- **Interface completion and fillability probe [L3.0.1]:** the first cut of `L.Recursion`
  asked an instance for **single-valuedness**, which is the wrong thing to ask, because an
  instance never has a relation to start with. It has a *function*, written in the
  meta-language by ordinary recursion, and it wants that function's table. The recursion
  itself never needs internalizing: the step, the well-founded descent and the pattern
  match on constructors all happen in Agda, and only the **graph** crosses into the object
  language. So the form to fill is now `Definition` (domain, function, defining formula,
  and the two directions of adequacy), single-valuedness is derived from it in one line
  (a type of things equal to a given one is contractible), and `Image` reads off the
  table. **The defining formula and its adequacy are the entire obligation.**

  Fillability was then probed rather than assumed, and the probe is not committed (a
  chapter with no consumer would violate the consumption discipline). Instance: the
  singleton map `x ↦ {x}` on an arbitrary set of `L`, delivering that `{ {x} : x ∈ a }`
  is a set of `L`. **35 lines**, of which the defining formula is 2:
  `x ∈̇ y ∧̇ ∀̇∈ y (u ≐ x)`. Every field of `Definition` was exercised, `extensionalL`
  discharged `only`, and it typechecked in four iterations, all of them mechanical (a
  missing `inr`, a `Σ≡Prop` whose implicits needed a declared result type, and a
  `where` attached at the wrong depth). No conversion cost: the chapter checks in about a
  second.

  What the probe does and does not establish. It establishes that the interface is
  inhabitable in practice and that a Δ₀ instance costs tens of lines rather than
  hundreds. It does **not** measure the reference or stress instances: `Depth` and `Cmp`
  have graphs that must talk about coded syntax, and the cost of *those* graphs is what
  `[L3.0.1]`'s kill criteria are about. The singleton instance says the frame holds, not
  that the hard instances are cheap.
- **Verdict measurement [L3.0.2], 2026-07-26,
  [memos/L3.0.2-verdict.md](memos/L3.0.2-verdict.md).** The source's `hasChoice` cone
  (48,229 lines, 142 modules) classified by reason-the-code-exists: **satisfaction 16,400
  (34%)**, recursion tables 12,019 (24%), order and choice 11,929 (24%), reflection and
  model assembly 3,517 (7%), other 2,669, coding substrate 1,695. Two measured compression
  ratios on chunks both repositories have built: reflection through arbitrary-φ
  comprehension **2,283 → 721 (3.2x)**, coding substrate **2,638 → 1,065 (2.5x)**; the
  internalization harness **4,673 → 96 (49x)**. **Those are selected slices**, and by whole
  buckets the two Bedrock has covered go 5,212 → 3,409, **1.53x**: compression is strongly
  uneven, at 1.2x to 1.6x for straight ports, about 3x where the design departs from the
  source, and 49x on pure Δ₀ tax. The projection turns on how much of the remaining 43k is
  tax rather than mathematics, which is the estimate's real load-bearing judgement. Per-clause unit, measured from
  `L.ReflectFo` (268 lines, four twelve-clause traversals): about **65 lines** per
  traversal with proofs.

  **D12 named the wrong lever, and the mistake is instructive.** D12 projected a general
  internalization theorem costing 1,400 to 2,000 lines and reaching 65% of the certificate
  mass. The theorem is 96 lines. The 13,518 the source spends on tier 1 exists because its
  comprehension is **Δ₀-only**, so a table has to be definable inside a stage; that forces
  absoluteness, per-clause Δ₀ and bounding witnesses, a bounding ordinal, a relabelling
  layer, and a coherence argument. All of it is Δ₀ tax and none of it is about recursion.
  The real lever was general-formula comprehension, paid at `[L2.2]` under a different
  code. D12 stands as a *decision* (attempt the lever early) and falls as an *analysis*
  (which lever, and what it costs).

  **Projection for the remaining 43,017 lines: 3,000 to 6,400**, so the `L` side lands at
  6,500 to 10,000 total against 3,361 already written, a **7x to 14x** compression against
  D12's 3x. Weakest row, stated as such in the memo: order and choice, medium-low
  confidence, error bar a factor of two on that row alone, because it holds the only
  non-scaffolding mathematics in the cone and none of it has been built here. The number
  is a projection from two measured ratios and one measured per-clause unit, and should
  not be quoted without that caveat.
- **Where the lever points next [L3.0.2 follow-up], 2026-07-26.** Satisfaction is not
  merely the largest bucket, it is the **bottom of the other two**. `<L` orders `L` by
  "the stage at which `x` first appears, then the formula and parameters defining it
  there", so its graph mentions a definable enumeration of `Def(A)`, which is a truth
  predicate. Order-and-choice (24%) therefore sits on satisfaction, and no reformulation
  avoids it: well-ordering a single `Lset σ` instead of all of `L` needs the same
  enumeration, and the alternative routes (condensation-plus-induction) need it too. This
  is Gödel's actual work, and general-formula comprehension does not touch it. The
  recursion-table bucket (24%) is the opposite: `Depth*` is a **termination measure** for
  the comparison recursion, which Agda's structural recursion does not need, and `Cmp` is
  a decidable comparison on `Formula`, a meta function. So of the remaining 43k, one third
  is irreducible mathematics sitting under another third, and the last third is
  bookkeeping for a language weaker than Agda.

  **Checked before committing to it: is the coding substrate on the right base?** It is
  not, quite. `[L3.14]`'s readers are `Formula (V ℓ) n`, while `L.Recursion` speaks
  `Formula S n`. The bridge exists, `Relabel.liftFo` from `[L2.2]`, but it consumes a
  `BoundedFo` witness, so every constant a reader names must be shown to be in `L`. Two
  further observations from the same check. The readers' Δ₀ witnesses (`Δ₀-prAt` and
  friends, roughly a third of the substrate's 1,065 lines) are **dead weight** for this
  purpose: nothing downstream needs Δ₀ any more. But their *shape* is not over-engineered,
  because Kuratowski pairing is naturally bounded, so the characterization lemmas carry
  over unchanged. The substrate is usable, not free, and not to be extended.

- **[L3.15]** (registered 2026-07-26) **Re-base the coding readers onto `S`.** Small and
  mechanical, and every remaining instance needs it. Deliverables: the readers stated over
  `Formula S n`, their constants shown to be in `L`, and a measurement of how much of the
  1,065 survives the loss of the Δ₀ obligations. Runs before the satisfaction instance,
  which is written on top of it. **Do not port further Δ₀ readers**: write new predicates
  with unbounded quantifiers, since the Δ₀ discipline is exactly the tax `[L2.2]`
  abolished.

  Then `[L3.0.1]`'s instance half, satisfaction, which is what converts the 78% to 85%
  projection into a measurement.

  **Reconnaissance and adjudication [L3.0.1], 2026-07-26. My working hypothesis was wrong,
  and it was wrong in a way that would have cost five build steps.** The `[L3.0.2]` memo
  says full comprehension "collapses the certificate machinery". It does not. It collapses
  everything *around* it. Two fan-outs settled this: five parallel readings of what the
  satisfaction graph needs, then, because the adversarial check on the load-bearing finding
  crashed mid-run, three independent attacks on that finding alone. Ruling: the finding's
  operative content **holds**, but its stated mechanism is **false**, and the false version
  must not reach the book.

  - **Not circularity of existence, and not of uniqueness.** Both are provable
    non-circularly; the source does prove them. Uniqueness is not the obstruction, it is
    what *kills the shortcut*, by depriving the description of a smaller witness.
  - **The real mechanism is witness-locality.** Satisfaction is read at the model, so an
    object-language `∃̇` ranges over `L`: discharging one means producing an element of `L`.
    A graph therefore may not describe an object by asserting the existence of that very
    object, because discharging the assertion is the problem it was meant to solve. Pinned
    by the typechecker at `L.Recursion.witnessInModel` rather than left as an argument.
  - **One sentence for the book:** every element of `L` is, at its birth stage, the
    extension of one finite object formula (`𝒟ₒ-inv`); `finSetL` escapes this only by
    writing that formula out as a finite disjunction; and a description whose existential
    witness is the described object describes nothing.
  - **Design change, and it retires machinery before it is written.** The claim as first
    stated over-specified the fix ("quantify over a table on a subformula-closed slot").
    Under `L.Recursion` the graph need not quantify over a table at all: make the slot the
    recursion **index** and the table over it the **value**, so the clauses are stated of
    `y` directly with quantifiers bounded by the index. No `∃̇C ∃̇S` wrapper, no standalone
    `φ_sat` to define and prove sound.
  - **`[L3.0.5]` is load-bearing after all.** `finSetL` glues the per-formula extensions
    into a set of `L` without needing a prior formula, and it is the only route that does.
    The "superseded within the hour" note stands corrected: it was superseded as *stage 7's
    prerequisite* and is now load-bearing for a different reason.
  - **Failure mode avoided.** Had the plan followed the total-certificate route that two of
    the three attacks argued for, step 6 would have failed at `Definition.defines` **after
    steps 1 to 5 were already paid**.
  - **Largest residual risk is now step 1**, the object-level readers, ahead of anything
    certificate-shaped. Revised estimate for the bucket: **1,200 to 1,850**, so the standing
    1,150 to 1,900 holds with the risk mass relocated.

  **Steps 1 and 2 delivered 2026-07-26, and one obligation surfaced that the build order
  did not scope.** `L.Coding.Model` (183) carries the object language's notion of function
  (`prAtL`, `appAt`, `svAt`, `domAt`), the pair on the value side (`prʟ`), the tag readers,
  and `envOverAt`; `L.Coding.InL` (43) proves every code is an element of `L`. Against the
  order's own estimates (≈190 and ≈150) that is 226 for work it budgeted at 340, and the
  step it called the **largest residual risk** came in without overrun.

  Two roads were used and both are kept, with the rule written into the chapter. A reader
  with no constants is **quoted** through `[L3.15]`: a four-link chain, no thought. A reader
  naming a numeral is **written fresh**, because quoting it would thread a constructibility
  witness through the formula's whole shape while writing it needs one unbounded
  existential, and the numeral of `L` is already a legal constant of the model. Unbounded is
  free now, which is precisely the case `L.Absoluteness` says not to route through the
  bridge.

  **The unscoped obligation.** The set-valued arrangement makes the negation clause
  `T(¬̇a) = E ∖ T(a)`, so the ambient set `E` of environments of a given length over `B`
  must itself be an element of `L`, and the arity changes under `∃̇`, so it is needed for
  every length. `envOverAt` says what it is to *be* an environment; it does not say that
  the set of all of them exists. That set is `B` to the power `n`, built by recursion on
  `n` from replacement (`Bⁿ⁺¹` is the image of `Bⁿ` under consing), so it is a genuine
  sub-unit of step 3 rather than a lemma, and the build order's step-3 estimate of ≈340
  does not appear to include it. Flagged rather than absorbed: it is the first place the
  reconnaissance's arithmetic looks thin.

  **And the flag is already half retired, cheaper than either estimate.** "Recursion on `n`
  from replacement" was the wrong shape twice over. First, an environment **is** a finite
  set, on the nose: `env g` and `finSet n (λ i → pr (# (toℕ i)) (g i))` are the same image
  of the same lifted index type, so `envIsFinSet` is `refl` and `[L3.0.5]`'s `finSetL`
  applies to environments with no argument at all. `envL` follows in three lines: no
  recursion on the length, no replacement. Second, `L.Coding.Environment.seqSet` already
  collects the sequences over a set **at every length at once**, indexed by the small type
  `Σ[ n ∈ ℕ ] (Fin n → ⟪ A ⟫)`, so the ambient set is a `smallDom`-plus-separation away
  rather than a nested replacement, and the arity changing under `∃̇` costs nothing because
  all arities are already there. What remains of the obligation is the *characterization*
  (a set satisfying `envOverAt` is an `envIn`), which is genuine content and belongs with
  the clauses. `[L3.0.5]` is now load-bearing in a third distinct way.

  **Step 3 opened, and the twelve clauses are not twelve things.** Two frames carry them.
  `extAt` says "this value is the set of exactly those things satisfying such-and-such",
  once, with the condition a parameter; its two readings are its two projections, so it
  proves nothing, and after it a clause costs only its condition. The set operations
  (`interAt`, `unionAt`, `diffAt`, `sameAt`, `emptyAt`) are its one-line instances.
  `binClauseAt` is then the shape the three binary constructors share: for every code in
  the index with this tag over these two subcodes, and the three values the table records,
  the relation holds. Six binders, and the relation speaks of positions two, one and zero,
  which is exactly the argument order the set operations take, so a binary clause is one
  application and no arithmetic at the call site. The unary, nullary and
  bounded-quantifier shapes follow the same pattern and land when their conditions do.
  `binClause-out` reads a clause in the direction soundness consumes; `-in` is the same
  chain reversed and waits for the construction that needs it rather than being guessed.

  This is the fifth time the winning move has been to find what the argument actually
  needs and write it once: `Ladder`, `Definition`, `witnessInModel`, `extAt`,
  `binClauseAt`.

  **Mis-count caught and corrected, same day.** The first version of `binClauseAt` baked
  three table lookups into the frame (at the code and at both payload components) and the
  chapter claimed it covered seven constructors. **Wrong**: an atom's payload is a pair of
  *term* codes and a bounded quantifier's is a term code paired with a formula code, and
  the table has no entries at term codes at all. Grouping clauses by *what the payload
  components are* gives five shapes, not three. The fix is to have the frames bind only
  what every constructor has (the code, its payload, and the value at the code) and leave
  any lookups to the relation, which may perform them freely; that collapses five back to
  three and makes the frames genuinely uniform. Recorded because the error was in the
  committed prose, not just in a draft, and because eyeballing a twelve-way encoding is
  evidently not reliable: an adversarial check on the corrected taxonomy was run.

  **It came back `claim-fails`, on two grounds, and the second was a silent bug in
  committed code.** (a) "Three frames" over-counted by one: `⌜⊤̇⌝ = mkTag 6 (encℕ 0)` is
  the single-component shape, so the constants are instances of the unary frame whose
  relation ignores the payload, and no third frame was ever written. **Two** frames, twelve
  relations. (b) The fatal one: `taggedCodes` entries are `pr (# n) ⌜φ⌝`, so a code carries
  its **arity on the outside**, and both frames read only one layer. With `pr-inj` and
  `#-inj′` in force, matching forced the arity against the constructor tag and bound the
  payload's own tag as though it were a subcode: the clause was vacuous at every arity but
  one, and wrong at that one. **Both `-out` lemmas still typechecked and were still true**;
  the failure would have surfaced only when a consumer could not supply the shape argument,
  which is to say several chapters later.

  Fixed by reading the key in two layers (`arityTagPairAtL`, `arityTagAtL`, each an
  existential over the inner code with the pair reader pinning the outer layer and the tag
  reader the inner) and by binding the arity in both frames, which the four arity-bumping
  constructors need anyway. The prose is corrected in both languages, including the
  paragraph that had been half-corrected and left the chapter self-contradicting.

  Recorded as a rule, not an anecdote: **a shape reader that reads fewer layers than the
  data has is silently vacuous rather than ill-typed.** Nothing downstream depended on the
  frames yet, so the cost was zero, and it was zero because the check ran before a consumer
  existed rather than after.

  **Twelve-clause audit, 2026-07-26.** Six lenses over the finished twelve (the four
  connectives; the atoms and constants; the unbounded quantifiers; the bounded ones; a
  de Bruijn auditor instructed to assume every hand-computed index wrong; and a
  do-they-determine-`T` lens), then an independent verifier per reported defect. **14
  proposed, 11 confirmed, 6 distinct defects after de-duplication, two of them fatal.**

  - **Every de Bruijn index was recomputed mechanically and every one was correct**, as
    were all twelve tags, both frames' two-layer key reads, and all arity threading. The
    place I had flagged as most likely to hide a silent error was clean; the errors were in
    the *semantics*.
  - **Fatal 1: `envOverAt` described a proper class.** Single-valued, this domain, these
    values: all three speak about the *pairs* in a set and say nothing about a member that
    is not one. Harmless while the predicate is only tested, fatal under `extAt`, which
    asserts both directions: the ambient set would have to contain every junk-bearing set.
    **Nine of the twelve clauses were vacuously true**, and the missing hypothesis was
    *false*, not merely unproved, so no downstream proof would have caught it. Fixed by a
    fourth conjunct pinning members to pairs.
  - **Fatal 2: the universal clause's outer guard was `⇒̇` where every other clause has
    `∧̇`.** Under `extAt` that forces the value to contain the whole complement of the
    ambient set. One token, and it made the clause unsatisfiable rather than wrong.
  - **Assumption-bill defect: implication was material.** `(E ∖ T(a)) ∪ T(b)` against the
    reference's Heyting arrow; the gap is exactly excluded middle for "this environment
    satisfies the antecedent". Taken constructively rather than by adding `lem`, since the
    alternative changes what the chapter costs.
  - **Two scope defects in the bounded quantifiers**: both ranged over the bound alone
    where the reference ranges over the carrier and guards by the bound. The universal was
    wrong outright (correct only under an unstated transitivity assumption on `B`); the
    existential was extensionally equivalent but only via a global invariant of the table.
  - **A prose defect that is the interesting one.** The sentence "the same with the two
    innermost quantifiers turned around, which is the only place the two differ" asserted
    an invariant the code violated. It is precisely the sentence that should have caught
    fatal 2, and it hid it instead. Prose that states an invariant is load-bearing and has
    to be checked like code.

  The audit also listed **unstated constraints** that no clause states and a later chapter
  must: that the ambient set exists at all (now a Power-or-Separation argument, since after
  the fix an environment is a subset of a product); that `T`'s values are subsets of the
  ambient set at the code's own arity; that the index is subcode-closed at arity `n` for the
  connectives and `suc n` for the four binders; and that codes carry no constants, which is
  true here only because the index ranges over parameter-free formulas and is nowhere
  recorded as the reason. Those belong with steps 4 and 5.
- **`[L3.2]` re-evaluation, 2026-07-27, and it is a downgrade.** Asked whether the macro
  should be re-scheduled after the twelve-clause count came up, and measured instead of
  reasoning from the inherited figure. Three results.

  (a) **The headroom shrank about twentyfold in translation.** 8k to 10k of hand-built
  material in the source is **338 lines** here (`FOL.Manipulation.{Relabelling, Renaming,
  Bounding, Relativize}`, almost entirely traversal), or **827 lines, 14% of `src/`**,
  counting every traversal-dense module. The macro reaches only the congruence-shaped part:
  **200 to 350 lines**.

  (b) **Ordinary abstraction has already done the job five times**, each time cheaper and
  more legible than a macro: `Ladder`, `Definition`, `extAt`, the clause frames, and
  `L.ReflectFo`'s box combinators (16 uses there, 40 in `L.Coding.Model`). The pattern is
  now well enough established to be the default answer to a repeated traversal.

  (c) **Bedrock pays costs the source did not.** The traversals are *exposition* in a book
  whose stated audience is readers learning the mathematics; generated proof terms are the
  documented cause of conversion blowups, against a baseline currently at 18.5 s with zero
  `-- perf:` markers; and `FOL.Reification` has had **zero consumers for nine goals**.

  Status **DORMANT** with a measurable re-open trigger (a congruence family written by hand
  a third time with no combinator available, or the traversal-dense share passing 20%), so
  the decision is not re-litigated by taste. **Correction on the record:** one turn earlier
  I called `[L3.2]` "the real lever" on the twenty-nine traversals; that was said before
  measuring and the measurement does not support it.

  **Structural correction taken on the way in [L2.1 revisited], 2026-07-26.** Step 1 needs
  numerals as *constants of the object language*, hence `isL (# k)`, and the obvious source
  was `L.Axioms.Infinity`, which takes `lem`. Checking first (the rule that has paid twice
  already): the chapter mentions `lem` exactly **twice**, both for `ω∈L`. The whole numeral
  chain is constructive, which PLAN recorded in prose at `[L2.1]` but never made structural.
  So the chapter is split: `L.Axioms.Numerals` (constructive: the model's pairing, union and
  successor, the projection equations, `numeralL` and the two model equations) and
  `L.Axioms.Infinity` (classical: `ω∈L` and the collection step, and nothing else). The
  recorded finding is now true at the module level, and `L.Coding.Model` stays `lem`-free
  where it could easily have acquired a classical parameter it does not use. Watch for, but do **not** build first, a generic
  "definable step gives a definable recursion" lemma: the standard approximation-function
  argument is uniform in the step and would cut every later instance, but per the
  `Ladder` lesson the interface is discovered from a real consumer and guessed wrong in
  the abstract. Let it fall out of satisfaction if it wants to.

  **Outcome [L3.15], same day: 34 lines, and the word "re-base" was wrong.** Nothing is
  re-based. `L.Absoluteness` instantiates the existing `Relabel` once, at the bound
  "constructible" instead of "inside a stage" (`down c p = (c , p)`, round trip `refl`),
  and composes four already-proved steps into
  `(γ ⊨ liftFo φ h) ≡ ((map fst γ) ⊨v φ)`: absoluteness, then the relabelling theorem
  twice, with the relabelling's own correctness in the middle. No induction of its own,
  because every induction it needs was done in `[L2.2]` and `[L1.x]`.

  Two things the estimate had wrong. The `BoundedFo InL` witness is **free for
  constant-free readers**, and most of the structural readers (`sglAt`, `pairAt`,
  `prAt`, `tripleInT`) are constant-free: they speak entirely through variables and
  bounded quantifiers. And the identity relabelling in the last step is needed, because a
  formula is not definitionally its own image under the identity map on constants,
  though its meaning is; that is `⊨-map` at `f = id` and it costs one line rather than a
  twelve-clause `mapFo-id`.

  Standing limit recorded in the chapter: the bridge is **Δ₀ only**, because absoluteness
  is. That no longer restricts what can be *said* in `L`, only what can be *imported* from
  the hierarchy for free. A predicate that is easier unbounded is to be written unbounded,
  directly over the model, and not routed through the bridge.

- **Route audit to `hasChoiceL` [L3.20 follow-up], 2026-07-27, five claims adversarially
  checked against built code.** Two refuted, three survived with corrections, and the
  corrections are the deliverable.

  **Refuted, and it removes work.** "The recursion's domain must be the set of all keys,
  because rank does not descend." The rank arithmetic is right (`key {n} φ = pr (# n) ⌜φ⌝`,
  and for `φ = ∃̇⊤̇` at arity 10 the parent key has rank 12 and the subkey 13, so key-rank
  is **not** a descent measure, which is worth recording on its own). Everything after
  "hence" is wrong three ways: `Recursion` demands no descent at all (the descent happens
  in Agda, outside), the delivered instance uses none, and its domain is the per-formula
  closure, already in `L`. No new subgoal, and `L.Coding.InL`'s disclaimer stands.

  **Refuted, and it corrects a mechanism, not a conclusion.** "`L.Recursion`'s first
  genuine consumer is the uniform relation, because its domain is infinite and cannot be
  built by hand." The delivered instance's domain **is** finite and hand-buildable and it
  still goes through the theorem. The real discriminator: whether the object need merely
  **be** in `L`, or be **defined by an object-language formula**. `finSetL` gives the
  first; only `L.Recursion` gives the second, and the second is what an internal
  well-order reads off.

  **Corrected: `hasChoiceL` is the transversal form**, not a well-ordering statement
  (`L.Frontier.ChoiceStatement`), and the equivalence of forms is unbuilt model-internal
  mathematics. Earlier notes that phrase the target as "well-order every set of `L`" are
  loose. The necessity of internal definability survives on a structural argument, not a
  theorem: `isL` **is** definability, and every producer of it bottoms out at
  `Lset→isL`, so a transversal has to be exhibited by a formula. One design note kept from
  the attack: for pairwise-disjoint families **of ordinals**, `⊆`-least is already
  object-language (`subFo-is-⊆` is `refl`), so that case falls out of separation with no
  satisfaction predicate. The cost localizes exactly where the ordinals stop carrying the
  order.

  **Corrected: `[L3.17]` is a characterization debt, not a blocker.** Separation needs a
  *superset* in `L`, not the environment set itself, and `envL` + `boundingOrd`/`smallDom`
  + separation by `envOverAt` supplies one today. What `[L3.17]` owes is that a set
  satisfying `envOverAt` **is** the environment set.

  **The route, in dependency order, with the confidence attached to each number.**

  | # | Subgoal | Est. | Confidence |
  |---|---|---:|---|
  | 1 | ~~`[L3.17]` ambient environment set, plus its characterization~~ | ~~80–150~~ **DONE, 229** | high |
  | 2 | ~~`[L3.0.1]` steps 4 to 7: the satisfaction graph, `funct`, adequacy~~ | ~~500–1,000~~ **DONE, 2,186** | **low** |
  | 3 | `[L3.21]` the code set at a stage, with an object predicate | 100–250 | low |
  | 4 | `Def` internalized at a stage (consumes 2 and 3) | 150–300 | low |
  | 5 | `[L3.19]` the internal `L`-hierarchy, over the ordinals | 200–400 | low |
  | 6 | `[L2.4]` `<L`: `Cmp`, the order formula, well-orderedness, `leastOf` | 600–1,500 | **lowest** |
  | 7 | `hasChoiceL`: union, then separation by the least-member formula | 60–150 | high |

  **Total 1,700 to 3,750**, against the earlier 2,000 to 4,000 for the same cone. **Rows 1
  and 2 are now measured, and row 2 is the largest single miss this plan has recorded:
  500–1,000 estimated, 2,186 delivered** (`Sat` 179, `Table` 248, `Sound` 801, `Unique` 630,
  `Slot` 187, `Graph` 67, `Satisfaction` 74). The confidence column called it, and the
  mechanism is stated in the `[L3.0.1]` row: the twelve clauses are one statement written
  twice, so `Sound` and `Unique` together are 1,431 lines of relating two things the
  estimate counted once. Rows 3 to 7 were sized by the same method as row 2 and none has
  been re-estimated since. The
  route does **not** need the set of all codes absolutely, does not need a per-formula
  satisfaction table, and does not need replacement for step 1.

  **The one question that now matters most, and it did not exist a day ago: does the
  least-fixed-point idiom transfer to satisfaction?** `[L3.20]`'s 62-line frame bought its
  uniqueness by antisymmetry, and satisfaction has no such characterization: the `¬̇`
  clause takes a complement, so the value is not monotone in the table. If the idiom
  transfers even partially (positive clauses split from negative), step 2 collapses the
  way the closure's uniqueness did. If it does not, `[L3.20]` measured the frame against
  an unrepresentative sample and said so in advance. **Split the question before paying
  step 2.**

  **Cheapest available de-risking, unproposed until now**: `Cmp`'s graph is plausibly
  independent of satisfaction, and if so it can be built **in parallel, today**, ahead of
  step 2, against the row that carries the largest error bar.

  Three smaller items the audit surfaced. `smallDom` is `boundingOrd` + `stage` + `LsetS`
  + `Lset-mono` with no replacement in it, and steps 1 and 3 want it without the
  replacement wrapper: it probably belongs in `L.Ordinal` or `L.Axioms.Basic`. Whether the
  satisfaction table must be uniform in the **stage** as well as the code is unasked, and
  is the likeliest place step 2's estimate doubles. And `[L2.4]` has never certified its
  assumption bill, where `[L2.3]` did.

- **Design ruling for satisfaction's `funct` [L3.0.1], 2026-07-27.** Four idioms designed
  independently, three lenses each, then synthesised. **The coherence lemma wins**, and the
  question `[L3.20]` left open is closed against it.

  **The least-fixed-point rescue does not transfer, and the reason should stop it being
  reopened.** On a subcode-closed index the twelve clauses already pin every value outright,
  because formulas are well founded: `⊥̇` pins the empty set, `⊤̇` pins the ambient set, and
  every compound value is determined by its subvalues through `extAt`. The clause system is a
  structural definition, not a fixed-point equation, so **"least" has nothing to quantify
  over**. `[L3.20]`'s antisymmetry shortcut was available because *closedness* is a closure
  condition; satisfaction's clauses are equations.

  **The graph.** The twelve clauses conjoined, guarded by `closedAt C`, `x ∈ C`, and
  **`domAt T C`**, with the carrier bound rather than named (`∃̇ (var zero ≐ con B)`, the
  `tagAtL` idiom). `domAt T C` is load-bearing, not decoration: without "every key in `C` has
  an entry" the eight compound clauses are vacuous, which is the same finding `closedAt` came
  from, one level in. `svAt T` is **not** wanted: single-valuedness on `C` falls out of the
  coherence lemma at `T' := T`, and demanding it in the graph buys an injectivity obligation
  for the wrong reason.

  **The estimate moves from 500 to 1,000 up to 1,375 to 1,970**, midpoint about 1,650, and the
  honest split matters. Row `[L3.0.1]`'s own scope (steps 4 to 7) is **900 to 1,320**: the
  row's top end plus about a third, not double. **The rest of the overrun is in items that
  belong to other rows and were priced at zero**: a defect in delivered `[L3.16]` code (below),
  the introduction half of the twelve clauses, which `[L3.16]` never wrote because only the
  first instance needed the closedness half, `[L3.17]` (three times its estimate), and
  `[L3.9]`.

  **`⌜⌝`-injectivity returns, and it returns as a new code.** It is an unavoidable
  prerequisite of this unit, and the plan records it as dropped by consumption audit, with
  `[L3.8]` abandoned on the ground that "the one real grid (`⌜⌝-inj`, 132 clauses) was
  dropped". **This unit is the consumer.** *(Correction, same day: an earlier draft of this
  note said `[L3.9]` must be un-deferred and `[L3.8]`'s abandonment reversed. Both are wrong
  under §6.0 rule 3, and the second is wrong on its subject as well: `[L3.9]` is the transport
  and cast solver, a different goal, and its own row already says "a future need returns as a
  new code"; `[L3.8]` is dispatch-grid generation, whose premise the grid's return does not
  restore, since one grid is not a generator. The §11 pointer at `FOL.Coding` that sends the
  obligation to `[L3.9]` is the source of the confusion and is corrected in place. The
  obligation is registered as `[L3.22]`.)* The table is a set, so
  if two subformula occurrences share a key with different values it is genuinely multi-valued
  and **existence fails**, not merely its proof. Head-versus-tail collisions die to a rank
  argument; collisions between the two branches of `a ∧̇ b` do not. Est. 150 to 200, and it
  carries the one genuine failure mode left in the design, so it is the spike to run first
  (a five-constructor fragment, 25 cases, measuring whether the 20 off-diagonal `clash` cases
  reduce or whether `mkTag` being a function forces normalization of two nested pair values).

  **`Sat` must be defined on `Formula S n`, not `Formula K n`.** Under `[L3.18]` the alphabet
  is stage-relative with `f : K → V ℓ`, and if `f` is not injective then
  `⌜ mapFo f χ ⌝ ≡ ⌜ mapFo f χ' ⌝` does not give `χ ≡ χ'`, so the injectivity the unit needs
  is **false** over an arbitrary alphabet. Defining it at the model's own carrier costs
  nothing (`isL` is a proposition, so `Σ≡Prop` recovers element equality) and the `K`-level
  statement follows by composition. This does not overturn `[L3.18]`; it says where the
  alphabet may and may not be arbitrary.

  **The blowup hazard was measured, and it is not where anyone put it.** The twelve clauses
  conjoined are about 8,830 constructor nodes against `closureGraph`'s 2,240, and it costs
  nothing: a `Recursion` carrying the full satisfaction graph through `Of` cold-checks at
  1.34 s against 1.33 s with the `Of` application deleted, and inhabiting all twelve clauses
  vacuously, fully eta-expanded, costs about 0.1 s. `mkReflect` and `relativize` are never
  normalized at elaboration time. **The predictor is induction count times truncation
  elimination, not formula size**: the shipped instance's 12.7 s is 25 lines of `holds` and
  `uniq`. So the items to be careful with are the two twelve-case inductions and the
  inversion, which every design budgeted as the cheap part.

- **Defect in delivered `[L3.16]` code, found 2026-07-27 and verified independently:
  `tmValAt` reads one tag of two.** `tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ …)` matches
  tag 1, the variable codes, while `⌜ con x ⌝ᵗ = mkTag 0 x`. It sits under `extAt`, which
  asserts **both** directions, so a term code that is a constant is not left unconstrained:
  the value is **pinned to the empty set**. **Four clauses, not two**: the two atoms use it on
  both sides, and `bodyAll`/`bodyEx` use it on the *bound* term of the two bounded quantifiers.
  And the case is not exotic, it is the normal form: `relativize c (∀̇ φ) = ∀̇∈ (con c) …`, so
  every relativized bounded quantifier carries a constant bound. Fix: a tag-0 disjunct whose
  payload is the value, in the `tagAtL` idiom, plus adequacy both ways, then re-read the four
  clauses. Est. 55 to 80. **Blocking: nothing resting on the atoms or the bounded quantifiers
  is trustworthy until it lands.**

  **FIXED the same day, at 26 lines against the 55 to 80 estimate, chapter unchanged at 3.3 s.**
  `tmValAt` gains the constant disjunct (`tagAtL t 0 v`, "the code is the constant tag over the
  value itself"), and the four clauses consume it unchanged, since the change is inside the
  reader. What the estimate paid for and the fix did not need: no clause had to be re-cut,
  because `binClauseAt`/`unClauseAt` never descend into a term code, which is the property the
  frames were built with. A sweep confirms the defect was localized: `tmValAt` was the only
  reader in the live chapters that matched a term tag at all.

  **What the fix adds beyond the repair is the reason it will not recur.** The reader now
  carries `tmValAt-var`, `tmValAt-con` and `tmValAt-out`, a characterization in both
  directions. It had none before, which is exactly why a one-case reader could sit under a
  two-directional frame for a day without a typechecker complaining. **Every reader that a
  clause consumes should carry one**, and the two that do not (`atomBody`, `bodyAll`/`bodyEx`
  are `private` and index-rigid) are where to look next if another clause turns out wrong.

  **And the prose is the third finding.** The sentence that justified the one-case reader,
  "a term of a parameter-free formula is a variable", was true of the alphabet when it was
  written and stopped being true at `[L3.18]`, which widened it. It is the second time in this
  goal that **a prose sentence stating an invariant hid a defect that the code could not
  report**; the chapter now says both cases and says why.

- **The build order's letters retire into codes, 2026-07-27.** The design ruling above came
  back with a build order labelled `U0` to `U7`. Those letters are not codes and must not
  become any; §6.0 rule 4 is the reason, and applying it is the whole of the mapping: **a code
  is a goal with its own success criterion, and individual lemmas and modules are artifacts
  hanging under one.** Six of the ten units are lemmas inside a single goal whose success
  criterion is one thing, `Recursion` filled for satisfaction.

  | unit | owner | note |
  |---|---|---|
  | `U0` repair `tmValAt` | `[L3.16]` | a defect in delivered code, not a goal. **DONE** |
  | `U1` the ambient environment set | `[L3.17]` | **DONE 2026-07-27 at 228 lines, 1.8 s.** `envSet` reads both ways: `envSet-in` puts every environment over the carrier in it, `envSet-out` recovers from any member the function whose graph it is. The recovery is the blocking half and the only place the description's four conjuncts work together: the domain conjunct gives an entry at every index below the length, single-valuedness gives at most one, **so the entry is a proposition and the truncation the domain hands back comes off**; the index is then untruncated because a set's own indexing has untruncated fibres. The `[L3.17]` estimate was 60 to 120 and the audit's remainder 90 to 140; **the whole goal cost 228**, so the original was low by about 2x and the audit's remainder was right |
  | `U2` the introduction half of the twelve clauses | `[L3.16]` | residue: the chapter wrote both halves of the closedness predicate, because the first instance had to *satisfy* it, and only the elimination half of the value clauses. **DONE 2026-07-27 at 241 lines against 170 to 230, chapter 836 → 1,077, 5.3 s.** Both frames now read both ways, and so do all five relation idioms; the count of readers went from four to sixteen, since **the audit's "introduction half" understated it: five of the twelve clauses had no reader in *either* direction**. Three families are parameterized by tag and body rather than written twice (`quantClause`, `atomClause`, `bndClause`), so eight clauses cost three pairs. `quantRel`, `atomRel`, `bndRel` and the four bodies had to leave `private`, which the audit predicted and priced at +80; the actual cost was the dedent, because a consumer that must *satisfy* a clause has to be able to say what the clause says. `domAt` gained its introduction, and the naming accident is recorded in the chapter: `domAt-in` and `domAt-out` are **both eliminations**, so the introduction took a third name |
  | `U3` the meta value function | `[L3.0.1]` | **DONE 2026-07-27 at 74 lines against 130 to 180, 1.2 s.** `L.Coding.Sat`: for a meta formula and a carrier, the set of environments satisfying it, by recursion on the formula, each step one separation off `envSet` naming the previous steps' sets as constants. **Splitting the condition from the value is what made it small**: `cond` and `Sat` are mutually recursive, `Sat φ = sep (envSet B n) (cond φ)`, and the twelve membership equations then collapse to **one line covering all twelve** rather than twelve. The atoms are shorter than their internal counterparts for a reason worth keeping: **the recursion knows whether a term is a variable or a constant, so `tmIs` has one case where `tmValAt` needs two** |
  | `U4a` `⌜⌝`-injectivity | **`[L3.22]`** | its own success criterion, its own gate, and a consumer outside itself |
  | `U4b` the table, its constructibility and its inversion | `[L3.0.1]` | **DONE 2026-07-27. `L.Coding.Table`, 248 lines.** The record of the block follows, because its diagnosis became one of the goal's four standing rules. **BLOCKED on a measured conversion wall, 2026-07-27, and the block is informative.** `entry-out` needs key injectivity, and `[L3.22]` supplies it at a structure's own carrier. Two routes reach it. **Route one, taken and reverted**: instantiate the coding chapter at the *model* (`FOL.Coding 𝒮ʟ prʟ prʟ-inj numeralL numeralL-inj`), so codes are elements of `L` by construction and injectivity is immediate. `prʟ-inj` and `numeralL-inj` cost nine lines and check in 6.3 s; **the module application itself does not finish in ten minutes.** The diagnosis is the chapter's own hazard at module-application scale: `prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)` and `pairʟ` carries a constructibility certificate, so the twelve `refl`s inside the coding chapter's shape lemma each force a certificate tower through normalization. **The named fix is the one already timed at 600 s → 259 ms elsewhere: seal `pairʟ` and `numeralL` with `opaque` at their construction sites**, then retry the application. **Route two**: keep codes on the hierarchy and add `mapFo`-injectivity, which needs constructor injectivity and distinctness for `Term` and `Formula`, roughly 65 lines and no conversion risk. `prʟ-inj` and `numeralL-inj` are kept either way. **The seal was tried first and it worked, same day.** `pairʟ`, `unionʟ`, `sucʟ`, `numeralL` and their four projection equations go into one `opaque` block in `L.Axioms.Numerals`; **nothing downstream needed to unfold them**, because everything reads them through the projections. The module application then costs **about a third of a second** against a wall of more than ten minutes, and `L.Coding.Model` carries `LCode`, `prʟ-inj`, `numeralL-inj` and the fourteen-clause `codeBridge` at **5.8 s**, up from 5.5 s without them. Route two is not needed and is not taken. **The general finding, and it is new at this scale: a module application is a conversion site, and a large one, since it re-elaborates every definition in the chapter being applied.** The rule about sealing a certificate where the element is built was known; that it applies to instantiating a chapter, not only to using a value, was not. **DONE 2026-07-27 at 149 lines against 150 to 210**: `L.Coding.Table` (125) plus the model-level singleton and union with their five membership lemmas in `L.Coding.InL` (+24). **`satTableL` was never written and is not needed**: with the codes taken in the model's own coding, every entry is an element of `L` by construction, so the constructibility half of the unit disappeared rather than being paid. `satTable-inv` is `closure-inv` with the inclusion combinators and without the widening, since the caller does not need the containment. `key-determines` is where `[L3.22]` is spent: the numeral half of the key gives the arities equal, the other half gives the code equation, and **the first is eliminated by path induction so the second is used at the single arity where it is true** |
  | `U5a` the value-carrying tag dispatch | `[L3.0.1]` | **DONE 2026-07-27 at 21 lines against 150 to 200**, because the device it was going to rebuild already existed and only had to be exported. `FOL.Coding`'s `⌜⌝-inj` was written by **computing the constructor from the tag** (`tagOf`, `payOf`, `shape`, `Match`, `matches`), and those five were `private` for no reason; unsealed, `keyʟ-shape` is one lemma serving all twelve clauses, handing back the formula's constructor, that the arity read is its arity, and that the payload read is its payload. **The estimate assumed a twelve-case value-carrying `Concl₂` family**; what the clauses actually need is the constructor, and the value comes from `entry-out`, which is already built. Third time this device has paid: `byTag` (96 → 12), `⌜⌝-inj` (144 → 12), and now this |
  | `U5b` existence: the twelve clause verifications | `[L3.0.1]` | **DONE 2026-07-28. `L.Coding.Sound`, 801 lines.** Record of the estimate as it stood follows. **Setup landed 2026-07-27, the twelve are next.** The table and the **slot** it is indexed by have the same shape, so they are one recursion with the gathered thing as a parameter: `tree f`, with `satTable = tree ent` and `slot = tree keyʟ`, and `tree-inv` proved once for both. That also means the two agree constructor for constructor by construction, which the clauses need and which two separate recursions would have owed a lemma. `slot-in` puts a formula's own key in its slot. **What remains is the twelve, and each is now three moves**: invert the index to a formula, `keyʟ-shape` to its constructor, `entry-out` to its value, then the clause's set identity from `Sat-mem`. The identities are the only part not yet exercised, and they are where the 240-to-380 estimate lives. **First clause measured 2026-07-27: conjunction verifies at 66 lines**, chapter 102, 1.4 s. **Of the 66, about 40 are the `parts` lemma**, which turns the clause's five hypotheses into the three formulas and the three value equations, and **that lemma is the same for every clause of the same frame**: what changes between conjunction and disjunction is the tag and the set operation, nothing else. So the honest projection is **not twelve times 66**. Reading it by frame: three propositional clauses share one `parts` (66 + 2 × 25), the two atoms share another, the two quantifiers another, the two bounded quantifiers another, and negation, implication and the two constants are singletons. **Second clause measured the same day, and it moves the number down.** Generalising the shared half over its frame (tag, constructor, and the payload equation, all parameters) leaves **`Bin` at 43 lines, conjunction at 19, disjunction at 25**; chapter 128, 1.5 s. So a frame costs about 43 once and a clause about 20 to 25 after it, not 66 each. **Projection 250 to 320** over five frames and twelve clauses, back inside the 240-to-380 estimate. Disjunction is longer than conjunction for a reason that will repeat: its identity is a *disjunction*, so both directions run under a truncation and the ambient-set obligation has to be discharged from whichever disjunct arrived. The negative clauses will pay that again, and they also have to turn a clause's *bound* ambient set back into the one this development built. **Half of that is done**: `[L3.17]`'s recovery now takes its environment and its three slots as parameters, because a clause puts them where its own frame puts them. **Done 2026-07-27, and not the way the note said.** Generalizing `envOver` the way `Recover` was generalized is not the cheapest route; **transporting the description is**. Every reader of `envOverAt` is stated through `fst` of a lookup and nothing else, so `envOverAt-transport` moves a description between any two frames that put the same three sets where it looks: **41 lines in `L.Coding.Model`, at variable environments throughout, so no conversion risk**, and it needed one missing companion (`valuesInAt-in`). `L.Coding.Sound.Ambient` is then 20 lines and gives both directions for all seven ambient-consuming clauses. The lesson is worth keeping: **when a statement is invariant under changing an environment that agrees where it looks, transport the statement rather than re-parameterizing its proof**. **Six of twelve done 2026-07-27** across four frames (`Bin` 43, `Un` 34, `Const` 20, `Atom` 40) plus the shared `Ambient` (20, on `envOverAt-transport`'s 41) and the term bridge (`TermAgree`, `termAgree`, `tmIs`'s readings, about 90 across two chapters). Conjunction 19, disjunction 25, negation 25, implication 26, top 21, bottom 10. **The two atoms hit a conversion wall, and the known fix cleared it the same day.** Their body is two nested truncations, and running the term bridge under them at a *concrete* environment is the shape this development had already measured twice at over ten minutes. The fix is the recorded one: **flatten the nesting into a reading stated at a variable environment, on both sides**. `atomBody-in`/`atomBody-out` in `L.Coding.Model` (18 lines) and `cond∈`/`cond≐` in `L.Coding.Sat` (28) do that; each atom is then **38 lines and the chapter checks in 3.0 s**. `memRel` and `eqRel` are named in `L.Coding.Model` so the clauses can be stated from outside at all. **All twelve, 2026-07-27**, bundled as `soundness`. `L.Coding.Sound` is 781 lines and checks in 5.5 s; five frames (`Bin` 43, `Un` 34, `UnSucc` 35, `Const` 20, `Atom` 40, `BinSucc` 42) carry them, and the shared apparatus is `Ambient` with `asEnv`, the term bridge, and the six flattened body readings on each side. **Against the 240-to-380 estimate the unit came to roughly 700 including its shared half**, which the row's own accounting had put in the wrong place: the flattenings and the transports are not the clauses, and they are what the estimate omitted. **One defect found by attempting the verification**, and it is the argument for doing it: `Sat`'s two bounded-quantifier clauses drew the bound variable from the value of the bounding term alone, which is the very error the twelve-clause audit had already caught on the object-language side. The two sides now both state the guard in their signatures rather than only in their bodies |
  | `U6` uniqueness: the coherence lemma | `[L3.0.1]` | **DONE 2026-07-28. `L.Coding.Unique`, 630 lines**, and the design instruction below is what it was written to. Record follows. **Entry built, first case walled, and the wall is diagnostic.** `AmbientHolds` supplies the producing direction of the ambient agreement, which seven of the twelve cases need; `keyʟ-shape-in` produces a key's shape, which all twelve need. Then the `⊥̇` case, the one with no ambient set, no subvalue and no induction hypothesis, **did not finish in ten minutes**. **The diagnosis is a design instruction, not a repair**: the case was stated at `keyʟ ⊥̇` and `Sat B ⊥̇` *instantiated*, so a satisfaction had two concrete constructions inside it. The clause readers already show the right form -- they take the code, the arity and the value as **variables** and the shape as a **hypothesis** -- and the coherence lemma must be stated the same way, with the formula recovered from the key rather than substituted into it. That is how the existence half is written and why it never walled after the atoms. Est. unchanged; the draft is out rather than half-in
  | `U7` the instance chapter | `[L3.0.1]` | artifact. **DONE 2026-07-28**: `L.Coding.Graph` 67 and `L.Coding.Satisfaction` 74, plus `L.Coding.Slot` 187 for the index set's closedness, which no unit named |

  Two route rows also resolve rather than needing codes. **"`Def` internalized at a stage" is
  `[L3.19]`**, not a row beside it: that goal is "the internal definition of `L` off which the
  internal well-order is read", and internalizing the definable powerset at a stage is how
  `Lset (α+1)` gets defined internally. And **`hasChoiceL` itself is `[L2.4]`**, whose scope is
  the well-order and choice trunk together.

  So the route to `hasChoiceL` is **eight codes, not fifteen units**: `[L3.16]` residue,
  `[L3.17]`, `[L3.22]`, `[L3.0.1]`, `[L3.21]`, `[L3.19]`, `[L2.4]`, with `[L3.20]` closed
  behind them. Sizes are unchanged; only the bookkeeping is.

- **Post-`[L3.0.1]` inventory, 2026-07-28.** The satisfaction instance closed, so the whole
  remainder was re-counted from the source rather than from this file, by three independent
  methods (analogy to measured chapters, obligation-by-obligation structure, and source
  ratio) with an adversarial pass in each direction over the result.

  **The count.** `src/` is **9,659** non-blank lines inside ```agda fences, 62 files
  (`L` 7,764, `FOL` 984, `V` 614, `Base` 213, the rest 84). The `[L3.0.1]` cone alone is
  4,142, or 43% of the development.

  **What is left in L3 is two codes.** Of nine open L3 rows, five carry **zero lines**
  (`[L3.1]` is a standing audit whose headroom is source-side, `[L3.7]`'s scope was
  re-attributed away, `[L3.16]`, `[L3.17]` and `[L3.20]` are delivered) and `[L3.10]` is
  churn. All genuine L3 mass is `[L3.21]` and `[L3.19]`; the rest of the route is `[L2.4]`.

  **Projection: remainder 2,125 to 5,465, retirement −529, so `src/` finishes at 11,255 to
  14,595**, mid ≈ 12,900, or 2.9x to 3.8x compression against the source's 42,354. Per item:
  `[L3.21]` 200–420, `[L3.23]` 150–350, `[L3.19]` 570–1,200 across its two halves, `[L2.4]`
  900–2,120, plus 300–850 of substrate growth and conversion-wall contingency and 30–535 of
  tail. **`[L3.0.2]`'s "L side 6,500 to 10,000" is superseded**: the `L` side is 7,764 today
  with the two largest items unbuilt.

  **Retirement, all verified by importer count rather than by intent.** Zero non-`Everything`
  importers, and the `[L3.0.1]` D14 warrant that covered them expired when the goal closed:
  `L.Coding.Entry` 78, `L.Coding.Tagged` 98, `L.Coding.Length` 158, `L.Coding.Recursion` 62,
  and the closed `FOL.Reification` namespace 133. **529 lines.** `L.Coding.Closed` (163) is a
  dead subtree behind `L.Coding.Recursion` but `closedAt`-leastness is a plausible `[L3.21]`
  input, so it is held until that goal rules.

  **The three risks, in order of how much of the number they move.** (1) `<ʟ` may need its
  own transfinite recursion rather than a comparison: `[L3.18]` made the alphabet
  stage-relative, so comparing two codes compares their set constants, which is `<ʟ` below
  the stage; if that stratification does not close after the hierarchy is internalized,
  `[L2.4]` goes to 2,500–3,500. `L.WellOrder.Base` has never been exercised by anything.
  (2) `[L3.23]`'s overturn condition, above. (3) `[L3.21]`'s decode is an ∈-induction under
  truncations at concrete codes, which is exactly the shape that walled five times in
  `[L3.0.1]`, and the recorded fix is not local: applied to two atom clauses it cost 46 lines
  directly and dictated the shape of all 630 lines of `L.Coding.Unique`.

  **Four bookkeeping defects found and fixed in the same pass**, recorded because each of
  them silently corrupts a projection. `[L3.17]` carried two statuses (PLANNED in §11,
  DONE in the unit table). `[L3.16]`'s row quoted 647 and 52 against a measured 1,289 and
  330. `FOL.Coding` stated in both languages that `⌜⌝`-injectivity "is not proved here; it
  is not needed by any consumer", 130 lines above the proof, in a chapter whose last section
  is about that proof. `L.WellOrder.Base` opened by naming reflection as one of its two
  consumers, and `[L2.2]` delivered reflection with no order at all; the chapter still has
  no importer. A fifth candidate was raised and **rejected**: `L.Frontier` saying choice
  "wants a well-ordering" is a claim about the route, and the route is the well-order, so it
  stands even though `ChoiceStatement` is the transversal form.

  **Next: `[L3.21]`, decode first, behind a probe of 60 lines or less.** It is the only
  remaining prerequisite that unblocks two items at once (`[L3.23]` and `[L3.19]` both
  consume the decode, and `[L2.4]` consumes those), it carries the one genuinely new proof
  technique left before `[L2.4]` (internal-to-meta recovery), and it is the last place on
  the route where a red result changes the shape of everything downstream. Probe one tag,
  binary case, with the closure certificate as the induction handle, and time it: if it
  walls at concrete codes, restate at variable arguments **before** the other eleven cases
  exist. That lesson cost five walls to buy.
