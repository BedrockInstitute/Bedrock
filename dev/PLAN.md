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
| D12 | L3 reduction strategy | Ruled 2026-07-25: **take the big lever first.** Before the certificate clusters are reduced one by one, attempt a general **internalization theorem for L-recursion** (goal `[L3.0]`). Grounds: the §2.1 measurement shows the certificate mass is 8 to 10 hand-built instantiations of one pipeline, repeating because the source has no rudimentary-function / Σ-recursion absoluteness layer; the syntactic levers cap out at 25% to 40%, the theorem reaches roughly 65%. This is research, not refactoring, so it runs under an explicit paper-level gate and pre-agreed kill criteria (`[L3.0.3]`, `[L3.0.1]`), and D3's per-cluster reduction review stands as the route for whatever the theorem does not absorb. Schedule ruling, same day: the paper-level probe `[L3.0.3]` opens **before** L2, so the route's cheap kill signal arrives before the axiom branches commit to a Frontier cut at the certificate boundary. |

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
| `ZF.Coding` | `FOL.Coding` | `[L3.3]`: un-deferred as L3 phase B opens. Namespace by subject, `FOL/`: it codes the object language into a structure, and it is generic over that structure (an injective pairing and an injection of the naturals, as module parameters), so it belongs beside `FOL.ZFStructure` rather than under the model chapter. Reads at the Part 4 doorstep with `Relabelling` and `Bounding`. **`⌜⌝-inj` is dropped by consumption audit** (`[L3.1]`, S9): it is the 12-by-12 grid of §10's S8, 132 of whose 144 clauses carry no mathematics, and the `Codes` relation with `codes-canon` is what every consumer was designed around. It returns only if a consumer demands it, and then as `[L3.9]` work |
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
> **C, machinery**: `[L3.11]` clause bundle → `[L3.0.1]` tier-1 proof of concept →
> `[L3.0.2]` verdict → green: `[L3.12]` stage-indexed theorem and `[L3.13]`
> partial-certificate variant / red: `[L3.4]` scaffolding merge.
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
  - **[L3.0.1]** **Proof of concept (tier 1, the constant-table theorem).**
    Prerequisites: `[L3.3]`, the coding substrate, since certificates quantify over
    coded formulas and sequences; and `[L3.11]`, whose bundle is the specification's
    `clauses` field. Prove the theorem and re-derive `Depth` and `FFST` as instances,
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
- **[L3.2]** **`reify!` industrialization (S6).** Extend the source's reflection macro
  (currently deferred with zero consumers, §4 ledger) with the three things the L side
  needs: Δ₀ witness output, `BoundedFo` witnesses, and L-side environment slices. Then
  re-derive one hand-built formula group and compare. Measured headroom 4k to 6k against
  roughly 8k to 10k of hand-built formula / witness / adequacy triples. **Independent of
  the `[L3.0]` verdict**: both routes still need object formulas. Prerequisite: `[L2.2]`
  (which lands `BoundedFo` and the reflection vocabulary). Gate: the first re-derived
  group must be smaller and must not regress §7.6's per-module budget, since macro
  output that misses the playbook's safe shapes will blow up conversion; land it before
  `[L3.3]` completes so the coding cluster is its first beneficiary.
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
| L2.2 | Separation and Replacement | ACTIVE 2026-07-25 (resumed after L3.14 closed). Landed: `L.Stage`, `Relabel` (into `FOL.Manipulation.Bounding`); `Relativize` was already ported at `[L1.4]`. Landed also `L.Axioms.Separation` (the Δ₀ engine). Remaining: the parameter-bounding recursion, `WellOrder`, the three reflection chapters, `ModelACSep` |
| L2.3 | Power via Condensation | PLANNED, deferred behind L3 phase B |
| L2.4 | Well-order and Choice trunk | PLANNED, deferred behind L3 phase B |
| L3 | Technical layer (big lever first, D12; renumbered 2026-07-25 into execution order) | PLANNED |
| L3.0 | Internalization theorem for L-recursion (S5) | PLANNED (registered 2026-07-25; gates L3.5 to L3.7) |
| L3.0.0 | Design memo (single) | SUPERSEDED 2026-07-25 by L3.0.3 + L3.0.4; never started |
| L3.0.3 | Subsumption probe, source-reading only | ACTIVE: memo delivered 2026-07-25, **awaiting owner gate**; verdict amber (route alive, projection corrected) |
| L3.0.4 | Theorem statement in Bedrock's idiom | ACTIVE: memo delivered 2026-07-25, **awaiting owner gate**; prerequisite narrowed from all of L2.2 to `BoundedFo` + the closure engine, both now ported |
| L3.0.1 | Two-instance proof of concept | PLANNED (after L3.3) |
| L3.0.2 | Verdict and rollout ruling | PLANNED |
| L3.1 | Transition-layer sweep (S9) | ACTIVE 2026-07-25, standing: first drop recorded at `FOL.Coding` (`⌜⌝-inj`, the 132-clause off-diagonal grid, no consumer) |
| L3.2 | `reify!` industrialization (S6) | PLANNED (registered 2026-07-25; after L2.2, lands before L3.3 completes) |
| L3.3 | Coding cluster (as originally scoped) | SUPERSEDED 2026-07-25 by L3.14; `FOL.Coding` and `V.Coding` landed under it and stand |
| L3.14 | Coding substrate: the Δ₀ code readers | DONE 2026-07-25. Seven chapters: `L.WellOrder.Base`, `FOL.Coding`, `V.Coding`, `L.Coding.{Base, Environment, Tagged, Length, Entry}`. The source's `SatCert*` split by subject rather than by session |
| L3.11 | Per-tag clause bundle (S10) | PLANNED (registered 2026-07-25 from the L3.0.3 measurement; runs before L3.0.1, which consumes it) |
| L3.12 | Stage-indexed theorem, tier 2 (S11) | PLANNED, conditional (registered 2026-07-25; opens only on a green L3.0.2; memo, PoC and verdict as sub-goals) |
| L3.13 | Partial-certificate variant, tier 3 (S12) | PLANNED, conditional (registered 2026-07-25; green L3.0.2, runs before L3.5) |
| L3.4 | Scaffolding parameterization (S3) | PLANNED, conditional (registered 2026-07-25; opens only on a red L3.0.2) |
| L3.5 | Satisfaction cluster | PLANNED |
| L3.6 | Closure cluster | PLANNED |
| L3.7 | Certificate cluster | PLANNED |
| L3.8 | Dispatch-grid generation (S8) | PLANNED, opportunistic (registered 2026-07-25; inside the first cluster that hits a grid) |
| L3.9 | Transport and cast solver (S7) | PLANNED, spike first (registered 2026-07-25; lowest priority, ABANDONED on a failed shape check) |
| L3.10 | Re-layering review of L/ | PLANNED |
| L4 | Convergence | PLANNED |
| L4.0 | Empty Frontier, unconditional root | PLANNED |
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
- **Cold-check baseline (§7.5):** whole-tree cold check well inside the ceiling at
  `[L2.0]`; no module is near the §7.6 per-module budget, and no performance idiom has
  been needed yet (zero `-- perf:` markers in `src/`).
- **Frontier field count:** **4** (opened at 11 on `[L1.7]`; `[L2.0]` deleted
  `hasEmptyL`, `hasPairL`, `hasUnionL`; `[L2.1]` deleted the numeral chain's three and
  then `hasInfinityL`). Remaining: separation, replacement, power, choice, all four
  hard. Nine of the twelve model fields are theorems.
