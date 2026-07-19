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

## 4. Target skeleton (D5)

Top-level parts mirror the book's parts. The part level (Base, FOL, ZF, V, L,
Landmarks) is fixed; **cluster-internal layout is provisional until the L3.4
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
    ├─ Satisfaction/         internal Tarski truth in L
    ├─ Coding/               formula and sequence coding
    ├─ Closure/              "x is in L" closure lemmas
    ├─ Axioms/               per-axiom chapters: Basic, Separation, Replacement, Infinity, Power
    ├─ Condensation/         condensation and the power-set bound
    ├─ WellOrder/            the global well-order <L; Certificates/ pending L3.3 (§10 S3)
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
| `L.{Cmp*, Depth*, Order*, Trace*, Coh*}` | `L.WellOrder.Certificates.*` | layout decided by the L3.3 reduction review |
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
   SUPERSEDED with a pointer.
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
- **[L0.5+]** Reserved for mid-course legislation, opened as discovered.

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
the owner reads the trunk end to end as a book and signs off the tone.

**[L2] The axiom branches, in pedagogical order.**
Each branch descends until it hits a technical cluster flagged for reduction review;
those cuts stay in the Frontier (T3). Per-branch exit: check green, prose complete
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

**[L3] The technical layer, reduction-first (D3).**
Per cluster, in this order: (1) a **reduction review memo** (what the cluster does,
why it is as large as it is, the consolidation plan, the projected size, the layering
design for the narration, and the **impact list** on already ported chapters, T5);
(2) owner gate on the memo; (3) port per the approved plan, measuring check-time
throughout (§7); (4) prose at full narrative quality by default, with the D3
per-cluster fallback only on explicit sign-off.

- **[L3.0]** Coding cluster (source `Code*`, `Formula*`, `VarCoding`, `SeqChar`).
- **[L3.1]** Satisfaction cluster (source `Sat*`, `Tarski*`, `Realize`, `Reflect*`
  remnants).
- **[L3.2]** Closure cluster (source `FFST*`, `Canon*`, `SatSetInL`, `SeqSetInL`).
- **[L3.3]** Well-order certificate cluster (source `Cmp*`, `Depth*`, `Order*`,
  `Trace*`, `Coh*`); the largest, and the §10 S3 unification review.
- **[L3.4]** Post-reduction **re-layering review** of the whole `L/` subtree (T2):
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
  level of §4 is fixed; everything below is provisional until the dedicated L3.4
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
| S3 | Unify the five graph-certificate families under shared combinators | This is the L3.3 reduction review itself | open |
| S4 | Fold `ZF.Encoding` / `ZF.Coding` into their consumers | Map their import sites | open |

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
| L2 | Axiom branches | PLANNED |
| L2.0 | Basic axioms | PLANNED |
| L2.1 | Infinity | PLANNED |
| L2.2 | Separation and Replacement | PLANNED |
| L2.3 | Power via Condensation | PLANNED |
| L2.4 | Well-order and Choice trunk | PLANNED |
| L3 | Technical layer (reduction-first) | PLANNED |
| L3.0 | Coding cluster | PLANNED |
| L3.1 | Satisfaction cluster | PLANNED |
| L3.2 | Closure cluster | PLANNED |
| L3.3 | Certificate cluster (S3) | PLANNED |
| L3.4 | Re-layering review of L/ | PLANNED |
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
- **Cold-check baseline (§7.5):** n/a (no ported modules yet).
- **Frontier field count:** n/a (record not yet created).
