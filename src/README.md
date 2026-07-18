# src

The Agda development: literate `.lagda.md` **masters**, the single source of truth for both
the proofs and their prose. This is an English developer-facing folder guide; see
[AGENTS.md](../AGENTS.md) for the full rulebook.

## What a master is

Each module is **one `.lagda.md` file**. The Agda code appears once; prose for every language
lives in the same file, wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->` markers
(grammar: [dev/STYLE-i18n.md](../dev/STYLE-i18n.md)). The markers are HTML comments, invisible
to Agda, so a master typechecks directly. Code is **English-only** inside ` ```agda ` fences.
Nothing here is generated: the woven mono-lingual copies and the rendered site live under
`_build/` (git-ignored).

## `Everything.lagda.md`

The aggregator and the book's **reading catalog** (PLAN §5: two-catalog doctrine). It
imports every module, so `agda src/Everything.lagda.md` typechecks the whole development
(this is what `make check` runs). It is also rendered as the **site landing page**
(`index.html`); its prose lists every module with a one-line bilingual description, its
import order is the reading order, and each chapter page carries previous/next links along
it. The sidebar's module tree is the **structure catalog**, derived from the namespace tree
and never hand-maintained. **When you add a module, add its import here and its one-line
entry in the reading catalog**, at the position its first consumer dictates.

## Current modules

- `Base/`: Part 0, host-language groundwork, landed with `[L1.1]`:
  - `Base/Prelude.lagda.md`: the host vocabulary (curated cubical re-exports, defining
    nothing of its own). One of the two designated hubs (STYLE-agda §2).
  - `Base/Truth.lagda.md`: the truth algebra `TruthAlg` (a pure operation signature;
    the book's only source of logic symbols) and its canonical instance `hPropAlg`.
    The other hub.
  - `Base/Classical.lagda.md`: excluded middle as the parameter interface `LEM`, plus
    its two dividends `lem→smallΩ` (small classifier) and `lem→resize` (propositional
    resizing). No postulate, per PLAN D2.
- `FOL/`: Part 1, first-order logic as an object of study, landed with `[L1.2]`:
  - `FOL/Syntax.lagda.md`: the deeply embedded `Formula` (constant domain as a
    parameter, intrinsic scoping, all constructors primitive) and the parameter-free
    formulas with `embed` (via the library's `Empty.rec*`); sentences are the `n = 0`
    instance, deliberately unnamed.
  - `FOL/Structure.lagda.md`: `ZFStructure` (carrier, equality, membership, valued in
    a truth algebra), `pathStructure`, `∈ᵗ`, restriction `↾`, and environments `_^_`.
    Re-cut from `ZF/` (PLAN §4 ledger); `Transitive` deferred to `[L1.3]`.
  - `FOL/Semantics.lagda.md`: evaluation `⟦_⟧` and satisfaction `_⊨_` by structural
    recursion; relabelling lemmas `⟦⟧-map`, `⊨-map`, `embed-⊨`.
  - `FOL/Renaming.lagda.md`: `renameFo` and the correctness theorem `⊨-rename`
    (weakening, exchange, contraction in one stroke).
  - `FOL/Reification/`, landed with `[L1.3]` (consumption-pruned; deferrals in the
    PLAN ledger):
    - `Base.lagda.md`: representation = formula × adequacy certificate; `RepP`,
      `RepS`, `translate`, `adequacy`.
    - `Combinators.lagda.md`: the certificate algebra, one combinator per
      constructor, publicly re-exporting Base.
    - `Graded.lagda.md`: Δ₀/Σ₁/Π₁ and the Σₙ/Πₙ tower as inductive certificates;
      `mapΔ₀` and friends; `Certified` (graded representations `RepΔ₀`).
    - `Absoluteness.lagda.md`: `Transitive` (landed here per the ledger), `Single`
      (`abs₀`, `σ₁-up`, `π₁-down`, `transfer`).
    - `Relativize.lagda.md`: `relativize`, `Δ₀-relativize`, and `Correct`
      (`_⊨ᴬ_`, `relativize-correct`).
- `ZF/`: Part 2, what a ZF(C) model is, landed with `[L1.4]`:
  - `ZF/Model.lagda.md`: `IsSetOf`/`SetOf` (class realization), the description
    operator `℩`, `_⊆ˢ_`, the `ZFModel` record (extensionality, meta-level
    `regularity`, unique-existence fields, first-order `hasSeparation`/
    `hasReplacement`, strong infinity via the `numeral` field pinned by
    `numeral-zero`/`numeral-suc`), derived operations (`∅ pair ⋃ ∪ ⁺ separate 𝒫 ∩`
    with `-spec`s), and `ZFCModel` (choice-set form `hasChoice`). The compactness
    ceiling (why regularity is meta-level) lives here as prose, per the ledger's
    `Reification.Ceiling` row.

- `V/`: Part 3, the cumulative hierarchy realizes ZF(C), landed with `[L1.5]`
  (`Definability`/`Coding`/`Satisfaction` deferred to `[L2.x]` by consumption
  audit; see the ledger):
  - `V/Hierarchy.lagda.md`: the library HIT `V` introduced; `𝒮ᵥ` via
    `pathStructure`; `extensionalV` and `regularityV` (the two record fields the
    HIT gives free).
  - `V/Smallness.lagda.md`: `isSmall`, atomic compressions (`small-∈`,
    `small-≡`), connective + bounded-quantifier closure, `separateFromSmall`
    (the one separation pipe), `Δ₀Small.Δ₀-small`, and the flagship
    `separateΔ₀` (Δ₀ separation is axiom-free).
  - `V/Model.lagda.md`: stock-set specs, `replaceImage` (free replacement),
    `numeralV`/`numeralV≡#`/`ω-specV` + the `sucV` case-analysis lemmas,
    `VResizing` + `lem→VResizing`, `Power.𝒫V`, `VModel.V⊨ZF`, `SetChoice`,
    `ChoiceLemma.choice`, `VZFC.V⊨ZFC`.
  - `V/Definability.lagda.md`: the `Def` operator, landed with `[L1.6]`:
    `DefOf` (inner semantics via `InnerSmall`, `smallSat`, `defSet`, `Def`),
    membership specs (`Def-spec`, `defSet-mem`, `defSet⊆A`, `Def∋⊆A`),
    `A∈Def`, and `Refine.A⊆Def` under transitivity. Reads at the head of
    Part 4 (its first consumer).
- `L/`: Part 4, the constructible universe, trunk landed with `[L1.6]`/`[L1.7]`:
  - `L/Constructible.lagda.md`: transitivity closure lemmas, `IsOrd` (just the
    predicate), `isLayer` + `layer-trans`, the tower `Lset` by ∈-recursion
    (`opaque`-sealed; `Lset-compute` is the official unfolding), `Lset-layer`,
    the class `isL` (the source's `isL'`, primes dropped), `isL-trans`, and
    the structure `𝒮ʟ`.
  - `L/Frontier.lagda.md`: the debt registry (PLAN §5), landed with `[L1.7]`:
    `ChoiceStatement` and the `Frontier` record, eleven fields mirroring the
    model fields at `𝒮ʟ` verbatim. Fields are deleted as they are proven.
  - `L/Model.lagda.md`: the root, landed with `[L1.7]`: the honest D1 framing,
    `extensionalL`/`regularityL` proven from transitivity, and
    `L⊨ZF`/`L⊨ZFC` assembled from the frontier. Module telescope:
    `{ℓ} (lem : ∀ {ℓ'} → LEM ℓ') (F : Frontier {ℓ})`.

Note the **reading order** (the `Everything` import order) is not the namespace
order: the `FOL.Reification` chapters read after `ZF.Model` (whose separation and
replacement motivate them), and `FOL.Renaming` + `FOL.Reification.Relativize` read
at the tail, ahead of their Part 4 consumers (PLAN §5, two-catalog doctrine;
re-cut executed with `[L1.4]`).

## Reserved namespaces (currently empty, marked with `.gitkeep`)

The book-part skeleton fixed by [dev/PLAN.md](../dev/PLAN.md) §4; porting fills these in
per the route tree (`[L1]` onward). By part:

- `V/`: Part 3, the cumulative hierarchy as a HIT, and `V ⊨ ZF(C)`; later, set-theoretic
  geology (grounds, the mantle).
- `L/`: Part 4, the constructible universe as an inductive predicate: the capstone
  `L ⊨ ZFC`, built root-first through the temporary `Frontier` record (PLAN §5).

`Landmarks.lagda.md` (landed with `[L1.8]`): the trophy case: `V⊨ZF`,
`V⊨ZF-classical`, `V⊨ZFC`, and the frontier-conditional `L⊨ZFC`, each a
self-contained signature naming its proving chapter.

## Symbol master table

Required by [dev/STYLE-agda.md](../dev/STYLE-agda.md) §5: one row per symbol introduced
so far. Layers are the marking system of STYLE-agda §4 (① host, ② truth algebra,
③ structure fields, ④ object syntax).

| Symbol | Reading | Layer | Chapter | Input |
|---|---|---|---|---|
| `⟨_⟩` | the underlying type of | ① | `Base.Prelude` (re-export) | `\<` `\>` |
| `⊥*` | lifted empty type | ① | `Base.Prelude` (re-export) | `\bot` `*` |
| `⊓` | and (meet) | ② | `Base.Truth` | `\glb` |
| `⊔` | or (join) | ② | `Base.Truth` | `\lub` |
| `⇒` | implies | ② | `Base.Truth` | `\=>` |
| `¬` | not | ② | `Base.Truth` | `\neg` |
| `⊤` | true | ② | `Base.Truth` | `\top` |
| `⊥` | false | ② | `Base.Truth` | `\bot` |
| `⋀` | indexed meet (universal) | ② | `Base.Truth` | `\bigwedge` |
| `⋁` | indexed join (existential) | ② | `Base.Truth` | `\bigvee` |
| `∈̇` | object membership | ④ | `FOL.Syntax` | `\in` `\^.` |
| `≐` | object equality | ④ | `FOL.Syntax` | `\.=` |
| `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` | dotted connectives | ④ | `FOL.Syntax` | base symbol + `\^.` |
| `∃̇ ∀̇` | quantifiers | ④ | `FOL.Syntax` | `\ex` / `\all` + `\^.` |
| `∀̇∈ ∃̇∈` | bounded quantifiers | ④ | `FOL.Syntax` | dotted quantifier + `\in` |
| `≈ˢ` | structure equality | ③ | `FOL.Structure` | `\~~` `\^s` |
| `∈ˢ` | structure membership | ③ | `FOL.Structure` | `\in` `\^s` |
| `∈ᵗ` | Type-valued membership | ③ | `FOL.Structure` | `\in` `\^t` |
| `↾` | restriction (substructure) | ① | `FOL.Structure` | `\rest` |
| `_^_` | power (environments) | ① | `FOL.Structure` | `^` |
| `⟦_⟧` | the value of (evaluation) | ① | `FOL.Semantics` | `\[[` `\]]` |
| `⊨` | satisfies | ① | `FOL.Semantics` | `\models` |
| `⊨ᵛ ⊨ᵐ` | satisfies, evaluated outside / inside | ① | `FOL.Reification.Absoluteness` | `\models` + `\^v` / `\^m` |
| `⊨ᴬ` | satisfies with quantifiers bounded by `A` | ① | `FOL.Reification.Relativize` | `\models` + `\^A` |
| `℩` | that (description operator) | ① | `ZF.Model` | `\riota` |
| `⊆ˢ` | subset (structure layer) | ③ | `ZF.Model` | `\sub=` `\^s` |
| `∅` | empty set | ① | `ZF.Model` | `\emptyset` |
| `⋃` | union | ① | `ZF.Model` | `\bigcup` |
| `∪` | binary union | ① | `ZF.Model` | `\cup` |
| `⁺` | successor | ① | `ZF.Model` | `\^+` |
| `𝒫` | power set | ① | `ZF.Model` | `\McP` |
| `𝒮ᵥ` | the cumulative-hierarchy structure | ③ | `V.Hierarchy` | `\McS` `\_v` |
| `𝒟` | the definable-subsets operator | ① | `L.Constructible` | `\McD` |
| `𝒮ʟ` | the constructible structure | ③ | `L.Constructible` | `\McS` `\_L` |
| `∩` | binary intersection | ① | `ZF.Model` | `\cap` |
| `ω` | the set of numerals | ① | `ZF.Model` | `\omega` |
