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
  - `Base/Truth.lagda.md`: the truth algebra `TruthAlgebra` (a pure operation signature;
    the book's only source of logic symbols) and its canonical instance `hPropAlgebra`.
    The other hub.
  - `Base/Classical.lagda.md`: excluded middle as the parameter interface `LEM`, plus
    its two dividends, named `HPropSmallness` (small classifier, by
    `lem→hPropSmallness`) and `Resizing` (propositional resizing, by
    `lem→resizing`), bundled as `Impredicativity` with `lem→impredicativity` as
    the classical redemption. No postulate, per PLAN D2.
  - `Base/Choice.lagda.md` (landed with `[L1.9]`): the choice interface `SetChoice`
    (levelwise, LEM-style) and Diaconescu's theorem `choice→lem` via set quotients.
    By owner ruling it reads in Part 0, right after `Base.Classical`.
- `FOL/`: Part 1, first-order logic as an object of study, landed with `[L1.2]`:
  - `FOL/Syntax.lagda.md`: the deeply embedded `Formula` (constant domain as a
    parameter, intrinsic scoping, all constructors primitive); sentences are the
    `n = 0` instance, deliberately unnamed.
  - `FOL/Structure.lagda.md`: `ZFStructure` (carrier, equality, membership, valued in
    a truth algebra), `pathStructure`, `∈ᵗ`, restriction `↾`, and environments `_^_`.
    Re-cut from `ZF/` (PLAN §4 ledger); `Transitive` deferred to `[L1.3]`.
  - `FOL/Semantics.lagda.md`: evaluation `⟦_⟧` and satisfaction `_⊨_` by structural
    recursion.
  - `FOL/Graded.lagda.md`: Δ₀/Σ₁/Π₁ and the Σₙ/Πₙ tower as inductive
    certificates. (Re-homed from `FOL.Reification` by owner ruling 2026-07-18;
    see the ledger.)
  - `FOL/Manipulation/` (owner ruling 2026-07-18): the syntax-manipulation
    cluster, zero trunk consumers, reads at the tail:
    - `Relabelling.lagda.md`: the constant-domain kit: `mapTm`/`mapFo`,
      `ParamFree` + `embed`, `⟦⟧-map`/`⊨-map`/`embed-⊨`, `mapΔ₀`/`mapΣₙ`/`mapΠₙ`.
    - `Renaming.lagda.md`: `renameFo` and the correctness theorem `⊨-rename`
      (weakening, exchange, contraction in one stroke).
    - `Relativize.lagda.md`: `relativize`, `Δ₀-relativize`, and `Correct`
      (`_⊨ᴬ_`, `relativize-correct`).
  - `FOL/Absoluteness.lagda.md`: `Transitive`, `Single` (`abs₀`, `σ₁-up`,
    `π₁-down`). Re-homed likewise.
  - `FOL/Reification/`, landed with `[L1.3]`, re-cut 2026-07-18 to the
    representation framework proper (zero consumers today; reads at the tail):
    - `Base.lagda.md`: representation = formula × adequacy certificate; `RepP`,
      `RepS`, `translate`, `adequacy`.
    - `Combinators.lagda.md`: the assembly line, one combinator per constructor,
      publicly re-exporting Base.
    - `Certified.lagda.md`: the graded tier: `Certified` (graded representations
      `RepΔ₀`, graded combinators) and `Transfer.transfer` (adequacy composed
      with absoluteness).
- `ZF.lagda.md`: Part 2, what a ZF(C) model is, landed with `[L1.4]` (renamed
  from `ZF.Model` by owner ruling; `ZF.Coding` nests under it at `[L2.x]`):
  - `IsSetOf`/`SetOf` (class realization), the description
    operator `℩`, `_⊆ˢ_`, the `isZFModel` record (extensionality, meta-level
    `regularity`, unique-existence fields, first-order `hasSeparation`/
    `hasReplacement`, strong infinity via the `numeral` field pinned by
    `numeral-zero`/`numeral-suc`), derived operations (`∅ pair ⋃ ∪ ⁺ separate 𝒫 ∩`
    with `-spec`s), and `isZFCModel` (choice-set form `hasChoice`). The compactness
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
    `Power.𝒫V`, `VModel.V⊨ZF-impredicative` (parameterized over
    `Impredicativity`), `ChoiceLemma.choice`, the classical headline `V⊨ZF`,
    and `V⊨ZFC` from choice alone (via `Base.Choice`).
- `L/`: Part 4, the constructible universe, trunk landed with `[L1.6]`/`[L1.7]`:
  - `L/Definability.lagda.md`: the `Def` operator, landed with `[L1.6]` as
    `V.Definability`, re-homed to `L` by owner ruling (the ledger): `DefOf`
    (inner semantics via `InnerSmall`, `smallSat`, `defSet`, `Def`), membership
    specs (`Def-spec`, `defSet-mem`, `defSet⊆A`, `Def∋⊆A`), `A∈Def`, and
    `Refine.A⊆Def` under transitivity. Reads at the head of Part 4.
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
replacement motivate them), and the zero-consumer trio `FOL.Reification.Combinators`
+ `FOL.Renaming` + `FOL.Reification.Relativize` reads at the very end, after
Part 4 (PLAN §5, two-catalog doctrine; re-cuts executed with `[L1.4]` and, by
owner ruling 2026-07-18, after the dependency map made the zero-consumer status
visible).

## Reserved namespaces (currently empty, marked with `.gitkeep`)

The book-part skeleton fixed by [dev/PLAN.md](../dev/PLAN.md) §4; porting fills these in
per the route tree (`[L1]` onward). By part:

- `V/`: Part 3, the cumulative hierarchy as a HIT, and `V ⊨ ZF(C)`; later, set-theoretic
  geology (grounds, the mantle).
- `L/`: Part 4, the constructible universe as an inductive predicate: the capstone
  `L ⊨ ZFC`, built root-first through the temporary `Frontier` record (PLAN §5).

`Landmarks.lagda.md` (landed with `[L1.8]`): the trophy case: `V⊨ZF`,
`V⊨ZF-impredicative`, `V⊨ZFC` (choice alone), and the frontier-conditional
`L⊨ZFC`, each a self-contained signature naming its proving chapter. By owner
ruling it reads **first** in the catalog (the storefront), before Part 0.

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
| `⊨ᵛ ⊨ᵐ` | satisfies, evaluated outside / inside | ① | `FOL.Absoluteness` | `\models` + `\^v` / `\^m` |
| `⊨ᴬ` | satisfies with quantifiers bounded by `A` | ① | `FOL.Relativize` | `\models` + `\^A` |
| `℩` | that (description operator) | ① | `ZF` | `\riota` |
| `⊆ˢ` | subset (structure layer) | ③ | `ZF` | `\sub=` `\^s` |
| `∅` | empty set | ① | `ZF` | `\emptyset` |
| `⋃` | union | ① | `ZF` | `\bigcup` |
| `∪` | binary union | ① | `ZF` | `\cup` |
| `⁺` | successor | ① | `ZF` | `\^+` |
| `𝒫` | power set | ① | `ZF` | `\McP` |
| `𝒮ᵥ` | the cumulative-hierarchy structure | ③ | `V.Hierarchy` | `\McS` `\_v` |
| `𝒟` | the definable-subsets operator | ① | `L.Constructible` | `\McD` |
| `𝒮ʟ` | the constructible structure | ③ | `L.Constructible` | `\McS` `\_L` |
| `∩` | binary intersection | ① | `ZF` | `\cap` |
| `ω` | the set of numerals | ① | `ZF` | `\omega` |
