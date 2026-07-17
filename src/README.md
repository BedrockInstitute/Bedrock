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

The aggregator and the book's **table of contents**. It imports every module, so
`agda src/Everything.lagda.md` typechecks the whole development (this is what `make check`
runs). It is also rendered as the **site landing page** (`index.html`); its prose lists every
module with a one-line bilingual description, and its import order is the reading order (the
Modules sidebar follows it). **When you add a module, add its import here and its one-line
entry in the table of contents**, in reading order.

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
    parameter, intrinsic scoping, all constructors primitive), sentences, and the
    closed syntax with `embed` (via the library's `Empty.rec*`).
  - `FOL/Structure.lagda.md`: `ZFStructure` (carrier, equality, membership, valued in
    a truth algebra), `pathStructure`, `∈ᵗ`, `Transitive`, restriction `↾`, and
    environments `_^_`. Re-cut from `ZF/` (PLAN §4 ledger).
  - `FOL/Semantics.lagda.md`: evaluation `⟦_⟧` and satisfaction `_⊨_` by structural
    recursion; relabelling lemmas `⟦⟧-map`, `⊨-map`, `embed-⊨`.
  - `FOL/Renaming.lagda.md`: `renameFo` and the correctness theorem `⊨-rename`
    (weakening, exchange, contraction in one stroke).

## Reserved namespaces (currently empty, marked with `.gitkeep`)

The book-part skeleton fixed by [dev/PLAN.md](../dev/PLAN.md) §4; porting fills these in
per the route tree (`[L1]` onward). By part:

- `FOL/Reification/`: the rest of Part 1: the bridge between host predicates and object
  formulas, with machine-checked adequacy certificates.
- `ZF/`: Part 2, what a ZF(C) model is: `Model` (the axiom-field records), in
  type-theory-native idiom (not transcribed axiom by axiom).
- `V/`: Part 3, the cumulative hierarchy as a HIT, and `V ⊨ ZF(C)`; later, set-theoretic
  geology (grounds, the mantle).
- `L/`: Part 4, the constructible universe as an inductive predicate: the capstone
  `L ⊨ ZFC`, built root-first through the temporary `Frontier` record (PLAN §5).

`Landmarks.lagda.md` (milestone theorems restated, the trophy case) arrives with `[L1.8]`.

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
