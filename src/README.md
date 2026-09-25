# src

The Agda development: literate `.lagda.md` **masters**, the single source of truth for both
the proofs and their prose. This is an English developer-facing folder guide; the rule set is
[AGENTS.md](../AGENTS.md).

## What a master is

Each module is **one `.lagda.md` file**. The Agda code appears once; prose for every language
lives in the same file, wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->` markers
(grammar: [site/STYLE-i18n.md](../site/STYLE-i18n.md)). The markers are HTML comments, invisible
to Agda, so a master typechecks directly. Code is **English-only** inside ` ```agda ` fences.
Nothing here is generated: the woven mono-lingual copies and the rendered site live under
`_build/` (git-ignored).

## `Origin.lagda.md` and the reading catalog

`Origin.lagda.md` is the Agda and HTML build root. Its import closure reaches every
other module. Use `make typecheck` from the repository root to check that closure
with the pinned local compiler and isolated pure-check cache, not a global
`agda` executable. `make check` also runs lint and unit tests; `make milestone-lint`
separately verifies that all source modules are consumed by Origin. The
machine-readable reading catalog lives in [`site/reading-catalog.json`](../site/reading-catalog.json):
it stores the reading order, translated chapter labels, stages, descriptions and routes.
The site renders the interactive contents from that data and derives the
namespace dependency graph from actual imports. When you add a module, add it to the reading catalog after
its prerequisites and before its substantive consumers; `scripts/gate/check-reading-order.py`
checks exact coverage and prerequisite order. Origin is the explicitly labelled preview.

## Current modules

`Origin.lagda.md` is the trophy case and reads first in the catalog: the
storefront, before the foundations stage. It displays the implications `SetChoice→LEM` and
`LEM→ΩResizing`, followed by `V⊨ZF`, `V⊨ZFC`, `L⊨ZFC` and
`L⊨GCH`, each imported from its proving chapter. **Both `L` trophies are
proved.** `L⊨GCH` was proved on 2026-09-05; its statement type is `GCHStatement` in
`L/GCH.lagda.md` and its proof term is `L⊨GCH` in `L/GCH/Theorem.lagda.md`. The only
hypothesis either takes is `LEM (ℓ-suc ℓ)`.

The namespace tree is the structure catalog, derived and never hand-maintained. **The reading
order is not the namespace order** (the two-catalog doctrine in
[site/STYLE-agda.md](../site/STYLE-agda.md)). Retired chapters are not build inputs;
use Git history to inspect removed material rather than relying on a contributor's
private archive location.

## Authoring and verification

Follow [Agda conventions](../site/STYLE-agda.md),
[trilingual prose rules](../site/STYLE-i18n.md) and the reusable
[Markdown contract](../outcrop/docs/RENDERER-MARKDOWN.md). The catalog owns
human-review status; automated checks do not grant it. Glossary introductions
and explicit forward links follow [GLOSSARY](../site/GLOSSARY.md).

Statements and proofs require accompanying Agda code, not an explicit Markdown
`∎`. The website places QED overlays from compiler-certified signature/equation
endings, including submodules but not where-local helpers. Keep proof prose next
to its code without adding layout-only source text.

Inline Agda expressions use complete `{.Agda}` spans. Inline LaTeX follows the
figure-reference or explicit-approval rules in STYLE-i18n; temporary later-chapter
allowances expire on human review. [scripts/](../scripts/README.md) documents the
gates and supplemental literary audit. Source/semantic changes require a fresh
`make site`, not just rerendering old compiler output.

## Symbol master table

Required by [site/STYLE-agda.md](../site/STYLE-agda.md) §5: one row per symbol introduced
so far. Layers are the marking system of STYLE-agda §4 (① host, ③ structure fields,
④ object syntax).

| Symbol | Reading | Layer | Chapter | Input |
|---|---|---|---|---|
| `⟨_⟩` | the underlying type of | ① | `Base.Prelude` (re-export) | `\<` `\>` |
| `⊥*` | lifted empty type | ① | `Base.Prelude` (re-export) | `\bot` `*` |
| `∈ᶜ` | class membership | ① | `Base.Prelude` (re-export) | `\in` `\^c` |
| `⊓` | and (meet) | ① | `Base.Prelude` (re-export) | `\glb` |
| `⊔` | or (join) | ① | `Base.Prelude` (re-export) | `\lub` |
| `⇒` | implies | ① | `Base.Prelude` (re-export) | `\=>` |
| `¬` | not | ① | `Base.Prelude` (re-export) | `\neg` |
| `⊤` | true | ① | `Base.Prelude` (re-export) | `\top` |
| `⊥` | false | ① | `Base.Prelude` (re-export) | `\bot` |
| `∀[ x ] P x` | universal quantification (`∀[]-syntax`) | ① | `Base.Prelude` (re-export) | `\all` |
| `∃[ x ] P x` | existential quantification (`∃[]-syntax`) | ① | `Base.Prelude` (re-export) | `\ex` |
| `∈̇` | object membership | ④ | `FOL.Syntax` | `\in` `\^.` |
| `≐` | object equality | ④ | `FOL.Syntax` | `\.=` |
| `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` | dotted connectives | ④ | `FOL.Syntax` | base symbol + `\^.` |
| `∃̇ ∀̇` | quantifiers | ④ | `FOL.Syntax` | `\ex` / `\all` + `\^.` |
| `∀̇∈ ∃̇∈` | bounded quantifiers | ④ | `FOL.Syntax` | dotted quantifier + `\in` |
| `≈ˢ` | structure equality | ③ | `FOL.ZFStructure` | `\~~` `\^s` |
| `∈ˢ` | structure membership | ③ | `FOL.ZFStructure` | `\in` `\^s` |
| `∈ᵗ` | Type-valued membership | ③ | `FOL.ZFStructure` | `\in` `\^t` |
| `↾` | restriction (substructure) | ① | `FOL.ZFStructure` | `\rest` |
| `_^_` | power (environments) | ① | `FOL.Semantics` | `^` |
| `⟦_⟧` | the value of (evaluation) | ① | `FOL.Semantics` | `\[[` `\]]` |
| `⊨` | satisfies | ① | `FOL.Semantics` | `\models` |
| `⊨ᵛ ⊨ᵐ` | satisfies, evaluated outside / inside | ① | `FOL.Absoluteness` | `\models` + `\^v` / `\^m` |
| `⊨∘ ⊨∅` | satisfies, under the composite / the empty-domain entry | ① | `FOL.Manipulation.Relabelling` | `\models` + `\comp` / `\emptyset` |
| `⊨ᴬ` | satisfies with quantifiers bounded by `A` | ① | `FOL.Manipulation.Relativization` | `\models` + `\^A` |
| `℩` | that (description operator) | ① | `FOL.ZFModel` | `\riota` |
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
