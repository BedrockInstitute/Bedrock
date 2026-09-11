# src

The Agda development: literate `.lagda.md` **masters**, the single source of truth for both
the proofs and their prose. This is an English developer-facing folder guide; the rule set is
[AGENTS.md](../AGENTS.md).

## What a master is

Each module is **one `.lagda.md` file**. The Agda code appears once; prose for every language
lives in the same file, wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->` markers
(grammar: [dev/STYLE-i18n.md](../dev/STYLE-i18n.md)). The markers are HTML comments, invisible
to Agda, so a master typechecks directly. Code is **English-only** inside ` ```agda ` fences.
Nothing here is generated: the woven mono-lingual copies and the rendered site live under
`_build/` (git-ignored).

## `Milestones.lagda.md` and the reading catalog

`Milestones.lagda.md` is the Agda and HTML build root. Its import closure reaches every
other module, so `agda src/Milestones.lagda.md` typechecks the whole development. The
machine-readable reading catalog lives in [`dev/reading-catalog.json`](../dev/reading-catalog.json):
it stores the reading order, translated chapter labels, stages, descriptions and routes.
The site renders the reading guide from that data, while the sidebar's module tree remains
the derived **structure catalog**. When you add a module, add it to the reading catalog after
its prerequisites and before its substantive consumers; `scripts/gate/check-reading-order.py`
checks exact coverage and prerequisite order. Milestones is the explicitly labelled preview.

## Current modules

`Milestones.lagda.md` is the trophy case and reads first in the catalog: the
storefront, before the foundations stage. It states `V⊨ZF`, `V⊨ZF-impredicative`, `V⊨ZFC`, `L⊨ZFC` and
`L⊨GCH`, each a self-contained signature naming its proving chapter. **Both `L` trophies are
proved.** `L⊨GCH` was proved on 2026-09-05; its statement type is `GCHStatement` in
`L/GCH.lagda.md` and its proof term is `L⊨GCH` in `L/GCH/Theorem.lagda.md`. The only
hypothesis either takes is `LEM (ℓ-suc ℓ)`.

The namespace tree is the structure catalog, derived and never hand-maintained. **The reading
order is not the namespace order** (the two-catalog doctrine in
[dev/STYLE-agda.md](../dev/STYLE-agda.md)). Retired chapters left the tree entirely on
2026-09-06: the archive now lives outside the repository, at `~/Agentic/Archive/Bedrock-archive`,
mirroring the paths the files had here.

## Symbol master table

Required by [dev/STYLE-agda.md](../dev/STYLE-agda.md) §5: one row per symbol introduced
so far. Layers are the marking system of STYLE-agda §4 (① host, ② truth algebra,
③ structure fields, ④ object syntax).

| Symbol | Reading | Layer | Chapter | Input |
|---|---|---|---|---|
| `⟨_⟩` | the underlying type of | ① | `Base.Prelude` (re-export) | `\<` `\>` |
| `⊥*` | lifted empty type | ① | `Base.Prelude` (re-export) | `\bot` `*` |
| `∈ᶜ` | class membership | ① | `Base.Prelude` (re-export) | `\in` `\^c` |
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
