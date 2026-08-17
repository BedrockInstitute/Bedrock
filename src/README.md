# src

The Agda development: literate `.lagda.md` **masters**, the single source of truth for both
the proofs and their prose. This is an English developer-facing folder guide; the rule set is
[dev/POD.md](../dev/POD.md) section 3, and `AGENTS.md` holds it until the POD cutover.

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

`Everything.lagda.md` is the reading catalog and the ONE list of modules. It imports every
master, in reading order, with a one-line description for each. Read it there. This file does
not duplicate it, because a second list drifts: MEASURED 2026-08-17, this section described a
20-master tree with `V/` and `L/` empty, while the tree held 97 tracked masters, 7 under
`src/V/` and 72 under `src/L/`, and the repository held zero `.gitkeep` files.

`Landmarks.lagda.md` is the trophy case and reads first in the catalog, by owner ruling: the
storefront, before Part 0. It states `V⊨ZF`, `V⊨ZF-impredicative`, `V⊨ZFC` and `L⊨ZFC`, each a
self-contained signature naming its proving chapter. **`L ⊨ GCH` is NOT there yet**: its
statement type is `GCHStatement` at `src/L/GCH.lagda.md:59-60` and no proof term exists.

The book-part skeleton is [dev/PLAN.md](../dev/PLAN.md) §4 and the namespace tree is the
structure catalog, derived and never hand-maintained. **The reading order is not the namespace
order** (PLAN §5, the two-catalog doctrine). Two retirement records that used to sit in this
section moved to [dev/ARCHIVE.md](../dev/ARCHIVE.md) on 2026-08-17: `FOL/Reification/` and the
`L/Frontier.lagda.md` debt registry, each with its measurement.

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
| `⊨ᴬ` | satisfies with quantifiers bounded by `A` | ① | `FOL.Manipulation.Relativize` | `\models` + `\^A` |
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
