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

The aggregator. It imports every module, so `agda src/Everything.lagda.md` typechecks the
whole development (this is what `make check` runs). It is also rendered as the **site landing
page** (`index.html`), and its import block is the hyperlinked module list. **When you add a
module, add its import here** so it is typechecked, listed on the site, and reachable from the
Modules sidebar.

## Current modules

- `HelloWorld.lagda.md`: minimal smoke-test module.
- `Example/Naturals.lagda.md`, `Example/Doubling.lagda.md`: demo modules with real `##`
  sections that exercise the renderer's per-page table of contents and inline
  `` `name`{.Agda} `` references. Honest demo material, not part of the mathematics.

## Reserved namespaces (currently empty, marked with `.gitkeep`)

The book-part skeleton fixed by [dev/PLAN.md](../dev/PLAN.md) §4; porting fills these in
per the route tree (`[L1]` onward). By part:

- `Base/`: Part 0, host-language groundwork: `Prelude` (cubical re-exports and global
  conventions), `Truth` (truth values), `Classical` (LEM as a parameter interface; no
  postulate anywhere, per PLAN D2).
- `FOL/`: Part 1, first-order logic as an object of study: `Syntax` (the deeply embedded
  `Formula`), `Semantics` (Tarski satisfaction by structural recursion), `Renaming`, and
  `Reification/` (the bridge between host predicates and object formulas, with
  machine-checked adequacy certificates).
- `ZF/`: Part 2, what a ZF(C) model is: `Structure` and `Model` (the axiom-field
  records), in type-theory-native idiom (not transcribed axiom by axiom).
- `V/`: Part 3, the cumulative hierarchy as a HIT, and `V ⊨ ZF(C)`; later, set-theoretic
  geology (grounds, the mantle).
- `L/`: Part 4, the constructible universe as an inductive predicate: the capstone
  `L ⊨ ZFC`, built root-first through the temporary `Frontier` record (PLAN §5).

`Landmarks.lagda.md` (milestone theorems restated, the trophy case) arrives with `[L1.8]`.

## Symbol master table

Required by [dev/STYLE-agda.md](../dev/STYLE-agda.md) §5: one row per symbol, giving
symbol / reading / layer / defining chapter / Agda input sequence. Lands with the first
ported symbols (`[L1.1]` onward).
