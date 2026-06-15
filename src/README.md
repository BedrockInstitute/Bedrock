# src

The Agda development: literate `.lagda.md` **masters**, the single source of truth for both
the proofs and their prose. This is an English developer-facing folder guide; see
[CONTRIBUTING.md](../CONTRIBUTING.md) for the full contributor guide.

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

Placeholders for the development; see the [Charter](../docs/en/CHARTER.md) for the intended
content. By their role there:

- `FOL/`: first-order logic, the deeply embedded `Formula` and Tarski satisfaction.
- `Reification/`: the reflection bridge from `Formula` to host predicates, with the
  machine-checked adequacy certificate.
- `ZF/`: ZF reconstructed in type-theory-native idiom (not transcribed axiom by axiom).
- `V/`: the cumulative hierarchy and set-theoretic geology (grounds, the mantle).
- `L/`: the constructible hierarchy, as an inductive predicate.
