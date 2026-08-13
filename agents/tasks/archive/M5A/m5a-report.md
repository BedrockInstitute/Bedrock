# M5a report: the name order re-cut to skeleton and parameters

## Status

Complete. Both edited files typecheck standalone; the scaffold
`src/L/Godel/Step.lagda.md` rechecks untouched; `src/Everything.lagda.md` is
green; all runnable linters pass.

- `agda src/L/WellOrder/Base.lagda.md` — clean.
- `agda src/L/Godel/Name.lagda.md` — clean.
- `agda src/L/Godel/Step.lagda.md` — clean, untouched.
- `agda src/Everything.lagda.md` — clean.
- `lint-agda.py` on both edited files — clean (import necessity and style).
- `lint-prose.py --check` on both edited files — clean (one spacing fix was
  applied with `--fix`).
- `weave-i18n.py --check` — clean.
- `check-glossary.py` — clean.
- `reuse lint` — could not run in this sandbox (its `ProcessPoolExecutor`
  fails with a `PermissionError` on `os.sysconf("SC_SEM_NSEMS_MAX")`). The
  change adds no files, so the `REUSE.toml` carve-outs are untouched.

## Timings (cold, this machine)

| Check | Time |
| --- | --- |
| `Base.lagda.md` | ≈0.8 s |
| `Name.lagda.md` | ≈1.7 s (see Surprises: the first formulation was far over budget) |
| `Step.lagda.md` | ≈2.6 s |
| `Everything.lagda.md` | ≈45 s cold, ≈4 s warm |

## The `Lab₀` choice

As the brief specifies: `Lab₀ = (ℕ × ℕ × ℕ) × (Unit* {ℓ} ⊎ Unit* {ℓ})`. The
strip is structure-preserving (`inl _ ↦ inl tt*`, `inr _ ↦ inr tt*`), so the
graft can tell a parameter slot from a plain slot. A custom two-constructor
data type (the previous draft's `slot₀`/`param₀`) was considered and rejected
in favour of the brief's choice; the brief's type worked once the proof
formulation was fixed (below).

## Deviation in the graft equations

The brief's equations use `let (cs' , rest) = graftL cs ps in …` bindings. The
final code writes the same content as explicit `fst`/`snd` projections, e.g.

```
graftT (node ((i , j , k) , inl _) cs) ps =
  (node ((i , j , k) , inl tt*) (fst (graftL cs ps))) , snd (graftL cs ps)
```

The graft semantics are unchanged and exactly the brief's: an `inl` node
consumes no parameter and threads the children with the whole remainder; an
`inr` node consumes the head parameter and threads the children with the rest;
the `inr`-with-`[]` default returns `junk` and `[]`. The projection form is
what lets the retraction proofs below be written as direct path lambdas (see
Surprises); with the `let`/`where` form the definitional-equality checks did
not terminate inside the budget.

The retraction is proved exactly as prescribed: mutual `graftT-strip` /
`graftL-strip`, and `strip-par-inj` as the corollary at `rest = []` using
`++-unit-r`, reading first components.

## The `++` lemmas

Both lemmas came from the library, `Cubical.Data.List.Properties`:

- `++-unit-r : (xs : List A) → xs ++ [] ≡ xs` (used in `strip-par-inj`);
- `++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs`
  (used in the cons clause of `graftL-strip`, where
  `parL (u ∷ us) ++ rest` is `(parT u ++ parL us) ++ rest`).

No repo-local `++` lemmas were needed. (`length++`, `takeLength++`,
`dropLength++` also exist in the library; the final version does not use
them.)

## Earliest-disagreement zh rendering

The brief's suggested 最早相异 is **not** the established rendering.
`dev/glossary.toml` has no entry for the term; the established zh rendering
lives in `src/L/Choice/Finite.lagda.md`: the heading for "The earliest
disagreement" is **最先的分歧**, and the prose uses **最先分歧处** /
**最先的分歧点** (lines 51, 631, 719, 810, 916, 1152). The new prose reuses
those renderings.

The new load-bearing terms 骨架 (skeleton), 参数表 (parameter list), and 回植
(graft) were introduced with the brief's renderings. They are not yet in
`dev/glossary.toml`; per AGENTS.md new terms would enter the glossary, but the
brief restricts changes to the two files plus this report, so the entries are
surfaced here instead.

## What was pruned

In `Name.lagda.md`, the re-cut orphaned the tree-order route (`labSWO`,
`module TO`, and any `sumSWO`/`unitSWO`/`natSWO`/tree-order imports were
already gone in the prior draft; the final file imports only `Tree; node` from
`L.WellOrder.Tree`). The previous broken draft's failed direct-induction
machinery was removed wholesale: `strip-children`, `sub-tree`, `strip-slot`,
`strip-nums`, `tl-l`, `hd-l'`, `cons-head`, `cons-tail`, `split-concat`, the
`par-count` length machinery, the `slot∈limit` helper, and every `{!!}` hole.

Imports pruned from `Name.lagda.md`: `take`, `drop`, `length` from
`Cubical.Data.List`; `length++`, `takeLength++`, `dropLength++` from
`Cubical.Data.List.Properties`; `J` from `Cubical.Foundations.Prelude`;
`Σ≡Prop` from `Cubical.Data.Sigma`; `injSuc` from `Cubical.Data.Nat`;
`∈∈ₛ` from `Cubical.HITs.CumulativeHierarchy.Properties`; `false≢true` from
`Cubical.Data.Bool`; `∣_∣₁` from `Cubical.HITs.PropositionalTruncation`.

## Surprises

1. **`cong` with a function lambda hangs on `⟪ A ⟫`-valued goals.** The first
   formulation of the graft retraction used `cong (λ p → …) …` (even with a
   plain non-pattern lambda) and `subst` over an equality motive. It ran past
   6 minutes for the file (well over the 180 s per-definition tripwire), while
   the identical code over an abstract `X : Type ℓ` checked in under a second.
   Replacing every such step with a direct path lambda
   (`λ ι → let p = … ι in …`) made the whole file check in ≈1.7 s. This is a
   new data point alongside memo §9's laws P-d/P-f: at concrete towers the
   path former should be written directly, not through `cong` with a
   function whose domain carries the presentation type.
2. `# 0` is definitionally `∅` (InfinitySet), so the nil/cons code clash is
   the predicted ~5-line `pr≢∅` via `∅-empty` + `pairing-ax`, and `codeL-inj`
   needs no case analysis beyond it.
3. The `reuse` binary cannot start its worker pool inside this sandbox; the
   licensing check is unaffected because the change modifies only two existing
   files (no new files, so the `**` AGPL default and the content/font carve-outs
   are untouched).
