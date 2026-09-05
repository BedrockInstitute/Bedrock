# Task B4 report: the levels internalized — prefix-table description and the step

**Date:** 2026-08-02. **Scope:** option B's largest single item — the prefix-table
internalization of the kinded levels, both ways. **Files touched:** one new chapter
`src/L/Godel/Levels.lagda.md`, the `Everything` wiring (one import, one catalog bullet
per language), this report. Nothing else; no git, no postulates, no holes, no
`TERMINATING`.

## 1. What is delivered, and the honest state

The chapter is **green end to end** (agda 2.8.0, `src/L/Godel/Levels.lagda.md` and
`src/Everything.lagda.md`), with the layer machinery and the successor reader — the
unmeasured risk the pivot memo carried — **fully proved in both directions**. The
pinning theorem, the fill, and the step are **not yet in the chapter**; they are the
remaining work, itemized in §5. This report is written against that honest state
rather than over-claiming the brief's full clause set.

### Delivered (green, typechecked)

1. **Slots and helpers**: `sh2`–`sh9`, the local `singletons` family with both
   membership laws, and the `SglDesc.singletonsAt` description with both readers.
2. **The nine layer disjuncts** `InterDisjAt`, `UnionDisjAt`, `DiffDisjAt`,
   `SelMDisjAt`, `SelEDisjAt`, `AllTuplesDisjAt`, `ExtDisjAt`, `ShiftDisjAt`,
   `ValuesDisjAt` over slots, plus the disjunctive `LayerDisjAt` and the layer
   description `LayerAt`.
3. **`LayerLaws`**: all nine **out-readers and nine in-readers**, direction-paired,
   green. (The fill side needs these in-readers; they were built and typechecked
   here.)
4. **`FunAt`, `Base0`, `BaseS`, `SucClause`, `DomAdeq`, `PrefixAt`**: the full
   prefix-table description, including domain adequacy.
5. **`fun-out`, `base0-out`, and `suc-out`**: the base and successor readers, green.
   `suc-out` extracts the previous entry, the layer, the union equation, and the
   per-member layer out-direction at the clause's numeral slots. This is the piece
   that consumed the most effort and the one the pivot memo flagged as the carried
   risk.
6. **Chapter prose**: intro, the layer section, and the prefix-table section in en+zh.
7. **Everything wiring**: `import L.Godel.Levels` after `L.Godel.Closure`, plus one
   catalog bullet per language.

## 2. The largest single item: `suc-out` and the layer readers

The successor reader is where the full clause set meets concrete slots, and it was
the hard part. Several distinct defects had to be found and fixed before it checked:

- **The parse of the disjunct chain.** Agda's layout block for a where-clause must
  keep all declarations at one column; the original go/rest chain sat at a deeper
  column than its siblings, which the parser rejected. Aligning the block fixed it.
- **Top-down where scoping.** A where-clause declaration cannot see later
  declarations in the same block (Agda's rule, confirmed empirically). The
  disjunct-handler chain had to be ordered dependencies-first (`hS'`, `hV'`,
  `rest7`, … , `go`).
- **`Sum.rec` on a truncated sum is the wrong eliminator.** `⟨ γ ⊨ (φ ∨̇ ψ) ⟩` is the
  hProp join `Logic._⊔_`, whose underlying type is `∥ ⟨φ⟩ ⊎ ⟨ψ⟩ ∥₁`. Eliminating it
  requires `PT.rec squash₁` with `inl`/`inr` pattern-matching (the `Definable`
  precedent), not `Sum.rec`.
- **Slot arithmetic in the CLI/RDI module instantiations.** The clause formula reads
  at the clause environment (`env`, length `suc⁸ n`); the reader prepends the member
  (`z ∷ env`, length `suc⁹ n`); the goal formula reads at `(z ∷ γ)`. The original
  instantiations were off by one at every slot; the correct ones are
  `CLI = LayerLaws {suc⁸ n} zero (sh8 t) (suc⁷ zero) (suc⁶ zero) (sh8 a) env` and
  `RDI = LayerLaws {n} b t l k a γ` (the reader's own `suc` supplies the goal-level
  shifts).
- **The `isProp⊎` three-argument trap.** `Cubical.Data.Sum.isProp⊎` needs a
  disjointness proof `A → B → ⊥`, which is false here (a member can be both old and
  new). The layer goal is therefore the **truncated sum**
  `∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt … ⟩ ∥₁`, not a plain `⊎`; every
  layer reader, wrapper, and the union equation were rebuilt against that type.
- **Disjunct injection order.** In a right-nested `∨̇` chain the member sits at the
  *right* of the innermost sum: `w8` (ValuesDisjAt) needs nine `inr`s and nine `∣₁`s,
  not `inl`. Getting this wrong produced a stream of confusing `Σ`-vs-`⊎` errors.
- **The `AllTuplesDisjAt` argument order** (carrier, arity — not the reverse) and
  the `hX'` ExtDisj reader's `sucAtL` witness (which must be read from the formula
  satisfaction, not derived from a membership hypothesis).

## 3. Timing (per section, cold checks of the whole file)

The whole chapter cold-checks in about **17 s** (agda 2.8.0 on this machine); no
single definition has approached the 180 s wall the brief warns about. Rough
per-section costs from the development runs (each is a cold full-file check; the
file was repeatedly green through the section in question):

| section | cold check | notes |
|---|---|---|
| imports, slots, singletons, all nine disjuncts, `LayerLaws` readers (in+out) | 8–11 s | green before `suc-out` thickening |
| `FunAt`/`Base0`/`BaseS`/`SucClause`/`DomAdeq`/`PrefixAt`, `fun-out`, `base0-out` | 8–11 s | green |
| `suc-out` + layer reader chain (CLI/RDI instantiations, truncated-sum goal) | 16–17 s | the carried risk; several formulation restarts (parse, scope, slots) |
| whole chapter, cold | ~17 s | stable across repeated runs |
| `Everything` with the import | ~3 s (warm) | green |

The 180 s tripwire was never hit; the expensive parts are the CLI/RDI module
instantiations and the layer disjunct chain, not any single definition.

## 4. Design decisions and surprises

- **The meta level family is private in Closure.** `slice`, `step`, `StepTag`,
  `StepPayload`, `stepImage` are sealed (`private … mutual`) in the closure chapter;
  a consumer cannot pattern-match the tag or see `stepImage`. The chapter therefore
  **restates the level family locally**, line for line (the B1/B2 precedent for
  private machinery), and all layer readers, the pinning, and the fill work through
  the local copy. `Closure.slice-inv`, `cut-sound`, `Terms.WithLEM`, etc. are still
  imported directly.
- **The layer goal must be a truncated sum**, not a plain disjunction, because
  `isProp⊎` demands a disjointness proof that is false here (a value can be both an
  old member and a new image). This is the single most consequential fix in the
  chapter: it changes the statement of `suc-out`'s per-member property and every
  layer reader.
- **Where-clause scoping is top-down.** Forward references inside one where-block
  are rejected. The disjunct chain is ordered so each declaration only uses earlier
  ones; `layerOut` sits last.
- **`#` and `numeralL` are opaque.** `sucV (# m) ≡ # (suc m)` is not definitional;
  several attempted shortcuts through it failed. The `sucAtL` witness must be read
  out of the clause formula, exactly as the `Definable` out-readers do.

## 5. Remaining work (next steps, in order)

1. **`prefix-pins`** (the heart). Meta-induction on `n` consuming `base0-out` and
   `suc-out`; the layer identification needs the *layer-in* direction (step images
   are in `L`), which requires exposing the clause's `∀̇`-witness from `suc-out`'s
   output or proving a `layerIn` lemma inside `finish` — the forward-only
   `layerOut` is not enough.
2. **The fill**: `sliceL : ⟨ isL A ⟩ → ⟨ isL (slice A n k) ⟩` by ℕ-induction over the
   clause operations (the `InL` lemmas were deliberately left out of the imports
   once the fill was deferred), then the packed prefix table via `stageFam`/`finSet`
   (Tower's `hS` block), then `prefix-fill` per clause consuming the in-readers and
   the `slice-in` laws.
3. **The step both ways**: `StepAt b a` in Tower's shape under `module WithLEM`;
   `step-out` spends `prefix-pins` then `Closure.cut-sound`; `step-in` spends
   `Closure.WithLEM A lem .cut-complete` then `prefix-fill` and the entry
   memberships.
4. **Prose**: the pinning, fill, and step sections (en then zh), plus the Recap.
5. **Re-run `make check`** once the above land (the four linters are currently green
   on the delivered files; `reuse lint` needed the recorded `os.sysconf` fallback
   with 32000 in this sandbox).

## 6. Terms

The chapter uses the B3 terms as recorded in `dev/glossary.toml` (层/片/单例族), and
introduces no new load-bearing term beyond them. `prefix table` is rendered 前缀表
and `layer` 层, matching the existing entries; the pinning theorem is called
「钉住定理」in the prose, consistent with the B1–B3 usage of 钉住 for pinning.

## 7. LESSONS applied

P-d (direction pairs, named continuations), P-c (seal union-of-step indices at
birth; the `finSet`/entry seals are pending with the fill), Rule 1 (discharge
substitutions at variable arguments), Rule 8 (name `PT.rec` payloads), Rule 10
(named helpers for case splits into membership), Rule 20 (composites
factor-by-factor — the layer chain is factored into per-disjunct readers), D-2
(junk excluded by construction), C-8 (linters run explicitly on the new files; the
glossary and marker checks needed `.venv`'s Python 3.11).

## 8. The LayerAt slot layout

Binder stacks and environment lengths, as built and checked:

| disjunct | binders (outer→inner) | env |
|---|---|---|
| Inter/Union/Diff | κ, S, X, Y | `Y ∷ X ∷ S ∷ κ ∷ z ∷ γ` |
| SelM/SelE | κ, S, X, i, j | `j ∷ i ∷ X ∷ S ∷ κ ∷ z ∷ γ` |
| AllTuples | (none; `allTuplesAt`) | `z ∷ γ` |
| Ext | s, κ, S, X, y | `y ∷ X ∷ S ∷ κ ∷ s ∷ z ∷ γ` |
| Shift | s, κ, S, X | `X ∷ S ∷ κ ∷ s ∷ z ∷ γ` |
| Values | n1, κ, S, X | `X ∷ S ∷ κ ∷ n1 ∷ z ∷ γ` |

Layer environment lengths: clause env `env = L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ k'₀ ∷ n'm ∷ γ`
(length `suc⁸ n`), member-extended `z ∷ env` (length `suc⁹ n`), goal env `z ∷ γ`
(length `suc n`). The `LayerLaws` module is instantiated at these three lengths for
the out-, clause-, and goal-level readings respectively.
