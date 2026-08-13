# R3b report: the per-operation definability descriptions, F0-F7 and F9

**Date:** 2026-08-02. **Scope:** one new literate master
`src/L/Rud/Describe.lagda.md` plus this report. Nothing else was created or
modified: no `src/Everything.lagda.md`, none of the parallel agents' files
(`L.Rud.Images`, `L.Rud.Realize`, `L.Rud.Hierarchy`), no git, no postulates,
no holes, no `TERMINATING` pragmas, no LEM spent. Every agda invocation ran
under `GHCRTS=-M8g`, one typecheck at a time (C-12); the module typechecks
clean (cold 3.3 s wall, warm 1.1 s wall, exit 0), `lint-agda --check`,
`lint-prose --check`, `weave-i18n --check`, and `check-glossary --check` are
all green. Stop-line 1,400 code lines: 662 used.

## 1. What is delivered, operation by operation

Each operation gets a defining formula over `⟪ A ⟫` (one free variable `v`,
the arguments `a`, `b` as constants), its Delta-0 witness, and the adequacy
directions. The carrier `A` and the argument memberships are abstract module
parameters throughout (P-h); nothing of the operations ever unfolds, and the
membership-form theorems consume exactly the exported `Fᵢ-spec`.

| op | formula | Δ₀ | adequacy | defSet equation |
|---|---|---|---|---|
| F0 | `v ≐ a ∨̇ v ≐ b` (F0F9Frame) | `δ-∨ δ-≐ δ-≐` | both directions to membership (`F0-desc-out/in`) | `F0-defSet≡` ✓ |
| F1 | `(v ∈̇ a) ∧̇ ¬̇ (v ∈̇ b)` | `δ-∧ δ-∈ (δ-¬ δ-∈)` | both directions to membership | `F1-defSet≡` ✓ |
| F2 | `∃̇∈ a (∃̇∈ b (prAt′ t u w))` | `δ-∃∈ δ-∃∈ Δ₀-prAt′` | both directions to `F2-DRHS` (own copy) | debt: sealed hop |
| F3 | 10-binder tower + middle-pair waypoints (InsertAppendFrame) | 10×`δ-∃∈` + atoms | **no-go** (see §4) | sealed hop + no-go |
| F4 | same frame, slots exchanged | same frame | **no-go** (see §4) | sealed hop + no-go |
| F5 | `∃̇∈ a (v ∈̇ w)` | `δ-∃∈ δ-∈` | both directions to membership | `F5-defSet≡` ✓ |
| F6 | two `⋃⋃`-towers + pair waypoint + equality atom | 7×`δ-∃∈` + atoms | both directions to `F6-DRHS` | debt: sealed hop |
| F7 | `∃̇∈ a (∃̇∈ a (u ∈̇ v ∧̇ prAt′ t u v))` | `δ-∃∈ δ-∃∈ (δ-∧ δ-∈ Δ₀-prAt′)` | both directions to `F7-DRHS` | debt: sealed hop |
| F9 | `v ≐ ⁅ a ⁆s ∨̇ v ≐ ⁅ a , b ⁆` (F0F9Frame) | `δ-∨ δ-≐ δ-≐` | both directions to membership | `F9-defSet≡` ✓ |

Shared frames: `F0F9Frame` carries F0 and F9 (disjunctive equality over two
named members); `InsertAppendFrame` carries F3 and F4 (double-union towers,
pair waypoint, middle-pair waypoints; the two operations differ by one
coordinate exchange in the middle clause). The pair reader (`prAt′` and its
Delta-0 witnesses) is restated once over an arbitrary constant domain, with
its adequacy one line from `L.Coding.Base`; the double-union tower readers
(`tower-out`/`tower-in`) are shared by F3/F4/F6.

## 2. The adequacy face

For F0, F1, F5, F9 the adequacy is `⟨ (v ∷ []) ⊨ Φᵢ ⟩` against
`⟨ v ∈ˢ Fᵢ a b ⟩` in both directions, composed with the exported `Fᵢ-spec`,
and the `defSet Φᵢ ≡ Fᵢ a b` equation closes in the InL style through one
shared chain (`defSet-mem` specification, the Delta-0 absoluteness bridge,
one relabelling). F1 and F5 use transitivity for the image-inside-carrier
step; F9 carries the pair-membership hypotheses (the closure the switch
supplies); F0 needs no transitivity beyond the chain.

For F2, F6, F7 the adequacy is stated against `Fᵢ-DRHS`, a transparent copy
of the specification's right-hand side under this chapter's own name. The
specification's right-hand sides for these operations are **sealed names**
inside `L.Rud.Ops`'s `opaque` blocks (see §3): from outside, `Fᵢ-RHS a b v`
is an opaque hProp with no constructors and no destructors, so the final hop
`DRHSᵢ a b v ≡ Fᵢ-RHS a b v` (one line, definitionally `refl` once the seal
is opened) cannot be proved here. The formula-plus-adequacy core is complete
and forward-compatible: if `Fᵢ-RHS` moves out of the `opaque` block (the
operations stay sealed), the adequacy composes with `Fᵢ-spec` by refl.

## 3. The seal finding (surprise 1)

`F2-spec` through `F7-spec` are exported, but their right-hand sides are the
sealed names `Fᵢ-RHS`, and Agda's `opaque` gives them no outside
constructors. Three probes confirmed this mechanically (a hand-built
truncated witness does not typecheck against `fst (F2-RHS a b v)`; a
destructor from `⟨ F2-RHS a b v ⟩` is impossible; the same for F1's sibling
sealed ops). Consequently "satisfaction iff membership" through the spec is
unprovable for F2/F3/F4/F6/F7 as the seal stands. The minimal remediation is
to move the `Fᵢ-RHS` hProp definitions outside the `opaque` blocks in
`src/L/Rud/Ops.lagda.md` (the set-valued operations remain opaque); this is
recorded as the batch's load-bearing dependency for the switch batch.

## 4. The F3/F4 no-go trail

The shared frame's two adequacy directions (satisfaction against its own
`DRHS`) are recorded as a no-go after more than three genuinely different
formulations. The formula and the Delta-0 witness for both operations are
delivered and typecheck; what failed:

- (a) the frame was first parameterized by an abstract middle-clause formula
  and its adequacy; the midSat-input obligation hit a stuck unification of
  the abstract formula's satisfaction with the body's conjunct;
- (b) with the middle clause made concrete (`prAt′ f0 mid₁ mid₂` with
  abstract slots), the sat-in's emission against the three-layer DRHS
  `⋁ u (⋁ z (⋁ w …))` resisted the destructuring of the inner existential
  (`h₂`-shaped obligations); the sat-out's `midSat` input similarly resisted
  several projection counts and a destructuring let;
- (c) the `midCorr` composition fixed the sat-out's output side, and the
  sat-in progressed past the tower and waypoint witnesses, but the inner-`⋁`
  destructuring and the midSat-input unification remained unresolved.

The tower, the waypoints, the pair reader, and the DRHS shapes all
typecheck; the concrete obstruction is the bookkeeping of the DRHS's nested
truncated existentials against the satisfaction's nested `⋁`s inside a
`let`/`PT.rec` stack. A later batch should restructure the sat-in to thread
the witnesses through named helper functions (the `tower-out` pattern) rather
than one nested `PT.rec` chain.

## 5. Timings and walls

Module-level: cold 3.3 s wall, warm 1.1 s wall; during development most
single-file checks ran 3-4 s (the heaviest ~4 s). No check approached the
180 s wall; no heap exhaustion; no exit 137/251. One attempted brute-force
loop over projection depths produced `rc=42` from the environment watchdog
(sequential subprocess spawning was too fast for the quota); it was
abandoned and no such loop was run again.

## 6. LESSONS applied and surprises

- **P-h, P-c, I-2, R-34, C-11** observed: abstract carriers everywhere; the
  pair-at kit and tower readers are private restatements (the operations stay
  sealed); every hProp expression is `⟨_⟩`-wrapped or level-pinned; `⋁`
  applications name their index type; module bodies indent under their
  headers.
- **Surprise 2 (Agda scoping):** sibling module names are not in scope in
  later top-level signatures (only inside module bodies), and a top-level
  module alias (`module SemTop = FOL.Semantics …`) shadows the qualified name
  in signatures. Workaround: nested telescopes keep the satisfaction in scope
  (`MidAdeq`), and the F3/F4 frame's parameters avoid satisfaction-typed
  telescopes.
- **Surprise 3:** `FOL.Semantics._^_` lives inside the module telescope;
  importing it at top level mis-instantiates the implicit module parameters.
  Open it per-module.
- **Surprise 4:** `⟨ P ⊔ Q ⟩`/`⟨ P ⊓ Q ⟩` in type positions displayed
  misleadingly (extra `∥_∥₁`); the robust pattern is to apply the
  specification result directly to a named step function instead of nesting
  `PT.rec`.
- **Surprise 5:** where-bound functions in `where` blocks must align
  indentation with their signatures, and nested `where` blocks inside
  `where` blocks are fragile; a `let … in` with a destructuring pattern
  worked where the nested `where` failed.
- **Surprise 6:** `∈pair-introR` returns the HIT membership; wrapping it in
  `∈∈ₛ .snd` (which expects the small membership) fails; use the raw HIT
  membership where the target is structure membership.
- **Surprise 7:** `lint-prose --fix` joins over-broken CJK paragraphs; the
  zh prose must be written as single long lines.

## 7. Protocol compliance

Created only `src/L/Rud/Describe.lagda.md` (untracked) and this report;
typechecked only the module, never `Everything`/`make check`; no postulates,
holes, or `TERMINATING`; bilingual prose groups balanced (28/28/28 markers);
no em dash; no half-width CJK punctuation; the zh rendering of the
rudimentary class follows the glossary (初步函数 where the term appears).
