# p1 probe report: the realization induction, priced in miniature

**Verdict: GO.** The induction shape of the rud route's realization leg
(every Delta-0-definable subset of a transitive `u` is `EVAL` of a finite
composite of basis operations) typechecks cleanly at a miniature scale:
339 code lines, cold-checked in 2.9 s, no wall, no postulates, no holes, no
`TERMINATING` pragmas. The clause shapes are cheap and mechanical; the
extrapolated full-fragment leg is a bounded multiple of one delivered
chapter, with the unprobed parameter plumbing as the one genuinely open
cost driver.

Probe file: `src/ProbeRudComp.agda` (untracked; 431 lines total, 339 code
lines). Checked with `agda src/ProbeRudComp.agda` from this worktree
(`--cubical --safe --guardedness`, project library file).

## 1. What the probe prices

The leg under price is SZ Lemma 1.4's "contains" direction: for every
Delta-0 `φ` with parameters in a transitive `u`, the set
`u ∩ {x | φ}` is a composite of basis operations applied to `u` and the
parameters. The paper blueprint is W Lemma 7's term-simulation induction
(clauses (i)-(xiv): atoms, negation, conjunction, variable permutation,
substitution, bounded quantifier), and SZ 1.3 (f),(c),(h),(g) as the closure
facts. The other direction (per-operation definability descriptions) is not
probed here; the B4a-B4d batches already measured it.

### 1.1 Design choices (recorded as the task requires)

- **Formula fragment: probe-local, not FOL.Syntax.** A 25-line
  `FmQ`/`Fm` pair (atoms `x ∈ y`, `∧`, `¬`, bounded `∃`) over `Fin n`
  variables beats reusing `src/FOL/`: reuse would drag in `Term`,
  structure-based satisfaction and the `L.Definability` chain, none of
  which the miniature needs. De Bruijn-free indexing (variable 0 = the
  separated `x`, variable 1 = the family variable, 2.. = parameters)
  keeps the environment threading definitional.
- **Definable subset: probe-local sett, the library's separation
  constructor** `⁅ u ∶ φ ⁆` (`Cubical.HITs.CumulativeHierarchy.Constructions`
  `SeparationSet`), whose membership classification `separation-ax` is
  already proven. This is cheaper than the tree's `defSet` idiom, which
  would import the constructible tower; the report's equality form
  (`eval t ≡ SepSet u φ ρ`, [ProbeRudComp.agda](src/ProbeRudComp.agda:428))
  is exactly the extensional content the route consumes.
- **Abstract basis as module parameters (lesson P-h).** The probe is
  parameterized over `pair/diff/inter/prod/mem/union/col/chSep` plus (one
  level down, in `module Realize`) `img`, all with extension equations as
  module parameters, so the probe is neutral between SZ's F0..F15 and
  Mathias's R0..R8. The induction consumes `diff`, `inter`, `union`,
  `col`, `chSep`, `img`; `pair`/`prod`/`mem` are carried (they enter via
  the relation-route extrapolation).
- **Constructivity wedge:** the classical identity `A ∩ B = A ∖ (A ∖ B)`
  is not constructive (the difference gives `¬¬`, not `∧`), so the
  abstract basis carries an **intersection operation** (`interOp`) rather
  than deriving `∩` from `∖`. The classical bases get `∩` from SZ 1.3(c);
  the route's algebra must do the same at the abstract-op level.
- **Transitivity** is stated in `∈ₛ` form and used exactly once, in the
  bounded-`∃` clause, to lift a witness `z ∈ bound ∈ u` to `z ∈ u` before
  applying the family realization; this is where the paper proof uses it.
- **Bounded-`∃` semantics over the bound's presentation** (`⟪ bound ⟫`,
  level `ℓ`) rather than over `V ℓ`, so satisfaction stays at `hProp ℓ`
  and the separation sett's classification remains applicable.
- **Family strengthening:** the induction is split into closed-composite
  realization (`realizeQ`, `realizeCh`) and a unary-family version
  (`realizeFam`) whose free variable is the bounded witness; the bounded-
  `∃` clause is `⋃ (imgOp fψ (ρ j))`, i.e. image plus bounded union, the
  R8/F8-family route of the blueprint. Bounded-`∃` bodies are restricted
  to quantifier-free formulas: nesting `∃` inside the family would need
  binary composites (the parameter plumbing), which is the probe's
  documented boundary.
- **`img` is parameterized one level down** (`module Realize`): its
  function argument is the composite syntax, so its signature must follow
  the syntax definition.

## 2. Per-clause price table

Line counts are non-blank, non-comment code lines; anchors point into
`src/ProbeRudComp.agda`.

| Clause | Lines | Anchors | What it is |
|---|---|---|---|
| atom (separated-variable membership shapes) | 35 | [atom dispatch](src/ProbeRudComp.agda:350), [family atom dispatch](src/ProbeRudComp.agda:372), [diagonal spec](src/ProbeRudComp.agda:219) | `x ∈ v`, `v ∈ x` (incl. `x ∈ x` via regularity); 4 shapes in Comp-land, 9 in family-land |
| `∧` | 39 | [and-ch](src/ProbeRudComp.agda:243), [and-ch1](src/ProbeRudComp.agda:267), [dispatches](src/ProbeRudComp.agda:358), [realizeCh](src/ProbeRudComp.agda:405) | intersection of the two realizations via `interOp` |
| `¬` | 28 | [neg-ch](src/ProbeRudComp.agda:257), [neg-ch1](src/ProbeRudComp.agda:282), [dispatches](src/ProbeRudComp.agda:362) | `u ∖` realization via `diffOp` |
| bounded `∃` (bound = named parameter) | 47 | [bex-mem](src/ProbeRudComp.agda:297), [dispatch](src/ProbeRudComp.agda:412), [semantics](src/ProbeRudComp.agda:154) | `⋃ (imgOp fψ (ρ j))`; image + bounded union + transitivity |
| statement + extensional equality | 13 | [ext≡](src/ProbeRudComp.agda:418), [realize](src/ProbeRudComp.agda:428) | membership characterization -> `eval t ≡ SepSet` via `separation-ax` |
| **clause work total** | **162** | | |

The remaining 177 code lines are the fixed machinery: the abstract basis
telescope and extension equations, the `FmQ`/`Fm` syntax and satisfaction,
the `Comp1`/`Comp` syntax and evals, transitivity and the regularity proof
for `V`, and the `SepSet` bridge.

## 3. Walls and formulation trail

**No wall hit.** Every typecheck of the probe ran under 3 s wall clock
(cold, after deleting the interface cache: 2.9 s; warm: ~0.8 s), versus the
180 s tripwire. No obligation needed three genuinely different failed
formulations; each obstacle below was resolved on its first or second
formulation, and is recorded as a surprise rather than a wall.

## 4. Extrapolation to the real build's comprehension leg

The probe prices four clause shapes plus the statement bridge. The full
Delta-0 fragment adds equality atoms, `∨`, bounded `∀`, quantifiers with
arbitrary bounds (including the separated variable), nesting, and the
parameter plumbing. The multiplier column states what each factor covers;
it is a shape multiplier, to be combined with the D-6 production factor.

| Probe clause | Probe lines | Full-fragment analogue | Multiplier | What the multiplier covers |
|---|---|---|---|---|
| atom | 35 | all atoms (`∈`, `=`) | 2.6x | `=` doubles the atom shapes (4 new shapes in each of two recursions); closed atoms and the diagonal are already present in the probe |
| `∧` | 39 | `∧` and `∨` | 2.2x | the `∨` clause (constructively not a De Morgan abbreviation) in all three recursions |
| `¬` | 28 | `¬` and bounded `∀` | 2.7x | bounded `∀` via `¬∃¬` plus its direct clause; two quantifier polarities |
| bounded `∃` | 47 | `∃`/`∀` over arbitrary bounds | 3.2x | bound = separated or family variable; nesting of quantifiers; the uniformity term machinery |
| statement/equality | 13 | production definable-subset bridge | 3.0x | defSet-style membership in both directions, environment plumbing per formula shape |
| parameter plumbing | 0 (unary families only) | k-ary composites, variable permutation/substitution, graph/image machinery | n/a | W Lemma 7 clauses (viii)-(xiv) and SZ's "simple functions" half; the single largest unprobed item |
| **totals** | **162** | | **4.6-5.5x** | **740-890 lines** for the full-fragment leg at probe discipline |

Applying the measured D-6 production factor (roughly 3x for readers in
both directions, guards, dispatch chains and environment plumbing) gives a
headline budget of roughly **2,200-2,700 lines** for the real build's
comprehension leg. For calibration: the route's replaced formula-to-
operation chapters are 1.1-1.3k lines each, so the rud comprehension leg
is priced at about 1.7-2.5 delivered chapters, with the parameter
plumbing the dominant uncertainty.

## 5. Surprises and lesson candidates

1. **Parameterized module bodies at column 0 silently lose parameter
   scope after the first declaration** (Agda layout): only the first
   declaration of a `module M (p : ...) where` whose body sits at the
   same column as `M` sees `p`; later declarations report `p` out of
   scope. Fix: indent the body deeper than the module header. A nested
   parameterized module additionally needs its `where` indented deeper
   than its telescope. Lesson candidate (C-series): "parameterized module
   bodies and nested-module `where` must be indented deeper than the
   header/telescope".
2. **The library hProp connectives fail in type positions.** `_⊔_`,
   `_⊓_`, `_⇔_`, `¬_`, `∃[ _ ]` all carry an unsolved result level
   (`hProp _`), which Agda cannot solve in a signature codomain ("should
   be a sort"); an hProp-valued expression in a codomain is also rejected
   even with explicit levels, while `⟨ expr ⟩` (content) or a named type
   is accepted. Fix: explicit-level wrapper connectives plus `⟨_⟩` around
   signature-level hProp expressions. Lesson candidate (I-series): the
   hProp-expression-in-type-position inference trap.
3. **Constructive `∩` is not `∖`-derived**: `u ∖ (u ∖ a)` realizes
   `{x ∈ u | ¬¬ (x ∈ a)}`, not `u ∩ a`. The abstract basis therefore
   carries `interOp`; the route must too (the classical 1.3(c) derivation
   is non-constructive). Lesson candidate (D-series): the rud basis
   interface needs an intersection operation.
4. **Where-clauses do not see a signature's implicit arguments** unless
   re-bound in the function's own patterns (`f {A} {B} ... = ... where
   h : ... A ...`), while explicitly bound pattern variables are visible.
5. **The bounded-`∃` semantics must quantify over the bound's
   presentation** (`⟪ bound ⟫`) to stay at `hProp ℓ`; quantifying over
   `V ℓ` bumps the level and breaks the separation sett's
   classification. This matches how the defSet idiom keeps smallness.
6. **Nesting cost driver:** one bounded quantifier level is free with
   unary families; the second level (a `∃` whose body quantifies again,
   or whose bound is the separated/family variable) requires binary
   composites and the permutation/substitution clauses. This is the
   parameter-plumbing multiplier's concrete content.

## 6. Protocol compliance

- Probe budget: 431 total / 339 code lines (under 400 code lines).
- Walls: none (max cold check 2.9 s; no obligation failed three times).
- No postulates (only module parameters), no holes, no `TERMINATING`
  pragmas; `--cubical --safe --guardedness`.
- No git commits, no pushes; only `src/ProbeRudComp.agda` and this report
  written; no existing file modified; `git status` shows the probe
  untracked and nothing else.
