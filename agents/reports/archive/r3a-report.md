# r3a report: the realization induction, first pass

**Verdict: NO-GO on the full induction; partial front delivered and
typechecking.** The abstract-basis telescope, the composite syntax with
evaluation, the DefOf-face satisfaction machinery, the satisfaction
congruence, and the variable plumbing (term classification, term-value
membership bridge) typecheck cleanly (543 lines, ~6.5 s cold, `GHCRTS=-M10g`).
The walk's atom clause and the term-membership helper each hit an in-situ
conversion wall after many genuinely different formulations; per the wall
protocol this batch stops with a clean trail rather than a workaround. The
report records every wall, the LEM-spend inventory as designed, and the
deltas from the probe.

Deliverable file: `src/L/Rud/Realize.lagda.md` (543 lines, typechecks
`agda --cubical --safe --guardedness`; the orchestrator's `Everything`
wiring is untouched, as are the sibling `L.Rud.*` files).

## 1. What is delivered (all typechecking)

- **The abstract basis telescope** (the probe's list plus one extension,
  each operation with a two-direction extension spec): pair, difference,
  intersection, product, membership relation, union, collection,
  characteristic separation, image-with-stack spec, and the new
  `eqSepOp`/`eqSepSpec` (constant-equality separation, see section 4).
  The classical law `lem : LEM (ℓ-suc ℓ)` is a module parameter.
- **The k-ary composite syntax** `Comp : ℕ → Type` with the witness-stack
  evaluation `eval : Comp k → Vec (V ℓ) k → V ℓ`, including the image
  constructor and the equality-separation constructor (the latter now
  evaluates through the abstract `eqSepOp`, not through a LEM decision).
- **The DefOf face**: `satN` (inner satisfaction compressed one universe),
  `ρV` (parameter environments), `DefSetK` (the separated subset as a
  sett over the small member type), `defmemK` (its membership
  characterization), and the environment congruence `satN-resp` (12
  formula clauses).
- **The variable plumbing**: `split`/`sucMap`, `termC` (term to composite
  or separated-variable marker), `valSem`/`valSplit`, `lookup-split`,
  `val≡` (term evaluation agrees with the composite evaluation),
  `valSem-semSplit`, and the sum-injectivity kit. The satisfaction- and
  membership-in-signature walls (below) forced the named-head pattern
  (`satAt`-style definitions and `eval-cong` as a path lambda) into the
  design; those fixes are in the delivered front where they typecheck.

The statement of record (the induction's target, from the brief) is the
realization at depth zero: for every `Δ₀` formula with parameter variables
and every environment over a transitive `u`, a composite whose value is
extensionally the separated subset, with the `DefOf.defSet` bridge at no
parameters. Its shape is fixed in the report's section 5; the clause
machinery needed to prove it is the walled part.

## 2. Per-clause price table

The probe's rows, with the realized (typechecking) versus walled (NO-GO)
status. "Lines" are the delivered front's counts; walled rows carry the
trail anchors.

| Clause | Status | Notes |
|---|---|---|
| basis telescope + `Comp`/`eval` | DELIVERED | 210 code lines; `eqSepOp` added (section 4) |
| `Trans`, regularity | DELIVERED | probe's proofs, unchanged |
| satisfaction face (`satN`, `ρV`, `DefSetK`, `defmemK`) | DELIVERED | 70 lines; `defmemK` via the large-membership route (DefOf shape) |
| satisfaction congruence (`satN-resp`) | DELIVERED | 45 lines, 12 clauses, named `cons-resp`/`tmVal` heads |
| variable plumbing (`split`..`val≡`) | DELIVERED | 75 lines; `valSem-semSplit` bridges the two value forms |
| term-membership (`termC∈u`) | **WALLED** | section 3, wall 2; the split-inr bridge walls in situ |
| `bound∈u`, `rewrite-∈` | **WALLED** (blocked by termC∈u) | written, not typechecked |
| atom `∈` (4 shapes) | **WALLED** | section 3, wall 1; the m-indexed characterization type walls |
| atom `=` (4 shapes) | **WALLED** | depends on atom `∈` shape |
| `∧`, `∨`, `¬`, `⇒` helpers | **WALLED** (blocked) | designed (inter, pair-union, diff, diff+DNE) |
| bounded `∃`, bounded `∀` | **WALLED** (blocked) | designed (image+union; complement+DNE) |
| nesting/permutation/substitution | **WALLED** (blocked) | the k-ary `Comp` machinery is delivered; the clause dispatch is not |
| statement + `DefOf.defSet` bridge | **WALLED** (blocked) | `extEq`/`realize`/`defSet-bridge` written, not typechecked |

## 3. Walls (full trail, per the wall protocol)

### Wall 1: the atom-membership characterization (atom-mem / atom-chSep)

The obligation: for the composite `chSepC a b (conC u)` and a satisfaction
`Q`, prove `⟨ ⟪u⟫↪ m ∈ₛ eval (chSepC a b (conC u)) (map fst ws) ⇔ₚ Q ⟩`
with `Q` the tree's atom satisfaction at the separated index. In-situ
typechecking exceeds the 180 s tripwire (measured >240 s). Formulations
attempted, each a genuinely different shape, all walling in situ (the
isolated machinery does not reproduce the wall, per P-i):

1. the with-based atom dispatch with the `satN`-in-signature (the original
   design);
2. the same with a named `atomSat` head in the signature (fast signature,
   walled clause bodies);
3. the content-level `×` return type;
4. the `⊆u` certificate changed to the m-indexed form;
5. the large-membership (`∈`) statement form;
6. a top-level named `atom-chSep` helper with the fwd/bwd in a where-block
   (annotated and unannotated);
7. `rewrite-∈` with the satisfaction stated through `satAt` (named head);
8. direct double-subst fwd/bwd; and
9. the probe's exact shape over arbitrary `x : V ℓ`.

Every variant walls in situ; the identical obligation in the probe (its
`realizeQ` membership atoms) typechecked in 2.9 s. The in-situ difference
is the file context: the deep module nesting, the k-ary witness stack
(`map fst ws`), and the satisfaction-of-the-tree-atom content in the
obligation type. Lesson candidates: the m-indexed membership
characterization type is a new wall class on this codebase; the probe's
fast shapes do not transfer to the k-ary/DefOf-face context unchanged.

### Wall 2: the term-membership helper (termC∈u)

The obligation: for an x-free term `t` classified `inl c`, prove
`⟨ eval c (map fst ws) ∈ₛ u ⟩`. The `cong (λ c' → eval c' (map fst ws))`
formulation produced a presentation-normalization error (fast, not a
hang); every subsequent formulation walls in situ (>180 s, measured
>240 s):

1. `cong` with the eval function lambda (P-g hazard, errored fast);
2. `eval-cong` as a named path lambda, used with `subst` and `sym`;
3. the transport path lambda `transport (λ i → ⟨ eval (p i) (map fst ws)
   ∈ₛ u ⟩)` for the con case (fast alone) and the var cases;
4. the where-helper dispatcher on the split result (fast with two clauses
   real, walls with the third; the inr cases, both one-liners, wall
   together);
5. the named `valParam`-head sub-helpers (fast with the sub-helpers alone,
   walls when the dispatcher's inr clause calls them);
6. the `~`-transport bridge between the two value forms (walls).

The in-situ wall class: any transport/subst whose motive is membership in
a value produced by the composite evaluation, in the presence of the
full clause grid. The P-i [C′] lesson (cheap codomains for grids) was
applied and moved the wall but did not clear it.

**Wall protocol compliance:** each wall exceeds the 180 s per-definition
tripwire; three or more genuinely different failed formulations were
attempted on each obligation before stopping. No `postulate`, hole, or
`TERMINATING` pragma was left in the delivered file (the diagnostics used
temporary placeholders, all removed; the delivered file typechecks with
`--safe`).

## 4. LEM-spend inventory (as designed; the classical spends)

- **Constant-equality atoms** (`v₁ ≐ v₂`, both x-free): the probe spent
  LEM inside the evaluation of a `eqSepC` constructor. The in-situ wall
  on that obligation (the first wall resolved in this batch) forced an
  upstream reshape per P-i [E]: the telescope now carries an abstract
  **equality-separation operation** `eqSepOp` with a two-direction spec,
  so the realization itself is LEM-free on equality atoms and the
  classical spend moves to the operations layer (R1/R3 assembly), where
  `eqSepOp` is built by excluded middle. This is the report's first
  recorded spend, relocated by design.
- **Implication** (`φ ⇒̇ ψ`): `u ∖ (a ∖ b)` with the forward direction
  landing on a double negation, discharged by `dne` (`lem`), the second
  spend (clause designed, not built).
- **Bounded universal** (`∀̇∈ t ψ`): the complement `u ∖ ⋃ (img (u ∖
  Sepψ) b)`, forward direction via `dne` (SZ 1.3(f),(h) shape), the third
  spend (clause designed, not built).
- Intersection-from-difference: not spent; the basis carries `interOp`
  per the probe ruling (D-7).

## 5. Delta from the probe

- **Index convention:** the tree's de Bruijn formulas force the witness
  stack in front of the separated variable; the formula index is
  `k + suc n` (not the probe's bespoke `Fin n`), which makes the Δ₀
  quantifier bodies align definitionally with the recursion's depth.
- **Satisfaction:** the tree's inner satisfaction (`⊨ᵐ-small`) replaces
  the probe's local `Sat`; the u-indexed small forms of the bounded
  quantifiers are definitional (verified in a scratch), which is the
  intended bridge.
- **Membership characterization:** stated at the m-indexed member
  `⟪u⟫↪ m` (probe: arbitrary `x : V ℓ` with an explicit `x ∈ u`
  conjunct), matching the DefOf face; this is the wall-1 shape.
- **Named heads:** the satisfaction-in-signature walls forced named
  definitions (`satAt` for satisfactions, `eval-cong` as a path lambda)
  so obligation types keep stuck heads; this is now a recorded technique
  for this codebase (lesson candidate).
- **LEM placement:** equality separation moved to the abstract basis
  (section 4), the first design delta from the probe's LEM-in-eval.
- **Variable permutation/substitution:** the tree's de Bruijn syntax
  makes permutation definitional (lookup), so W Lemma 7's clauses
  (viii)-(xiv) compress into the `split`/`lookup-split` machinery; the
  k-ary `Comp` structure carries the substitution plumbing.

## 6. LESSONS applied and new candidates

- P-h: the whole front is module-parameterized; nothing concrete unfolds.
- P-g: `cong` with a function lambda over `Comp`-valued evaluations
  triggers presentation normalization; named path-lambda heads
  (`eval-cong`) are the cure.
- P-i: the in-situ wall class (isolated machinery does not reproduce the
  wall) confirmed twice; rule B (seal `lemL` opaque), rule C ([C′] cheap
  codomains), rule E (reshape the interface: `eqSepOp`) each moved a wall;
  the [C′] grid-elasticity cost persists on the termC∈u and atom-mem
  grids.
- New lesson candidates: (a) a named head for a satisfaction/valuation
  expression in an obligation type can clear a wall that the unfolded
  form walls on; (b) where-blocks in this Agda are not mutually
  recursive (forward references report NotInScope; order matters);
  (c) the m-indexed membership characterization type is a wall class of
  its own on this codebase; (d) transport/subst with a membership-over-
  value motive walls in the full grid context even when each clause is
  fast alone.

## 7. Protocol compliance

- Files written: `src/L/Rud/Realize.lagda.md` (deliverable, typechecks)
  and this report. No other repo file touched; no git commits.
- Walls: two (both documented with the formulation trail); each run above
  the 180 s tripwire was killed and the trail recorded.
- Guardrails: every `agda` run used `GHCRTS=-M10g`; one typecheck at a
  time.
- Stop-line: the delivered front is 543 lines (including prose), far
  under the 2,000 code-line stop-line; the batch stops on the wall
  protocol, not the line budget.
