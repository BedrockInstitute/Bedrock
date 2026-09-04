# Review of `table-sat`: NO-GO at the SPLIT scope (the membranes still blow the bound)

**The target, restated:** `table-sat : (γ) (oγ) (hγ) (x) → ⟨ x ∈ˢ γ ⟩ → ⟨ ω ∈ˢ γ ⟩
→ ⟨ sucV (sucV x) ∈ˢ γ ⟩ → ⟨ pr x (Lset x) ∈ˢ carved ⟩` at the `Carved` frame of
`agents/tasks/LJ-1-698/Probe698.agda:107-123`. **The SPLIT scope is still too
tight.** The approximation's own rank now fits (the scope fixed what
`[LJ-1.724]` measured); what fails at this height is the **`DefAt` membrane
inside the Step conjunct**: its code, its satisfaction graph, its index set and
its table must all lie inside `A = Lset γ` once relativized, and the rank chain
through them forces `rank z + 6 < γ` for every `z` the Step's `extAt` clause
reaches. At `γ = sucV (sucV (sucV x))` with `x ≥ ω` all three hypotheses of the
brief hold and the reading is false. This is D-10's check firing again: the
corrected scope recorded by `[LJ-1.724]`'s review priced the truth of the
target from the approximation's rank alone and under-priced the membranes.

## The chain, each link at its in-tree anchor

1. `carveSat` (`src/L/Axioms/Separation.lagda.md:163-168`) equates membership
   of the pair in `carved` with the satisfaction of `φᵣ` at the pair's
   environment; the probe's `to-reading`/`from-reading`
   (`agents/tasks/LJ-1-724-SPLIT/Probe724Split.agda`, `AtPair`) reduce the
   obligation to exactly this reading through the pair's own fiber.
2. `relativize-correct` (`src/FOL/Manipulation/Relativize.lagda.md:142-148`)
   turns the reading into the `A`-bounded reading of the recording, with
   `A = ι (LsetS γ oγ) = (Lset γ , _)` (`src/L/Axioms/Basic.lagda.md:160-161`).
3. Unfolding the bounded reading (`src/FOL/Manipulation/Relativize.lagda.md:47-60`,
   the `relativize` clauses; correctness at `:142-148`),
   the goal needs witnesses `c₀, w, f ∈ᴬ A` with `p =ᴬ pr c₀ w`,
   `f` an `A`-bounded approximation on `c₀`, and `w` the `A`-bounded step at
   `c₀` from `f`. At the SPLIT scope these exist (`c₀ = x`, `w = Lset x`,
   `f` the table; the pair's rank is `x+2` and the table's is `x+3`-ish):
   **the rank of the approximation is no longer the obstruction.**
4. The Step conjunct is `StepAt v b f = extAt v (∃̇ ∃̇ ∃̇ (StepBody b f))`
   (`src/L/Coding/Sequence.lagda.md:119-120`). Its `extAt` clause (i)
   (`src/L/Coding/Model.lagda.md:662-673`) reaches **every** `z ∈ᴬ A` with
   `z ∈ᴬ w`: for each such `z` the body needs `c', w', d ∈ᴬ A` with
   `c' ∈ᴬ c₀`, `pr c' w' ∈ᴬ f`, `DefAt d w'`, `z ∈ᴬ d`.
5. `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
   (`src/L/Coding/Powerset.lagda.md:442-443`): the code and the graph are raw
   `∃̇`, so `relativize` binds each at `con A`
   (`src/FOL/Manipulation/Relativize.lagda.md:55-56`): **code `∈ᴬ A` and graph
   `∈ᴬ A` are demanded.**
6. `DefinesAt x w v = extAt x ((var zero ∈̇ var (suc w)) ∧̇ ∃̇ (envOneAt zero
   (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))))`
   (`src/L/Coding/Powerset.lagda.md:217-220`). The conjunction (not an
   implication) is what pins the subset to the carrier: clause (i) at `z`
   yields `z ∈ᴬ carrier(w')` **and** an `E ∈ᴬ A` with `E ≐ᴬ envOne(z)` and
   `E ∈ᴬ graph` (the decoding is `DefinesAt-out`, read through
   `envOneAt-out`). So **`rank(graph) ≥ rank(envOne z) + 1 = rank z + 3`**
   (`envOne` is the pair of a numeral and the member,
   `src/L/Coding/Powerset.lagda.md:125-139`, `envOne` and its reading).
7. The graph conjunct `satGraphAt` is the twelve-clause frame with its table
   `T` and index set `C` existentially bound
   (`src/L/Coding/Graph.lagda.md:151-164`; the witness record is the
   `GraphWitOn` block at `:140-147`), and the record clause is literally
   `⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T ⟩` at `:145`: the pair
   **`pr(code, graph)` lies
   in `T`**, and `T ∈ᴬ A`. So **`rank(T) ≥ rank z + 6`**.
8. `T ∈ᴬ Lset γ` forces `rank(T) < γ` (`rank-Lset`,
   `src/L/Ordinal/Stages.lagda.md:190-191`: a set in `Lset α` has its rank in
   `α`). Hence **`rank z + 6 < γ` for every `z ∈ᴬ w` the clause reaches**, and
   the clause reaches all of `Lset x ∩ A`, which is all of `Lset x` (stages
   are transitive, and `w ∈ᴬ A`).
9. Members of `Lset x` have ranks cofinal in `x`: `Lset δ ∈ᴬ Lset (sucV δ)`
   (`src/L/Definability.lagda.md:178`, `defSet ⊤̇ ≡ A`) and
   `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`) put `Lset δ` in `Lset x`
   for every `δ` with `δ⁺ ≤ x`, with `rank(Lset δ) = δ` inductively. So the
   reading demands `c + 6 < γ` cofinally in `x`, i.e. **`x + 5 < γ`**.

**The counterexample shape:** any `x ≥ ω`, `γ := sucV (sucV (sucV x))`. Then
`x ∈ˢ γ` holds, `ω ∈ˢ γ` holds, `sucV (sucV x) ∈ˢ γ` holds: every hypothesis
of the brief. Step 9's `z := Lset c` for `c ∈ˢ x` with `c + 6 ≥ γ = x + 3`,
i.e. any `c ≥ x − 4`, is in `Lset x`, and step 8 forbids its witnesses. The
reading is false, and by link 1 the pair is not in `carved`.

## What the scope must be, for the next brief

- **Per-entry scope:** `ω ≤ γ` **and `x + 6 ≤ γ`** (the codes enter at `ω`;
  the membranes' graph, index set and table then fit with two stages of
  slack). At `γ ≥ x + 6` no step of the chain above bites, and the GO case
  is live again; the chain here refutes only its named site (C-42).
- **Frame scope:** re-bound the frame at a limit `λ ≥ x + ω`. The in-tree
  route is `BoundOver` (`src/L/Coding/Bound.lagda.md:33-45`): the closure
  engine over any tower supplying the five facts, at a limit with successor
  closure. It packages exactly "decompose, merge by trichotomy, climb one
  successor", which is what the membrane witnesses need. Whether `Lset`
  instantiates the five facts is measured, not analogized (Boundary): the
  tower facts `T-pr`/`T-trans`/`T-ord` would each need their own probe.
- **What survives:** everything the probe delivered. `dφ` is green;
  `γ ∈ˢ σ` (the frame's stage is past `γ`) reads off the bounding
  certificate's first constant; `pr x (Lset x) ∈ˢ Lset σ` holds **at the
  SPLIT scope** (724's scope could not give this leg); the door
  (`to-reading`/`from-reading`) reduces the obligation to the reading at the
  pair's own fiber. A future GO at the widened scope re-enters through
  `from-reading` and assembles the reading with witnesses that fit.

## Disposition

NO-GO at the SPLIT scope: the target is false at `γ = x+3`, `x ≥ ω`. Nothing
is landed in `src/`. The negative is model-side, as in `[LJ-1.724]`'s review:
the tree-side anchors above are code-verified shapes, but no in-tree term
refutes the obligation, since the negative would have to decide the
non-existence of the reading's witnesses through the opaque `carve`. If the
program re-queues this target, it should queue the widened scope (`x + 6 ≤ γ`,
`ω ≤ γ`) or the limit-bounded frame, not the stated one.
