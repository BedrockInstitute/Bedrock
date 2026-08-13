# R2c report: the concrete step and the telescope discharge (`[L3.31-R2c]`)

## 1. Deliverables and status

| item | state |
|---|---|
| `src/L/Rud/Step.lagda.md` | created; `GHCRTS=-M8g agda src/L/Rud/Step.lagda.md` checks clean |
| code lines | 446 (stop-line 1,500; 29.7%) |
| prose lint (`lint-prose.py --check`) | clean |
| i18n markers (`weave-i18n.py --check`) | clean |
| Agda lint (`lint-agda.py --check`) | clean |
| glossary (`check-glossary.py --check`) | clean (no glossary-term hits) |
| `_build/r2c-report.md` | this file |
| deliverable 1 (step, step-out/step-in) | **green** |
| deliverable 2a (`step-⊆`, `step-∈`) | **green** |
| deliverable 2b (`step-mono`) | **NO-GO wall** (counterexample in section 6) |
| deliverable 2c (`step-trans`) | **partial** (9 of 16 per-op cases green; 5 blocked by an opaque-spec obstacle, 2 by a projection-junk sub-obligation; sections 7-8) |
| deliverable 3 (ConcreteS tower) | **blocked** by the `step-mono` wall (the engine demands the universal property) |
| deliverable 4 (limit-level rud closedness) | **deferred**: blocked by 3, and the brief's "one-step fact" is false under the forced reading (section 9) |
| walls | one NO-GO trail (`step-mono`, section 6); two partial trails (`F2`-`F7` specs, `F13`/`F14`, sections 7-8) |

Nothing else in the checkout was touched: only `src/L/Rud/Step.lagda.md` and
this report were created. The committed `L.Rud.Ops`, `L.Rud.Images`,
`L.Rud.OrdArith`, and `L.Rud.Hierarchy` are imported and untouched;
`L.Rud.Realize` and `L.Rud.Describe` are never imported.

## 2. The concrete step: construction and semantics

The step is the union, over the sixteen operations, of the unions of the
per-operation image sets:

```text
step u = ⋃ { ⋃ { F_i(a,b) : a,b ∈ u ∪ {u} } : i ≤ 15 }
```

Each per-operation image is the `sett` over `⟪ u ∪ {u} ⟫²` of the values
`F_i(a,b)`, exactly as the brief specifies; the step is then the union of
those values. This is the only reading that satisfies the engine's `step-⊆`
and `step-∈` (a member of `u` and `u` itself are members of `F0`'s value
`{x,u}` / `{u}`), and the per-operation transitivity analysis of section 7
confirms it is also the reading where the tuple operations catch the
intermediate objects (the brief's footnote-5 gloss).

**Correction recorded (semantics, not a slip in the brief's intent).** The
brief's deliverable-1 phrasing "`w ∈ step u` iff some `i, a, b ∈ u ∪ {u}`
with `w ≡ F_i(a,b)`" describes membership in the *per-operation image sett*
(a member of the sett is equal to a value). Step membership, forced by the
engine's `step-⊆`/`step-∈` and by the brief's own "the singleton via `F0`"
route, is `w ∈ F_i(a,b)` (membership in the value), i.e. the union of the
values rather than the set of values. The module's `step-out`/`step-in`
export the membership characterization; the report records the discrepancy
so later batches read the right surface. Under the set-of-values reading
(the literal SZ range notation `F_i"(U ∪ {U})²`), `u ∉ step u` and
`x ∈ u` does not imply `x ∈ step u` for arbitrary `u`, so that reading
cannot discharge the committed engine at all.

## 3. Per-item inventory: sizes and timings

The whole file checks in **1.2-1.5 s user / 1.2-1.5 s wall, cold**, under
`GHCRTS=-M8g` (measured on every incremental check; the final clean check
1.4 s). No heap event, no watchdog kill, no 180 s wall. The incremental
debug cycle (probes in `/tmp`, small-file typechecks) is included in
section 10's timings; per-definition timings are not separately measurable
with this Agda's profile output.

| item | code lines | state |
|---|---:|---|
| imports, header (`{ℓ}` + the `A : V ℓ` slot) | 25 | green |
| `u'`, membership lemmas (`u'-in`, `u-self-in`, `u'-cases`, `u'-trans`) | 44 | green |
| `doubleUnion`, `in-⋃⋃`, `⋃⋃→u'` | 15 | green |
| `Op16`, `F15A` + spec, `Fof`, `im` | 62 | green |
| `opaque step` | 5 | green |
| `step-out`, `step-in` (the characterization) | 61 | green |
| `step-⊆`, `step-∈`, `u'-member→step` | 12 | green |
| `pr-member`, `singl-member`, `pair→step` | 17 | green |
| `prL/prR-in-doubleUnion` | 17 | green |
| per-op transitivity: `trans-F0` | 12 | green |
| per-op transitivity: `trans-F1` | 7 | green |
| per-op transitivity: `trans-F5` | 11 | green |
| per-op transitivity: `trans-F8` | 23 | green |
| per-op transitivity: `trans-F9` | 18 | green |
| per-op transitivity: `trans-F10` | 16 | green |
| per-op transitivity: `trans-F11` | 28 | green |
| per-op transitivity: `trans-F12` | 28 | green |
| per-op transitivity: `trans-F15` | 5 | green |
| prose blocks | 22 | lint-clean |

## 4. The op-combination table for `step-⊆` and `step-∈`

Both growth properties use exactly one operation, the pairing image `F0`,
with the classical singleton route the brief predicts:

| fact | witness | arguments in `u ∪ {u}` | why it lands |
|---|---|---|---|
| `x ∈ u → x ∈ step u` (`step-⊆`) | `x ∈ F0 x u = {x,u}` | `x ∈ u` via `u'-in`; `u ∈ {u}` via `u-self-in` | `F0 x u` is a value over the square, so `x ∈ F0 x u ⊆ step u` |
| `u ∈ step u` (`step-∈`) | `u ∈ F0 u u = {u}` | `u ∈ u'` twice via `u-self-in` | `F0 u u` is a value over the square, so `u ∈ F0 u u ⊆ step u` |

No other operation is needed; `F0` is the sole producer. The `u'-member→step`
bridge then converts "member of `u ∪ {u}`" into "member of the step" by the
same two facts plus the `u'-cases` split (`a ∈ u ∪ {u}` decides between
`a ∈ u` and `a ≡ u`, the latter via `∈-irrefl`).

## 5. The shared transitivity frames

Two frames recur across the per-op cases. **The pair frame** (`pair→step`):
a member of `pr a b` is `{a}` or `{a,b}` (`pr-member`), and both are members
of the pair images `F9 a a` / `F9 a b`, whose arguments lie in the argument
set; so any pair of argument-set members lands in the step. **The argument
frame** (`u'-trans` + `u'-member→step`): members of members of `u ∪ {u}`
are again in it (one `u'-cases` split per level), and members of the argument
set land in the step. Every case reduces to: decompose `x ∈ F_i(a,b)` by the
specification, chase the resulting memberships to `u ∪ {u}`, and reassemble
via `pair→step` or the argument frame. The intermediate objects the brief
attributes to footnote 5 are exactly what `F9` catches: `{a}` and `{a,b}`
for pair-shaped values, `left b` and `pr a (right b)` for `F11`/`F12`
(caught by `F13`/`F14`'s values), and the left/right components of pairs in
the `F3`/`F4`/`F8`/`F10` shapes (chased through `⋃⋃`).

## 6. `step-mono`: NO-GO trail (the telescope cannot be discharged as committed)

**Obligation.** The committed engine (R2b) demands, universally:
`step-mono : {u v} → (u ⊆ v pointwise) → step u ⊆ step v`.

**Three failed formulations.** (a) Reading A (union of values, the reading
forced by `step-⊆`/`step-∈`): the `x = {u}` witness is in `step u` (it is
`F9(u,u)`'s member), but for `u ⊆ v` the set `{u}` is not in `step v` in
general. (b) Reading B (set of values): `step-⊆`/`step-∈` fail for arbitrary
`u`, so the engine is unsatisfiable anyway. (c) Reading C (`u ∪ {u}`
adjoined to the images): `step-mono` still fails at `x = {u}`. Augmenting
the step with the power set or the power set of the double union fixes
`x = {u}` but leaves the `F8`-slice and `F9`-singleton cases of the
`c = u` argument branch open, and the step is no longer the sixteen images.

**The counterexample (reading A, the only viable reading).** Take
`u = {∅, {∅}}`, `v = {∅, {∅}, {{∅}}}`, `x = {u} = {{∅,{∅}}}`.
- `u ⊆ v` pointwise: `∅ ∈ v`, `{∅} ∈ v` ✓.
- `x ∈ step u`: `x = {u}` is a member of `F9(u,u) = {{u}}`, and `F9(u,u)`
  is a value over `u ∪ {u}` ✓.
- `x ∉ step v`: `v' = {∅, {∅}, {{∅}}, v}`; enumerating all sixteen
  operations at all argument pairs from `v'` (F0: `x` equals no argument;
  F1/F15: `x ∈ c` fails for all `c ∈ v'`; F2/F3/F4/F7/F9/F11/F12: values
  are pair/triple-shaped sets, `x` is a one-element non-pair;
  F5: `x ∈ e ∈ c` fails; F6: `dom(c)` is `∅` or `{∅}` since the only pair
  in `v'` is `pr ∅ ∅ = {{∅}}`; F8/F10: slices of `v'`-members are `∅` or
  `{∅}`; F13/F14: `left d = ∅` and `pr (right d) c` is pair-shaped for all
  `d ∈ v'`) — no value contains `x` ✓.

So `u ⊆ v`, `x ∈ step u`, `x ∉ step v`: the universal `step-mono` is false
for the sixteen-image step under every candidate reading. The engine's
telescope is therefore **unsatisfiable as committed**: no sixteen-image step
can discharge all four universal properties. This is the batch's headline
finding; the orchestrator's "unions of images are monotone" expectation
holds only for argument sets that satisfy `u ∈ v ∪ {v}` (level pairs do, via
`Sset-in` + `step-∈`; arbitrary sets do not). The engine's only use of
`step-mono` is at level pairs (`Sset-suc`), so the abstract engine itself is
sound; the universal parameter is what no concrete step can satisfy.

## 7. `step-trans`: the per-op case sizes and the opaque-spec obstacle

The nine green cases and their sizes are in section 3. What each case does:

| op | shape of the value member | route |
|---|---|---|
| `F0` | `x ≡ a` or `b` | argument frame |
| `F1` | `x ∈ a` | argument frame |
| `F5` | `x ∈ v ∈ a` | argument frame (three `u'-trans` steps) |
| `F8` | `x ≡ F10 a z`, `y ∈ x` | `F10-spec` gives `pr z y ∈ a`; chase `y ∈ {z,y} ∈ pr z y` to the argument set |
| `F9` | `x ≡ {a}` or `{a,b}` | singleton/pair reading into the argument set |
| `F10` | `pr b x ∈ a` | same `{b,x} ∈ pr b x` chase |
| `F11` | `x ≡ {left b}` or `{left b, pr a (right b)}` | `left b` caught by `F13(b,b)`; `pr a (right b)` caught by `F14(a,b)` |
| `F12` | mirror of `F11` | `pr (right b) a` caught by `F13(a,b)` |
| `F15` | `x ∈ a` | argument frame |

**Blocked cases `F2`, `F3`, `F4`, `F6`, `F7` (opaque-spec obstacle).** The
operations chapter (R1a) seals these five operations `opaque`, and their
specification right-hand sides (`F2-RHS`...`F7-RHS`) sit inside the same
opaque blocks. Outside those blocks, `fst (F2-RHS a b x)` is an
opaque-stuck hProp carrier that is not definitionally the truncation over
the plain Sigma, so it cannot be eliminated; the same holds for the large
membership `x ∈ F2 a b` (the HIT's `∈` is defined by cases on the set, which
is opaque). Verified by `/tmp` probes: a locally redefined copy of the RHS
reduces (`refl`), the imported opaque one does not. The green cases all
avoid the obstacle: `F0`/`F9` specs return inline `⊔`-carriers, `F1` an
inline `⊓`-carrier, `F5` a non-opaque RHS, `F8`/`F10` plain path-based specs
in the images module, `F11`-`F14` plain definitions. **Lesson candidate:**
sealing an operation's spec inside the same `opaque` block as the operation
makes the fwd direction unusable from consumers; the spec should either be
outside the block or its RHS should be an inline expression (or the opaque
block should end before the RHS names).

**Blocked cases `F13`, `F14` (projection-junk sub-obligation).** The
`F13`/`F14` values are `{left b, pr (right b) a}` / `{left b, pr a (right b)}`,
so their member `x ≡ pr (right b) a` (resp. `pr a (right b)`) decomposes into
`y ≡ {right b}` or `{right b, a}`. The pair frame catches these only with
arguments `(right b, right b)` / `(right b, a)`, which requires
`right b ∈ u ∪ {u}`. For `b` a Kuratowski pair `pr p q`, transitivity gives
`right b = q ∈ u`; for `b = u` and for non-pair `b ∈ u`, `right b` is the
junk `⋃(rightSlice b)` and membership in `u ∪ {u}` requires classifying `b`
as a pair or not (`∃ p q. b ≡ pr p q`, a non-decidable disjunction, so LEM
or a junk analysis of `rightSlice`). That classification is a genuine open
sub-obligation; the brief's expectation that the tuple operations "catch"
these intermediates is confirmed for `F11`/`F12` (which only ever need the
values `F13(b,b)`/`F14(a,b)` as wholes) but not yet for `F13`/`F14`
themselves.

## 8. What discharged cleanly vs what fought

**Clean:** the step construction; the `step-out`/`step-in` characterization
(sealed `opaque` per P-c); `step-⊆`; `step-∈`; the argument-set machinery
(`u'-cases` with `∈-irrefl`); the pair frame; the double-union chases; nine
transitivity cases. All were first-try or one-fix (the recurring fix class:
small-vs-large membership direction through `∈∈ₛ`, and `sym` direction in
`subst`).

**Fought:** `step-mono` (NO-GO, section 6); the five opaque-spec cases
(section 7); the `F13`/`F14` projection-junk cases (section 7); the
`Lift (Fin 16)` index (replaced by a dedicated `Op16` type in `Type ℓ`,
because the `Lift` level could not be inferred); and the F15 slot
(`L.Rud.Images` keeps `F15Of` after its final `private` block, so it is not
importable — the module defines `F15A` locally with the same separation
spec, and the report records the obstacle).

## 9. Deliverable 4 (limit-level rud closedness): deferred

`F_i(a,b) ∈ Jset λ` for `a,b ∈ Jset λ` at a limit `λ` is deferred, on two
grounds. (1) It is blocked by the `step-mono` wall: without `step-mono` the
engine cannot be instantiated, so `Jset` is not available. (2) Under the
forced reading A, the brief's "one-step fact" (`F_i(a,b) ∈ step u` for
`a,b ∈ u ∪ {u}`) is false in general: for `i = F1`, `a\b` with three or more
elements is not a member of any value over `v ∪ {v}` (a member of a value
over the square is an element of `a`, a component of a pair/triple, a slice,
or one of the arguments; a three-element difference is none of these in
general). The classical "J-levels are rud closed" fact belongs to the
set-of-values reading, which the engine cannot use; under reading A the
correct limit-absorption route is a two-step climb through `S_{δ+2}` with
`δ = max` of the containing stages, and even that needs the per-op
value-in-step facts that fail for `F1`. Recorded for the orchestrator.

## 10. Timings

| activity | time |
|---|---|
| reading the committed modules, digest, reports, LESSONS | ~40 min |
| the semantics analysis (reading A vs B vs C, the three failed `step-mono` formulations, the counterexample, the per-op analysis incl. the `F13`/`F14` junk question) | ~2.5 h (the mathematical heart; no typecheck time) |
| probing the library surface (`∈∈ₛ` directions, hProp carriers, opaque behaviour, `Lift`) | ~1 h (~20 probes, each <1 s) |
| writing + typechecking the module (19 incremental checks) | ~1.5 h (each check 1.2-1.5 s, no wall, no heap event) |
| report | ~40 min |

## 11. Surprises and lesson candidates

1. **The committed telescope is unsatisfiable by the sixteen-image step.**
   `step-mono` (universal) is false with a two-element counterexample
   (section 6). The engine's own usage is level-only, so the fix belongs to
   the telescope's shape, not the proofs: either state `step-mono` for level
   pairs, or accept a step with a subset-clause (power-set-like) that is no
   longer the sixteen images. Lesson candidate: universal monotonicity of a
   step that contains `u` via `F0(u,u)` forces `u ∈ v ∪ {v}` from `u ⊆ v`,
   which is false; the classical proofs only ever need level-wise
   monotonicity.
2. **Opaque specs are not consumable.** Sealing `F2`-`F7` and their RHS
   names `opaque` in the same block makes the specs' fwd directions
   unusable outside the block (the carrier does not reduce; verified by
   probes). This is a P-c over-application: the operation is sealed, but the
   spec's *decomposition* is exactly what consumers need. Lesson candidate:
   the RHS names of a sealed operation must live outside the opaque block,
   or the spec must be stated with inline carriers.
3. **`F15Of` is private.** The images module's last `private` block runs to
   the end of the module, so `F15Of` is not importable even though the
   recap announces it as the consumers' slot. Local redefinition cost 5
   lines; recorded so the images module can be asked to end its private
   region before `F15Of`.
4. **`Lift (Fin 16)` level inference fails.** `a ⊔ b = ℓ` does not pin `b`;
   a dedicated `data Op16 : Type ℓ` with sixteen constructors is cleaner and
   removes the level drama. Lesson candidate: for a finite index over an
   arbitrary `ℓ`, define the index type in `Type ℓ`, don't lift a `Type₀`
   one.
5. **`hProp` carriers and `PT.rec`.** `⟨ F-RHS a b x ⟩` (a defined hProp)
   is not always definitionally the truncation it denotes; `PT.rec` then
   rejects it. Working pattern: eliminate the *inline* carrier (the fwd
   output of a plain spec) or the plain Sigma, never a named hProp whose
   body is out of scope.
6. **The brief's "≡" characterization is the sett membership, not the step
   membership.** Step membership is membership in a value; the set-of-values
   reading fails `step-⊆`/`step-∈` outright. The report records the
   correction; the module exports the correct surface.
7. **`F11`/`F12` catch their intermediates with no junk analysis** (`left b`
   via `F13(b,b)`, `pr a (right b)` via `F14(a,b)`, whole values), while
   `F13`/`F14`'s own cases need `right b ∈ u ∪ {u}` and hence the pair
   classification. The footnote-5 gloss is confirmed case-by-case, with the
   residual at exactly the two operations that *produce* `right`-shaped
   objects.

## 12. What the module exports

`step` (opaque), `step-out`/`step-in` (the characterization), `step-⊆`,
`step-∈`, `u'-member→step`, the shared frames, and the nine green
per-operation transitivity lemmas, all parameterized by the `A` slot of the
relativized basis (the plain trunk instantiates `A` at the empty set at
assembly). The tower instantiation is not present because the telescope
cannot be discharged; the trails above are the inputs the orchestrator needs
to reshape the engine's `step-mono` (or the step's definition) and to relax
the opaque sealing of the five RHS names.

# Part 2 record (telescope reshape bf0e3d9; commits 0322860 + the R2c part-2
# appendix to Ops)

## P1. Status

| item | state |
|---|---|
| `step-mono∈` (deliverable 1) | **green** (section P2) |
| F2-F7 read lemmas appended to `src/L/Rud/Ops.lagda.md` | **green** (section P3; `GHCRTS=-M8g agda src/L/Rud/Ops.lagda.md` clean, linters clean) |
| transitivity, the granted five (`F2`, `F3`, `F4`, `F6`, `F7`) | `F2`, `F6`, `F7` **green**; `F3`, `F4` **NO-GO** (mathematical obstruction, section P5) |
| transitivity `F13`/`F14` (LEM classification) | pair branch **green** (section P6); non-pair branch **walled** (private Images junk) |
| total clean per-op transitivity cases | 12 of 16 (F0, F1, F2, F5, F6, F7, F8, F9, F10, F11, F12, F15) |
| ConcreteS (deliverable 3) | **blocked**: `step-trans` is false for this operator shape (F3/F4), so the engine cannot be instantiated |
| rud-closure of limit levels (deliverable 4) | **blocked** by 3; the brief's "one-step fact" additionally fails under the forced reading (part-1 section 9 stands) |
| `src/L/Rud/Step.lagda.md` | 548 code lines, typechecks clean, linters clean (cold recompile ~26 s once after the interface change, warm 0.9 s) |

Nothing else was touched: `Step.lagda.md`, the Ops appendix, and this report
only. The committed `Hierarchy`, `Images`, `OrdArith` are imported, not
modified (the Ops appendix is the only granted edit to a committed file).

## P2. `step-mono∈` discharge shape

The reshaped obligation is `u ⊆ v → u ∈ v → step u ⊆ step v`. The key
observation from the part-1 report is now a three-line proof: with `u ∈ v`,
every `c ∈ u ∪ {u}` lands in `v ∪ {v}` (`c ∈ u` via the subset, `c ≡ u`
via the membership hypothesis), so every witness of `x ∈ step u` from the
step-out (an index `i` and arguments `a, b ∈ u ∪ {u}` with `x ∈ F_i(a,b)`)
re-enters through the step-in with the same index and the transported
arguments. No per-operation work is needed; `step-mono∈` is 17 code lines
and closes first-try. This confirms the part-1 report's note that the
obligation was satisfiable once membership was conditioned in.

## P3. The Ops appendix inventory

Five read lemmas were appended to `src/L/Rud/Ops.lagda.md`, each in its own
`opaque unfolding F{i}` block: the operation's body unfolds inside the
block, the decomposition is proved exactly as the original fwd direction,
and the lemma itself stays opaque so only its explicit truncated type is
exported. Nothing existing was changed, renamed, or unsealed; the only
edit to an existing statement is the additive `∥_∥₁; squash₁` on the
`open PT using` line, required to state the truncated types.

| export | size | returns (for `x ∈ F_i a b`) |
|---|---|---|
| `F2-read` | 20 | `∃ p q. p ∈ a ∧ q ∈ b ∧ x ≡ₕ pr p q` |
| `F3-read` | 33 | `∃ u z v. z ∈ a ∧ pr u v ∈ b ∧ x ≡ₕ pr u (pr z v)` |
| `F4-read` | 33 | `∃ u v z. z ∈ a ∧ pr u v ∈ b ∧ x ≡ₕ pr u (pr v z)` |
| `F6-read` | 24 | `∃ u v. pr u v ∈ a ∧ x ≡ₕ u` |
| `F7-read` | 25 | `∃ u v. u ∈ a ∧ v ∈ a ∧ u ∈ v ∧ x ≡ₕ pr u v` |

All five typecheck clean in the committed file. The `F3-read`/`F4-read` are
correct decompositions and stay as exports even though their transitivity
cases are mathematically blocked (section P5).

## P4. The new transitivity cases: per-case sizes

| lemma | code lines | route |
|---|---:|---|
| `trans-F2` | 12 | read gives `x ≡ pr p q`, `p ∈ a`, `q ∈ b`; pair frame (`{p}`, `{p,q}` via `F9`) |
| `trans-F6` | 12 | read gives `x ≡ p`, `pr p q ∈ a`; `p ∈ u ∪ {u}` via the double-union chase; argument frame |
| `trans-F7` | 13 | read gives `x ≡ pr p q`, `p,q ∈ a`; pair frame |
| `isPair` + `left-in-u'-pair` + `right-in-u'-pair` | 6 + 19 + 19 | the F13/F14 pair-case machinery (section P6) |
| `step-mono∈` | 17 | section P2 |

## P5. `F3` and `F4`: NO-GO (a mathematical obstruction, not a wall)

With the read lemmas in hand, the `F3`/`F4` transitivity cases were
attempted and fail for a mathematical reason, not a library-access one. A
member `x` of the `F3` value is a right-nested triple `pr u (pr z v)` with
`z ∈ a` and `pr u v ∈ b`. A member `y ∈ x` of the triple is `{u}` or
`{u, pr z v}` (the two members of the Kuratowski pair). The first is caught
by `F9(u,u)`. The second, `{u, pr z v}`, is the unordered pair of `u` and
`pr z v`, and the pair frame catches it only at arguments `(u, pr z v)`,
which requires `pr z v ∈ u ∪ {u}`. But `pr z v` is a pair of a member of
`a` and a component of `b`; it is outside `u ∪ {u}` in general, and
checking all sixteen operations at all argument pairs from `u ∪ {u}` shows
`{u, pr z v}` is not a member of any value there either (F0/F9 need one of
the components in the argument set; F13/F14 need `left d = u` with
`right d = v`, i.e. `d = pr u v ∉ u ∪ {u}`; F2/F3/F4/F7 need `u` to be a
singleton or `v = z`; F5/F6/F8/F10/F1/F15 fail on shape). So under the
forced reading A, `step-trans` is **false** for the sixteen-image step, at
`F3` and `F4`: the levels `S_{α+1}` are not transitive for this operator.
This is a second, independent obstruction to the telescope (the first was
`step-mono`, fixed by the membership-conditioned reshape): `step-mono∈`
discharges, but `step-trans` cannot. The report records it as the headline
part-2 finding, with the concrete shape `{u, pr z v}` (and its sub-object
`pr z v`) as the witness of non-membership. `F3-read`/`F4-read` remain
correct; the transitivity facts themselves are false.

## P6. `F13` and `F14`: the pair classification, and the non-pair wall

The granted LEM classification is implemented and green on the pair branch:
`isPair b` is the single-truncation hProp "`b ≡ pr p q` for some `p q`",
`lem (isPair b)` splits, and `left-in-u'-pair` / `right-in-u'-pair` show
`left b ∈ u ∪ {u}` / `right b ∈ u ∪ {u}` when `b` is a pair: the
projections are the components (`left-spec`/`right-spec`), and each
component is in `u` by transitivity through `b`'s own members
(`p ∈ {p} ∈ b`, `q ∈ {p,q} ∈ b`). LEM is spent exactly at the
classification, as granted.

The non-pair branch is walled by library access, not by mathematics: for a
non-pair `b`, `left b = ⋃(⋂ b)` and `right b = ⋃(rightSlice b)` are the
empty set (their indices are empty because a witness would exhibit `b ≡ pr
left b X`, contradicting non-pairness), and `∅ ∈ u ∪ {u}` for transitive
`u`. But `⋂` and `rightSlice`/`sndExtract` sit in the images chapter's
`private` blocks (lines 77-107 and 231-380 of `Images.lagda.md`), and
probes confirm their bodies neither reduce nor are nameable from outside,
so the junk facts are not provable in `Step` or in an Ops appendix. The
grants cover Ops only; closing `F13`/`F14` requires either one public
lemma in Images (`left-nonpair-empty`, `right-nonpair-empty` under
`¬ isPair b`) or un-privating `⋂`/`rightSlice`. Recorded for the
orchestrator; the pair-branch machinery is in the module.

## P7. Deliverables 3 and 4: blocked, with the precise chain

ConcreteS needs the engine's five obligations, of which `step-trans`
remains. Since `step-trans` is false at `F3`/`F4` under the forced reading
(section P5) and `F13`/`F14`'s non-pair branches need Images-private junk
(section P6), no total `step-trans` term exists in this batch, so the
instantiation cannot be written and the tower is not exported. Deliverable
4 (limit-level rud closure) is blocked by the same chain; independently,
the brief's "one-step fact" (`F_i(a,b) ∈ step u` for `a,b ∈ u ∪ {u}`)
remains false under the forced reading for `F1`/`F5`/`F9` values (part-1
section 9), so the stated route would not work even with the tower. The
report's recommendation: the engine's `step-trans` (or the step's shape)
needs a third design pass, informed by the `{u, pr z v}` obstruction and
the reading-B failure of the same case, before the tower can be
instantiated.

## P8. Timings

| activity | time |
|---|---|
| re-reading the reshaped Hierarchy, the committed Step, Ops | ~20 min |
| probing the read-lemma pattern, the private-reduction question, the `right`-interior elimination (8 probes) | ~1 h |
| the Ops appendix (5 read lemmas) | ~30 min |
| the Step updates (step-mono∈, F2/F6/F7, pair machinery) | ~1 h (cold recompile 26 s once after the interface change; warm checks 0.9 s) |
| the F3/F4 and F13/F14 analysis (the obstruction, the junk facts, the reading-B check) | ~2 h (no typecheck time) |

## P9. Surprises and lesson candidates

1. **`step-trans` is false under the forced reading, at `F3`/`F4`.**
   The intermediate `{u, pr z v}` of a triple member is not a member of any
   value over the argument square. The part-1 report's "clean" claim for
   the F3/F4-adjacent cases was an unverified analysis error (it assumed
   `pr z v ∈ u ∪ {u}` from `pr u v ∈ b`); with the read lemmas the cases
   were actually attempted and fail. Lesson candidate: the S-level
   transitivity of SZ requires a step whose one-step images also admit the
   triple-members' intermediate pairs, which the sixteen-image union over
   `(u ∪ {u})²` does not provide; the same obstruction appears under the
   set-of-values reading (the triple `pr u (pr z v)` is not a value over
   the square either), so the SZ semantics is a third shape the route has
   not yet pinned.
2. **The `opaque unfolding` pattern is the correct read-lemma vehicle.**
   An opaque operation's body can be unfolded inside a new `opaque
   unfolding F{i}` block, the decomposition proved there, and only the
   explicit truncated type exported; consumers eliminate it normally. This
   is the P-c-compatible way to give consumers decompositions of sealed
   operations, and it should be the house pattern for any future sealed
   spec.
3. **Private definitions neither reduce nor name from outside.** `⋂` and
   `rightSlice` in Images are private, and probes confirm their bodies do
   not unfold for importing modules (the large membership of `right b`
   cannot be eliminated; `UnequalLevel`). The `F13`/`F14` junk facts are
   provable only inside Images. Lesson candidate: a private helper that a
   consumer's proof needs must be re-exported as a public lemma; privacy is
   a name-and-reduction wall, not just a hygiene marker.
4. **Nested `∃[p]∃[q]` carriers are double-truncated.** The carrier of
   `∃[ p ] ∃[ q ] P` is `∥ Σ p ∥ Σ q ⟨ P ⟩ ∥₁ ∥₁`; a single explicit
   `∥ Σ p Σ q ⟨ P ⟩ ∥₁` hProp is easier to eliminate and just as good for
   LEM.
5. **The membership-conditioned reshape works exactly as promised.**
   `step-mono∈` closes in 17 lines with no per-operation work, confirming
   the part-1 counterexample's diagnosis (the missing hypothesis was
   membership of `u` in `v`, not a deeper defect). The residual blocker is
   purely `step-trans`.
6. **`subst` direction discipline again.** Both `sym`-direction errors in
   the pair machinery (`left≡p`, `right≡q`) were the same class as part
   1's; the report's fix class is stable.

## P10. What the module now exports (part 2 additions)

`step-mono∈`; `trans-F2`, `trans-F6`, `trans-F7`; `isPair`,
`left-in-u'-pair`, `right-in-u'-pair` (the F13/F14 pair branch); and the
Ops appendix's `F2-read`, `F3-read`, `F4-read`, `F6-read`, `F7-read`.
`step-trans` (total) and `ConcreteS` are absent because `step-trans` is
false for this operator shape; the report's sections P5-P7 are the inputs
for the next telescope decision.

# Part 3 record (the cumulative step-shape ruling; part-2 state committed as 7c69beb)

## Q1. Status

| item | state |
|---|---|
| step rewritten to the ruled cumulative form `u ∪ {u} ∪ (sixteen image sets)` | **green** (section Q2) |
| step-in / step-out adjusted to the three-armed shape (member of `u`, `u` itself, image value), sealed `opaque`, the only surface (P-c) | **green** (section Q2) |
| step-⊆ / step-∈ as the definitional floor | **green** (section Q3) |
| step-mono∈ re-checked against the cumulative form | **green** (section Q4) |
| transitivity, all sixteen against the cumulative form | **12 of 16 green**: F0-F10, F15, F3, F4 (sections Q5-Q6) |
| transitivity F11-F14 | pair-branch machinery **green** (`isPair`, `left-in-u'-pair`, `right-in-u'-pair`); the total lemmas are absent because the non-pair branch is **walled** on a genuine missing Images read (section Q7) |
| ConcreteS (the Hierarchy engine instantiation, five obligations) | **blocked**: `step-trans` is not total (F11-F14 non-pair), so the engine cannot be instantiated (section Q8) |
| rud-closure of limit levels | **deferred**, same chain (section Q9) |
| `src/L/Rud/Step.lagda.md` | 558 code lines (stop-line 1,500; 37%), `GHCRTS=-M8g agda src/L/Rud/Step.lagda.md` checks clean; prose/i18n/agda/glossary linters clean |
| walls | one heap wall trail (StepArm carrying `u' u` memberships, section Q10); no 180 s wall, no watchdog kill |

Nothing else in the checkout was touched: only `Step.lagda.md` and this report.
The committed `Ops`, `Images`, `OrdArith`, `Hierarchy` are imported and
untouched; `Realize` and `Describe` are never imported; `Everything` is
never compiled; no git commit.

## Q2. The cumulative step and the three-armed surface

The step is now the ruled cumulative form:

```text
step u = u ∪ {u} ∪ { F_i(a,b) : i ≤ 15, a, b ∈ u ∪ {u} }
```

implemented as `step u = ⋃ ⁅ u' u , values u ⁆` with `u' u = ⋃ ⁅ u , ⁅ u ⁆s ⁆`
and `values u` the union of the sixteen per-operation image setts over
`⟪ u' u ⟫²`. The `Fof` family is sealed in one `opaque` block and the
surface is the three-armed `StepArm` type (`arm-member`, `arm-self`,
`arm-image`) with `step-out` (characterization out) and the three `step-in`
directions (`step-in`, `step-in-self`, `step-in-img`), all inside
`opaque unfolding step` blocks, so consumers read only the characterization.
Two extra `opaque unfolding Fof` exports (`Fof-f0`, `Fof-f9`, `Fof-f10`,
`Fof-f11`, `Fof-f12`) give the per-constructor equalities `Fof fi a b ≡
Fi a b` that the image arm needs; the seal itself is what keeps the
sixteen-way definition out of downstream conversion (see Q10 for why the
seal exists).

## Q3. The op-combination table for step-⊆ and step-∈ (now the floor)

Under the cumulative form both growth properties are the definitional
floor, not image chases:

| fact | route | why it lands |
|---|---|---|
| `x ∈ u → x ∈ step u` (`step-⊆ = step-in`) | member arm of `u' u` | `step u = ⋃ {u' u, values u}` and `u' u = u ∪ {u}` ∋ `x` via `u'-in` |
| `u ∈ step u` (`step-∈ = step-in-self`) | self arm of `u' u` | `u ∈ ⁅ u ⁆s ⊆ u' u` via `u-self-in` |
| `a, b ∈ u ∪ {u} → F_i(a,b) ∈ step u` (`step-in-img`) | image arm | `Fof i a b` is a value over the square, so it sits in `im i u ⊆ values u` |

No operation is consumed for the floor; the sixteen images are only needed
for the third arm. `u'-member→step` bridges `u' u`-membership to step
membership by the `u'-cases` split (`a ∈ u` vs `a ≡ u`, the latter via
`∈-irrefl`).

## Q4. step-mono∈ against the cumulative form

The obligation `u ⊆ v → u ∈ v → step u ⊆ step v` transfers from part 2
unchanged: the three arms are closed by `step-out`, and each of `a ∈ u`
and `a ≡ u` for the image arguments re-enters `v ∪ {v}` through the subset
or the membership hypothesis, so every image value over `u ∪ {u}` is an
image value over `v ∪ {v}`. 22 code lines, closed without per-operation
work, first try after the shape change.

## Q5. The per-case table over the cumulative form

| case | code lines | route |
|---|---:|---|
| `trans-F0` | 11 | `y ≡ a` or `b`; argument frame |
| `trans-F1` | 7 | `y ∈ a`; argument frame |
| `trans-F2` | 12 | read gives `y ≡ pr p q`, `p ∈ a`, `q ∈ b`; pair frame |
| `trans-F3` | 16 | read gives `y ≡ pr u (pr z v)`; `y ≡ F11 z (pr u v)` at the existing pair (orchestrator hint 1); image arm |
| `trans-F4` | 16 | mirror via `F12 z (pr u v)`; image arm |
| `trans-F5` | 10 | `y ∈ v ∈ a`; argument frame (two `u'-trans`) |
| `trans-F6` | 12 | read gives `y ≡ p`, `pr p q ∈ a`; double-union chase; argument frame |
| `trans-F7` | 13 | read gives `y ≡ pr p q`, `p, q ∈ a`; pair frame |
| `trans-F8` | 12 | `y ≡ F10 a z` with `z ∈ b`; image arm at `(a, z)` |
| `trans-F9` | 6 | `y ∈ pr a b`; pair frame (`pair→step`) |
| `trans-F10` | 17 | `pr b y ∈ a`; chase `y ∈ {b,y} ∈ pr b y`; argument frame |
| `trans-F15` | 6 | `y ∈ a`; argument frame |
| `isPair`, `left-in-u'-pair`, `right-in-u'-pair` | 45 | the F11-F14 pair-branch machinery (components of a pair land in `u ∪ {u}` through the pair's own members) |

The F3/F4 discharge is exactly the orchestrator's hint: a member of the F3
value is the triple `pr u (pr z v)`, which is the `F11`-value at the
existing arguments `(z, pr u v)`, where `z ∈ a ⊆ u' u` and `pr u v ∈ b ⊆
u' u` by transitivity; the F4 mirror uses `F12`. No left/right projections
are opened anywhere in these two cases. The `Fof-f*` equalities supply the
`Fof fi a b ≡ Fi a b` rewrites that the sealed index family needs.

## Q6. What discharged cleanly vs what fought

**Clean:** the cumulative step; the three-armed surface (once the
constructor-shape fix of Q10 landed); `step-⊆`/`step-∈`/`u'-member→step`;
`step-mono∈`; the pair frame (`pair→step` with the new `singl≡pair`
lemma); the double-union chases; twelve trans cases, including F3/F4
first-try after the ruling.

**Fought:** (1) the `Fof` seal: making the sixteen-way definition opaque
is what keeps conversion bounded (Q10), but it broke definitional equality
`Fof fi a b ≡ Fi a b` at every image arm; the `opaque unfolding Fof`
equality lemmas cure all of them. (2) The small-vs-large membership
directions through `∈∈ₛ` and the `subst` direction (`sym x≡` vs `x≡`) in
the per-op inputs; both are the same fix class as parts 1-2 (the report's
recurring lesson). (3) The F11-F14 non-pair branches (Q7).

## Q7. F11-F14: pair branch green, non-pair branch walled on a genuine missing read

The F11-F14 transitivity cases split on `lem (isPair b)` exactly as the
part-2 grant allows. On the pair branch `b ≡ pr p q`, `left-in-u'-pair`
and `right-in-u'-pair` show `left b = p ∈ u ∪ {u}` and `right b = q ∈
u ∪ {u}` through the pair's own members, and the case analysis shows all
four would close: `trans-F11`/`trans-F12` catch
`{left b}` by the singleton image and the
pair constituent `{left b, pr a (right b)}` / `{left b, pr (right b) a}`
as the `F14`/`F13` values at `(a, b)`; `trans-F13`/`trans-F14` catch
`left b` by the member arm and `pr (right b) a` / `pr a (right b)` by the
pair frame at `(right b, a)` / `(a, right b)`.

The non-pair branch is walled by library access, not by mathematics. For a
non-pair `b`, `left b = ⋃ (⋂ b)` and `right b = ⋃ (rightSlice b)` are
junk values (classically `left b` is empty or a single member of `u`, and
`right b = ∅` because any rightSlice witness would exhibit `b ≡ pr (left b)
X`); the floor arms would then absorb them (`∅` or a member of `u` land in
`u ∪ {u}`). Probes in this batch confirm the part-2 wall precisely: the
membership `x ∈ₛ right b` cannot be eliminated from outside because the
union's index type and map are built from `rightSlice` and `sndExtract`,
both private to the images chapter (lines 178-229 of `Images.lagda.md`),
and the contradiction witness `q` in `b ≡ pr (left b) q` is exactly the
unnameable `sndExtract` value; no reformulation of the non-pair hypothesis
(including the constructively equivalent pointwise `(p q : V) → b ≢ₕ
pr p q`) can name it. The left junk facts are in principle provable from
outside through the public `⋂` (the "at most one distinct member of
`⋂ b`" analysis plus `∅ ∈ u ∪ {u}` for transitive `u`), but they would not
close F13/F14, which also need `right`.

**Exact missing reads from Images (do not touch Images; another agent owns
it):** for the four cases to become total, the images chapter should export
one of (a) `right-nonpair-empty : ¬ isPair b → right b ≡ ∅` (with the
`∅ ∈ u ∪ {u}` floor fact for transitive `u`), or (b) `right-nonpair-mem :
Trans u → b ∈ˢ u' u → ¬ isPair b → right b ∈ˢ u' u`, or simply make
`rightSlice` and `sndExtract` public; dually `left-nonpair-...` for the
left projection (or the `⋂`-at-most-one analysis exported). With those,
all sixteen cases close and `step-trans` becomes total.

## Q8. ConcreteS: blocked on step-trans

The Hierarchy engine's five obligations are `step-⊆`, `step-∈`,
`step-mono∈`, `step-trans`, plus `lem`. The first three are green (Q3-Q4).
`step-trans` needs all sixteen per-op cases; the F11-F14 non-pair branches
are walled (Q7), so no total `step-trans` term exists in this batch and
`module ConcreteS = L.Rud.Hierarchy ...` cannot be written. The engine's
only use of `step-trans` is `level-trans (step-level ...)`, so the tower
math is unaffected; the missing reads of Q7 are the entire remaining debt.

## Q9. Deliverable 4 (rud-closure of limit levels): deferred

`F_i(a,b) ∈ Jset λ` for `a, b ∈ Jset λ` at a limit `λ` is deferred on the
same chain as part 2: `Jset` exists only through the instantiated engine,
which is blocked on `step-trans` (Q8). Independent of that, the brief's
"one-step fact" (`F_i(a,b) ∈ step u` for `a, b ∈ u ∪ {u}`) holds for every
operation under the cumulative form through `step-in-img` (an image value
over the square is a member of the step), so the stated limit-absorption
route is now sound; it only awaits the tower. Recorded for the orchestrator.

## Q10. Wall trail: StepArm carrying `u' u` memberships blows the heap

The first cumulative rewrite put `⟨ a ∈ˢ u' u ⟩` inside the `arm-image`
constructor of `StepArm`. Every typecheck with that shape heap-exhausted
at the 8 GB cap (~185 s) even after trimming `step-in-self`, `step-out`,
and the trans cases; bisection isolated the `u' u`-membership constructor
field as the trigger. The cure, applied and verified: the constructor
carries the lighter two-way split `(⟨ a ∈ˢ u ⟩ ⊎ a ≡ u)` (and likewise for
`b`), with `u'-cases` deciding the split at construction time and the
`u' u`-membership reconstructed only when needed (`u'-in` /
`u-self-in`). The split form typechecks fast and the whole file checks in
26 s cold / ~1 s warm. Lesson candidate: a dependent field whose carrier is
a double union over a `sett`-defined set drags the whole union machinery
into every pattern match; carry the decided case split instead and rebuild
the membership on demand (P-i playbook: bisect, seal, restructure).

## Q11. Timings

| activity | time |
|---|---|
| re-reading the cumulative ruling, Hierarchy, Ops appendix, Images' pairing kit | ~20 min |
| the F13/F14 analysis (pair branch, the junk values, three failed formulations: ⋂-analysis + rightSlice elimination, floor-arm absorption, F5-value route) | ~2 h (probes in `/tmp`, each < 1 s) |
| the `right`-reduction probes (the private-name wall, Probe1-4) | ~45 min |
| the step rewrite fix-up (Fof-f* lemmas, subst directions, small/large membership) | ~1 h (about 12 typecheck rounds, 1-26 s each) |
| prose updates + linters | ~30 min |
| report | ~40 min |

No heap event in this batch's checks (all under `GHCRTS=-M8g`, one at a
time); the part-3 heap trail of Q10 predates the current file state and is
recorded for the lesson.

## Q12. Surprises and lesson candidates

1. **The cumulative form dissolves the F3/F4 obstruction exactly as the
   ruling predicted.** With the step containing the image values, a member
   of the F3 value is the triple itself, and the triple is the F11 value at
   the existing pair `pr u v ∈ b`; the pair-member `{u, pr z v}` one level
   down is the F14 value at the same pair. No left/right projection is
   opened. The orchestrator's two hints typecheck as written.
2. **The remaining blocker is precisely the part-2 wall, re-confirmed by
   reduction probes.** The F11-F14 non-pair branches need the right
   projection's junk facts; `rightSlice`/`sndExtract` are private and
   unnameable, and the contradiction witness for non-pairness IS the
   private `sndExtract` value, so no hypothesis reformulation helps. This
   is the exact missing read the report requests (Q7); it is a library
   export decision, not a proof-shape decision.
3. **The `Fof` seal both saves and costs.** Sealing the sixteen-way family
   `opaque` is what keeps conversion bounded (the StepArm fix of Q10 alone
   was not enough), but every consumer rewrite then needs an
   `opaque unfolding Fof` equality per constructor. Lesson candidate: an
   opaque index family wants a small block of unfolding equalities next to
   it, as the operation index's official interface.
4. **`∈ˢ` is the structure's large membership, not `∈ₛ`.** The recurring
   small-vs-large confusion (parts 1-2) resolved cleanly once the mapping
   was pinned: `x ∈ˢ u` (structure field) is the large `x ∈ u`, and
   `∈∈ₛ .fst/.snd` convert to the small fibre form. The spec inputs take
   the large form directly; no `∈∈ₛ` wrapper is needed at the subst sites.
5. **`subst` direction discipline, third occurrence.** All twelve trans
   cases had `(sym x≡)` where `x≡ : x ≡ₕ F_i a b` already points the right
   way; the pattern is now stable in the report and should be checked by
   construction in future batches (state the equality the way the subst
   consumes it).
6. **`∅ ∈ u ∪ {u}` for transitive `u` needs foundation.** The floor
   absorption of the junk values bottoms out at this fact, which is
   provable by ∈-minimality (not constructively for free); the report
   records it so the images export can include it.

## Q13. What the module now exports (part 3 state)

`step` (opaque, cumulative), `StepArm` + `step-out` + `step-in` /
`step-in-self` / `step-in-img` (the only surface), `step-⊆`, `step-∈`,
`step-mono∈`, `u'-member→step`, the pair frame (`pair→step`,
`singl≡pair`, `prL/prR-in-doubleUnion`), `Fof-f0/f9/f10/f11/f12`, the
twelve trans cases (F0-F10, F15, F3, F4), and the pair-branch machinery
`isPair`, `left-in-u'-pair`, `right-in-u'-pair`. `trans-F11`-`trans-F14`
(total), `step-trans`, `ConcreteS`, and the limit-level closure facts are
absent; sections Q7-Q9 record the exact reasons and the missing reads.

# Part 4 record (the endgame design: junk lemmas, the conditioned telescope, all sixteen cases, ConcreteS, Jset-rud)

## R1. Status

| item | state |
|---|---|
| MOVE 1, Images append: `right-nonpair`, `⋂-member-in-all`, `left-⋂-collapse`, `left-⋂-empty` | **green**, constructive, no LEM (section R2) |
| MOVE 2, Hierarchy edit: `step-trans` conditioned on `⟨ ∅ ∈ u ⟩ ⊎ (u ≡ ∅)`; `level-∅-cond` derived; `level-trans` feeds it; all other exports frozen | **green** (section R3) |
| Step: total `left-in-u'`, `right-in-u'`, `∅-in-u'` | **green** (section R4) |
| transitivity: all sixteen per-op cases | **green** (section R5) |
| `step-trans` total under the conditioned signature | **green** |
| `ConcreteS` (all five obligations) + tower exports | **green** (section R6) |
| deliverable 4: `Jset-rud` (rud closure of limit levels) | **green** (section R7) |
| typechecks | `Images` 50 s, `Hierarchy` ~1-2 s, `Step` 26 s cold / ~1 s warm, all under `GHCRTS=-M8g`, one at a time; no heap event, no 180 s wall, no watchdog kill |
| linters | prose/i18n/agda/glossary clean on all three files |
| code lines | Step 827 (stop-line 1,500); Images append 62 net new code lines; Hierarchy +89 net new code lines |

Only the three granted files were touched (`Images` append, `Hierarchy` edit,
`Step`), plus this report. `Ops`, `OrdArith` untouched; `Realize`,
`Describe`, `Everything` never touched or compiled; no git commit.

## R2. MOVE 1: the Images junk lemmas as actually provable

Appended to `src/L/Rud/Images.lagda.md` (new opaque read-lemma blocks in the
part-2 Ops pattern; private machinery used in scope; no existing export
changed, renamed, or unsealed; additive imports only):

| lemma | statement | size |
|---|---|---|
| `right-nonpair` | `(b : V ℓ) → ((p q : V ℓ) → ⟨ b ≡ₕ pr p q ⟩ → Empty.⊥) → right b ≡ ∅` | 24 |
| `⋂-member-in-all` | `(b c w : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ w ∈ₛ b ⟩ → ⟨ c ∈ₛ w ⟩` | 14 |
| `left-⋂-collapse` | `(b c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → left b ≡ c` | 13 |
| `left-⋂-empty` | `(b : V ℓ) → ((c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → Empty.⊥) → left b ≡ ∅` | 11 |

plus the private `⋂-single` (the intersection has at most one distinct
member: two members of `⋂ b` each lie in every member of `b`, hence in each
other's witness member, so each is a subset of the other's union witness and
they are equal by extensionality) and `⋃∅` helpers. `right-nonpair` is the
empty-slice argument: every right-slice witness would exhibit
`b ≡ pr (left b) (sndExtract ...)`, contradicting the hypothesis, so the
slice is empty and `right b = ⋃ ∅ = ∅`.

**Correction to the brief's "dually left".** `left b ≡ ∅` for non-pair `b`
is FALSE in general: for `b = {{0,2},{1,2}}` (a non-pair), `⋂ b = {2}` and
`left b = 2 ≠ ∅`. The left junk lemma is therefore the collapse/empty
pair (`left-⋂-collapse` + `left-⋂-empty`), not a plain empty statement;
the brief's own "state whatever the private machinery actually proves"
covers exactly this, and the Step side consumes both lemmas through LEM.

## R3. MOVE 2: the conditioned telescope

One edit to `src/L/Rud/Hierarchy.lagda.md`, everything else frozen. The
`step-trans` parameter now takes the empty-set hypothesis:

```text
(step-trans : (u : V ℓ) → (⟨ ∅ ∈ u ⟩ ⊎ (u ≡ ∅))
            → Trans u → Trans (step u))
```

and the engine derives `level-∅-cond : {A : S} → isLevel A →
⟨ ∅ ∈ A ⟩ ⊎ (A ≡ ∅)` by induction on the level: the empty level is `∅`
itself; the step of a level inherits the hypothesis through `step-⊆` (a
member of `u`) or `step-∈` (when `u ≡ ∅`, `step ∅` contains `∅`); and the
two union constructors split by the excluded middle (if some member
contains `∅` the union does, else every member is empty and the union is).
`level-trans`'s step-level case feeds it:

```text
level-trans (step-level {A} lA) = step-trans A (level-∅-cond lA) (level-trans lA)
```

This is the abstract form of the brief's "every successor level contains
∅": the concrete F1(u,u) image makes `∅ ∈ step u` when the condition
fails to come from the floor, but the engine only needs the abstract
`step-⊆`/`step-∈` stand-ins. `Sset-trans`, `Sset-level`, `Sset-suc`,
`Sset-limit`, `Jset` and all other exports are untouched.

## R4. Step: the total projections and the ∅-floor

New in `Step.lagda.md`:

- `∅-in-u' : (u) → ⟨ ∅ ∈ u ⟩ ⊎ (u ≡ ∅) → ⟨ ∅ ∈ˢ u' u ⟩` (member arm via
  `u'-in`, or the self arm when `u ≡ ∅`).
- `left-in-u' : (u) → cond → Trans u → (b) → ⟨ b ∈ˢ u' u ⟩ → ⟨ left b ∈ˢ u' u ⟩`
  (41 lines). Splits on `lem (isPair b)`: the pair branch is the part-2
  `left-in-u'-pair`; the non-pair branch splits on `lem (∃ c. c ∈ₛ ⋂ b)`:
  if a member `c` of the intersection exists, `left-⋂-collapse` gives
  `left b ≡ c` and `⋂-member-in-all` chases `c ∈ w ∈ b` into `u` through
  `u'`-transitivity; if not, `left-⋂-empty` gives `left b ≡ ∅` and the
  ∅-floor applies. LEM is spent at exactly the pair and intersection
  classifications (recorded per the grant).
- `right-in-u'` (12 lines): pair branch via `right-in-u'-pair`; non-pair
  branch via `right-nonpair` (giving `right b ≡ ∅`) plus the ∅-floor.

## R5. The complete sixteen-case table

| case | code lines | route |
|---|---:|---|
| `trans-F0` | 11 | `y ≡ a` or `b`; argument frame |
| `trans-F1` | 7 | `y ∈ a`; argument frame |
| `trans-F2` | 12 | read: `y ≡ pr p q`; pair frame |
| `trans-F3` | 16 | read: `y ≡ pr u (pr z v) = F11 z (pr u v)`; image arm |
| `trans-F4` | 16 | mirror via `F12 z (pr u v)`; image arm |
| `trans-F5` | 10 | `y ∈ v ∈ a`; argument frame |
| `trans-F6` | 12 | read: `y ≡ p`, `pr p q ∈ a`; double-union chase |
| `trans-F7` | 13 | read: `y ≡ pr p q`; pair frame |
| `trans-F8` | 12 | `y ≡ F10 a z`; image arm |
| `trans-F9` | 6 | `y ∈ pr a b`; pair frame |
| `trans-F10` | 17 | `pr b y ∈ a`; pair chase |
| `trans-F11` | 17 | members `{left b}` (F0 image via `left-in-u'`) and `{left b, pr a (right b)} = F14 a b` |
| `trans-F12` | 17 | mirror via `F13 a b` |
| `trans-F13` | 14 | members `left b` (member arm via `left-in-u'`) and `pr (right b) a` (F9 image via `right-in-u'`) |
| `trans-F14` | 14 | mirror with `pr a (right b)` |
| `trans-F15` | 10 | `y ∈ a`; argument frame |

`step-trans` (53 lines) assembles the sixteen through the three-armed
surface: member and self arms are the floor, and the image arm case-splits
on the `Op16` index, threading the `Fof-f*` equality lemmas for each
constructor. Total under the conditioned signature.

## R6. ConcreteS and the instantiated tower

```text
module ConcreteS = L.Rud.Hierarchy lem step step-⊆ step-∈ step-mono∈ step-trans
```

with all five obligations discharged (the first three from part 3,
`step-trans` now total). The instantiated tower is re-exported under the
engine's own trunk-facing names: `Sset`, `Sset-compute`, `Sset-in`,
`Sset-out`, `Sset-mono`, `Sset-mem`, `Sset-suc`, `Sset-limit`,
`Sset-level`, `Sset-trans`, `Jset`, `Jset-mono`, `Jset-limit`,
`limit-succ-mem`. The engine's `level-∅-cond` supplies the condition at
every tower level, so `Sset-trans` goes through for all levels.

## R7. Deliverable 4: `Jset-rud` (rud closure of limit levels)

```text
Jset-rud : (α : V ℓ) → (lim : ⟨ isLimit α ⟩) → (i : Op16) → (a b : V ℓ)
         → ⟨ a ∈ˢ Jset α lim ⟩ → ⟨ b ∈ˢ Jset α lim ⟩
         → ⟨ Fof i a b ∈ˢ Jset α lim ⟩
```

65 lines, exactly the one-step fact plus limit absorption: `Sset-out`
locates `a ∈ step (Sset δₐ)` and `b ∈ step (Sset δᵦ)`; the trivial
`step-member→u'-suc` (4 lines, via `Sset-suc` + `u'-in`) puts each in
`u' (Sset (sucV δ))`; `ord-tri` on the successors picks a common stage,
`u'-mono∈` (8 lines) transports across `Sset-mono`/`Sset-mem`; the
one-step fact `step-in-img` makes `Fof i a b` a member of
`step (Sset δ)`; and `Sset-in` with `limit-succ-mem` closes it into
`Jset α lim`. No `Sset-limit` unfolding was needed (the successor-membership
route is the limit equation's essence).

## R8. Walls and surprises

No heap event, no 180 s wall, no watchdog kill in this batch. Surprises:

1. **`left b ≡ ∅` is false for non-pairs** (corrected in R2): the junk
   characterization had to be the collapse/empty pair, and the collapse
   rests on the at-most-one-member analysis of `⋂` (each member of `⋂ b`
   lies in every member of `b`). Lesson candidate: the brief's "dually
   left" assumption is not the true statement; the true one is
   `left-⋂-collapse` + `left-⋂-empty`.
2. **The `∃[ x ∈ A ]` and `∃[ x ∶ A ]` binder forms do not parse when
   `_∈_` is in scope** (the binder conflicts with the infix operator);
   the untyped `∃[ x ] P` form works. Lesson candidate: in modules that
   import a membership infix, use the untyped ∃-binder.
3. **`where`-clause forward references fail in this setup** (three
   occurrences: `⋂-single`, `left∈u'`, `enter`); order the where
   definitions before their users.
4. **The engine's union cases genuinely need LEM** (constructive
   distribution over an arbitrary family of members fails); the engine
   already carried `lem`, so this is the only classical expenditure of
   `level-∅-cond`, matching the brief's design.
5. **`⟨ P ⟩` for `P : hProp` is the carrier type** in this codebase, so
   `∃`-bundle predicates take the unboxed hProp (`∃[ c ] (c ∈ₛ ⋂ b)`),
   not `⟨ c ∈ₛ ⋂ b ⟩`. The recurring small/large and boxing disciplines
   from parts 1-3 each resurfaced once.
6. **The `Fof` seal keeps paying**: the total `step-trans` assembly needs
   all sixteen `Fof-f*` unfolding equalities (one per constructor); the
   pattern from part 3 extended without trouble.

## R9. Timings

| activity | time |
|---|---|
| the endgame design analysis (junk statements, the at-most-one proof, the ∅-condition engine lemma, the F13/F14 non-pair route) | ~1.5 h |
| Images append (junk lemmas, ~8 typecheck rounds at 50 s each) | ~1 h |
| Hierarchy edit (conditioned signature, level-∅-cond, ~6 rounds) | ~1 h |
| Step edits (total projections, F11-F14, step-trans, ConcreteS, Jset-rud; ~10 rounds at 26 s each) | ~2 h |
| report | ~40 min |

## R10. What the module now exports (part 4 additions)

Images: `right-nonpair`, `⋂-member-in-all`, `left-⋂-collapse`,
`left-⋂-empty`. Hierarchy: the conditioned `step-trans` parameter and
`level-∅-cond`. Step: `∅-in-u'`, `left-in-u'`, `right-in-u'`,
`trans-F11`-`trans-F14`, total `step-trans`, `ConcreteS` with the
instantiated tower exports, and `Jset-rud`. The telescope is fully
discharged and the tower is instantiated.
