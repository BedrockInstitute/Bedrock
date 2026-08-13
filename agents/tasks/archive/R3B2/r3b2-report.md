# R3b-2 report: the description half completed (F2-F7 hops, F3/F4 adequacy, the seven image operations)

**Date:** 2026-08-03. **Scope:** `src/L/Rud/Describe.lagda.md` plus this
report, nothing else: no `src/Everything.lagda.md`, no `L.Rud.Realize`,
`L.Rud.Step`, `L.Rud.Hierarchy`, no `L.Rud.Order` (the parallel R4 batch's
file, left untouched), no git, no postulates, no holes, no `TERMINATING`.
Every agda invocation ran under `GHCRTS=-M8g`, one typecheck at a time
(C-12). The module typechecks clean (warm 1.1-1.2 s wall, exit 0); the
only triple-digit run was a deliberate full-cold rebuild of the whole
dependency tree (64.6 s, exit 0), and no development check exceeded 10 s,
so no wall event occurred and the P-i playbook was not needed. Stop-line
1,400 code lines: **1,182 used** (the batch grew the file from 560 to
1,182). `lint-agda --check`, `lint-prose --check`, `weave-i18n --check`,
and `check-glossary --check` are all green; no em dash, no half-width CJK
punctuation, zh paragraphs single-line.

## 1. The completed per-operation table (all sixteen)

| op | formula | Δ₀ | adequacy | defSet equation |
|---|---|---|---|---|
| F0 | disjunctive equality over `a`, `b` (frame) | `δ-∨ δ-≐ δ-≐` | both directions to membership | `F0-defSet≡` ✓ |
| F1 | membership ∧ negation | `δ-∧ δ-∈ (δ-¬ δ-∈)` | both directions | ✓ |
| F2 | `∃̇∈ a (∃̇∈ b (prAt′ …))` | `δ-∃∈ δ-∃∈ Δ₀-prAt′` | sat↔DRHS (part 1) + `F2-desc-in` via `F2-read`; **desc-out NO-GO** (seal, §4) | **NO-GO** (seal; the plain equation is moreover false, §5.2) |
| F3 | 10-binder tower + middle-pair waypoints (frame) | 10×`δ-∃∈` + atoms | **sat↔DRHS restructured and green** (§3) + `F3-desc-in` via `F3-read`; **desc-out NO-GO** | **NO-GO** (seal; triple not in the carrier) |
| F4 | same frame, slots exchanged | same | same as F3, `F4-desc-in` via `F4-read`; **desc-out NO-GO** | **NO-GO** (seal; triple not in the carrier) |
| F5 | `∃̇∈ a (v ∈̇ w)` | `δ-∃∈ δ-∈` | both directions | ✓ |
| F6 | two `⋃⋃`-towers + pair waypoint + equality | 7×`δ-∃∈` + atoms | sat↔DRHS + `F6-desc-in` via `F6-read` + **`F6-defSet-in`** (read direction, closes); **desc-out NO-GO** | read direction ✓; equation NO-GO (§5.2) |
| F7 | `∃̇∈ a (∃̇∈ a (u ∈̇ v ∧̇ prAt′ …))` | `δ-∃∈ δ-∃∈ (δ-∧ δ-∈ Δ₀-prAt′)` | sat↔DRHS + `F7-desc-in` via `F7-read`; **desc-out NO-GO** | **NO-GO** (seal; pair not in the carrier) |
| F8 | slice equality: `∃̇∈ y` of two `∀̇∈` inclusions with the pair reader | `δ-∃∈ (δ-∧ δ-∀∈ δ-⇒ …)` | **both directions** (extensional slice equality, fibre into the small-index spec) | ✓ under the slice-closure hypothesis `F8 x y ⊆ A` |
| F9 | disjunctive equality over the pair's two members (frame) | as F0 | both directions | ✓ |
| F10 | `∃̇∈ x (∃̇∈ p (∃̇∈ w (prAt′ f2 f0 f3 ∧̇ f0 ≐ con y)))` | `δ-∃∈ δ-∃∈ δ-∃∈ (δ-∧ Δ₀-prAt′ δ-≐)` | **both directions** (via the spec's path) | ✓ (image ⊆ A by transitivity) |
| F11 | pair-value frame, members `{a}`, `{a, pr x b}` | `δ-∨ δ-≐ δ-≐` | **both directions** (frame; spec under `y ≡ pr a b`) | ✓ under the member hypotheses |
| F12 | same frame, members `{a}`, `{a, pr b x}` | as F11 | both | ✓ under the member hypotheses |
| F13 | same frame, members `a`, `pr b x` | as F11 | both | ✓ under the member hypotheses |
| F14 | same frame, members `a`, `pr x b` | as F11 | both | ✓ under the member hypotheses |
| F15 | `(v ∈̇ x) ∧̇ (v ∈̇ P)`, `P` the predicate slot of `F15Of` | `δ-∧ δ-∈ δ-∈` | **both directions** | ✓ (the `v ∈ P` conjunct carries the carrier membership) |

## 2. Part-1 debts paid and standing

**Paid.**

1. **The sealed-hop direction (membership into the shape) for F2/F3/F4/F6/F7.**
   Each of the five read lemmas (`F2-read` … `F7-read`, R-36 pattern) now
   feeds the chapter's own DRHS shape: `Fᵢ-mem-DRHS` reassembles the read's
   decomposition into `Fᵢ-DRHS`, and `Fᵢ-desc-in` composes it with the
   part-1 sat-in, so the chain membership → read → DRHS → satisfaction
   closes end to end for all five operations. For F6 the same hop closes the
   defSet inclusion `F6 a b ⊆ defSet Φ₆` (the domain's components lie in
   `⋃⋃ a ⊆ A` by transitivity).
2. **The F3/F4 adequacy no-go.** The two directions sat↔DRHS are delivered
   (§3); the part-1 trail is closed.

**Standing (recorded per operation, the wall protocol's NO-GO trail).** The
reverse direction `DRHSᵢ → membership` (hence `desc-out` and the defSet
sub-inclusion `defSet ⊆ Fᵢ a b`) remains **impossible while the Ops seal
stands**: the specification's RHS names sit inside the same `opaque` blocks
as the operations, and the read lemmas are one-directional by R-36's
design. Three genuinely different formulations of the obligation were
attempted (the trail in §4); all fail on the same measured fact, and the
report's earlier one-line remediation (move the `Fᵢ-RHS` hProp definitions
outside the opaque blocks, or add reverse `Fᵢ-write` read lemmas in new
`opaque unfolding` blocks) is the load-bearing dependency for the switch's
consumption of these operations.

## 3. The F3/F4 restructure record

The part-1 trail had three failure modes: (a) the abstract middle-clause
formula's satisfaction would not unify with the body's conjunct; (b) the
sat-in's emission against the three-layer DRHS resisted the inner
destructuring; (c) the sat-out's midSat input resisted projection counts.
The restructure, exactly along the report's proposal (thread witnesses
through named eliminations, the tower-out pattern) plus the I-4 cures:

1. **The middle clause stays concrete** (`prAt′ f0 mid₁ mid₂` with the two
   slots as Fin parameters), and the adequacy of the frame is parameterized
   only by the **carrier-level path** `midCorr` (I-4): a path between
   `pr (⟦var mid₁⟧ γ) (⟦var mid₂⟧ γ)` and `midp (⟦var f7⟧ γ) (⟦var f3⟧ γ)
   (⟦var f4⟧ γ)`, so every implicit is solved from a path and none is
   inverted through `⟨_⟩`. Both instantiations instantiate `midCorr` by
   `refl`.
2. **Sat-out** peels the ten bounded existentials one per named lambda and
   reads the body through `PA.prAt′-in` with explicit Fin positions (the
   F2/F6/F7 idiom), assembling `∣ u , ∣ z , ∣ w , (z∈a , (pruw∈b , v≡)) ∣₁
   ∣₁ ∣₁`; the middle clause feeds `midCorr` directly and the triple
   equality composes by paths.
3. **Sat-in** builds the satisfaction from the DRHS by eliminating the two
   component towers with `tower-out` (exactly as F6's sat-in), rebuilding
   the pair `p₃ = pr u w` and the middle pair via `prAt′-out`, and
   witnessing the middle pair inside the candidate with the pair's own
   members. The middle-pair **value is the frame parameter** `midp u z w`
   (not the concrete `pr z w`): the midCorr path then discharges the
   coordinate exchange for both instantiations, and `prAt′-out f0 mid₁ mid₂`
   takes `sym (midCorr env)` as its path. The ten binders' memberships are
   threaded with the `qₐ`/`q_b` transports at the constant bounds.
4. Both `F3Desc` and `F4Desc` instantiate the frame with `midCorr = refl`,
   name `Fᵢ-sat-out`/`Fᵢ-sat-in`, and add `Fᵢ-mem-DRHS`/`Fᵢ-desc-in` from
   the read lemmas (F3's read returns `x ≡ₕ pr u (pr z v)`, F4's
   `x ≡ₕ pr u (pr v z)`, matching the coordinate exchange).

## 4. The NO-GO trail for `DRHS → membership` (F2/F3/F4/F6/F7)

The obligation: `⟨ Fᵢ-DRHS a b v ⟩ → ⟨ v ∈ˢ Fᵢ a b ⟩` (equivalently
`desc-out` and the defSet sub-inclusion). Three formulations, all measured:

1. **Construct the sealed RHS from DRHS witnesses.** Reassemble the
   decomposition into `⟨ Fᵢ-RHS a b v ⟩` and apply the spec's bwd
   direction. Fails: `Fᵢ-RHS` is an opaque name, `fst (Fᵢ-RHS a b v)` is a
   stuck type, and the probe error is exactly `∥ _A_28 ∥₁ !=< fst (F2-RHS a
   b v)` (UnequalTerms). This reproduces the r2c measurement.
2. **Reverse the read lemma.** `Fᵢ-read : ⟨ v ∈ˢ Fᵢ a b ⟩ → ∥ dec ∥₁` is
   one-directional (R-36's design); its inverse would inhabit the sealed
   sett membership `v ∈ˢ Fᵢ a b` from `∥ dec ∥₁`, and the operation's body
   is opaque, so no constructor exists (the r2c report's destructor probe).
3. **Bridge the hProps.** `Fᵢ-DRHS a b v ≡ Fᵢ-RHS a b v` by hProp
   extensionality would need both directions of the same block: constructing
   a point of the stuck carrier and eliminating one, both impossible.

These are not three independent hypotheses: they are three routes to the
same sealed boundary, and the seal is the boundary (verified by probe, not
inferred). The `desc-in` directions, by contrast, close because the reads
provide exactly the membership-to-decomposition direction. A reverse read
`Fᵢ-write` (in Ops, R-36 pattern) or the RHS names outside the opaque
blocks unblocks everything recorded in the table's NO-GO cells.

## 5. The seven image operations

**F10.** The formula binds the pair `p ∈ x`, a waypoint `w ∈ p`, and a
first-component copy `y₀ ∈ w`, with `prAt′ f2 f0 f3` reading `p = pr y₀ v`
and the atom `f0 ≐ con m_y` forcing `y₀ = y`. This needs **no new pair
reader with a constant slot**: the copy is ranged over the pair's own
singleton member (`y ∈ {y} ∈ p`), which is exactly the "pair-shaped fiber"
the existing reader governs. Adequacy both directions through the
specification's path; the defSet equation closes because `v ∈ F10 x y`
puts `v` in `⋃⋃ x ⊆ A` (transitivity).

**F8.** The formula states the slice equality extensionally: `∃ z ∈ y` with
the two inclusions `∀ v ∈ w. ∃ p ∈ x. p = pr z v` and `∀ p ∈ x. ∀ w' ∈ p.
∀ v ∈ w'. p = pr z v → v ∈ w` (both with the plain pair reader, since `z`
is a bound variable). Adequacy closes both directions: the inclusions give
`w ≡ F10 x z` by extensionality, the fibre of `z` in `⟪ y ⟫` feeds the
specification's small-index form, and the reverse rebuilds the inclusions
from the path. The defSet equation is stated under the slice-closure
hypothesis `⟨ F8 x y ⊆ A ⟩` (the collection's members are slices, not
carrier elements, so the plain equation is false without it; the ∩-form is
recorded as the unconditional alternative, deferred).

**F11-F14.** One `PairValFrame` (the InL sharing discipline): parameters
are the two members `m₁`, `m₂`, their carrier memberships, the value
equation `val ≡ F0 m₁ m₂`, and transitivity. The frame delivers the
F0F9Frame formula, both adequacy directions (through `F0-spec` and the
value equation), and the defSet equation. The four instantiations differ
only in the coordinates: F11/F12 take `m₁ = {a}`, `m₂ = {a, pr x b}` /
`{a, pr b x}` with the value equation from `F11-spec`/`F12-spec`; F13/F14
take `m₁ = a`, `m₂ = pr b x` / `pr x b` from `F13-spec`/`F14-spec`. The
pair decomposition `y ≡ pr a b` is a module hypothesis, matching the
"describe only the pair-shaped fibers the specs govern" instruction.

**F15.** The predicate slot of `F15Of` enters as a module parameter `P` and
an ordinary carrier member; the formula is the two membership atoms, the
adequacy is both directions through the spec's path, and the defSet
equation closes because the `v ∈ P` conjunct already places the candidate
in the carrier.

## 6. Timings

| run | wall |
|---|---:|
| development checks (file, warm cache) | 1.1-9.0 s |
| final warm check | 1.2 s |
| full cold rebuild (whole dependency tree, one-time) | 64.6 s |
| probe checks (seal ground truth) | 0.8-1.0 s |

No check approached the 180 s tripwire; no heap exhaustion, no exit
137/251. One earlier attempt to force a fresh cold check by moving the
`_build/2.8.0` interface cache aside was recovered immediately by moving it
back (no destructive command was used).

## 7. Surprises and lesson candidates

1. **The reads dissolve only one side of the seal.** R-36's read lemmas are
   one-directional by design (`membership → decomposition`), so the reverse
   hop `DRHS → membership` for F2/F3/F4/F6/F7 is still impossible without a
   reverse read or RHS unsealing. The brief's "the full chains now closing
   end to end" is true for the membership-to-shape direction and the
   sat↔DRHS direction; the other side is recorded as the standing NO-GO with
   its trail. Lesson candidate: when a seal is exposed by a read, the read's
   direction is a public interface choice, and a consumer that needs both
   directions must state the reverse read as its dependency, not assume it.
2. **The plain defSet equations for F2/F3/F4/F7 are false, not just
   sealed.** F2's members are pairs of members of `a`, `b`; F7's are pairs;
   F3/F4's are triples; none is in the carrier `A` in general, so
   `defSet Φᵢ ≡ Fᵢ a b` fails even with the seal open (a concrete
   counterexample: `A = {∅}`, `F2 ∅ ∅ = { {∅} } ⊄ A`). Only F6's domain lies
   in `A` by transitivity. The part-1 debt label "sealed hop" understated
   this: the honest forms are the hypothesis versions or the ∩-form, which
   the switch's `defSet ⊆ step` needs in any case. This is why the table
   records F2/F3/F4/F7 defSet as NO-GO on both grounds.
3. **`DefOf A .defSet` in a type fails scope in nested modules.** The
   module-alias pattern (`module DefA = DefOf A` then `DefA.defSet`) is the
   house style and is required; the F11-F14 instantiations needed the alias.
4. **The middle pair must be the frame parameter, not the concrete shape.**
   Inside the parameterized frame, `midp u z w` is abstract, so the sat-in's
   middle-pair value must be `midp u z w` (with `sym (midCorr env)` as the
   pair reader's path), not `pr z w`; the coordinate exchange then lives
   entirely in `midCorr`, which is `refl` for both F3 and F4. This is the
   I-4 lesson in the frame's own language.
5. **Peel-shape discipline for nested `⋁`s versus nested `⊨`s.** In the
   DRHS peels (sat-in), each `⋁` level's second component is the inner
   truncation directly; in the formula-satisfaction peels (sat-out), each
   bounded existential's second component is a `⊓`-conjunction needing
   `.snd`. Mixing the two was the source of most projection-count errors in
   this batch; naming the peel levels (as the F6 model does) fixes it.
6. **F10 needs no constant-slot pair reader.** The trick of binding a copy
   of the constant first component over a member of the pair (`y ∈ {y} ∈
   p`) plus one equality atom reuses the existing `prAt′`; the "pair-shaped
   fiber" instruction paid off directly.

## 8. Protocol compliance

Created/modified only `src/L/Rud/Describe.lagda.md` and this report;
typechecked only the module (never `Everything`, never `make check`); every
agda run under `GHCRTS=-M8g`, one at a time; no postulates, holes, or
`TERMINATING`; prose groups balanced, no em dash, no half-width CJK
punctuation; the rudimentary-class rendering follows the glossary (初步函数
is the only zh rendering used). The parallel R4 file (`L.Rud.Order`) was
left untouched.
