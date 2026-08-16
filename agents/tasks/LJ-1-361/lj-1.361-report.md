# LJ-1.361 report: Cantor-Bernstein over an arbitrary model of ZF

Written incrementally from the first five minutes (C-22). All Agda runs
used one process with `GHCRTS="-A64m -I0 -M8g"`. The cap was never
raised. The slot count was read before every invocation (C-12) and was
0 of 2 each time.

## VERDICT

**OPEN-BUT-NOT-CHEAPER. One number: about 700 lines, INFERRED, basis
the `[LJ-1.353]` survey table re-anchored on the delivered `L.Coding`
rows, plus a generic reader-adequacy layer anchored on
`src/L/Coding/Base.lagda.md` at 185 measured code lines, minus the
projection overhead the miniature shows to be absent.**

The owner's route is OPEN. The proof needs only record fields, and the
miniature typechecked the load-bearing separation at an abstract
structure. The route is NOT cheaper on first cost: the generic theorem
is the same theorem over the same steps, so the 650 keeps its shape.
It is paid ONCE and every model inherits, which is a different and
better deal. Two delivered models wait today: `L` at
`src/L/Model.lagda.md:98` and `V` at `src/V/Model.lagda.md:415`.

Nothing that landed today is retired by this route. `V.CantorBernstein`
and `L.CantorBernstein` serve the AMBIENT reading. A generic internal
theorem would produce a CODED bijection, which is a different object.
Both readings stand beside each other.

## D-10 and C-57: does the tree already hold the generic form

**MEASURED absent.** Greps for `Bernstein`, `Schroeder`, `Tarski` over
`src/` return the two chapters that landed today and nothing else. The
semantic search found the parts: the coding vocabulary, the `InjChain`
devices, and the ambient corollary. No chapter states a theorem at an
abstract `ZFStructure` with an `isZFModel`. The `Tarski` hits are the
Tarski-Vaught criterion at `src/L/Hull.lagda.md:178`, which is a
different theorem.

## PART 1: the generic statement, as a type

The statement can be made generic with NO new vocabulary. Every piece
is in scope at the abstract site:

```agda
module FOL.Bernstein {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
  module ZF = FOL.ZFModel 𝒮

  -- over the record at src/FOL/ZFModel.lagda.md:187, with the
  -- parameter-free formula families svAt, domAt, injAt, inRanAt
  -- written at Formula (ZFStructure.S 𝒮) n instead of Formula S n
  CSB : ZF.isZFModel → Type (ℓ-suc ℓ)
  CSB M = (a b F G : ZFStructure.S 𝒮)
        → ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
        → ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
        → ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
        → ⟨ (F ∷ a ∷ []) ⊨ rbd zero (suc zero) ⟩
        → ⟨ (G ∷ b ∷ []) ⊨ svAt zero ⟩
        → ⟨ (G ∷ b ∷ []) ⊨ domAt zero (suc zero) ⟩
        → ⟨ (G ∷ b ∷ []) ⊨ injAt zero ⟩
        → ⟨ (G ∷ b ∷ []) ⊨ rbd zero (suc zero) ⟩
        → ∥ Σ[ H ∈ ZFStructure.S 𝒮 ] BijCode H a b ∥₁
```

`rbd` is the range-bounded clause: every pair of the code has its
second component in the target. It is writable from the delivered
`inRanAt` shape at `src/L/Coding/Injection.lagda.md:221-232`, with the
bounded quantifier of `domAt` as the pattern. `BijCode` is the
`[LJ-1.353]` row 1 predicate, about 20 lines. The miniature proves the
container question below. So the statement closes with nothing
missing.

An alternative reading states CSB as one object-language sentence and
asserts its satisfaction. The code-level form above is the useful one,
because it consumes the trophy's facts directly.

## PART 2: the crux. Is the bounded separation a field

**YES. MEASURED by the miniature.** The field is
`hasSeparation : (a : S) (φ : Formula S 1) → isContr (...)` at
`src/FOL/ZFModel.lagda.md:194`, and it takes ANY first-order formula,
not only a bounded one. The syntax has bounded quantifiers as
primitive constructors: `∀̇∈` and `∃̇∈` at
`src/FOL/Syntax.lagda.md:100`. The power object comes from the field
`hasPower` at `src/FOL/ZFModel.lagda.md:199`, and the derived
operation `𝒫` sits at `:287`. The Tarski formula's constants are legal
terms: `con` takes any value of the carrier.

So the one separation the fixed-point argument needs is an application
of `separate` at `src/FOL/ZFModel.lagda.md:281`. It needs nothing a
particular model supplies. The miniature typed it end to end.

One premise correction: the brief says two fields take a
`Formula S 1` at `:159`. MEASURED: one field takes `Formula S 1`,
`hasSeparation` at `:194`. One field takes `Formula S 2`,
`hasReplacement` at `:196`. The prose at `:159` says "a Formula S 1 or
a Formula S 2". The conclusion stands either way.

## PART 3: what the 650 becomes

**The three closure facts are GENERIC.** They are inferences about
satisfaction in whatever model holds the record. Each one moves
membership facts and satisfaction facts through the carved set's
specification, and the specification is the record's projection at
`src/FOL/ZFModel.lagda.md:284`. None of the three names
constructibility or the tower. The full field list the proof consumes
is `separate`, `𝒫`, `pair`, `⋃`, `extensional`, plus excluded middle
at the model's level. All are fields or one-line consequences.

So the 250 does not shrink. It is paid once at the generic site, and
every model inherits it forever. The table:

| Part | L-sited, `[LJ-1.353]` | Generic site |
|---|---|---|
| `BijCode` and friends | 20 | 20 |
| Tarski formula and adequacy | 150 | 200, generic adequacy against the derived pair is new work |
| The three closure facts | 250 | 250, same work at a generic site |
| Graph carve and conjuncts | 200 | 200, same |
| Readback and assembly | 30 | 30 |
| Instantiation glue at `L` | none | 30, one substitution plus import rewiring |

The generic adequacy row is new because the L chapters inherit their
pair characterization from the ambient `V.Coding`. A generic chapter
must prove it from `pair` and `extensional`. The offset runs the other
way too: satisfaction at an abstract carrier computes definitionally,
which the miniature's `refl` shows, while the L chapters carry
projection substitutions in every adequacy lemma. Net: about 700
against the 650, plus 30 glue per model.

The second model is where the deal turns: `V` instantiates through
`V⊨ZF` at `src/V/Model.lagda.md:415` for the glue price alone.

## PART 4: is InjCode L-specific in substance, and what would move

**MEASURED: three conjuncts of four are generic in substance.** Read
the dependencies one by one at `src/L/Cardinal.lagda.md:223-228`:

- `S` is the carrier of `𝒮ʟ`, and `𝒮ʟ = 𝒮ᵥ ↾ isL` at
  `src/L/Constructible.lagda.md:410-411`. Any structure has a carrier.
- `⊨` resolves to `AbsL._⊨ᵐ_`. `FOL.Absoluteness.Single` DEFINES it as
  plain `FOL.Semantics` over the restricted structure, opened at
  `src/FOL/Absoluteness.lagda.md:74-78`. So the satisfaction of
  `InjCode` IS the generic satisfaction at `𝒮ʟ`, by construction. A
  generic theorem instantiated at `𝒮ʟ` speaks the same relation with
  no bridge.
- `svAt`, `domAt`, `injAt` are variable-only, parameter-free syntax:
  `svAt` at `src/L/Coding/Model.lagda.md:210-214`, `domAt` at
  `:278-279`, `injAt` at `src/L/Coding/Injection.lagda.md:44-48`. The
  pair reader underneath is `prAt` at
  `src/L/Coding/Base.lagda.md:285-287`, also parameter-free. Their
  definitions carry no constant, so the same trees typecheck at any
  carrier.
- The FOURTH conjunct is L-specific AND ambient: it uses `pr` from
  `V.Coding`, `fst` from the Sigma carrier, and ambient `_∈_`. This is
  the one place the statement leaves the generic world.

So the premise at risk in the brief is HALF false. The first three
conjuncts drag no `L` in by definition. The fourth does. The generic
theorem would restate the fourth as the satisfaction clause `rbd` from
Part 1, and the L side would keep the ambient fourth conjunct for its
readback consumers.

**What would move, priced and not proposed:**

- The parameter-free builders and their certificates move:
  `sglAt`, `pairAt`, `prAt` and the certificates from
  `src/L/Coding/Base.lagda.md`, about 60 code lines;
  `prAtL`, `appAt`, `svAt`, `domAt`, `inDomAt` from
  `src/L/Coding/Model.lagda.md`, about 40;
  `injAt`, `inRanAt`, `ranAt` from
  `src/L/Coding/Injection.lagda.md`, about 25. About 125 lines in
  total.
- Ten live consumers rewire import lists: MEASURED count from grep,
  `src/L/Absorption.lagda.md`, `src/L/Cardinal.lagda.md`, six
  `src/L/Choice/` chapters, `src/L/Condensation.lagda.md`,
  `src/L/Hierarchy.lagda.md`, `src/L/InjChain.lagda.md`, plus
  `src/Everything.lagda.md`.
- The adequacy-to-ambient layer STAYS. It is the heart of
  `L.Coding.Model`, 1354 measured code lines, and it runs on `abs₀`,
  `codeBridge` and `isL-trans`. Those are L facts.
- `InjCode` itself does not move whole. Its fourth conjunct is
  ambient. Its statement survives a move unchanged in substance: only
  the import paths of the three families change.

This is a route-level finding. A move touches 13 files and deserves
its own ruling under D29 if taken. The generic CSB chapter does not
REQUIRE the move: it can carry its own copy of the parameter-free
trees, about 125 lines, and leave `L.Coding` untouched. That is the
cheaper first step, at the cost of a temporary duplicate.

## THE MINIATURE

`agents/tasks/LJ-1-361/MiniSep.agda`. Exit 0, 1.34 s wall, empty-file
floor 0.62 s, slot count 0 of 2. It decides Part 2 mechanically:

1. It takes an ABSTRACT `𝒮 : ZFStructure (hPropAlgebra ℓ)` and an
   abstract `isZFModel`.
2. It builds the Tarski separation shape as a `Formula S 1`: a bounded
   existential over `con (𝒫 a)` with the closure condition abstract
   and `a`, `b`, `F`, `G` as constants.
3. It obtains the carved set through `separate` and its specification
   through `separate-spec`, both from the record alone.
4. Bonus: it proves by `refl` that satisfaction of the bounded
   quantifier computes to the truth algebra's sup. No translation
   layer stands between the formula and the host logic at an abstract
   carrier.

What the miniature does NOT decide: the closure condition's content,
the pair-reader adequacy against the derived pair, and the graph
carve. Those are `[LJ-1.353]` rows 2 to 4 and keep their anchors. The
instantiation at `L` was not typed: it is one substitution,
`FOL.Bernstein 𝒮ʟ` with `L⊨ZF`, and INFERRED mechanical.

## DD4 and DD5

Axis (C-46): tower naming. The generic CSB names no tower, no stage
and no satisfaction bridge. It belongs under `src/FOL/`, below both
trophies, and both inherit it by import.

What it does to the closures: the AC closure and the GCH closure both
gain one shared chapter when it is wired in. The GCH closure figure
still reads from a statement whose proof is not wired, so it
UNDERSTATES by about 1,028 GCH lines and 36 shared, bounded by
construction at `dev/ledger.toml:195-206`. A generic CSB placed and
not yet consumed would deepen that understatement by its own size,
which is the same blind spot `L.InjChain` and `L.Absorption` already
occupy. The `--reuse` report reads the surviving tree, so the fix is
wiring, not placement.

DD5, one line: a theorem proved over an arbitrary ZF model is
inherited by the internalization route too, so the benchmark endpoint
keeps whatever it pays here. That is insurance, and it does not change
today's price.

## WHAT IT BUYS, stated against the abort criteria

- OPEN AND CHEAPER: NO. The first cost is about 700 against the 650,
  with the basis stated in the verdict.
- OPEN AND NOT CHEAPER: YES. It buys one proof serving `L`, `V` and
  every future model, with the second instance at glue price. That is
  the DD4 answer. D16 at `archive/dev/DECISIONS-archived.md:38` rules
  the shape: asset durability equals genericity. D29 at `:48` rules
  the discipline: a recon that returns only the fixed-carrier shape
  has not finished. This report returns both shapes with prices.
- The 34 lines that landed today: NOT redundant. They answer a
  different reading, the ambient one, and the trophy consumes that
  reading today.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-100`. The
  module line `module CSB (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) ...`: stated
  at a FIXED carrier and at the ambient index types, chain form. The
  retired route never packaged CSB inside a model. TOOK: the opposite
  packaging choice, as direct evidence that the generic-model form was
  never built on either route.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`.
  The retired ruling: equinumerosity is a bijection, never injections
  both ways, to avoid a per-consumer CSB obligation. WHY NOT the
  ruling itself: the live route re-ruled the opposite at
  `[LJ-1.323]` 7.4, and `[LJ-1.353]` section 6 records both.
- `archive/dev/DECISIONS-archived.md:38`. D16, genericity equals
  durability. TOOK: the framing of the DD4 answer.
- `archive/dev/DECISIONS-archived.md:48`. D29, the three named moments
  for the generic question. TOOK: this report answers moment 1 for
  CSB.
- `archive/dev/JOURNAL-archived.md:1377`. The trap the retired
  predicate ruling avoided: raw-injection cardinality forces every
  consumer to re-derive the bijection. TOOK: the same trap is what a
  generic CSB would close forever. WHY NOT the surrounding entries:
  they reason about the retired reification framework, which this tree
  replaced with satisfaction facts.

## LITERATURE USED

- `dev/literature/devlin-II5.md:145-166`. Devlin proves GCH in L by
  containment and counting: every subset of `κ` lands in `L_{κ⁺}` and
  `|L_{κ⁺}| = κ⁺`. He never proves Cantor-Bernstein inside `L` and
  never relativizes it. A set theorist proves CSB once in ZF and every
  inner model inherits it, exactly the owner's instinct. The tree pays
  for that inheritance either as the ambient corollary, delivered
  today at 80 to 100 lines, or as the generic internal form at about
  700.
- `dev/literature/digest.md:64-66`. The Q5 relativization block is
  about rudimentary functions and `x ∩ A`. WHY NOT: no bearing on
  model-level theorem placement.

## Measurements

| Item | Value | Kind |
|---|---|---|
| Miniature `MiniSep.agda` | exit 0, 1.34 s | MEASURED |
| Empty-file floor `Floor.agda` | 0.62 s | MEASURED |
| Slot count before each run | 0 of 2 (C-12) | MEASURED |
| `src/L/Coding/Base.lagda.md` code lines | 185 | MEASURED |
| `src/L/Coding/Model.lagda.md` code lines | 1354 | MEASURED |
| `src/L/Coding/Injection.lagda.md` code lines | 220 | MEASURED |
| Live consumers of the formula families outside `L.Coding` | 10 files | MEASURED |
| Builders and certificates that would move | about 125 lines | INFERRED from the three files |
| Generic CSB first cost | about 700 lines | INFERRED, basis in the verdict |
| Glue per model instance | about 30 lines | INFERRED |
| Generic model-level CSB in the tree | absent | MEASURED |
