# LJ-1.498 report: does the level graph name any constant at all

RESULT: **NO-GO on the obligation as written, and the wall is much smaller than
`[LJ-1.494]` could see.** The census is NOT empty: `LsetGraphAt` names 664
constants. But `mapFo` is the wrong instrument, the missing thing is not a map,
and the stage condition the constants need is ALREADY PROVED in `src/`.

The obligation `graphFo-at-SL` is not inhabited. `review-of-graphFo-at-SL.md`
states the stop. Nothing landed in `src/`.

## THE CONSTANT CENSUS

**NOT NONE. `LsetGraphAt w b` names 664 constants**, at `n`, `w` and `b` all
variable. Machine computed, not read off by eye: `countFo` counts `con`
occurrences and nothing else (src/FOL/Manipulation/Parameters.lagda.md:70-86),
and the probe asserts the figure GREEN, not as an error message
(agents/tasks/LJ-1-498/Probe498.agda:63-64, run agents/tasks/LJ-1-498/runs/full-0.out).

The seal at src/L/Coding/Graph.lagda.md:203 blocks the count. Opened in the
probe; nothing in `src/` is touched by that.

### Attribution

One run, base-100000 packing, decoded from
agents/tasks/LJ-1-498/runs/w3-3.out:4 and runs/w3-4.out:4.

| formula | file:line | constants |
|---|---|---|
| `prAtL q u v` | src/L/Coding/Model.lagda.md:122 | 0 |
| `appAt f x y` | src/L/Coding/Model.lagda.md:160 | 0 |
| `domAt f d` | src/L/Coding/Model.lagda.md:278 | 0 |
| `tagAtL s k x` | src/L/Coding/Model.lagda.md:585 | **1** |
| `isTmAt t N A` | src/L/Coding/Shape.lagda.md:140 | 2 |
| `binForm k rel` | src/L/Coding/Shape.lagda.md:100 | 1 + rel |
| `unForm k rel` | src/L/Coding/Shape.lagda.md:104 | 1 + rel |
| `zeroPay` | src/L/Coding/Shape.lagda.md:179 | **1** |
| `bothTm A` | src/L/Coding/Shape.lagda.md:171 | 4 |
| `shapes A` | src/L/Coding/Shape.lagda.md:183 | 26 |
| `shapedAt C A` | src/L/Coding/Shape.lagda.md:189 | 26 |
| `closedAt C` | src/L/Coding/Model.lagda.md:2191 | 8 |
| `keyArityAtL c 1` | src/L/Coding/CodeSet.lagda.md:135 | 1 |
| `hasWitnessAt A x` | src/L/Coding/CodeSet.lagda.md:240 | 34 |
| `isCodeAt c w` | src/L/Coding/Powerset.lagda.md:297 | 35 |
| `envOneAt e y` | src/L/Coding/Powerset.lagda.md:128 | 2 |
| `DefinesAt x w v` | src/L/Coding/Powerset.lagda.md:217 | 4 |
| `satGraphAt B x y` | src/L/Coding/Graph.lagda.md:204 | 44 |
| `DefBody w` | src/L/Coding/Powerset.lagda.md:437 | 83 |
| `DefAt u w` | src/L/Coding/Powerset.lagda.md:442 | 166 |
| `LsetGraphAt w b` | src/L/Coding/Sequence.lagda.md:349 | **664** |

The arithmetic closes with **nothing unattributed**:

- 26 = 12 form tags + 8 (`bothTm` twice) + 4 (`fstTm` twice) + 2 (`zeroPay` twice)
- 34 = 8 + 26, 35 = 1 + 34, 83 = 35 + 44 + 4
- 166 = 2 x 83, because `extAt y φ` writes `φ` twice
  (src/L/Coding/Model.lagda.md:662-664)
- 664 = 4 x 166: `StepAt` = 2 x `DefAt` through `extAt`
  (src/L/Coding/Sequence.lagda.md:119-120), `ApproxAt` carries one `Step` and
  `domAt`/`appAt` contribute 0 (src/L/Coding/Sequence.lagda.md:286), and
  `GraphAt` carries `ApproxAt` and one more `Step`
  (src/L/Coding/Sequence.lagda.md:291).

### What the constants ARE

**Two `con` sites are reachable, and only two.** Grep over every module the
census reaches (Model, Shape, CodeSet, Powerset, Graph, Sequence):

1. src/L/Coding/Model.lagda.md:586
   `tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))`
2. src/L/Coding/Shape.lagda.md:179
   `zeroPay = var zero ≐ con (numeralL 0)`

**Every one of the 664 is `numeralL k`.** The other `con` sites in those files
are NOT reachable: `satGraph B` (src/L/Coding/Graph.lagda.md:239) is the
constant-carrier twin of `satGraphAt`, which uses `var` instead
(src/L/Coding/Graph.lagda.md:205); `hasWitness A`
(src/L/Coding/CodeSet.lagda.md:245) is the pinned twin of `hasWitnessAt`; and
`arityNumAtL` (src/L/Coding/CodeSet.lagda.md:186-187) is the only site that
names `ωʟ`, and the attribution above shows it is not in this tree, because
`isCodeAt` is exactly `keyArityAtL` + `hasWitnessAt` and both are accounted for.

**So `Everything.lagda.md:741` does not describe this formula.** It says the
stage condition is said "through `LsetGraphAt` at the constant `ωʟ`". `ωʟ` is
supplied by the CALLER, in the surrounding formula, not by `LsetGraphAt`.
`LsetGraphAt` names no `ωʟ`.

### Do they lie in the stage

Each constant's underlying set is `# k`: `numeralL-fst`,
src/L/Axioms/Numerals.lagda.md:179. The tags are the twelve constructor tags
and the two arity numerals, so `k` runs over 0 to 11
(src/L/Coding/Shape.lagda.md:183-187, src/L/Coding/Model.lagda.md:2182-2189,
`keyArityAtL c 1` at src/L/Coding/Powerset.lagda.md:298, `tagAtL zero 0` at
src/L/Coding/Powerset.lagda.md:129).

**At an ARBITRARY stage `α`: NO.** Nothing in the tree gives
`⟨ # k ∈ˢ Lset α ⟩` for an arbitrary `α`, and the brief's D-10 says stop there.
**That is the stop.**

**At a LIMIT stage: YES, and it is already proved.**
src/L/Coding/Bound.lagda.md:139-140

    num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩

That is EXACTLY the condition, at exactly the type, delivered by
`module Bound (lam) (ordλ) (succλ) (∅∈λ)`
(src/L/Coding/Bound.lagda.md:130-132). The probe wires it in and it typechecks
(agents/tasks/LJ-1-498/Probe498.agda:204-214).

## THE INSTRUMENT IS NOT `mapFo`

**The brief and `[LJ-1.494]` both frame the wall as a missing map, and that
frame is wrong.** `[LJ-1.494]` is right that no total `CS.S → SL` exists
(agents/tasks/LJ-1-494/lj-1.494-report.md:367). It is the wrong question.

`mapFo` wants a TOTAL map because it moves every constant. The tree has an
instrument for a PARTIAL one: `Relabel`, src/FOL/Manipulation/Bounding.lagda.md:146.
Its own prose at src/FOL/Manipulation/Bounding.lagda.md:135-138 names THIS
instance in words:

> the intended instance the source is the model's carrier, the target is a stage's
> member type, the world is the hierarchy, and the equation is the fact that a
> member of a stage, viewed as a set, is the set it was.

`SL` IS a stage's member type: `SM = Σ[ x ∈ S ] (x ∈ᶜ M)`
(src/FOL/Absoluteness.lagda.md:64-65) at `M = λ x → x ∈ˢ Lset α`
(src/L/Hull.lagda.md:153-156). So the instance is the one `L.Absoluteness`
already writes for constructibility (src/L/Absoluteness.lagda.md:90-91), with
"lies in this stage" in place of "is constructible".

**BUILT AND GREEN** (agents/tasks/LJ-1-498/Probe498.agda:140-149):

    module ToStage = Relabel {K = CS.S} {K' = SL} {W = S}
      fst fst P (λ c p → fst c , p) (λ c p → refl)

    graphFo-at-SL-given : {n : ℕ} (w b : Fin n) → Wall w b → Formula SL n
    graphFo-at-SL-given w b cert = ToStage.liftFo (LsetGraphAt w b) cert

So **the obligation is one certificate away, and not one map away.**

## THE WALL, IN ONE LINE OF AGDA

agents/tasks/LJ-1-498/Probe498.agda:144-145

    Wall : {n : ℕ} → Fin n → Fin n → Type (ℓ-suc ℓ)
    Wall w b = BoundedFo P (LsetGraphAt w b)

`BoundedFo` is the per-occurrence certificate
(src/FOL/Manipulation/Bounding.lagda.md:63-75). At this formula it is a nested
tuple with **664 leaves**, and by the census EVERY leaf is `P (numeralL k)`.

## HOW MUCH OF THE CERTIFICATE IS DISCHARGED

`NUM = (k : ℕ) → P (numeralL k)` is the whole of it
(agents/tasks/LJ-1-498/Probe498.agda:162-163), and `num∈λ` supplies `NUM` at a
limit stage with no new hypothesis (Probe498.agda:213-214).

**8 of the 664 leaves are discharged and green**: `bd-closedAt`,
Probe498.agda:185-196, twelve lines, from `NUM` alone. `closed-cert`
(Probe498.agda:217-218) shows it is unconditional at a limit stage.

**PRICE FOR THE REST, MEASURED NOT GUESSED.** 8 leaves cost 12 lines of tuple
plus 4 helper lemmas of 3 lines each (Probe498.agda:165-183). The residue is
656 leaves in five pieces: `shapedAt` 26, `keyArityAtL` 1, `envOneAt` 2,
`DefinesAt` 4, `satGraphAt` 44, then the composition to 664, which is pure
`extAt` doubling and costs nothing new. **At the measured rate that is about 80
to 110 lines.**

## THE SHAPE THAT RESISTED, AND IT WILL RESIST THE NEXT TASK TOO

**A certificate lemma stated at a VARIABLE payload does not apply.**
`binShapeAt C k rel` takes the payload `rel` as an argument
(src/L/Coding/Model.lagda.md:2043). `BoundedFo` pattern matches on the formula,
so it is not injective, and `BoundedFo P rel` never determines `rel`. Agda
leaves an unsolvable metavariable (the `blocked on _rel_845` constraint of the first attempt; that run was
overwritten by the green one, and the shape of the failure is recorded here
rather than in `runs/`).

**The cure, measured here:** write the tuple AT THE COMPOSITE, where the payload
is concrete, and let eta solve the constant-free parts as `_`. The same reason
lets `src/` write `prAtL q u v = liftFo (prAt q u v) _`
(src/L/Coding/Model.lagda.md:123). It applies to every `Fin` argument too, so
`bd-arityTagPairAtL _ _ 2 _ _` does not elaborate either: the leaves go in raw.

## THE MEASUREMENT

Three forced rechecks each, `.agdai` deleted before every run. ONE Agda process,
`GHCRTS=-A64m -I0 -M8g`, the wide caliber, set by the program and untouched. No
heap event.

| | median wall | peak RSS |
|---|---|---|
| W3 alone, the census | **1.59 s** | **394,772,480 B** |
| the full probe, 218 lines | **4.79 s** | **562,610,176 B** |

W3: runs/w3-recheck-1.time, -2, -3 (1.59, 1.59, 1.59).
Full: runs/full-recheck-1.time, -2, -3 (4.74, 4.79, 4.80).

The brief estimated "under 30 seconds of Agda" for W3. Measured 1.59 s. It
estimated about 120 lines for the probe with about 30 for the obligation.
Delivered 218 lines with the obligation NOT delivered; the extra is the census
instrumentation and the `Relabel` instance the brief did not anticipate.

## WHAT THE NEXT BRIEF NEEDS

1. **The stop is at the ARBITRARY stage, not at a limit.** Do not brief
   `graphFo-at-SL` at a variable `α` again. It is false there: `P (numeralL k)`
   has no supplier.
2. **Brief the certificate, not the map.** The obligation is
   `wall : NUM → BoundedFo P (LsetGraphAt w b)`, about 80 to 110 lines, and
   `graphFo-at-SL` then falls out of `ToStage.liftFo`, which is already green
   here.
3. **`num∈λ` is the supplier and it needs `module Bound`'s four arguments**
   (src/L/Coding/Bound.lagda.md:130-132): a limit `lam`, `IsOrd lam`, closure
   under `sucV`, and `∅ ∈ˢ lam`. Whoever owns the condensation leg must say
   whether the stage it works at is such a limit. **If it is not, the whole
   route is dead and this is where it dies.**
4. **`liftFo-correct` is the meaning half and it is NOT done here.**
   src/FOL/Manipulation/Bounding.lagda.md:198-199 gives
   `mapFo up (liftFo φ h) ≡ mapFo proj φ`. This task built the formula, not its
   satisfaction. `AbsL.⊨ᵐ` still has to be met.
5. **C-42 sweep, and it is NOT done here.** `DefAt`
   (src/L/Coding/Powerset.lagda.md:442) carries all 664. Every formula in the
   tree that reaches `DefAt` has the same shape, and the count says how many.
   Nobody has run that sweep and this task did not either.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` **READ.** Line 88 is the precedent for this
  whole shape of task, and its verdict is the same shape as this one:
  > `| LJ-1.30 | PRICE the cure: make consAtL constant-free | GO, ~110 lines | The 16 constants are ALL con (# 0), and # 0 IS the empty set, so the reader goes constant-free IN PLACE. Zero consumer edits |`
  There the census found 16 constants, all one numeral, and the cure was to
  remove them. **That cure does NOT transfer here** (AGENTS.md Boundary): 664
  constants at twelve distinct tags cannot be removed in place, because a tag
  is what a shape reader reads. Re-measured at this site, the cure is to CARRY
  them, not to delete them.
- `archive/dev/JOURNAL-archived.md` **READ.** Line 715:
  > `first-class via `FOL.Absoluteness.Single` + the delivered `Bounding.Relabel`,`
  That is the same pairing this report recommends, already recorded as the
  route. Line 720 records a prior census of 1,688 constants, so census-by-count
  is an established move in this tree and not an invention of this task.
- `archive/dev/JOURNAL.md` **not read.** The two lines the search scored
  (615, 992) are about a constant-free level story under `[LJ-0.4]`, a different
  leg; `JOURNAL-archived.md` carried the `Relabel` record this task needed.
- `archive/dev/DECISIONS-archived.md` **declined.** Read only its head:
  > `**The whole `D` series was ARCHIVED on 2026-08-09**, when the owner opened the`
  A bare `D<n>` is not a rule in force, so it can settle nothing about this task.
- `dev/ARCHIVE.md` **READ.** Line 265 records `L.Rud.OpGraph` as "The operation
  graphs in VARIABLES rather than constants: the constant-to-variable transfer".
  That is the OTHER cure for a constant census, and its row says `[T63]` refuted
  the wall it was built for. **Not applicable here** for the same reason as
  LJ-1.30: this task's constants are tags, and a tag in a variable slot is not
  the same reader.

## LITERATURE USED

- `dev/literature/terms-2026-08.md` **READ.** Line 199:
  > `constant list (`src/FOL/Count.lagda.md:461`).`
  It points at `FOL.Count`, which is where `countFo`'s companions `erase` and
  `constantsFo` live (src/FOL/Count.lagda.md:594-610). That is what made a
  MACHINE census possible instead of a hand reading, and it is why the empty
  case would have been provable by `refl` had the census been empty.
- `dev/literature/glossary-review-2026-08.md` **not used.** Its hits (45, 56,
  65) are translation rows for "relabelling"; this report names no new term, so
  the naming protocol is not engaged.
- `dev/literature/devlin-II5.md` **declined, not read.** This task reads a
  formula's syntax and counts `con` occurrences. No mathematical content of
  Devlin II.5 bears on a syntactic census.
- `dev/literature/truncation-and-selection.md` **declined, not read.** Its
  "constant" hits are weakly-constant maps, an unrelated sense of the word.
- `dev/literature/digest.md` **declined, not read.** No hit for any term of this
  task.
