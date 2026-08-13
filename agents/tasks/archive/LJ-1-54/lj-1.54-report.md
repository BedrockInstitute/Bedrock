# LJ-1.54: the last unbuilt term, then discharge `levelIn` and `cover`

Status: PARTIAL. Written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries two edits:
`src/L/BoundedSubset.lagda.md` (mine) and `dev/PLAN.md` (the
orchestrator's dispatch rows, not mine, not touched).

## 0. THE LEDGER (live)

| hypothesis | status | what it still needs |
|---|---|---|
| `levelIn` | NOT DISCHARGED | the adequacy chain of section 1.2 |
| `cover` | NOT DISCHARGED | the adequacy chain plus the least-delta selection of section 1.2 |

The one unbuilt term (the `DefBodyB`/`DefBody` leaf adequacy) is
PARTIALLY built: four of its atoms are machine-checked in
`src/ProbeLJ154A.agda`, and the composition and the two remaining
atoms are stated as the terms not written (C-36), section 1.1.

Wall 2 (the parameter-to-code relabelling) is PLACED and green in the
master. The `hotel` rename is done. Sections 2 and 3.

## 1. THE LEAF REDUCTION

The residual from [LJ-1.53] is the two-way satisfaction transfer

```text
⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBodyB w K N0 … N11 t0 t1 ⟩
  ↔ ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} w ⟩
```

at arity `8 + n`, under the site facts. The three conjuncts of
`DefBodyB` and `DefBody` decompose it:

1. `isCodeBS c w K Ns ↔ isCodeAt c w` (the key-arity part and the
   witness part),
2. `SatGraphB.satGraphB w K Ns ts ↔ satGraphAt (sh3 w) 1 0` (the
   twelve rows compose),
3. `DefinesBS x w v K N0 ↔ DefinesAt x w v`.

### 1.1 What is built (green in `src/ProbeLJ154A.agda`)

1. `TagAgree` (`ProbeLJ154A:61`): `tagBS s tag x K ↔ tagAtL s k x` at
   any environment, under the tag-slot-equals-numeral fact and the
   numeral-in-K fact. This is the atom under `envOneBndS` and
   `keyArBS`.
2. `KeyAgree` (`ProbeLJ154A:97`): `keyArBS c tag K ↔ keyArityAtL c k`
   under the tag fact, the numeral-in-K fact, and the
   key-value-in-K fact. This is the first conjunct of `isCodeBS ↔
   isCodeAt`.
3. `EnvOneAgree` (`ProbeLJ154A:154`): `envOneBndS v K N0 ↔ envOneAt
   zero (suc zero)` at the two-slot environment, via `TagAgree` and
   the delivered `extAtB→extAt`/`extAt→extAtB` frames
   (`src/L/Condensation.lagda.md:2496-2510`).
4. `DefinesAgree` (`ProbeLJ154A:192`): `DefinesBS x w v K N0 ↔
   DefinesAt x w v`, via `EnvOneAgree` and the same frames. This is
   the third conjunct of the leaf adequacy.

The probe typechecks at 1.92 / 1.99 / 2.03 s user, three cold runs,
one caliber (section 4). Its content is about 200 non-comment lines.

### 1.2 The terms not written (C-36)

1. `WitnessAgree`: `hasWitnessBS w c K Ns ↔ hasWitnessAt w c`, the
   second conjunct of `isCodeBS ↔ isCodeAt`. Its pieces are
   `closedBS C K N2..N11 ↔ closedAt C` (eight shape frames; each
   frame is `UnaryShape`/`BinaryShape` composed with an `appAt` or
   `sucAtL` relation that is the same formula on both sides), the
   shapedness transfer, and the `domB ↔ domAt` transfer. None is a
   new idea; all are the delivered shape agreements' shape
   (`src/L/Condensation.lagda.md:2512-2702`).
2. `TwelveAgree`: `SatGraphB.twelveB ↔ twelveAt Ci Ti Bi` at the
   twelve-frame environment (arity `11 + n`). **The twelve row
   agreements do not instantiate directly at this frame.** The
   agreements' convention has the bound K at environment slot 0 and
   the row slots at `suc C`, `suc T`, `suc B` (for example
   `BotAgree` at `src/L/Condensation.lagda.md:2704-2743`, `MemAgree`
   at `:4101`). The `twelveB` frame has B at slot 0, T at 1, C at 2,
   and K at `suc^6 K` (`SatGraphB` at `:2211-2310`). The instantiation
   needs `suc B = zero`, which has no solution. The composition needs
   a re-indexing layer between the two slot conventions before the
   twelve agreements compose. This is a measured finding of this
   dispatch, not an estimate.
3. `SatGraphAgree`: `SatGraphB.satGraphB ↔ satGraphAt (sh3 w) 1 0`,
   composing `TwelveAgree` with the closedness, domain, pin-equality
   and the three existential-frame transfers (with the in-K facts).
4. `LeafAgree`: the conjunction of `IsCodeAgree = KeyAgree ×
   WitnessAgree`, `SatGraphAgree`, and `DefinesAgree` (built). This is
   the residual term itself, one conjunction deep.

After the leaf reduction, the consumers need the class-carrier chain
of [LJ-1.52]: `StepAgree`/`ApproxAgree` (both directions) at the graph
environment, `GraphAgree` (`graphBndAt ↔ LsetGraphAt`), the `Adeq`
form and its two-way decode, and the stage truth of `Adeq m` (the
graph-construction direction through `Lset-defines`). Then `levelIn`
runs through `Co.elem-down` (placed), the `IsoInv` transfer to `πM`,
and the decode at the transitive collapse image, giving
`π (Lset m) = Lset (π m)`. `cover` adds the least-delta Skolem
selection and the level-membership relation in the hull's language.
None of that chain is built in this dispatch: it rests on the leaf
reduction.

## 2. THE TWO PLACEMENTS

**DONE, both green in the master.**

1. The canonical code at the hull: `CanonCode` instantiated at
   `CC.count`/`CC.count-inj` and the hull's own well-order, giving the
   code function `hedF` and its spec. The fibre coercion between the
   hull-member type and `⟪ M ⟫` is `V.Presentation.fiber`, applied
   with an explicit shared pattern so the opaque `⟪ M ⟫` does not
   leave a metavariable.
2. The ElemDown wiring: `HullElemDown.WithCode` at the hull's stage,
   and `Co.elem-down : DR54.ElemDown` for `DR54 = DownReflect lam
   ordλ UK.X UK.X⊆Lλ UK.∅∈λ`.

The placed modules are the probe's wall-2 content verbatim, with two
adaptations. `HullElemDown`'s code function is a named inner module
`WithCode` (`BoundedSubset:676`) instead of the probe's anonymous
module, because the probe never instantiated the anonymous form. The
`CloseSem` name clash with the file's `CS` alias is renamed to
`CseM`/`CseL`.

Locations: `CanonCode` at `BoundedSubset:463`, `CloseSyntax` at
`:506`, `CloseSem` at `:592`, `HullElemDown` at `:667`, the
instantiation in `Co` at `:1544-1562`, `elem-down` at `:1567`.

## 3. THE `hotel` RENAME

RENAMED to `absorbs-subset` at `src/L/BoundedSubset.lagda.md:1363`
(was `hotel` at `:1047` before this dispatch's insertion).
The stage absorbs its subset back into itself: `Lset α ∪ ⁅ x ⁆s`
injects into `Lset α` when `x ⊆ Lset α`. The composite with
`stage-card-upper` is the injection into `⟪ α ⟫` that `code-inj`
consumes at `:1529`. The theorem it feeds is untouched.

## 4. MEASUREMENTS

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process, quiet
machine. Every figure is three completed runs; no heap exhaustion, no
interruption.

| module | runs, user s | mean | spread | in-fence lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.BoundedSubset` (whole, cold) | 14.12 / 14.01 / 14.30 | 14.14 | 0.29 (2.1 pc) | 1,408 | 0.01004 |
| `L.BoundedSubset` import cone (warm) | 2.83 / 2.83 / 2.67 | 2.78 | 0.16 (5.8 pc) | 2 | n/a |
| `ProbeLJ154A` (leaf atoms, cold) | 1.92 / 1.99 / 2.03 | 1.98 | 0.11 (5.6 pc) | 200 | n/a |
| `ProbeLJ154A` import cone (warm) | 1.74 / 1.73 / 1.69 | 1.72 | 0.05 (2.9 pc) | 2 | n/a |

The whole-file rate of `BoundedSubset` is 0.01004 s per line, under
the DD24 live bar 0.012716 (`dev/ledger.toml:2590` times `:2810`).
The content rate (whole minus cone) is (14.14 - 2.78) / 1408 =
0.00807 s per line. The leaf atoms' marginal is (1.98 - 1.72) / 200 =
0.0013 s per line, the parameterized class at its cheapest, consistent
with the row-agreement atoms of [LJ-1.34-R]. The wall-2 placement
adds 307 in-fence lines; the
whole-file delta from the [LJ-1.51] baseline (11.09 s mean, same
caliber, same file, `_build/lj-1.51-report.md:35`) is 3.05 s, which
is 0.0099 s per line for the added content; the baseline is from a
different day, so the marginal is an estimate, not a price. The
probe-measured marginal of the same content (`ProbeLJ153A`,
0.790 s over 240 lines) is 0.0033 s per line, the parameterized
class.

The cone grew from the [LJ-1.51] 1.52 s to 2.78 s. The growth is the
placed content's interface, not content cost.

## 5. DD4 SPLIT

- Wall 2 (the placement): TEMPLATE. `CanonCode`, `CloseSyntax` and
  `CloseSem` mention no L Def syntax in any type. `HullElemDown` is
  generic in the `TermAlgebra` hull and its canonical-code function.
  The J tower instantiates the same modules with its own hull, its own
  codes and its own well-order.
- The leaf reduction: DEF-side at its core. `DefBodyB` and `DefBody`
  are per-tower instantiations of the bounded/machine description
  templates. The atoms of section 1.1 are template-shaped (they name
  only slots, the numerals and the frame transfers), but their
  instantiation at the leaf carries the per-tower slot layout. The
  twelve-row composition and its re-indexing are per-tower content.
- `levelIn` and `cover`: DEF-side, as D-26 predicts; they key on the
  `Lset` construction and its per-tower decode.

## 6. WHAT I AM NOT SURE OF

1. The `TwelveAgree` re-indexing has no price. The slot-convention
   mismatch is measured (section 1.2), but the re-indexing layer
   between the row agreements' convention and the `twelveB` frame is
   not built, so its seconds and lines are unknown.
2. The `WitnessAgree` pieces (closedness, shapedness, domain) are
   priced by shape only. Their frame relations are same-formula
   identities on one side, but the frame transfers carry site-fact
   plumbing that the atoms of section 1.1 did not exercise.
3. The placed `elem-down` has no consumer yet (C-35). Its first
   consumer is the `levelIn` discharge, which is not built.
4. `src/Everything.lagda.md` was NOT re-typechecked (the twelve-minute
   gate). `L.BoundedSubset`'s top-level signature is unchanged; the
   added modules are new content, so the bare import at
   `Everything:371` cannot break. The consumer probes `ProbeLJ152A`
   and `ProbeLJ152B` are re-checked green.
5. The `L.BoundedSubset` marginal estimate (0.0099 s per line) mixes
   two days of machine drift. The cone-only comparison (2.78 vs 1.52)
   shows interface growth; the content delta is contaminated.

## 7. ARCHIVE USED

- `_build/lj-1.53-report.md`, read WHOLE. Took the wall ledger
  (`:13-20`), the wall-2 placement note (`:28-38`), the wall-1
  residual statement (`:74-88`), the wall-3 route (`:90-118`), the
  measurements (`:120-145`).
- `src/ProbeLJ153A.agda`, read WHOLE. The wall-2 placement is its
  transplant (`CanonCode` `:57-94`, `CloseSyntax` `:102-186`,
  `CloseSem` `:190-263`, `HullElemDown` `:266-365`).
- `src/ProbeDD25H2.agda`, read WHOLE (the `EraseTransfer` leaf).
- `_build/lj-1.52-report.md`, read WHOLE. Took the
  `StepAgree`/`ApproxAgree`/`GraphAgree` decomposition (`:29-60`) and
  the `Adeq`-form statement (`:18-27`).
- `_build/lj-1.51-report.md`, read WHOLE. Took the `levelIn`/`cover`
  term structures (`:122-146`) and the `BoundedSubset` baseline
  (`:35`).
- `_build/lj-1.49-report.md`, read WHOLE. Took the residue naming
  (`:31-63`) and the `ElemDown` structure (`:81-99`).
- `_build/lj-1.48-report.md`, read WHOLE. Took the measured skeleton
  and the class split (`:126-170`).
- `src/L/Condensation.lagda.md`, read the row agreements
  (`:2496-5071`), `DefBodyB`/`SatGraphB` (`:2211-2360`), the frames
  (`:2496-2510`), `keyArBS`/`tagBS`/`envOneBndS`/`DefinesBS`
  (`:1463-1760`).
- `src/L/BoundedSubset.lagda.md`, read WHOLE (the placement sites and
  the `Co` consumer).
- `src/L/Hull.lagda.md`, read `AtStage`/`AtM`/`Hull`/`hull-closed`
  (`:148-425`).
- `src/L/Coding/Sequence.lagda.md`, read `StepAt`/`ApproxAt`/
  `LsetGraphAt` (`:119-354`); `src/L/Coding/Graph.lagda.md`, read
  `satGraphAt` (`:191-240`); `src/L/Coding/Powerset.lagda.md`, read
  `DefBody`/`isCodeAt`/`DefinesAt`/`envOneAt` (`:217-310`,
  `:437-443`); `src/L/Coding/Model.lagda.md`, read `tagAtL`/`prAtL`/
  `domAt` (`:118-131`, `:278-300`, `:585-595`); `src/L/Coding/
  CodeSet.lagda.md`, read `keyArityAtL` (`:135-148`).
- `src/L/Hierarchy.lagda.md`, read `Lset-only`/`Lset-defines`
  (`:320-355`, `:640-655`).
- `src/ProbeLJ152A.agda`, `src/ProbeLJ152B.agda`, read WHOLE (the
  `GraphAgree` chain).
- `dev/ledger.toml`, the DD24 bar (`:2590`, `:2810`) and the cone
  note (`:2580-2586`).
- `dev/PLAN.md`, read the dispatch rows only. WHY NOT more: the
  working-tree edit is the orchestrator's LJ-1.52/LJ-1.53 rows, not
  mine.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385`, Devlin 5.5's proof, read
  for the collapse route. TOOK: the hull is taken of `L_α ∪ {x}`, the
  condensation is asserted, and Devlin ASSUMES the Sigma-1 level-hood
  statement is absolute at transitive carriers and that the collapse
  preserves first-order truth; the formal proof must supply the
  satisfaction transfer.
- `dev/literature/devlin-II5.md:209-257` (Step C), read for the
  level-hood strength requirement (Sigma-1 with a bounded witness).
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids
  re-checking.

## 9. THE CONVERGENCE ANSWER

**Converging, more slowly than the brief hoped.** Wall 2 is placed and
green in the master, and the rename is done. The leaf reduction has
four machine-checked atoms; its composition and two remaining atoms
are stated with the exact shape. `levelIn` and `cover` are NOT
discharged: each rests on the leaf reduction's completion and the
class-carrier chain of section 1.2, none of which is built. The next
dispatch can either fund the remaining atoms (WitnessAgree,
TwelveAgree, SatGraphAgree) or stop at the re-indexing finding.
