# LJ-1.56: the closedness transfer, then SatGraphAgree and LeafAgree

Status: PARTIAL, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits:
three semantic fixes in `src/L/Condensation.lagda.md` and the three
probes `src/ProbeLJ156A.agda`, `src/ProbeLJ156Shape.agda`,
`src/ProbeLJ156Cone.agda`. The report is `_build/lj-1.56-report.md`.

## 0. THE LEDGER (live)

| hypothesis | status | what it still needs |
|---|---|---|
| `levelIn` | NOT DISCHARGED | the adequacy chain after the leaf reduction |
| `cover` | NOT DISCHARGED | the adequacy chain plus the least-delta selection |

## 1. THE FIVE STEPS, AS THEY LANDED

| step | status | the term not written |
|---|---|---|
| 1. the eight-frame closedness transfer | **LANDED** (probe) | none; `ClosedAgree` both directions, section 2 |
| 2. the domain transfer | **LANDED** (probe) | none; `DomainAgree` both directions under the site facts, section 3 |
| 3. the shapedness transfer | **PARTIAL** | the twelve-row frame walk of `shapesBS` against `shapes`; the atoms and the cure land, section 4 |
| 4. `SatGraphAgree` | **LANDED** (probe) | none; both directions at the graph frame, section 5 |
| 5. `LeafAgree` | NOT BUILT | the `WitnessAgree` conjunct, which rests on step 3's frame walk, section 6 |

## 2. THE CLOSEDNESS TRANSFER: LANDED

`ClosedAgree` (`ProbeLJ156A:396-481`) proves, at the generic frame and
under the site-fact bundle,

```text
⟨ γ ⊨ closedAt C ⟩ ↔ ⟨ γ ⊨ closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 ⟩
```

both directions, all eight frames. Each row instantiates one generic
frame agreement (`BinFrameAgree`/`UnFrameAgree`,
`ProbeLJ156A:234-333`), and the conjunction threads like `TwelveAgree`.
The frame shape transfers are `BinShapeClosed`/`UnShapeClosed`
(`ProbeLJ156A:63-214`), the bounded `arTagPairBS`/`arTagBS` against the
machine's `arityTagPairAtL`/`arityTagAtL` at the same frames. The
relations transfer pointwise (`BothSameRel`/`OneSameRel` are identity,
since the [LJ-1.55] cure made the bodies definitionally equal;
`OneSuccRel`/`SuccSndRel` differ only by the bounded existential, whose
witness lies in K by the `entryK` site fact).

The frame shape `arTagBS` was itself broken (section 7, fix 1); the
transfer is the cure's consumer test.

## 3. THE DOMAIN TRANSFER: LANDED, AND THE CLAIM TESTED

`DomainAgree` (`ProbeLJ156A:484-521`) proves both directions:

- `out` (`domAt -> domB`) under `entryK` (the entry witnesses lie in K);
- `back` (`domB -> domAt`) under `entryK` plus `domK` (every entry's
  components and every domain element lie in K).

**The claim from `[LJ-1.55]` is MEASURED, not accepted.** `domB -> domAt`
is FALSE at the generic frame: the back direction needs `x in K` for an
arbitrary `x` to apply the bounded bi-implication, and `y in K` for the
entry witness. The generic frame supplies neither (a countermodel: one
entry `pr x y` with `y not in K` and an empty domain satisfies `domB`
and refutes `domAt`). The missing memberships are exactly the `entryK`
and `domK` hypotheses above. The graph frame supplies them through the
site-fact bundle: the satGraph witnesses lie in K (`witK`,
`ProbeLJ156A:679-691`), the table's entries lie in K (`domEntryK`), and
the code set's members lie in K (`domK`). So the transfer is work, not
a wall, exactly as the brief's inference hoped; the memberships are the
bundle's content, not the frame's alone.

## 4. THE SHAPEDNESS TRANSFER: PARTIAL, WITH THE CURE

The atoms land: `TmBranch`/`TmAgree` (`ProbeLJ156A:524-615`) prove the
bounded term shape `isTmBS t A K N0 N1` against the machine's `isTmAt`
term disjuncts, both directions and both branches, under the tag
equations and the payload-in-K site facts. The twelve-row frame walk
of `shapesBS` against `shapes` (the `binFormBS`/`unFormBS` frames and
the disjunction) is NOT built; it is the remaining term of this step.

**The pre-cure story is MEASURED broken.** The delivered `isTmBS` had
only the constant branch (tag 0, payload in the carrier); the machine's
`isTmAt` is a disjunction (constant, or variable with the index in the
arity). `ConstVarDisjoint` (`ProbeLJ156A:617-640`) proves the two
machine branches are disjoint (`pr-inj` on the tag numerals), so a
machine witness in the variable branch has no image in the constant-only
story shape. The cure adds the variable branch (section 7, fix 2).

## 5. SatGraphAgree: LANDED

`SatGraphAgree` (`ProbeLJ156A:649-835`) proves, at the graph
environment `γ : S ^ (8 + n)`,

```text
⟨ γ ⊨ SatGraphB.satGraphB w K N0 .. N11 t0 t1 ⟩
  ↔ ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
```

both directions, composing `TwelveAgree` (a parameter), `ClosedAgree`,
`DomainAgree`, the pin/appAt identities (the formulas are the same on
both sides) and the three existential-frame transfers (machine to story
needs `witK`; story to machine keeps the bounded witnesses). This is
the consumer test of the `satGraphB` slot cure (section 7, fix 3): the
closedness now reads the code set at slot 2, matching the machine's
`closedAt Ci`.

## 6. LeafAgree: NOT BUILT

`LeafAgree` is the conjunction `KeyAgree x WitnessAgree x SatGraphAgree
x DefinesAgree`, one conjunction deep. `KeyAgree` and `DefinesAgree`
are delivered (`[LJ-1.54]`, `ProbeLJ154A`); `SatGraphAgree` is section
5. The missing conjunct is `WitnessAgree`
(`hasWitnessBS w c K Ns ↔ hasWitnessAt w c`), whose pieces are the
membership atom (identity), `ClosedAgree` (section 2), the bounded
existential frame, and `ShapedAgree` (section 4's frame walk). The
stated term not written is the `shapesBS ↔ shapes` twelve-row walk.

## 7. THE THREE MASTER FIXES (all MEASURED, all in `L.Condensation`)

Each is a delivered definition with zero semantic consumers that the
transfers' first consumption convicted (the C-35 class):

1. **`arTagBS`** (`Condensation:1502-1514`): the bounded unary shape at
   the 3-deep closedness frame carried an extra existential and pinned
   the payload instead of the tag. Cured to two existentials with the
   tag pin `var zero ≐ var (suc^5 tag)`; `Δ₀-arTagBS` updated. The
   corrected reading transfers to the machine's `arityTagAtL` in both
   directions (`ProbeLJ156Shape`), and the delivered reading cannot
   (its third existential yields `t = pr w z` where the machine needs
   `z = pr #k a`). The sibling `arTagPairBS` was verified CORRECT (its
   tag pin is `var (suc zero)`).
2. **`isTmBS`/`bothTmBS`/`fstTmBS`** (`Condensation:1622-1656`): added
   the variable branch (tag 1, payload in the arity slot), matching the
   machine's `isTmAt`; the `N1` slot is the tag-1 column. The `Δ₀`
   witnesses add `δ-∨`. All formulas stay constant-free, so `countFo ≡ 0`
   and the erase route are untouched.
3. **`satGraphB`** (`Condensation:2275-2312`): the closedness read slot
   0 (the pinned carrier) where the machine's `satGraphAt` reads slot 2
   (the code set). Cured to `closedBS (suc (suc zero))`; `Δ₀-satGraphB`
   updated. `SatGraphAgree` (section 5) is its consumer test.

No other master is touched. `L.BoundedSubset` re-checks green; the
consumer signature surface (`DefBodyB`, `Δ₀-DefBodyB`) is unchanged.

## 8. THE RATES

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved aside
before EVERY run), dependencies warm, one process, quiet machine.
Three completed runs each; no heap exhaustion, no interruption.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` (whole, cold) | 54.85 / 54.12 / 55.34 | 54.77 | 1.22 (2.2 pc) | 4,640 | 0.01181 |
| `ProbeLJ156A` (cold) | 27.48 / 26.78 / 27.41 | 27.22 | 0.70 (2.6 pc) | 712 | 0.0382 |
| `ProbeLJ156Shape` (cold) | 1.67 / 1.66 / 1.70 | 1.68 | 0.04 (2.4 pc) | 95 | 0.0177 |
| `ProbeLJ156Cone` (import cone) | 1.34 / 1.36 / 1.39 | 1.36 | 0.05 (3.7 pc) | 2 | n/a |

The whole-file rate of `L.Condensation` is 0.01181 s per line, under
the DD24 live bar 0.012716 (`dev/ledger.toml`). The three fixes are
line-neutral-ish (4,632 to 4,640 in-fence lines) and the mean is
54.77 s against `[LJ-1.55]`'s same-day-ish 58.08 s; the direction is
consistent with removing one existential from `arTagBS`, but the two
days are not one caliber, so I do not claim a cure-price.

The marginal rate of `ProbeLJ156A`'s content is (27.22 - 1.36) / 712 =
0.0363 s per line, the instantiation class (P-m): the `SatGraphAgree`
parameter bundle and the written `closedBS` formula types normalize the
satisfaction at the concrete graph frame, the same class `[LJ-1.55]`
measured for `TwelveAgree` (0.0136) at a heavier instantiation. The
shape probe's marginal is (1.68 - 1.36) / 95 = 0.0034 s per line, the
parameterized class, consistent with `[LJ-1.54]`'s leaf atoms.

## 9. THE DD4 ANSWER

The transfers are TEMPLATE content: `ClosedAgree`, `DomainAgree`,
`BinFrameAgree`/`UnFrameAgree`, `TmAgree` and `SatGraphAgree` all state
slots, environments and site facts as module parameters, with no
concrete carrier in any type. What the J tower inherits is the whole
generic layer: the frame agreements, the site-fact bundle shape, and
the `SatGraphAgree` composition, instantiated at its own slots. The
per-tower residue is the slot layout of the graph frame and the leg-D
facts, exactly as `[LJ-1.55]` predicted. The three fixes are per-tower
residue of the L tower's bounded restatement; they are one-slot or
one-branch corrections, not re-proofs.

## 10. THE CONVERGENCE ANSWER

CLOSING, with the obligation's shape changed. This dispatch did not
rename an obligation: it built the closedness transfer (both
directions, eight frames), the domain transfer (both directions, with
the `[LJ-1.55]` claim measured), the shapedness atoms after a cure, and
`SatGraphAgree` (both directions). The remaining unbuilt term is one
walk: the `shapesBS ↔ shapes` twelve-row frame walk, then the
`WitnessAgree` and `LeafAgree` conjunctions. Each dispatch since the
agreements gained a consumer has convicted one more delivered-but-
untested definition (the row semantics: `oneSameB`; the closedness
shape: `arTagBS`; the term shape: `isTmBS`; the graph body:
`satGraphB`). The defect count is finite and each cure is mechanical;
the pattern is C-35's predicted first-audit harvest, not re-proofs. The
next dispatch is well-defined and priced by shape: the twelve-row
shapedness walk, then `WitnessAgree`, then `LeafAgree`.

## 11. ARCHIVE USED

- `_build/lj-1.55-report.md`, read WHOLE. Took the slot finding and the
  `oneSameB` cure, the `TwelveAgree` composition, and the `domB`
  claim (`:114-122`) this dispatch tested.
- `src/ProbeLJ155A.agda`, `src/ProbeLJ155B.agda`,
  `src/ProbeLJ155C.agda`, read WHOLE. Took the frame conventions, the
  site-fact bundle shape and the `DomAgree.out` skeleton.
- `_build/lj-1.54-report.md` section 1 and `src/ProbeLJ154A.agda`,
  read WHOLE. Took the four atoms and the `WitnessAgree` decomposition.
- `_build/lj-1.53-report.md` and `_build/lj-1.52-report.md`, read
  WHOLE. Took the wall-1 statement (the machine-side leaf reduction)
  and the `SatGraphAgree`/`LeafAgree` decomposition.
- `_build/gch-design-audit.md`, read the two-spelling section
  (`:300-380`). Took the zero-consumer finding (C-35) that the
  transfers' first consumption convicted.
- `src/L/Coding/Model.lagda.md`, read the closedness, domain and shape
  readers (`:260-310`, `:700-790`, `:2043-2240`).
- `src/L/Coding/Shape.lagda.md`, read the term and shape predicates
  (`:109-250`, `:360-480`). Took `isTmAt`'s disjunction, which exposed
  the `isTmBS` gap.
- `src/L/Coding/Graph.lagda.md`, read `twelveAt`/`satGraphAt`
  (`:94-203`). Took the witness roles (code set at slot 2, table at
  slot 1, carrier at slot 0), which exposed the `satGraphB` slot bug.
- `src/L/Coding/CodeSet.lagda.md`, read `hasWitnessAt` and the graph
  consumers (`:240-245`, `:340-400`).
- `src/L/Coding/Powerset.lagda.md`, read `DefBody`/`DefinesAt`
  (`:217-218`, `:297-298`, `:437-443`).
- `src/L/BoundedSubset.lagda.md`, read the `DefBodyB` consumer
  (`:25-130`). WHY NOT more: the fix does not change any signature.
- `archive/rud-route/`, SHAPE only, per the brief.
- `dev/LESSONS.md`, read P-u, P-v, C-34, C-35, C-36, C-37, D-30
  (`:2908-3348`). Took the cure-or-wall and write-the-term actions.

## 12. LITERATURE USED

- `dev/literature/devlin-II5.md` Step C (`:209-257`) and
  `_build/literature/dev2.txt:1372-1385`, read for the leaf's
  mathematics. Devlin assumes the Σ₀ matrix is absolute for transitive
  carriers ("for free", Step C requirement 3) where this tree proves a
  bounded/unbounded transfer under explicit membership site facts; the
  difference is that this project's bound K is a slot whose closure
  facts must be supplied, not an ambient absoluteness.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids
  re-checking.
