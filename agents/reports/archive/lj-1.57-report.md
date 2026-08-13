# LJ-1.57: the shapedness walk, then WitnessAgree, LeafAgree, and the two hypotheses

Status: COMPLETE, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries this dispatch's edits: the
probes `src/ProbeLJ157A.agda` (and cone) and this report. No master is
touched: no cure was needed, so no master edit exists.

## 0. THE LEDGER (live)

| hypothesis | status | what it still needs |
|---|---|---|
| `levelIn` | NOT DISCHARGED | see section 8 |
| `cover` | NOT DISCHARGED | see section 8 |

| step | status | the term not written |
|---|---|---|
| 1. the twelve-row shapedness walk | **LANDED** (probe) | none |
| 2. `WitnessAgree` | **LANDED** (probe) | none |
| 3. `LeafAgree` | **LANDED** (probe) | none |

## 1. THE SHAPEDNESS WALK

**LANDED (probe), both directions, all twelve rows.** `ShapesAgree`
(`src/ProbeLJ157A.agda`, section 3) proves

```text
⟨ γ ⊨ shapes A ⟩ ↔ ⟨ γ ⊨ shapesBS A K N0..N11 ⟩
```

at the walk frame `γ : S ^ (1 + n)`, pointwise under the membership of
the frame's code in the code set (a value parameter, since the walk
frame has no code-set slot). Each row instantiates one frame agreement
(`BinFormAgree`/`UnFormAgree`, section 1) against the machine's
`binForm`/`unForm` at the same frame; the arTag transfers are
ProbeLJ156A's `BinShapeClosed`/`UnShapeClosed`, the term shapes are
`TmAgree`, the rows with `⊤̇` relations are identities, and rows 6/7
transfer the N0-slot pin against the machine's constant zero under the
N0-holds-numeral-0 site fact. No new atom was needed. The walk is the
consumer test of the [LJ-1.56] `isTmBS` cure at the shape frame: the
variable branch is exercised by rows 0/1 and 10/11 in both directions.

## 2. ShapedAgree AND WitnessAgree

**LANDED (probe), both directions.** `ShapedAgree` (probe section 4)

```text
⟨ γ ⊨ shapedAt C A ⟩ ↔ ⟨ γ ⊨ shapedBS C A K N0..N11 ⟩
```

as the forall-in wrapper around the section-1 walk, under the
code-set-site facts (`codesK`/`unCodesK` with `c ∈ C`). `WitnessAgree`
proves

```text
⟨ γ ⊨ hasWitnessAt A x ⟩ ↔ ⟨ γ ⊨ hasWitnessBS A x K N0..N11 ⟩
```

composing the membership atom (identity), the [LJ-1.56] `ClosedAgree`
at the witness frame (C = the witness, K and the tags suc-lifted), the
bounded existential frame (`witK` supplies the witness-in-K for
machine -> story) and `ShapedAgree`. The membership facts are
functions of the witness, because the witness is bound inside the
existential.

## 3. LeafAgree

**LANDED (probe), both directions.** `LeafAgree` (probe section 5)
the leaf adequacy itself,

```text
⟨ γ ⊨ DefBody {5 + n} w ⟩ ↔ ⟨ γ ⊨ DefBodyB w K N0..N11 t0 t1 ⟩
```

at the leaf environment `γ : S ^ (8 + n)`, one conjunction deep:
`isCodeBS ↔ isCodeAt` (KeyAgree x WitnessAgree), `SatGraphB.satGraphB
↔ satGraphAt (sh3 w) 1 0` (ProbeLJ156A's SatGraphAgree, whose
twelve-row composition enters as parameters), and `DefinesBS ↔
DefinesAt` (ProbeLJ154A's DefinesAgree). The composition is
conjunction threading; the parameter bundle is the leaf site facts,
the same class as the [LJ-1.56] SatGraphAgree bundle.

## 4. CURES: NONE

No delivered definition was convicted this round. The walk proved
`shapesBS A K N0..N11 ↔ shapes A` in both directions against the
machine's imported `shapes`, so the delivered reading holds at its
first consumer. The four convictions of `[LJ-1.56]` (`oneSameB`,
`arTagBS`, `isTmBS`, `satGraphB`) are exercised again by this dispatch
and hold. The one design note: the walk states the code-set membership
as a pointwise hypothesis (`c ∈ C` for the frame's code) with the code
set a module VALUE parameter, because the walk frame has no code-set
slot; this is the price of the frame's shape, and it is still
module-parameterized (P-h).

## 5. NEGATIVES

The only negative is that `levelIn` and `cover` are not discharged;
its deciding claim is that the post-leaf chain (section 8) is unbuilt.
That is **MEASURED**: the chain's pieces do not exist in the tree, and
the probe stops at the leaf. No mathematical claim was refuted this
round, so there is no inferred negative.

## 6. THE RATES

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process, quiet
machine. Three completed runs each; no heap exhaustion, no
interruption.

| module | runs, user s | mean | spread | content lines | rate |
|---|---:|---:|---:|---:|---:|
| `ProbeLJ157A` (whole, cold) | 68.31 / 69.07 / 67.25 | 68.21 | 1.82 (2.7 pc) | 884 | 0.0772 |
| `ProbeLJ157Cone` (import cone) | 1.48 / 1.45 / 1.40 | 1.44 | 0.08 (5.5 pc) | 3 | n/a |

The marginal rate of the new content is (68.21 - 1.44) / 884 =
0.0755 s per line, the instantiation class (P-m): every written type
in the walk and the leaf carries a full formula body (`shapesBS`,
`closedBS`, `shapedBS`, `DefBodyB`) whose satisfaction the elaborator
normalizes at the abstract slots. This is the same class [LJ-1.56]
measured for `SatGraphAgree` (0.0363) at a heavier payload: the walk
is twelve rows, and `WitnessAgree`/`LeafAgree` carry the leaf formulas
whole. The cone is 1.44 s, the same per-invocation interface cost the
[LJ-1.55]/[LJ-1.56] probes measured (1.43/1.36). No master rate moved:
`L.Condensation` is untouched, and `L.BoundedSubset` re-checks green
(warm deps) at 3.2 s. The DD24 live bar 0.012716 binds masters, not
probes; the probe's rate is a content-class certificate, not a bar
reading.

## 8. THE LEDGER NOTES ON levelIn AND cover

**NEITHER IS DISCHARGED.** The budget of this dispatch built the leaf
reduction (sections 1 to 3); the chain from the leaf to `levelIn` and
`cover` is the [LJ-1.52] assembly, still unbuilt, restated here as the
terms not written:

1. `StepAgree`/`ApproxAgree` (both directions) at the graph
   environment, from `LeafAgree` (`[LJ-1.52]` probe B's assembly
   shape, `ProbeLJ152B.agda:53-87`).
2. `GraphAgree` (`graphBndAt ↔ LsetGraphAt`) and the `Adeq` form
   (`ProbeLJ152A.agda:78-104`): the level AT the parameter index,
   witnessed inside K', decoding to `w' = Lset m`.
3. The stage truth of `Adeq m` at ordinal hull members (the graph
   construction direction through `Lset-defines`).
4. The ElemDown wiring (`[LJ-1.53]` wall 2, probe green): the
   `HullElemDown` instance placed in a master, and the arity-1
   `DownReflect.ElemDown` consumer (`BoundedSubset:432-437`).
5. The collapse-of-the-level `π (Lset m) = Lset (π m)` through the
   re-based decode and `IsoInv` (`[LJ-1.53]` section 4).

`levelIn` then runs through `Co.elem-down` and the decode at the
transitive collapse image; `cover` adds the least-delta Skolem
selection. All five are named in the archive; none is a rename of an
obligation this dispatch touched. The leaf is no longer among them.

## 9. THE DD4 ANSWER

**The walk and `LeafAgree` keep the template shape.** Every module
this dispatch wrote (`BinFormAgree`, `UnFormAgree`, the four relation
modules, `ShapesAgree`, `ShapedAgree`, `WitnessAgree`, `LeafAgree`)
states its slots, environments and site facts as module parameters;
no type mentions a concrete carrier. The walk's one deviation is the
code set as a value parameter (section 4), forced by the frame's
shape. What the J tower inherits is the whole generic layer: the two
frame agreements, the twelve-row walk, the forall-in and existential
wrappers, and the leaf composition, instantiated at its own slots and
site facts. The per-tower residue is exactly what [LJ-1.56] predicted:
the slot layout of the graph frame and the leg-D site-fact bundle.

## 10. THE CONVERGENCE ANSWER

**CLOSING.** This dispatch built the single unbuilt term [LJ-1.56]
named (the twelve-row shapedness walk), then `WitnessAgree` and
`LeafAgree`, and convicted nothing new: the walk verified the
delivered `shapesBS` reading in both directions, and the four
[LJ-1.56] cures held under their continued consumption. The obligation
did not get renamed; it shrank from one unbuilt term plus a composition
to the post-leaf assembly of [LJ-1.52] (section 8), which is a
different, downstream shape. The defect harvest predicted by C-35 has
not produced a fifth victim, which is itself evidence the harvest is
closing out.

## 11. ARCHIVE USED

- `_build/lj-1.56-report.md`, read WHOLE. Took the frame conventions
  (slots at the frame, facts at `lookup X γ`), the closedness transfer
  shape, the SatGraphAgree parameter bundle, and the measurement
  protocol.
- `src/ProbeLJ156A.agda`, read WHOLE. Took `BinShapeClosed`/
  `UnShapeClosed`/`TmAgree` (imported and instantiated by the walk),
  `ClosedAgree` (imported by `WitnessAgree`), `DomainAgree` and
  `SatGraphAgree` (imported by `LeafAgree`).
- `src/ProbeLJ156Shape.agda`, read WHOLE. Took the unary
  `arTagBS ↔ arityTagAtL` transfer shape at the 3-deep frame, which
  the walk's unary rows instantiate.
- `src/ProbeLJ156Cone.agda`, read WHOLE. Took the cone file shape and
  the cold-run protocol.
- `_build/lj-1.55-report.md`, read WHOLE, and `src/ProbeLJ155B.agda`,
  read WHOLE. Took the twelve-row instantiation shape and the
  `TwelveAgree` composition (`:452-468`), which enters `LeafAgree` as
  parameters.
- `src/ProbeLJ155C.agda`, read WHOLE. Took the `oneSameB` cure's
  consumer test and the `domB` one-way finding.
- `_build/lj-1.54-report.md` section 1 and `src/ProbeLJ154A.agda`,
  read WHOLE. Took `KeyAgree`/`DefinesAgree` (imported by
  `LeafAgree`) and the `WitnessAgree` decomposition.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, read
  WHOLE. Took the `StepAgree`/`ApproxAgree`/`GraphAgree`/`Adeq`
  assembly and the `levelIn`/`cover` survivor statements, restated in
  section 8.
- `_build/gch-design-audit.md`, read the two-spelling section
  (`:300-380`). Took the zero-consumer finding that motivated the
  walk's consumer-test role.
- `archive/rud-route/`, SHAPE only, per the brief: the directory
  README and the file list, to confirm the condensation content is
  archived and unrereadable as a price. WHY NOT more: `[LJ-1.11]`
  ruled its condensation target classically false, and the brief
  forbids taking a price from it.
- `dev/LESSONS.md`, via `scripts/rules.py --for build`, read the whole
  bundle (P-h, P-k, P-l, P-m, P-n, P-t, P-u, P-v, R-35, R-38, R-40,
  I-5, C-12, C-22, C-31..C-37, D-10, D-26, D-29, D-30). Took P-m
  (the class certificate), P-v (named proofs; no inline-refl pattern
  exists in the probe), and C-22 (the report written incrementally).

## 12. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385` and
  `dev/literature/devlin-II5.md` Step C, one pass each. WHY NOT more:
  `[LJ-1.56]` banked the answer this dispatch needs — Devlin assumes
  the Σ₀ matrix absolute for transitive carriers where this tree
  proves a bounded transfer under explicit membership site facts —
  and the walk changed nothing about it. The errata were NOT
  re-checked. WHY NOT: `[LJ-1.14]` verified that Chapter II section 5
  is not covered, and the brief forbids re-checking.
