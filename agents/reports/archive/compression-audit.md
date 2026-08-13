# Independent compression audit: the Gödel-operations route

Audit of `src/L/Godel/*`, `src/L/WellOrder/{Base,Tree}`, and the load-bearing
survivors (`L.Coding.Model`, `L.Axioms.Basic`) against the claims recorded in
`dev/PLAN.md` row L3.29 and `dev/memos/L3.28-ac-route.md`. Metric: non-blank
lines inside ` ```agda ` fences. For `Name.lagda.md` and `WellOrder/Base.lagda.md`
the analysis uses the committed state (`git show HEAD:<path>`), per the brief.
All line numbers cite the working tree except where noted.

## Verdict summary

The four recorded claims are all real levers but individually overpriced: they
sum to roughly 330-540 lines, not the banked 650-1,050. The total banked range
is nonetheless honest, because unrecorded levers make up the difference: ~160
lines of dead operations/descriptions with zero consumers, ~95-110 lines of
Table/Tower monotonicity duplication (net of the shared frame), and ~50-80
lines of 8-way dispatch ceremony shared by the two chapters. The largest single verified fact is that
Tower's certificate ω-membership conjuncts are redundant (the functionality
conjunct pins the numerals, and the ω witness is literally an unused hypothesis
at `Tower.lagda.md:1305`), worth 70-110 lines. Execute the dead-code deletion
first: it is pure removal, the largest risk-free yield in the route. Realistic
post-compression total: roughly 695-935 lines across all levers ranked below.

## Audited claims

### Claim 1: InL's per-operation stage-module frames, 300-500 lines — real, overstated at the high end

The repetitive frame is real and measurable. The five operation modules and two
staging lemmas each open the same kit:

- `module DefA = DefOf (Lset σ)`, `Atrans`, `module RefA = DefA.Refine` plus the
  per-argument fiber/path pairs (`mX`/`qX` etc.): `SelMem` 409-428 (17 lines),
  `SelEq` 543-562 (17), `Vals` 673-692 (15), `SftD` 1132-1151 (16), `ExtF`
  1559-1583 (22), `tailStage` 1037-1055 (17), `extStage` 1410-1431 (20):
  ~124 non-blank lines total.
- The `chain` lemma (4 lines, identical modulo names) at 439, 572, 695, 800,
  839, 890, 1055, 1163, 1446, 1607: 10 copies, ~40 lines.
- The `defSet≡` extensionality wrapper (`sub₁` PT.rec skeleton, 6-8 lines) at
  140, 193, 251, 447, 580, 703, 807, 1063, 1171, plus the `z`-variable variant
  in `extStage` (~1440) (9-10 sites): ~55-75 lines.

Gross duplicated structure: ~220-235 lines. A stage-parameterized frame
(`Describes`-style, as Definable already does at 108-141) leaves per-operation
bodies behind, so the net saving is ~180-240, not 300-500. Adding the
public-lemma ceremony (`capL`/`cupL`/`diffL`/`selectMemberL`/`selectEqualL`,
1821-1911, 84 lines, of which ~50-55 are instantiation-only) and the
mirror seek pair (`tailSeek` 953-1018 vs `extSeek` 1309-1390, 60+76 lines
sharing ~40 of structure) brings the honest range to ~250-330. The claim is
reachable only by counting the connective blocks (cap/cup/diff, 132-407) and
the climbs (779-932) into the same frame, which is a defensible but generous
reading. Risk: (b) same statements, re-proved under one frame; the frame's
module parameters carry the repo's measured module-application hazard (PLAN's
rule 13), so this is a "measure before landing" item.

### Claim 2: Definable's selection descriptions share a frame, 150-250 — overstated

`selectMemberAt` (414-500, 80 non-blank) and `selectEqualAt` (501-583, 77
non-blank) are structurally parallel, but only ~20-25 lines per block are
shareable: the `F/Ka/Kb` bindings, the singleton-key `memL`, the `-out`/`-in`
shells (10 lines each), and the identical `uL` constructibility chain. The
`readSel`/`fillSel` bodies differ in binder count, shift indices, environment
length, and witness shape (2 recorded values vs 1), so a parameterized
selection frame (tag + operation laws, in the style of Table's `SelLeaf`,
Table.lagda.md:419+) nets ~40-60 lines. Even counting the `-out`/`-in` pairs
across all ten descriptions (roughly 90 lines, of which ~70 are necessary type
statements), the realistic yield is ~50-80. The 150-250 figure is not
supported by the code. Risk: (b).

### Claim 3: Table's 64-case discrimination matrix, 100-150 — overstated; note the attribution error

The route's named 64-case matrix is `codeArity` in Tower (173-303, 131
non-blank), not in Table; Table's parallel object is the `use` matrix inside
`approx-val` (885-1075, 180 non-blank including the 12-line `n1z`..`n6s` helper
block at 883-895). Both matrices are already 1-line-per-clause: the 56
off-diagonals of each are single `Empty.rec (tagNe i j nij …)` lines, which is
the floor for this proof shape under law P-a (explicit-data discrimination).
The diagonal clauses (8 per matrix) are genuine recursive content. The
shrinkable residue is: one copy of the duplicated `n1z..n6z/n1s..n6s` helpers
(15+11 lines, move to Codes next to `tagNe`/`payNe`, Codes.lagda.md:270-277),
one shared row frame for the inter/union diagonal recursion (~6), and, if the
whole 8-way stack is re-indexed by tag (see Finding 5), a much larger but
statement-changing collapse. Matrix-in-isolation: ~20-50 lines, not 100-150.
Risk: (a) for the helper move, (c) for the re-indexing.

### Claim 4: Tower's certificate ω-membership conjuncts, 100-200 — verified, slightly understated at the top

Verified by direct inspection. `mEq` at Tower.lagda.md:1305 is

```agda
mEq : (mv : S) → ⟨ fst mv ∈ˢ ω ⟩ → ⟨ pr x (fst mv) ∈ H ⟩ → fst mv ≡ # m
mEq mv mω ann = sym (Cert-fun g h a γ cert (x , lx) (# m , l#m) mv hm ann)
```

The ω hypothesis `mω` is unused: functionality of the annotation table alone
pins `fst mv ≡ # m`, because both `(x, # m)` and `(x, fst mv)` are members of
`H`. The ω conjuncts therefore add nothing to honesty, and the fill side
produces them only to feed the certificate itself. Removing them touches:
the six `At` formulas (`∈̇ con ωS` conjuncts at 536, 591, 685, 781, 890, 973),
the six `Of` types (542, 598, 692, 791, 897, 982), the six `-out`/`-in`
readers, honesty's seven branch patterns and `mEq` call sites (~20 lines), the
eight `#∈ω m` witnesses in `certClause` (1699, 1708, 1719, 1730, 1744, 1762,
1778, 1793), and the `ωS` package (429-437, 8 lines) that exists only for
them. Realistic net: 70-110 lines, at the low edge of the claim's band.
Risk: (c), but confined to Tower: no module outside Tower consumes
`CertAt`/`CertOf`/`CertShape` (grep of the tree finds only Tower), and the
public `StepAt`/`nameAt`/`step-out`/`step-in` surface is unchanged.

## Independent findings

### F1. Dead operations and descriptions: `product`/`memberGraph` and `productAt`/`memberGraphAt` (158-170 lines, risk (a))

`product` (Operations.lagda.md:153-165) and `memberGraph` (171-196, ~38
non-blank total) have zero consumers anywhere in the tree; `productAt`
(Definable.lagda.md:251-305) and `memberGraphAt` (306-385, ~120 non-blank)
likewise. The PLAN records them as "no consumer yet" at M2, but the route is
complete (NormalForm's `GT` uses the raw Kuratowski pair `⁅_,_⁆`, not
`product`, NormalForm.lagda.md:79-103) and still no consumer exists. This is
undeclared dead weight, the single largest risk-free lever in the route.
Deletion requires recap-prose fixes in `Everything.lagda.md` (413-420) but no
Agda re-proving. ~158-170 lines, risk (a).

### F2. Table/Tower monotonicity duplication: ~130 lines, risk (a)/(b)

Table's `Denote` module proves a private 65-line monotonicity family
(Table.lagda.md:1146-1216, `private` at 1145); Tower's `CertFill` re-proves
the identical family against `D.apxS` (Tower.lagda.md:1559-1630, 66 lines)
and adds the mirror `hMono*` family (1631-1700, 64 lines). The `mono*` copy
is pure duplication: exporting Table's (risk (a)) deletes 66 lines with no
re-proving and no seal reopening (`mono*` uses only `apx-in`/`apx-out`, which
are already exported). The `hMono*` family is `mono*` with the entry map
replaced (`entry` vs `fst ∘ hEntry`, 324-365): one parameterized mono-frame
instantiated twice nets another ~30-45. Neither touches the recursion
assembly, so no measured performance law is engaged. 95-110 lines, risk
(a)/(b).

### F3. Three parallel "finite family over the subterm enumeration" constructions, 30-50 lines, risk (b)/(d)

Table's `domS` (1497-1527, 27 lines), Table's `apxS` (1098-1142, 37 lines),
and Tower's `hS` (324-365, 36 lines) are the same construction: `finSet
(sizeK T) (λ i → mk (subK T i))` plus a `stageFam` bound and `-in`/`-out`
readers, differing only in the entry map and its constructibility witness. A
shared `SubtermFamily (mk : SubK → S) (isl : …)` frame nets ~30-50. The
seals must be preserved (all three are `opaque` at birth per law P-c), and
the frame must not move the recursion values, so the frame covers only the
family and its readers.

### F4. The 8-way dispatch ceremony, 50-80 lines, risk (b)

Table's `Clause-out` br-chain plus `clause₀..₇` injections (730-820, ~88
lines) and Tower's `CertShape-out` br-chain plus `cert₀..₇` injections
(1058-1183, ~122 lines) are the same hand-unrolled right-nested sum peeling
over eight branches. A generic 8-way sum frame (module parameterized by the
eight types, their readers, and the injections) collapses both to ~20-30
lines each plus instantiation: ~50-80 total. This is the same change that
would let the two 64-case matrices dispatch on tag-indexed shapes instead of
nested sums; done that far, it absorbs most of claim 3's unrealized margin
but changes `ClauseOf`/`CertOf` and their consumers (risk (c): `ClauseOf` is
consumed by Table's `use`/`apx-clauseOf` and Tower's `D.approx-val`/`CertOf`
chain). Compatible with law P-a because the tag is carried as explicit data.

### F5. Honesty's continuation frames, 25-40 lines, risk (b)/(d)

`fromInter`/`fromUnion` (Tower 1392-1460) are identical modulo tag and code
equation and collapse into one `fromBin (tg : ℕ) (codeEq : …)`; the
index-recovery blocks in `fromSel`/`fromCon` (`∈#-elim m (fst iv) i∈m`,
`fromℕ'`, `iv→#i`) are a repeated ~8-line subroutine; `fromCompl`/`fromShift`
share their shape. The termination story is untouched: the recursion runs on
`Acc _∈⁺_` (103-124, the accTC/goTC pair), and the frames are non-recursive
continuations, so the transitive-closure descent survives any such refactor.
~25-40 lines.

### F6. The two Step copies: intentional, excluded from the bank

`L.Godel.Step` (362 agda lines) is line-for-line `L.Choice.Step` (362 agda
lines) with one import re-pointed, consumed by nothing except the index
(`Everything.lagda.md:342`). The docs say so explicitly and retire one copy
at M7's rewire. It is the largest single dedupe available (362 lines) but is
outside the compression pass by design; the banked 650-1,050 does not count
it.

### F7. Minor API residue

`capL`/`diffL`/`selectMemberL` (InL 1822-1865) have no external consumers
(only `denoteL` uses them internally); `connex` (Base HEAD 196-199) is used
only inside `prodSWO`; `payNe` (Codes 274-277) only by `tagNe`. Making them
private shrinks the export surface but not the line count. `natSWO`/`unitSWO`
(Base HEAD 218-252) have exactly one consumer, `Name` (HEAD 214), which the
plan's M5a re-cut already removes; Tree (241 lines) is slated for retirement
at M7 by the same ruling.

### The generator question

A meta-function producing formula + readers is not viable in this style:
Agda 2.8 in `--safe --cubical` has no macro system, and the per-description
residue (formula, `read`, `fill`) differs in binder count and witness shape.
The existing `Describes` frame (Definable 108-141) already is the generator
for the extensional identification; the remaining compressible residue is
the selection frame of claim 2 (~40-60). Nothing in the universe/level
discipline forbids the frames proposed above; the binding constraint is the
measured module-application and seal laws (rule 13, P-c), which the frames
respect by not moving recursion values and by keeping the `opaque` seals at
their birth sites.

## Ranked table

Ratings: risk (a) mechanical, (b) re-proving, same statements, (c) statement
or module-surface change, (d) touches a measured performance law or the
termination checker's known traps. Ranked by (lines saved)/(risk).

| # | Lever | Where | Lines saved | Risk | Verdict |
|---|---|---|---|---|---|
| 1 | Delete dead `product`/`memberGraph`/`productAt`/`memberGraphAt` | Operations 153-196; Definable 251-385 | 158-170 | (a) | Compression pass, first |
| 2 | Drop Tower certificate ω-conjuncts | Tower 429-437, 533-1039, 1269-1516, 1699-1793 | 70-110 | (c), internal only | Compression pass |
| 3 | Export Table `Denote.mono*`, delete Tower's `CertFill.mono*` copy | Table 1145-1216; Tower 1559-1630 | 60-66 | (a)/(b) | Compression pass |
| 4 | InL shared stage frame + ceremony + seek mirror | InL 98-128, 409-758, 1035-1539, 1821-1911 | 220-300 | (b), (d) rule 13 | Worth doing now, measured |
| 5 | 8-way dispatch frame (Clause/CertShape) | Table 730-820; Tower 1058-1183 | 50-80 | (b), (c) if tag-indexed | Compression pass |
| 6 | Definable selection frame | Definable 414-583 | 40-60 | (b) | Compression pass |
| 7 | Shared subterm-family frame (domS/apxS/hS) | Table 1098-1142, 1497-1527; Tower 324-365 | 30-50 | (b), (d) P-c seals | Compression pass |
| 8 | `hMono*` via shared mono-frame | Tower 1631-1700 | 30-45 | (b) | Compression pass |
| 9 | Honesty continuation frames (fromBin, index recovery) | Tower 1319-1500 | 25-40 | (b), (d) termination traps | Compression pass |
| 10 | Shared numeral-clash helpers (`n1z`..`n6s`) | Table 883-895; Tower 155-172 | 12 | (a) | Now |

Realistic sum: **~695-935 lines**, against the documents' banked **650-1,050**.

## Is the recorded estimate honest?

Honest in total, mis-attributed in composition. The four recorded claims alone
sum to ~330-540 (claims 2 and 3 are each roughly half their recorded value),
but unrecorded levers (F1 dead code 158-170, F2 mono duplication 60-110, F4
dispatch frames 50-80, F3 family frames 30-50, F5 honesty frames 25-40, plus
the shared numeral-clash helpers, 12) recover the balance. The banked figure is therefore neither
inflated nor understated as a total; it is a plausible ceiling rather than a
floor, and it is priced on the wrong line items. The single lever to execute
first is the dead-code deletion (F1): zero re-proving, zero statement risk,
and it corrects the only place where the docs' own "no consumer yet" note
was never followed up.

## What I could not determine without running the typechecker

- Whether the parameterized frames (F3, F4, and claim 1's stage frame)
  re-trigger the repo's measured module-application wall (PLAN rule 13:
  "abstraction is not the cure for non-locality", over 400 s with an order as
  a module parameter). The repo's own discipline requires a before-and-after
  bisect for each, and I could not run one (no Agda runs allowed).
- Whether dropping the ω-conjuncts (claim 4) changes check time in either
  direction; the readers get shorter, but the pattern reshuffling could alter
  the inference profile of `CertSel`/`CertBin` (which currently rely on
  explicit `finish` continuations per the recorded inference-trap law).
- Whether Table's `mono*` (F2) can be exported without reopening `apxS`'s
  seal in a way that re-engages the P-c mechanism; the lemmas only consume
  `apx-in`/`apx-out`, so it should be safe, but the seal boundary is exactly
  the class of thing that law punishes when moved.
- Whether a tag-indexed `ClauseOf`/`CertOf` (F4's deep cut) survives the
  checker at acceptable speed; the off-diagonal discriminations would remain
  explicit-data (P-a compatible) but the shape change touches the
  `use`-matrix and `certClause` recursion, whose locality the repo treats as
  load-bearing.
- The plan's chapter totals (Tower "1,723 code lines" vs my 1,606 non-blank
  fenced lines; InL "1,604" vs 1,517) differ by ~100 lines per chapter; the
  discrepancy is either a different counting convention (blank fenced lines,
  prose markers) or stale numbers, and I could not reconcile it without the
  measuring tooling.
