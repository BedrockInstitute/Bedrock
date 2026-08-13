# LJ-1.49: discharge the two hypotheses, then price what is left

Status: COMPLETE. Written incrementally per C-22. The report uses
ASD-STE100. No commit, no push.

## 1. THE VERDICT

**BOTH CURES ARE LANDED AND GREEN. The residue is priced, not built.**
`collapseCode` is deleted from the module parameters; `levelIn` and `cover`
still survive as hypotheses, and `isExt M` enters in the deleted
hypothesis's place (see section 3). The level-hood adequacy at the hull's
carrier and `ElemDown` are structurally priced and their one measured
machine piece (the erase-to-Delta-0 certificate transfer) is a genuine
cost: 150.13 s at the concrete leaf, stopped at the full matrix. Section 4
states the wall precisely.

The surviving module parameters of the condensation, exactly:

| hypothesis | home | status |
|---|---|---|
| `levelIn` | `HullStage.Condense` (:596-597) | SURVIVES; the level-hood adequacy at the hull's carrier is its discharge, priced in section 4 |
| `cover` | `HullStage.Condense` (:597-599) | SURVIVES; the rank/cofinality chain for hull members, priced with the adequacy |
| `collapseCode` | `BoundedSubsetAt.Co` | **DELETED** by cure 2 |
| `Mext : isExt HS.M` | `BoundedSubsetAt.Co` | NEW, in the deleted hypothesis's place; Devlin's extensionality-of-the-hull, priced provable from `hull-closed` |
| `sq`, `fin-inj`, `hotel` | `Devlin55` | survive (the size chain; `[LJ-1.47]` priced `sq`, `hotel` is O3's residue) |
| `succλ`, `x∈Lλ`, the cardinal premises | `BoundedSubsetAt` | survive (the instance premises of 5.5) |

## 2. CURE 1: THE SLOT SPELLING

The `*Bnum` chain in `src/L/Condensation.lagda.md` is replaced in place by
the slot spelling (one spelling, P-v). The leaf helpers `keyArBS`, `tagBS`,
`arTagPairBS`, `arTagBS`, the frames, `closedBS`, `shapesBS`, `isCodeBS`,
`envOneBndS`, `DefinesBS` and the `SatGraphB`/`DefBodyB` threading carry
the arity tags as `Fin` slots. `DefBodyB`'s signature is unchanged, so the
master needed zero consumer edits.

Verified green at the consumer's own objects:
- `countFo (DefBodyB ...) ≡ 0` by `refl` (`src/ProbeLJ149.agda`);
- `countFo (LevelHood0.matrix) ≡ 0` by `refl`;
- `Cnt.erase` applies to both;
- the Sigma-2 level-hood statement embeds to `Formula Code 1` at the hull
  of a stage, still constant-free (`HullPack.atHull`), in a 4.78 s probe;
- `Cnt.erase` applied to the leaf, with the Delta-0 certificate carried
  through (`erase-Δ₀`): **150.13 s user**, clean run, under the heap cap.
  The matrix-level certificate transfer did not complete in 2.5 minutes
  and was stopped. This is the measured price of the adequacy connector,
  reported in section 4.

`src/L/Condensation.lagda.md` re-checks at 56.71 s user / 58.46 s real
(one cold run), under `GHCRTS="-A64m -I0 -M8g"`.

## 3. CURE 2: DELETE `collapseCode`

`collapseCode : ⟪ HS.C.πX ⟫ ↪ HS.H.T.Code` is deleted from the `Co`
module's parameters. In its place `β↪α` composes the two-leg composite
transplanted from `src/ProbeDD25G3.agda`: leg 1 `⟪ πX ⟫ ↪ ⟪ M ⟫` (the
collapse fibre is a proposition because π is injective on M), leg 2
`⟪ M ⟫ ↪ ⟪ α ⟫` (the least count over `OrdSWO.ordSWO α ordα`, with
`CC.count`/`CC.count-inj`, the master's own code order). The generic
modules `InvColl` and `CodeSelect` live in the master at
`src/L/BoundedSubset.lagda.md:737-838`; the `Co` composite is at
`:1077-1093`.

The parameter that survives in the deleted hypothesis's place: `Mext :
isExt HS.M` in `Co`. It is Devlin's own extensionality-of-the-hull
hypothesis; the review predicted it (`_build/lj-1.7-review.md` not-sure
item 5). Section 4 prices its discharge from `hull-closed`.

`src/L/BoundedSubset.lagda.md` re-checks at 10.42 s user / 10.81 s real
(one cold run), under the cap.

## 4. THE RESIDUE: LEVEL-HOOD ADEQUACY AND `ElemDown`

Both are priced, neither is built. The wall and the measured pieces:

- `ElemDown` at the hull reduces, through the delivered
  `AtStage.AtM.TV-thm` equivalence, to one `TarskiVaught` instance for the
  hull at every arity. The `TermAlgebra.closed`/`hull-closed` machine
  provides the witness for `Formula Code 1`; the unbuilt bridge is the
  n-parameter-to-code relabelling (the least-code selection over
  `OrdSWO`/`CC.count`, the same fibre the review's leg 2 solves), plus a
  SWO transfer to `Code` and the `absFo`/`⊨-abs` satisfaction bridge.
  Structural price: 150 to 300 lines of parameterized content plus the
  site facts. The syntax has no substitution by design
  (`src/FOL/Manipulation/Renaming.lagda.md:7`), so the parameters must be
  carried as constants; that is the bridge.
- The level-hood adequacy at the hull's carrier needs the erased
  level-hood statement at the hull. The measured machine piece is the
  erase-to-Delta-0 certificate transfer: 150.13 s at the concrete
  `DefBodyB` leaf (one run), stopped (interrupted) at the full
  `LevelHood0.matrix` after more than 2.5 minutes. The count and the
  erasure themselves are fast (2.6 s probe); the certificate transfer is
  the instantiation-class cost. The statement-level connector is cheap:
  `embed (Cnt.erase Σ₂ refl)` at the hull checks in a 4.78 s probe.
  The remaining unbuilt chain is the twelve-row agreement re-based at the
  hull's carrier and the collapse-of-the-level step of `levelIn`; no price
  is offered for it, because nothing in the delivered tree measures it
  (the review's section 4 names it as the genuinely unbuilt term).
- `isExt M` (the new `Co` parameter) is provable from `hull-closed` plus
  LEM plus the least-code selection: two hull members that agree on the
  hull's membership differ nowhere, because a differing element would be
  the Skolem witness of the membership-separation formula. Structural
  price: 120 to 250 lines (the SWO transfer to `Code`, the
  membership-separation formula and its satisfaction proof, and the
  `hull-closed` application).

The discharge of `levelIn` itself (the level-hood adequacy at the hull
plus the collapse-of-the-level step) is the remaining term; section 9
states exactly what is not built.

## 5. THE MEASUREMENTS

All runs at `GHCRTS="-A64m -I0 -M8g"`, one process, cold (the module's
own interface moved aside), wall seconds from `scripts/check-timing.py`.

| piece | runs, wall s | mean | spread | rate |
|---|---:|---:|---:|---:|
| `BoundedSubset` whole file (976 in-fence lines) | 11.47 / 10.77 / 10.70 | 10.98 | 0.77 (7.0 percent) | 0.01125 s/line |
| `BoundedSubset` import cone | 2.01 / 1.90 / 1.90 | 1.94 | 0.11 (5.6 percent) | n/a |
| content rate (whole minus cone) | | 9.04 | | 0.0093 s/line |
| added content (cure 2, probe B) | 0.905 / 0.913 / 0.910 | 0.909 | 0.008 (0.9 percent) | n/a |
| added-content cone (probe B cone) | 0.68 / 0.67 / 0.67 | 0.674 | 0.01 (1.5 percent) | n/a |
| added-content marginal (88 in-fence lines) | | 0.235 | | 0.0027 s/line |
| `Condensation` whole file (4,632 in-fence lines) | 59.21 / 58.11 / 57.81 | 58.38 | 1.40 (2.4 percent) | 0.0126 s/line |
| `ProbeLJ149` (connector checks) | 3.90 / 3.78 / 3.77 | 3.81 | 0.14 (3.6 percent) | n/a |

The whole-file rate 0.01125 sits under the DD24 bar 0.012716
(`dev/ledger.toml:2590` x `:2810`). The marginal of the added content,
0.0027 s per line, is the parameterized class at its cheapest. The
cured `Condensation` checks at 58.38 s mean against the pre-cure 56.08 s
mean (user seconds, `_build/lj-1.7-report.md`); the cure's cost is inside
the run-to-run spread, so the slot spelling bought the zero-count for no
measurable time.

The whole-file user-seconds (one cold run each): `BoundedSubset` 10.42,
`Condensation` 56.71. The brief's stated 0.0111 for the pre-add master
(888 lines, user caliber) compares with the post-add 10.42 / 976 =
0.0107 user caliber; the additions check below the file's own average.

## 6. THE DD4 ANSWER

Cure 1 is a Def-side leaf surgery: the slot spelling lives in the
code-set description chain (`keyArBS` through `DefinesBS`), and the J
tower inherits the one-spelling discipline (P-v) and the generic
connector route (countFo = 0, erase, embed), not the Def rows. Cure 2 is
the shared template: `InvColl` and `CodeSelect` are generic in the
carrier, the code type, the value map and the count, so the J tower's
condensation uses the same two modules unchanged; its collapse is the
same `V.Collapse`, and its own code count plugs into `CodeSelect`.

## 7. ARCHIVE USED

- `_build/lj-1.7-review.md`, read WHOLE. Took the two overturns
  (`:12-35`), the count decomposition (`:100-160`), the probe verdicts
  (`:36-99`), and the not-sure list (`:331-371`).
- `_build/lj-1.7-report.md`, read WHOLE. Took the obligation table, the
  structure, the residue, and the whole-file measurements (9.91 s mean,
  user caliber, 888 lines, `:16-27`, `:160-175`).
- `_build/lj-1.48-report.md`, read WHOLE. Took the skeleton's shape and
  the residue naming (`:81-121`, `:315-317`).
- `src/ProbeDD25G1.agda`, `src/ProbeDD25G2.agda`, `src/ProbeDD25G3.agda`,
  read WHOLE. Took the count decomposition (`G1:50-54`), the slot-spelling
  chain (`G2:57-252`), and the two-leg composite verbatim (`G3:42-160`).
- `src/L/BoundedSubset.lagda.md`, read WHOLE (888 in-fence lines before
  this dispatch, 976 after). Took `Condense` (`:596-715`), `Co`
  (`:952-1093`), and the section 5 chain.
- `src/L/Condensation.lagda.md`, read the `*Bnum` family (`:1455-1504`),
  the rows (`:1111-1114`, `:435-460`), the graph and step blocks
  (`:2172-2420`), and the row agreements (`:2440+`).
- `src/L/Hull.lagda.md`, read `AtStage`/`AtM`/`TV-thm` (`:148-338`),
  `Hull`/`closed`/`hull-closed` (`:307-445`).
- `src/V/Collapse.lagda.md`, read `Collapse` (`:40-97`), `Inj`
  (`:107-214`), `InjExt` (`:220-312`), `fixes` (`:334-341`).
- `src/L/StageCardinal.lagda.md`, read `OrdSWO.ordSWO` (`:223-254`) and
  the successor pattern (`:265-320`).
- `src/FOL/Manipulation/Parameters.lagda.md` and
  `src/FOL/Count.lagda.md`, read the erase and absFo machinery.
- `dev/ledger.toml`: the DD24 bar and its provenance (:2590, :2810).
- `dev/LESSONS.md` via `scripts/rules.py --for build`: P-h, P-k, P-l,
  P-m, P-n, P-u, P-v, R-35, R-38, R-40, I-5, C-12, C-22, D-10, D-26,
  D-29, D-30, C-31, C-34, C-35, C-36, read as the bundle.

Nothing else in `archive/` was read. WHY NOT: the retired route's other
crossings do not bear on the condensation transfer; `[LJ-1.11]` ruled its
condensation target classically false, and the brief forbids taking a
price from it.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385`: the 5.5 statement and proof
  chain (the hull, the collapse, the condensation, the size equality).
- `dev/literature/devlin-II5.md` Step C (`:209-257`): the level-hood
  strength requirement (Sigma-1 with a bounded witness) and the transfer
  requirements. Took the shape that the erased Sigma-2 statement must
  carry at the hull.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.

## 9. WHAT I AM NOT SURE OF

1. The leaf `erase-Δ₀` cost (150.13 s) was measured three times with the
   leaf and once cleanly; the matrix-level variant was stopped after more
   than 2.5 minutes and its cost is an under-estimate ("more than 150 s").
2. The residue is priced, not built. `ElemDown`, the hull-side adequacy,
   and the `isExt M` discharge are structural prices (section 4), and the
   adequacy's deepest step (the collapse-of-the-level for `levelIn`) has
   no price at all: nothing in the tree measures it.
3. `Mext` enters as a parameter; it is provable from `hull-closed`, but
   the proof is not built, so the report does not claim the discharge.
4. The measurements used wall seconds from `scripts/check-timing.py`; the
   pre-add baselines (9.91 s / 56.08 s) are user seconds from the
   `[LJ-1.7]` reports, so the deltas are caliber-mixed and are stated as
   such. The machine load read 4 to 6 during the runs; the spreads are
   reported and the verdict does not sit inside a spread.
5. `src/Everything.lagda.md` imports `L.Condensation` bare (:369) and was
   not re-typechecked; a search shows no `Condensation.`-qualified use in
   the catalog, so the changed interface cannot break it.
