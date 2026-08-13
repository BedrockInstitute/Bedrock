# LJ-1.53: the three walls of the hull adequacy

Status: COMPLETE (partial discharge). Written incrementally per C-22.
ASD-STE100.
No commit. No push. No master edited: the wall-2 content lives in
`src/ProbeLJ153A.agda` (untracked), and the two scoped masters
(`BoundedSubset`, `Condensation`) are untouched. Probes:
`src/ProbeLJ153A.agda`, `src/ProbeLJ153Cone.agda`. The working tree
carries one non-probe edit, `dev/PLAN.md` (the orchestrator's LJ-1.52
and LJ-1.53 dispatch rows), which I did not make and did not touch.

## 0. THE LEDGER (live)

| wall | statement | status |
|---|---|---|
| 1. `DefBodyB`/`DefBody` leaf adequacy inside `StepAgree` | PENDING | section 3 |
| 2. parameter-to-code relabelling inside TV/ElemDown | **FELL** (probe green) | section 2 |
| 3. collapse/transitivity question | **ANSWERED**: no M-transitivity needed | section 4 |

`levelIn` and `cover`: NOT discharged (their last gates are the walls above).

## 1. THE RE-VERIFICATION (D-10)

Both LJ-1.52 probes re-run green at C-12:

| probe | runs, user s | LJ-1.52 mean |
|---|---:|---:|
| `ProbeLJ152A` | one run, 2.13 | 2.03 |
| `ProbeLJ152B` | one run, 2.08 | 1.95 |

No Agda process was running before the runs (process list unavailable;
see section 5 for the measurement protocol).

## 2. WALL 2: THE PARAMETER-TO-CODE RELABELLING

**FELL.** `src/ProbeLJ153A.agda` typechecks (mean 2.237 s user, three
cold runs; section 5).
The wall's two halves and the instance assembly are all built:

1. `CanonCode` (`ProbeLJ153A.agda:57-94`): the canonical code of each
   hull member, the CodeSelect least-of pattern. `canonical` picks the
   code with the least count over the ordinal's own well-order, and
   `canonical-spec` gives `val (canonical m) ≡ ⟪ M ⟫↪ m`. The fibre is a
   proposition by `cnt-inj` (`isPropFib`); the count injection and the
   well-order are the delivered `CC.count`/`CC.count-inj`/`OrdSWO` at
   `src/L/BoundedSubset.lagda.md:1073-1092`.
2. `CloseSyntax` (`:102-186`): the parameter-as-constant spelling. `close`
   replaces the top n variables of a formula by constants, keeping the
   witness variable free; `closeAll` closes every top variable.
3. `CloseSem` (`:190-263`): the satisfaction adequacy. `⊨-close`/
   `⊨-close₁`/`⊨-closeAll` prove the two-way transfer between the
   parameter-in-env and the parameter-as-constant readings at any
   structure, and `mapFo-close` proves relabelling commutes with the
   closure.
4. `HullElemDown` (`:266-365`): the instance. `rel` (`:289-294`) is the
   relabelling transfer (`mapFo val (mapFo f φ) ≡ mapFo inL φ`), `tv`
   (`:298-354`) is TarskiVaught at every arity from `hull-closed`,
   `elem` (`:359-360`) is `A.TV-thm .snd tv`, and `elem-down`
   (`:362-365`) is ElemDown at every arity.

The probe states the canonical code as a module hypothesis (`f`,
`f-spec`) and proves everything downstream; the hypothesis is exactly
the `CanonCode` output, instantiated at the consumer with the delivered
`CodeCount` and `OrdSWO`. The master placement (the instantiation at the
hull and the ElemDown wiring into `DownReflect`) is the remaining
mechanical step; the mathematical wall is down.

## 3. WALL 1: THE DefBodyB/DefBody LEAF ADEQUACY

**STANDING; one half green.** The leaf adequacy is the two-way
satisfaction transfer at a common environment:

```text
⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBodyB w K N0 … N11 t0 t1 ⟩
  ↔
⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody {5 + n} w ⟩
```

both at arity `8 + n`, under the leg-D site facts (the tag slots hold
the numerals, the satisfiers lie in K). `src/ProbeDD25H2.agda` is the
bounded half on the delivered `EraseTransfer` route and is green at
1.31 / 1.28 / 1.27 s (three cold runs, one caliber). The transfer never
calls `erase-Δ₀`: `abs₀` recurses on the Δ₀ witness
(`src/L/Condensation.lagda.md:273-294`), so the certificate never
crosses `erase`, exactly as the brief states.

The residual is the machine half: `DefBody` carries the numerals as
constants inside `isCodeAt`/`satGraphAt`/`DefinesAt`
(`src/L/Coding/Powerset.lagda.md:217-218`, `:297-298`), so it does not
erase to the same parameter-free axis. The reduction of `DefBody` to
the bounded reading under the site facts is the delivered row-agreement
content (`src/L/Condensation.lagda.md:2510-3430`, the LEG D agreements)
at the leaf: `isCodeBS ↔ isCodeAt`, `SatGraphB ↔ satGraphAt` (the
twelve rows compose), `DefinesBS ↔ DefinesAt`, each two-way. The
statement above is the term not written (C-36); its pieces are all the
rows' shape, none is a new idea, and the frame transfers
(`extAtB→extAt`/`extAt→extAtB`, `:2496-2510`) and the row agreements
are delivered.

The `EraseTransfer` is genuinely the right tool for the bounded half:
at the consumer's own leaf (`LevelHood0` with all sixteen slots zero,
`src/L/BoundedSubset.lagda.md:522-555`) the count is definitionally
zero and the certificate is `Δ₀-DefBodyB` at `refl`, so the
instantiation is the 0.22 s class (P-v measured), not the
hundred-second class.

## 4. WALL 3: THE COLLAPSE QUESTION

**ANSWERED: the statement is made after the collapse, and it needs
transitivity of neither M nor πM as a new hypothesis.** The "m ⊆ M"
clause in `[LJ-1.52]`'s piece-1 framing answers the wrong question.

Devlin's proof (`_build/literature/dev2.txt:1372-1385`) takes the hull
of `L_α ∪ {x}`; that generator is transitive BY CONSTRUCTION when
`x ⊆ L_α` (members of members land in `L_α` by stage transitivity and
in `x` by the hypothesis), so `fixes` applies to it and `π x = x`.
That is the only place the proof uses a transitive subset of M. The
formalization's own `levelIn` (`Lset δ ∈ πX` for ordinal `δ ∈ πX`) is
not Devlin's step; it is the closure content of the adequacy, and its
route is:

1. `δ = π m` for a hull member `m` (`Collapse.πX-member`,
   `src/V/Collapse.lagda.md:120-127`);
2. elementarity down (wall 2's `ElemDown`) turns the stage truth of the
   Σ₁ level-hood at `m` into witnesses `K' v' w' ∈ M` with `w' = Lset m`
   (the re-based decode, walls 1+2's product) — so `Lset m ∈ M`
   directly, no transitivity of M;
3. the satisfaction iso `M ≅ πM` (`IsoInv`, `BoundedSubset:142-348`,
   needing only `isExt M`, discharged by `HullExt`) transfers the
   level-hood statement to πM;
4. the decode at the transitive collapse image (walls 1+2's product,
   with `πX-trans` at `src/V/Collapse.lagda.md:98-118`) gives
   `π (Lset m) = Lset (π m)`;
5. `πX-intro` (`:128-131`) gives `Lset δ ∈ πX`.

So the value statement `π (Lset m) = Lset (π m)` is proved THROUGH the
collapse, which is exactly what the Mostowski collapse is for: the
source's non-transitivity is fixed by the collapse, not required of it.
`Collapse.InjExt` (`:220-312`) delivers the iso from `isExt` alone; no
`isTrans M` appears anywhere in the collapse module's iso story. The
transitivity that IS used is `πX-trans` — delivered — and it is used
only for the decode/absoluteness at the transitive carrier, never as
"`Lset m ⊆ M`". The fixes route (needing `Lset m ⊆ M` and `m ⊆ M`) is
one route and it is circular for arbitrary hull members; the iso route
is the other, and it carries the whole statement. The wall as framed
(hull transitivity) does not exist; the residual content is walls 1+2
themselves.

## 5. MEASUREMENTS

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, USER seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved aside
before EVERY run), dependencies warm, ONE process, quiet machine. Every
figure is three completed runs; no heap exhaustion, no interruption. No
Agda process was running before the batch (the process list is
unavailable in this environment; the measurement batch was serial and
each run exited 0).

| module | runs, user s | mean | spread | non-blank lines |
|---|---:|---:|---:|---:|
| `ProbeLJ153A` (wall 2 whole) | 2.32 / 2.25 / 2.14 | 2.237 | 0.18 (8.0 pc) | 272 |
| `ProbeLJ153Cone` (import cone) | 1.45 / 1.44 / 1.45 | 1.447 | 0.01 (0.7 pc) | 32 |
| `ProbeDD25H2` (wall 1's EraseTransfer leaf) | 1.60 / 1.62 / 1.63 | 1.617 | 0.03 (1.9 pc) | 40 |

The marginal rate of the wall-2 content: 2.237 - 1.447 = 0.790 s over
240 content lines (272 - 32) = **0.0033 s per line**, the P-m
parameterized class (modules checked at abstract parameters, never
instantiated). The whole-file rate is 2.237 / 272 = **0.0082 s per
line**, under the DD24 bar 0.012716 (`dev/ledger.toml:2590` times
`:2810`). The cone's per-invocation interface cost is the quoted
1.45 s (the ledger's own note, `dev/ledger.toml:2580-2586`).
`ProbeDD25H2`'s 1.617 s matches the 1.56 s band of `[LJ-1.50-R]`'s
measurement; the wall-1 leaf transfer is the 0.22 s content class, not
the hundred-second class.

The LJ-1.52 probes re-verify at 2.13 / 2.08 s user (one run each),
against the recorded 2.03 / 1.95 s means (section 1).

## 6. DD4 SPLIT

- Wall 2 (the close transfer and the canonical code): TEMPLATE. The
  `CloseSyntax`/`CloseSem` machinery is generic in the constant domain
  and the structure, and `CanonCode` is generic in the carrier, the
  codes, the count and the well-order; nothing mentions L's Def syntax
  in any type. The J tower instantiates the same modules with its own
  hull, its own codes and its own well-order. The `HullElemDown`
  instance is per-hull but the hull is the shared `TermAlgebra` hull,
  so the module is template-shaped; its anchor is the per-tower
  `hull-closed` machine, which is itself generic in the stage.
- Wall 1 (the leaf adequacy): DEF-side at its core. `DefBodyB` and
  `DefBody` are per-tower instantiations of the bounded/machine
  description templates (D-26 predicts the per-tower proof); the
  `EraseTransfer` frame is template (already shared, DD25's delivered
  route), and the LEG D row agreements are per-tower content.
- Wall 3 (the collapse piece): TEMPLATE statement, per-tower proof. The
  statement `π (Lset m) = Lset (π m)` names a generic tower and a
  generic collapse; its proof runs through the per-tower level-hood
  formula and its decode at the collapse image, exactly as `[LJ-1.52]`
  said. The collapse machinery itself (`πX-trans`, `InjExt`,
  `IsoInv`) is delivered and fully shared.
- `levelIn` and `cover`: DEF-side, as D-26 predicts; they key on the
  `Lset` construction and its per-tower decode.

## 7. WHAT I AM NOT SURE OF

1. The wall-2 probe takes the canonical code (`f`, `f-spec`) as a module
   hypothesis. The `CanonCode` construction proves the hypothesis's
   content generically, but the instantiation at the consumer (with
   `OrdSWO`, `CodeCount.count` and `count-inj`) is not typechecked in
   this dispatch; it uses only delivered pieces
   (`src/L/BoundedSubset.lagda.md:1073-1092`), but the composition is
   mechanical work not yet done.
2. The wall-2 content is not placed in a master. Its natural homes are
   `FOL.Manipulation.Parameters` (the close machinery) and `L.Hull`
   (the instance), which are OUTSIDE this dispatch's write scope; the
   alternative is a consumer-local copy in `BoundedSubset`, which
   duplicates template content (DD4 tension). The placement needs the
   orchestrator's ruling on the home.
3. The wall-1 residual (the machine-side reduction of `DefBody` to the
   bounded reading under the site facts) is stated but not built. Its
   pieces are the delivered row agreements' shape, but the isCode and
   Defines agreements at the leaf are new content; I did not price them
   in seconds, and I am not sure the EraseTransfer half composes with
   them without another frame transfer at the leaf env.
4. `ElemDown` at every arity is proved, but the consumer
   (`DownReflect`) is stated at every arity and used at arity 1
   (`src/L/BoundedSubset.lagda.md:432-437`). No consumer reshaping was
   needed, but the full-arity instance has not been typechecked against
   `DownReflect`'s exact `SM` (the probe's `A.SM` is the same type, but
   the module wiring is not done).
5. The cold marginal (0.790 s over 240 lines) is measured with the
   probe's own interface moved aside before each run. With a warm
   interface the same runs land at 1.5 to 1.6 s and the marginal
   vanishes into noise; the cold protocol is the one the ledger's
   caliber uses, and the warm numbers are the ones a consumer pays per
   invocation.
6. The `dev/PLAN.md` edit appeared in the tree during the dispatch and
   is not mine; I left it untouched and flag it for the orchestrator.

## 8. ARCHIVE USED

- `_build/lj-1.52-report.md`, read WHOLE. Took the survivor ledger
  (`:13-20`), the walls (`:106-124`), the measurements (`:126-138`), the
  DD4 split (`:140-169`).
- `src/ProbeLJ152A.agda`, `src/ProbeLJ152B.agda`, read WHOLE.
- `_build/lj-1.50-review.md`, read sections 5 to 8. Took the EraseTransfer
  route (`:9-50`, `:376-394`) and the probe measurements (`:224-240`).
- `src/ProbeDD25H2.agda`, read WHOLE. The EraseTransfer instantiation at
  the leaf.
- `_build/lj-1.51-report.md`, read WHOLE. Took the survivor prices
  (`:120-162`) and the DD4 split (`:164-174`).
- `_build/lj-1.7-review.md`, read sections 3 to 5. Took the leaf absence
  (`:186-191`) and the ElemDown residue (`:232-243`).
- `src/L/BoundedSubset.lagda.md`, read WHOLE. Took `LevelHood`
  (`:70-142`), `LevelHood0` (`:522-555`), `DownReflect` (`:350-450`),
  `AtHullInstance` (`:450-470`), `CodeSelect` (`:830-881`), `Co`
  (`:1077-1093`).
- `src/V/Collapse.lagda.md`, read WHOLE. Took `Collapse` (`:40-97`),
  `InjExt` (`:220-312`), `fixes` (`:334-341`), `πX-trans` (`:98-118`),
  `πX-member` (`:120-127`).
- `src/L/Condensation.lagda.md`, read `EraseTransfer` (`:273-294`),
  `RowTransfer`/`RowDecode` (`:1772-1806`), `SatGraphB` (`:2211-2258`),
  `DefBodyB` (`:2316-2350`), `GraphB`/`StepB`/`ApproxB` (`:2464-2508`),
  the row agreement (`:2510-3430`).
- `src/L/Hull.lagda.md`, read WHOLE. Took `TermAlgebra` (`:58-146`),
  `AtStage`/`AtM` (`:148-338`), `Hull`/`hull-closed` (`:313-425`).
- `src/L/Coding/Sequence.lagda.md`, read `StepAt`/`ApproxAt`/`GraphAt`
  (`:119-125`, `:286-330`), the renamings (`:349-354`).
- `src/L/Coding/Powerset.lagda.md`, read `DefBody`/`DefAt` (`:437-443`),
  `DefAt-in`/`DefAt-out` (`:645-666`).
- `src/ProbeLJ153A.agda` (written), `src/ProbeLJ153Cone.agda`
  (written), `src/ProbeDD25H2.agda` (re-verified and measured).
- `src/FOL/Manipulation/Parameters.lagda.md`, read WHOLE. Took
  `absFo`/`⊨-abs` (`:250-330`) and the `lookup-padRight`/`lookup-map`
  laws the close adequacy reuses.
- `src/FOL/Semantics.lagda.md`, read the `At` interface (`:71-150`).
- `src/L/WellOrder/Base.lagda.md`, read `SWO`/`leastOf`/`IsLeast`
  (`:54-170`).
- `src/L/Condensation.lagda.md`, read the row agreements (`:2510-3430`),
  the `PropAgree` interface (`:3074-3130`), `isCodeBS`/`DefinesBS`
  (`:1714-1770`), `StepAtB` (`:2422-2445`).
- `dev/PLAN.md`, read the dispatch rows only. WHY NOT more: the working
  tree edit is the orchestrator's LJ-1.52/LJ-1.53 rows, not mine.

## 9. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385`, Devlin 5.5's proof, read for
  wall 3. TOOK: the hull is taken of `L_α ∪ {x}`, the collapse `π : M ≅
  L_γ` is applied to the hull, and `L_α ∪ {x}` is a TRANSITIVE subset of
  M, which is why `π` fixes it.
- `dev/literature/devlin-II5.md:209-257` (Step C), read for the level-hood
  strength requirement.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.

## 10. THE CONVERGENCE ANSWER

**Converging, with the ledger now three named terms, one down.** This
dispatch did not rename the walls. Wall 2 fell with a machine-checked
probe (the transfer is built, not sketched); wall 3 was answered as a
non-wall (the transitivity clause was the wrong question, and the
collapse route needs only delivered pieces plus walls 1+2); wall 1
stands with one half green (the EraseTransfer at the leaf, measured at
1.617 s) and the residual stated as a concrete two-way term whose
pieces are the delivered row agreements' shape. The obligation is now
one unbuilt term (the machine-side leaf reduction under site facts)
plus two mechanical placements (wall 2's instantiation and wiring).
That is a different, smaller shape than the three walls this dispatch
opened with, so I call it converging.
