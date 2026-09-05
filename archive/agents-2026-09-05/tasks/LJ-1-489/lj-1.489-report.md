# LJ-1.489 report: does the collapse commute with the definable powerset

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-489/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-489/Probe489.agda`:

    piCommuteD :
        (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)

where `M` is the definable hull and `C = Collapse M`, copied from
`src/L/BoundedSubset.lagda.md:903-916`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## PREDECESSOR VERDICT, BEFORE ANY AGDA

`[LJ-1.477]` verdict at `agents/tasks/LJ-1-477/lj-1.477-report.md:99`:

    **NO-GO at the join of the two computation laws.** Both laws spend.

The critic upheld that return
(`agents/tasks/LJ-1-477/review-of-LJ-1-477-1.md:6`):

    verdict: upheld

The brief's gate is met: the verdict is a stated NO-GO. I take the
type `[LJ-1.477]` named as a need, not a delivered term. I do not
inhabit `piCommuteLset`. I do not inhabit `JoinSteps`. I do not
take `HullClosedLset` or `CoverWitnessesInHull` as a module
hypothesis.

Quote of `## 4. What the next brief needs`
(`agents/tasks/LJ-1-477/lj-1.477-report.md:299`):

```
## 4. What the next brief needs
```

Quote at `:312`:

```
  laws: it needs `π` to commute with `𝒟ₒ`, and it needs
```

Quote at `:313`:

```
  `Lset-out` witnesses to lie in `M`. The hull is not transitive
```

This task is the first of those two needs. The second is
`[LJ-1.487]`, named in flight by the brief, and is not this
obligation.

## D-10, BEFORE ANY AGDA

The two sides, at `file:line`.

1. Left. Collapse, `src/V/Collapse.lagda.md:47-48` and `:58-59`:

       step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
       step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (member x (p .fst)))

       π-compute : (x : S) → π x ≡ step x (λ y _ → π y)

   `Fiber x` is the small members of `x` that also lie in the carrier
   (`src/V/Collapse.lagda.md:44-45`). So `C.π (𝒟ₒ y)` is the `sett`
   of `π`-images of those small members of `𝒟ₒ y` that lie in `M`.

2. Right. Definable powerset, `src/L/Constructible.lagda.md:211-213`:

       opaque
         𝒟ₒ : S → S
         𝒟ₒ A = 𝒟 A

   `𝒟 A = DefOf.Def A` (`src/L/Constructible.lagda.md:53-54`).
   `Def` is `sett (Formula ⟪ A ⟫ 1) defSet`
   (`src/L/Definability.lagda.md:114-115`). The exported membership
   laws, inside `opaque; unfolding 𝒟ₒ` at
   `src/L/Constructible.lagda.md:301-308`:

       𝒟ₒ-intro : (A x : S)
                → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
                → ⟨ x ∈ˢ 𝒟ₒ A ⟩

       𝒟ₒ-inv : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
              → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁

   There is no `𝒟ₒ-compute`. The official unfolding named for the
   tower is `Lset-compute` (`src/L/Constructible.lagda.md:201-207`),
   and it unfolds `Lset`, not `𝒟ₒ`.

One line. The two sides cannot agree without elementarity. Left is
a `sett` of hull-filtered `π`-images. Right is every definable
subset of `C.π y`. A defining formula over `y` becomes a defining
formula over `C.π y` only if satisfaction transfers along `π`.
That transfer is not a computation law. The hull is not
transitive (`agents/tasks/LJ-1-160/lj-1.160-report.md:249`):

    mathematics.** A hull is not transitive, so a statement proved there must be

so `(y, ∈)` and `(C.π y, ∈)` are not even isomorphic: `C.π y`
drops members of `y` that lie outside `M`
(`src/V/Collapse.lagda.md:47-48` via `Fiber`).

Devlin 5.2 identifies the collapse image of an elementary
submodel of a limit stage with a level, by Φ and Σ₁ transfer
(`dev/literature/devlin-II5.md:95-106`). It does not commute
`π` with `Def` at an arbitrary hull member. That reading was
already measured for the stage operation at
`agents/tasks/LJ-1-160/lj-1.160-report.md:261`:

    **No step of Devlin's chain commutes the collapse with the level

I do not add an elementarity hypothesis. I do not add
transitivity of `M`. I do not take `HullClosedLset`. I do not
open either seal.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module
is generic in `ℓ`. `lam`, `X` and the limit hypotheses stay
parameters. No ordinal is fixed. No second copy at a concrete
stage. The conflict the clause names did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## VERDICT

**NO-GO at D-10 and at the join of `π-compute` with sealed `𝒟ₒ`.**
The two sides cannot agree without elementarity. W3's inclusion
does not close by the exported computation law. The obligation
term `piCommuteD` is not written. Witness meter: 1 UNRESOLVED of
1, `probe_red=False` (`runs/witness.out:1-2`).

This is an obstruction of the computation-law route at the
powerset step. It is not a refutation of `piCommuteD`. I did not
build a term of the negation.

The NO-GO is stated in
`agents/tasks/LJ-1-489/review-of-piCommuteD.md`. That file is the
critic's input. It does not close the task.

## 1. What was built

All in `agents/tasks/LJ-1-489/Probe489.agda`, module
`LJ-1-489.Probe489 {ℓ} (lem)`.

- Telescope `HullStage` (`:53-64`), copied from
  `src/L/BoundedSubset.lagda.md:903-916`. The module keyword is at
  `:903`. Line `:916` is `module Condense`, and it is not copied.
  `M = H.T.Hull`. `module C = Collapse M`.
- W3 stated: `OneWay` (`:88-90`) is the easier inclusion. Unbuilt.
  Direction tried: left to right, `C.π (𝒟ₒ y) ⊆ˢ 𝒟ₒ (C.π y)`. The
  converse also needs a preimage in `M`, so it is the harder
  direction.
- The computation law inhabited: `left-compute` (`:81-82`) is
  `C.π-compute (𝒟ₒ y)`. The hole in the type fills with
  `C.step (𝒟ₒ y) (λ z _ → C.π z)`. The seal on `π` does not open.
- The membership laws inhabited: `d-inv` (`:104-105`) is `𝒟ₒ-inv`.
  `d-intro` (`:107-110`) is `𝒟ₒ-intro`. The seal on `𝒟ₒ` does not
  open.
- The join as a type: `JoinAtD` (`:119-121`). Unbuilt.
- Formula transport as a type: `FormulaTransport` (`:128-134`).
  Unbuilt.
- Obligation type restated: `PiCommuteD` (`:139-141`). Unbuilt.
  No term named `piCommuteD`.

Measured non-blank non-comment lines: 54. Total lines: 141. The
brief estimate was about 150 lines, of which the obligation is
about 40. Nothing is funded against the estimate.

## STEP ONE, W3

**Direction tried: left to right.** A member of `C.π (𝒟ₒ y)` is
the collapse of a hull-filtered member of `𝒟ₒ y`. The question
is whether that image is still definable over `C.π y`. That is
where elementarity would be needed. The converse also needs a
preimage in `M`, so the left-to-right inclusion is the cheaper
direction the brief named.

**The exported law spends at `𝒟ₒ y` without unfolding the seal.**
`left-compute` (`Probe489.agda:81-82`) is the computation-law
half of W3, stated with the obligation omitted. The inclusion
itself is the type `OneWay` (`:88-90`) and is unbuilt. Three
forced rechecks of that W3-only file, `_build` interface removed
before each, dependencies warm, caliber `-A64m -I0 -M8g`, one
Agda process. Exit 0 every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.74 | 471547904 |
| `runs/w3-2.out` / `w3-2.time` | 2.55 | 471482368 |
| `runs/w3-3.out` / `w3-3.time` | 2.56 | 471465984 |

Median wall **2.56 s**. Median peak RSS **471482368 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 2.96 s and
449822720 bytes, also exit 0, also printed `Checking`. It is not
one of the three forced rechecks. The brief estimate for W3 was
about 15 lines and under 25 seconds. The measured median is under
that estimate. I do not fund this against `[LJ-1.477]`'s 1.97 s:
that measured a law application, not this inclusion type.

A diagnostic inhabitant `one-way y y∈M z z∈πD = subst (λ w → ⟨ z ∈ˢ w ⟩) (left-compute y) z∈πD`
failed with `[UnequalTerms]` (`runs/one-way-subst.out:2` and
`:11-13`):

    when checking that the expression
    subst (λ w → ⟨ z ∈ˢ w ⟩) (left-compute y) z∈πD has type
    ⟨ z ∈ˢ 𝒟ₒ (C.π y) ⟩

The left of that inequality is truncated membership in
`C.Fiber (𝒟ₒ y)` (`runs/one-way-subst.out:3-9`). The right is
membership in sealed `𝒟ₒ (C.π y)` (`:10` and `:13`). The `subst`
was then removed. The green file does not contain it. Exit of
that diagnostic was 42. It is not one of the kept full rechecks.

The inclusion does not close by the computation law. The
equation is out of reach at this site. The task stops at that
cheapest point.

## STEP TWO, THE OBLIGATION

The membership laws of `𝒟ₒ` spend without unfolding. The join
is unbuilt. Formula transport is unbuilt. The obligation is
omitted.

`d-inv` (`Probe489.agda:104-105`) applies `𝒟ₒ-inv`. `d-intro`
(`:107-110`) applies `𝒟ₒ-intro`. Together with `left-compute`,
the exported laws at this layer are now terms. Closing
`piCommuteD` then needs

    C.step (𝒟ₒ y) (λ z _ → C.π z) ≡ 𝒟ₒ (C.π y)

That type is `JoinAtD` (`Probe489.agda:119-121`). The diagnostic
already failed a `subst` that claimed the two sides agree at a
member. There is no `𝒟ₒ-compute` to join against.

Closing the inclusion `OneWay` still needs, after those laws,

    (y : S) → ⟨ y ∈ˢ M ⟩
    → (φ : Formula ⟪ y ⟫ 1)
    → ⟨ DefOf.defSet y φ ∈ˢ M ⟩
    → ∥ Σ[ ψ ∈ Formula ⟪ C.π y ⟫ 1 ]
          (DefOf.defSet (C.π y) ψ ≡ C.π (DefOf.defSet y φ)) ∥₁

That type is `FormulaTransport` (`Probe489.agda:128-134`). It is
elementarity of definability along `π`. I did not inhabit it. I
did not add it as a module hypothesis. The brief forbids an
elementarity hypothesis by D-10: if the sides cannot agree
without it, that is the finding.

I did not prove the type `piCommuteD` false. A hull member `y`
whose definable subsets use satisfaction that `π` does not
preserve is a candidate obstruction at this generality. I did
not build that counterexample.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency warm,
from the repository root. The probe interface was deleted before
every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-489/Probe489.agdai`).

- W3, three forced rechecks: see the table above. Median **2.56 s**,
  **471482368 bytes**. Exit 0.
- Full file, three forced rechecks. The membership laws are in the
  file. The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.72 | 478134272 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.25 | 478101504 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.25 | 478150656 |

Median wall **2.25 s**. Median peak RSS **478134272 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the remaining types were added, `runs/full-0.out`, was
2.91 s and 478134272 bytes, also exit 0. It is not one of the
three forced rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.41 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `piCommuteD` is not in scope. That is the intended NO-GO
  reading. This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py --brief agents/tasks/LJ-1-489/LJ-1.489.md`.
  I did not add a dependency. I did not create a local `.venv`.

## WHAT STEP FOUR NOW NEEDS

The two needs `[LJ-1.477]` named, as types, and which are built.

1. Collapse commutes with the definable powerset. UNBUILT. Type at
   `agents/tasks/LJ-1-489/Probe489.agda:139-141`:

       PiCommuteD :
           (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)

   This task measured it. D-10: the two sides cannot agree without
   elementarity. The computation-law join `JoinAtD`
   (`:119-121`) is unbuilt. The inclusion `OneWay` (`:88-90`) is
   unbuilt. Formula transport (`:128-134`) is unbuilt.

2. `Lset-out` witnesses lie in `M`. UNBUILT. Type delivered at
   `agents/tasks/LJ-1-484/Probe484.agda:123-126`:

       CoverWitnessesInHull :
           (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

   The brief names this as `[LJ-1.487]`'s work, in flight. This
   task did not take it as a module hypothesis and did not
   build it.

**Step 4 is blocked on both.** I do not claim `levelIn`. I do not
claim step 4. A GO would have left step 4 blocked on need 2 only.
This NO-GO does not discharge need 1 as a term. It measures that
need 1 is not a computation, so the four-step decomposition of
`[LJ-1.462]` is wrong at step 4: `levelIn` must be re-decomposed
along the elementarity route `[LJ-1.160]` already named, not
retried as `π` commuting with `𝒟ₒ`.

The join into `levelIn` stays the composition
`[LJ-1.477]` wrote at `lj-1.477-report.md:255-263`. That
composition uses `piCommuteLset` and `HullClosedLset`. It does
not become reachable by this return.

## 3. What NO-GO earns, and what is still owed

NO-GO names D-10 at this site: `π` and `𝒟ₒ` cannot agree without
elementarity. W3 names the cheaper inclusion. Both computation
and membership laws spend. `JoinAtD` does not. `OneWay` does
not. A `subst` between those right-hand sides is
`[UnequalTerms]`.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `piCommuteD`.
- It does not inhabit `OneWay`, `JoinAtD` or `FormulaTransport`.
- It does not inhabit `CoverWitnessesInHull`.
- It does not inhabit `HullClosedLset`.
- It does not inhabit `lset-code`.
- It does not inhabit `levelIn`.
- It does not refute `piCommuteD`.
- It does not pay `cover`.
- It does not edit `src/`.
- It does not touch `[LJ-1.487]`.

C-42: this is not a refutation. The sweep that law names does not
fire. The same unbuilt commutation already sits one layer up at
`agents/tasks/LJ-1-477/Probe477.agda:100-102` and
`agents/tasks/LJ-1-462/Probe462.agda:140-142`. I did not count
live `src/` occurrences of a false shape, because no false shape
was proved.

## 4. What the next brief needs

- Do not order `piCommuteD` from `π-compute` and the membership
  laws of `𝒟ₒ` again. They spend, and they do not join. The
  measurement is `runs/one-way-subst.out:2` (`[UnequalTerms]`)
  against membership in `𝒟ₒ (C.π y)`, with the remaining
  constructor type `JoinAtD` at `Probe489.agda:119-121`.
- Do not order an unfolding of `π` or of `𝒟ₒ` in order to spend
  those laws. W3 and step two measured that the exported laws
  spend without opening either seal. W3 median 2.56 s,
  471482368 bytes.
- Do not take `CoverWitnessesInHull` or `HullClosedLset` as a
  way to close `JoinAtD` or `OneWay`. Neither changes `step` or
  `𝒟ₒ`.
- Do not add `FormulaTransport` as a module hypothesis of this
  commutation. That hypothesis is the elementarity D-10 named.
  Assuming it makes the return a restatement of the finding.
- A proof of the commutation at this site is elementarity of
  definability along `π`, plus enough of `y` lying in `M` that
  `(y, ∈)` and `(C.π y, ∈)` match. The hull is not transitive
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:249`). Devlin 5.2
  identifies the collapse image with a level by Φ and Σ₁
  elementarity (`dev/literature/devlin-II5.md:95-106`). It does
  not commute `π` with `Def` at an arbitrary hull member.
- Re-decompose `levelIn` step 4 along that condensation route,
  or along the collapse-image route `[LJ-1.160]` measured. Do
  not keep `πCommuteLset` as a conjunct that this layer was
  going to fund.
- Need 2, `CoverWitnessesInHull`, remains independent. This
  return does not change its brief.
- What the statement cost: 54 non-blank non-comment lines, W3
  median 2.56 s, full median 2.25 s, peak RSS 478150656 bytes on
  the kept rechecks. What the shape resisted: `sett` of filtered
  `π`-images against sealed `𝒟ₒ`, and formula transport along
  `π`. What I had to weaken: nothing of the obligation. What I
  could not close: `OneWay`, `JoinAtD`, `FormulaTransport`,
  `piCommuteD`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not
  used. It is the retired dispatch index. This task measures a
  live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The
  history of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this
  task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4.
  W4 did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:72`. Quote:
  `> 5.2 Theorem (The Condensation Lemma). Let α be a limit ordinal. If`
  Also read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`
  Used: 5.2 is the literature form of condensation, and its engine
  is Φ plus Σ₁ transfer, not a commutation of `π` with `𝒟ₒ`. The
  predecessor type has no `IsOrd` on `y` and no elementarity
  hypothesis. I did not add them. I did not take 5.2 as a proof
  of `piCommuteD`.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is an inclusion at one argument. It is
  not a truncation question.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `piCommuteD`, `OneWay`, `JoinAtD`,
  `FormulaTransport` or `levelIn`.
- I did not take `HullClosedLset` or `CoverWitnessesInHull` as a
  module hypothesis.
- I did not postulate. I did not add an elementarity hypothesis.
- I did not unfold the seal on `π` or on `𝒟ₒ`.
- I did not touch `[LJ-1.487]`.
- I did not pay `cover`.
- I did not hide the constructor gap in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-489/`:

- `lj-1.489-report.md`, this report
- `Probe489.agda`, W3 and the unbuilt join
- `review-of-piCommuteD.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
