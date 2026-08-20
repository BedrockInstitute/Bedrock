# LJ-1.418 report: the stage injects into an ordinal, at every ordinal, with no pairing

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-418/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-418/Probe418.agda`:

    stage-into-bound : (α : S) → IsOrd α
                     → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))

at EVERY ordinal, with no `Init`, no band and no infiniteness. Take
`swo-into-ord` at `[LJ-1.417]`'s type as a module hypothesis. Do not
import `Probe417`. Do not rebuild the rank.

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-418/Probe418.agda`,
exit 0, median 0.99 s on three forced rechecks) and it PASSes the
program's witness meter (`scripts/pod/witness.py --code LJ-1-418 --brief
agents/tasks/LJ-1-418/LJ-1.418.md`, exit 0, 1.05 s, 0 UNRESOLVED of 1).
The term is an untruncated injection from every stage into some ordinal.
There is no pairing in the telescope. There is no `Init`, no band and
no infiniteness.

The dispatched direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. The on-disk file `dev/pod/direction.md:38` in this worktree
says "NONE. The owner has written no direction yet." The dispatched
text is what I was told, so it wins. This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict.

## 1. What was built

All in `agents/tasks/LJ-1-418/Probe418.agda`, module
`LJ-1-418.Probe418 {ℓ} (lem)`.

- `_↪_` (`:40-41`), as Cardinal writes it (`src/L/Cardinal.lagda.md:47-48`).
- W3: `carry-at-generic` (`:50-51`). Body is
  `carry (Lset α) (orderAt α oα)`.
- One module hypothesis (`:59-61`): `swo-into-ord`, packaged from
  `[LJ-1.417]`. I did not import `Probe417`. I did not rebuild the rank.
- `stage-into-bound` (`:64-66`). Body is
  `swo-into-ord (carry-at-generic α oα)`.

**Predecessor, opened as the slot clause requires.** I read
`agents/tasks/LJ-1-417/Probe417.agda` and
`agents/tasks/LJ-1-417/lj-1.417-report.md` in the sibling worktree
`.pod-state/worktrees/LJ-1-417`. Those files are not in THIS worktree.
Verdict of `[LJ-1.417]`: **GO**
(`agents/tasks/LJ-1-417/lj-1.417-report.md:18-19`). The type that
typechecked is `Probe417.agda:80`:

    swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))

under the module telescope `Probe417.agda:44-51`: `{A : Type ℓ}`,
`w : SWO {ℓc = ℓ} A`, and the three rank parameters `swo-rank`,
`swo-rank-ord`, `swo-rank-mono` taken from `[LJ-1.416]`. The brief of
this task forbids rebuilding that rank. The hypothesis here is the
same Sigma, with the rank left inside 417, as a function of a small
carrier and its `SWO` (`Probe418.agda:60-61`). That is the packaged
form the brief named. The report is GO, so I inhabit it.

## 2. W3: `carry-at-generic`, first

**GO.** The brief named the composition of `carry` and `orderAt` at a
generic ordinal as the widest unmeasured term, because the only
delivered consumer names `SiteBound.β`. The probe is
`carry-at-generic` (`Probe418.agda:50-51`).

```agda
carry-at-generic : (α : S) → IsOrd α → SWO {ℓc = ℓ} ⟪ Lset α ⟫
carry-at-generic α oα = carry (Lset α) (orderAt α oα)
```

No extra hypothesis. No `Init`, no band, no infiniteness, no
`SiteBound`. `orderAt` stayed sealed. There is no `unfolding` in the
file. The site bound supplies nothing this composition needs.

**TWO non-blank code lines** for `carry-at-generic`. The estimate was
about 4. The body is one application of each, as the brief said.

The tree already names this composition `stageOrder`
(`src/L/Choice/Step.lagda.md:738-739`). This probe restates it from
`carry` and `orderAt` at a generic ordinal, which is the measurement
the brief asked for. The two convert: same body, same type.

Stated and run alone, before the Sigma. Three runs, one Agda process
at a time, every dependency warm, from the repository root, caliber
`-A64m -I0 -M8g`:

- `runs/w3-1.out`: 1.03 s real, printed `Checking`, exit 0.
- `runs/w3-2.out`: 0.98 s real, exit 0.
- `runs/w3-3.out`: 0.97 s real, exit 0.

Median of the three **0.98 s**.

## 3. Levels, measured

This was the one thing to watch.

- Order level: `ℓ-suc ℓ`. `SWO` is imported from
  `L.WellOrder.Base {ℓ-suc ℓ}` (`Probe418.agda:32`, matching
  `src/L/Choice/Step.lagda.md:58`).
- Carrier of `orderAt α oα`: `Mem (Lset α)`, at `ℓ-suc ℓ`
  (`src/L/Choice/Step.lagda.md:217-218`).
- Carrier of `carry-at-generic α oα`: `⟪ Lset α ⟫`, at `ℓ`. The type
  annotation `SWO {ℓc = ℓ}` (`Probe418.agda:50`) was accepted. That is
  the drop `carry` exists for.
- `[LJ-1.417]`'s hypothesis, as this brief required and as written at
  `Probe418.agda:60-61`, is `{A : Type ℓ}` and `w : SWO {ℓc = ℓ} A`,
  with the same order level `ℓ-suc ℓ`. Conclusion
  `Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))`. No rank. No `∥ ∥₁`.

**The hypothesis accepted those two levels unchanged.** The application
`swo-into-ord (carry-at-generic α oα)` is the body of
`stage-into-bound` (`Probe418.agda:66`). No coercion, no lift, no
level annotation on the application. A mismatch would have been a
type error. There was none. That mismatch, if it had existed, was the
whole finding of this task. It does not exist.

## 4. The obligation

`stage-into-bound` (`Probe418.agda:64-66`) is three non-blank code
lines. Together with W3, **FIVE non-blank code lines** for the
composition. The estimate for the whole obligation was about 15. The
body is one hypothesis application. The rank stays inside 417.

Three full-file runs after the composition landed, same caliber, one
Agda process at a time, warm:

- `runs/full-1.out`: 1.07 s real, printed `Checking`, exit 0.
- `runs/full-2.out`: 0.98 s real, exit 0.
- `runs/full-3.out`: 0.99 s real, exit 0.

Median of the three **0.99 s**.

Witness: `runs/witness.out`, exit 0, 1.05 s,
`agents/tasks/LJ-1-418/Probe418.agda::stage-into-bound` PASSes.

The type of `stage-into-bound` is the brief's type, verbatim, under
the one module hypothesis. There is no `∥ ∥₁`. There is no bound
relating `β` and `α`. I did not state one and I did not attempt one.

## 5. `orderAt` is opaque, and I did not unfold it

`orderAt` is sealed at `src/L/Choice/Step.lagda.md:729-731`. This
probe names it (`Probe418.agda:51`) and does not look inside. There
is no `unfolding` pragma in the file. P-y: a consumer that only names
a sealed definition pays no unfold. P-l: the type quantifies over
`α` and `Lset α`. It does not name a transparent `sucV`-chain. The
full-file median 0.99 s is the measured cost of that naming.

## 6. W2 (DD4)

The term is generic in `α`. It names no band, no cardinal and no
numeral. It does not carry `α₀`, `sucV α₀` or `ω` into any telescope.
`swo-into-ord` is generic in the small carrier. This task instantiates
it at `A := ⟪ Lset α ⟫`. The rank is not rebuilt. Both proofs share
that term.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:308`
  "A4 is 88x cheaper because orderAt is sealed". That row records that
  a consumer that NAMES the sealed `orderAt` is cheap. This probe names
  it and does not unfold it (`Probe418.agda:51`). The measured full-file
  median 0.99 s is the same shape of cost.
- `archive/src/2026-08-09-rud-route/L/Choice/Stage.lagda.md:123`
  "Inhabited u → LeastOrd (meets u)". The archived stage chapter
  never used a well-order of a stage's members. There is no `SWO`, no
  `orderAt`, no `carry` and no `stageOrder` in that file. What it used
  is `leastOrd` on the property `meets u`, generic in the cell `u`. That
  is a least-ordinal operator on a property of ordinals, not an order
  on `Mem (Lset α)` at an ordinal `α`. The archive cannot show a generic
  use of `orderAt`, because it never used `orderAt`.
- `archive/dev/JOURNAL-archived.md`: DECLINED. It is the execution
  history of the retired route. It holds no statement about feeding
  `orderAt` at a generic ordinal to a small-carrier well-order term.
- `archive/dev/JOURNAL.md`: DECLINED. The file is archived 2026-08-20
  as the per-episode journal. It is not a source for this composition.
- `dev/ARCHIVE.md`: DECLINED. The registry of retired modules names
  other well-orders (`L.Godel.Name`, `L.WellOrder.Tree`, shortlex on
  labelled trees). Nothing in it is `orderAt` at a generic ordinal.
- `archive/dev/ORCHESTRATION.md`: DECLINED. It is the retired
  orchestrator's operating rules. It holds no mathematics about stages
  or well-orders.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:83`
  "So a proof that only needs cardinal arithmetic never needs an injection as".
  The ambient least-cardinal arrow is truncated at
  `src/L/Cardinal.lagda.md:133`. This term does not pass through it.
  The obligation is an untruncated injection as data. The sources do
  not supply that untruncation. The tree supplies it by feeding the
  tower's own order to `[LJ-1.417]`'s term.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  `dev/literature/digest.md:241`
  "when α is closed under Gödel pairing (SZ 1.17)". SZ defines the
  order at every `β`. The bound of the order type by `α` is a later
  step, and only under pairing-closure. This task's term gives some
  `β` and does not relate it to `α`. That bound is `[LJ-1.419]`.
- `dev/literature/devlin-II5.md`: DECLINED. Its well-order of `L_α` is
  the hull's least-witness device in condensation, not an injection of
  a stage's members into an ordinal.
- `dev/literature/terms-2026-08.md`: DECLINED. "canonical well-ordering"
  there is Gödel's order of `Ord × Ord`, the pairing product. This
  composition does not use pairing.
- `dev/literature/geology.md`: DECLINED. Nothing in it bears on
  `orderAt`, `carry`, or an injection of a stage into an ordinal. Why
  not: it is a geology-sources dossier.

## 7. What the next brief needs

- The tower's own order, carried to the small member type, is accepted
  by `[LJ-1.417]`'s term at every ordinal. The composition is
  `Probe418.agda:66`. The price is 0.99 s median, five code lines.
- The term gives some ordinal `β`. It does not say `β` is small enough
  for anything. `[LJ-1.419]` measures the pull-back to `α`.
- A GO here says the consumer parameter `sq`
  (`src/L/StageCardinal.lagda.md:17-19`) exists only to build such an
  arrow, and that parameter may be unnecessary. That is the measurement
  `[LJ-2.5]` asks for. This task does not discharge the consumer. It
  discharges the first half.
- Nothing in this file had to be weakened. The hypothesis type is
  `Probe418.agda:60-61`. The levels matched.

## THE TREE AS I LEAVE IT

I changed two files, and both are mine: `agents/tasks/LJ-1-418/Probe418.agda`
and `agents/tasks/LJ-1-418/lj-1.418-report.md`. Run logs sit under
`agents/tasks/LJ-1-418/runs/`. No file outside `agents/tasks/LJ-1-418/`
moved. I ran no `git add`, no commit and no push. The probe is green.
The first accept failed conjunct 6 for missing `ARCHIVE USED` and
`LITERATURE USED`. Those sections are now in this file.
