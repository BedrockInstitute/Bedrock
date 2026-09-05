# LJ-1.419 report: does the rank route discharge the consumer without the pairing parameter

slot: `coder`. Written early as a skeleton and filled as answers landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-419/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term `upper-from-rank` in
`agents/tasks/LJ-1-419/Probe419.agda`, at a generic band, with two
module hypotheses and no `sq`.

## VERDICT

**NO-GO.** The composition under the two hypotheses is three lines and
it typechecks as `from-two-hyps`. The residue `bound-into-ord`, as the
brief states it, is FALSE at this generality (D-10). The tight
correction is the consumer, or it spends the pairing. The pairing
parameter is not replaceable.

The obligation `upper-from-rank` is a hole. A green inhabitant of that
name would fire branch `go` and claim the pairing is replaceable. D-10
forbids that claim. The obstruction is `review-of-bound-into-ord.md`,
written for the branch `no-go-stated`.

The dispatched direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. The on-disk file `dev/pod/direction.md:37` in this worktree
says "NONE. The owner has written no direction yet." The dispatched
text is what I was told, so it wins. This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict.

## LITERATURE (W8), READ BEFORE ANY AGDA

Read, in this order: `dev/literature/j-hierarchy.md`,
`dev/literature/digest.md`, `dev/literature/devlin-errata.md`,
`dev/literature/devlin-II5.md`, `dev/literature/BIBLIOGRAPHY.md`.
Then the archive hit `[LJ-1.327]`. Then the Agda skeleton.

**The classical argument does bound the order type of a level by the
level's own ordinal, and it spends pairing to do it.**

SZ 1.17 (`dev/literature/j-hierarchy.md:147-149`): if `α` is closed
under the Gödel pairing function, `otp(<^A_α) = α`, and there is a
`Σ₁` surjection `α → J_α^A`. For arbitrary `α`, Jensen 1972 Lemma 2.10
still gives a `Σ₁` surjection `α → J_α^A`. SZ p. 10
(`dev/literature/j-hierarchy.md:60`) gives `J_α ∩ On = α` at limit `α`.
Devlin II.1.1(vii) (`dev/literature/devlin-II5.md:413`) is
`|L_α| = |α|` for `α ≥ ω`.

The spend is Gödel pairing, or Jensen 2.10. This tree does not form
the order type (`src/L/Ordinal/SquareLaw.lagda.md:10-11`). The
pairing route that would pay the spend is the open wall
(`agents/tasks/LJ-1-414/lj-1.414-report.md:20`).

The unrestricted residue is not an axiom with no condition this tree
meets. It is false. A literature-axiom stop does not fire. D-10 does.

## D-10

See `review-of-bound-into-ord.md`. Summary: `bound-into-ord` as a
`∀ β` is false, because `Lset α` injects into ordinals of larger
cardinality than `α` whenever it injects into `α` at all. The
corrected tight target is `|Lset α| ≤ |α|`, which is the consumer
(`src/L/StageCardinal.lagda.md:565`).

## 1. What was built

All in `agents/tasks/LJ-1-419/Probe419.agda`, module
`LJ-1-419.Probe419 {ℓ} (lem) (α₀) (oα₀)`. No `sq`.

- `_↪_` (`Probe419.agda:47-48`) and `comp-inj` (`:50-52`), local,
  three lines for the composition. Embedding composition was already
  in the consumer (`src/L/StageCardinal.lagda.md:500-502`) and in
  `agents/tasks/LJ-1-413/Probe413.agda:88-90`. This probe does not
  import either, so `sq` never enters the file as an identifier.
- Two module hypotheses: `stage-into-bound` at `[LJ-1.418]`'s type
  (`Probe419.agda:60-62`); `bound-into-ord` as the brief names it
  (`Probe419.agda:63-66`). This worktree has no `agents/tasks/LJ-1-418/`.
  The slot clause requires the predecessor's probe and report. I opened
  them in the main tree: `agents/tasks/LJ-1-418/Probe418.agda:64-65`
  and `agents/tasks/LJ-1-418/lj-1.418-report.md:19`. Verdict of
  `[LJ-1.418]`: **GO**. The type that typechecked is

      stage-into-bound : (α : S) → IsOrd α
                       → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))

  under `swo-into-ord` (`Probe418.agda:59-61`). The report is GO, so
  I inhabit that hypothesis. I did not import `Probe416`, `Probe417`
  or `Probe418`. I did not attempt the residue.
- `from-two-hyps` (`:72-85`), the composition. Fourteen non-blank
  lines, including the `where` unpacking.
- `ConsumerShape` (`:89-92`), the consumer's target verbatim
  (`src/L/StageCardinal.lagda.md:564-565`), with no `sq` in scope.
- `upper-from-rank` (`:98-99`), the obligation, a hole.

Exact type of the residue, as used (`Probe419.agda:63-66`):

```
bound-into-ord :
    (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (β : S) → IsOrd β → (⟪ Lset α ⟫ ↪ ⟪ β ⟫)
  → ⟪ β ⟫ ↪ ⟪ α ⟫
```

The band hypothesis `⟨ α ∈ˢ sucV α₀ ⟩` is unused (`:75` binds it as
`_`). Neither supplier reads it. It is kept so the type matches the
consumer.

## 2. W2 (DD4)

Generic in `α`. The two hypotheses are generic. No cardinal and no
numeral except `ω`, which the consumer's own type names. `α₀` is the
consumer's own band parameter. W2 holds.

## 3. The composition, as a type

```
from-two-hyps α oα _ infα =
  comp-inj emb (bound-into-ord α oα infα β oβ emb)
  where
  pack = stage-into-bound α oα
  β    = fst pack
  oβ   = fst (snd pack)
  emb  = snd (snd pack)
```

That is `Probe419.agda:75-85`.

Two hypothesis applications and one embedding composition. The shape
the brief named. It does not make the residue true.

## THE TWO BILLS

W3, `residue-vs-pairing`. Written after the composition was in the
file. Each claim has `file:line`.

### 1. What `bound-into-ord` demands, in one sentence

It demands that every ordinal `β` which already receives an embedding
from `⟪ Lset α ⟫` itself embeds into `α`
(`Probe419.agda:63-66`; brief `LJ-1.419.md:27-29`).

### 2. What `sq` demands, in one sentence, from the five reports

It demands an injective pairing on the members of every infinite band
ordinal, as DATA and not truncated: `[LJ-1.408]` refuted the truncated
grade (`agents/tasks/LJ-1-408/lj-1.408-report.md:25`); `[LJ-1.391]`
refuted both untruncation routes (this worktree has no
`agents/tasks/LJ-1-391/`; I opened
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-391/lj-1.391-report.md:37-38`,
routes A and B); `[LJ-1.413]` delivered the data-level recursion with
residue `amb-to-coded`
(`agents/tasks/LJ-1-413/lj-1.413-report.md:20-22`); `[LJ-1.414]`
measured that last implication NOT DECIDABLE in this tree
(`agents/tasks/LJ-1-414/lj-1.414-report.md:20`); `[LJ-1.390]` moved
the same bill onto `Init` at an internal cardinal
(`agents/tasks/LJ-1-390/lj-1.390-report.md:13-18`). The consumer
spends that pairing once, as a module parameter, at
`src/L/StageCardinal.lagda.md:17-19` and `:283`.

### 3. Whether the two are the same mathematical content in different clothes

**The unrestricted residue is not the pairing. It is false.** D-10,
`review-of-bound-into-ord.md`.

**The tight residue is the consumer, and the consumer's classical
proof spends the pairing.** SZ 1.17 bounds `otp(<^A_α)` by `α` exactly
when `α` is closed under Gödel pairing
(`dev/literature/j-hierarchy.md:147-149`). For an ordinal, members
are ordinals below it, so Gödel pairing-closure is an injective
pairing `⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫`, which is `sq α`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). Devlin II.1.1(vii) is
`|L_α| = |α|` (`dev/literature/devlin-II5.md:413`), and the archived
counting chapter stops on the square law as the one undelivered fact
(`archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:13-14`).
This tree never forms the order type
(`src/L/Ordinal/SquareLaw.lagda.md:10-11`), so the rank route cannot
pay SZ 1.17 without first building the object the square-law chapter
refused.

**The residue needs an order-type fact that itself needs a pairing.
The route is closed.** `[LJ-1.414]`'s NOT DECIDABLE is then a
statement about the architecture, not about one route.

**Archive warning `[LJ-1.327]`.**
`archive/dev/LJ-dispatch-index.md:382`: the coded square law is a
well-founded recursion, expensive, and consumed by nothing. That
verdict was: two pairing-shaped objects were NOT the same content,
because one had no consumer. Here the test goes the other way. The
tight residue and `sq` share one consumer,
`stage-card-upper` at `src/L/StageCardinal.lagda.md:564-565`, and the
classical proof of the residue spends Gödel pairing, which is `sq`.
They are the same bill. The coded-versus-ambient split of `[LJ-1.327]`
does not apply.

## 4. The consumer check

`ConsumerShape` restates `stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-565`) with no `sq` in scope.
`from-two-hyps` has that type. `upper-from-rank` is not inhabited, so
the consumer is not discharged. A term that plugs in from a false
residue has not finished.

## 5. What a GO would have changed, and what this NO-GO says instead

A GO would have removed the pairing parameter at
`src/L/StageCardinal.lagda.md:17-19` and the one spend at `:283`
(`module B = Bound α oα infα (sq α α∈suc infα)`), and replaced both
with the two hypotheses. That is what `[LJ-2.5]` would have been
owed.

This NO-GO says the pairing is necessary, not merely convenient. The
measured wall on the pairing route
(`agents/tasks/LJ-1-414/lj-1.414-report.md:20`) is a statement about
the architecture.

## 6. W4

No module was retired. Nothing moved to `archive/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:382` "pairomega is a well-founded RECURSION, and a coded square law is consumed by NOTHING today". Read. Used as `[LJ-1.327]`: two pairing-shaped objects are not the same content when one has no consumer. Here the tight residue and `sq` share one consumer, `stage-card-upper`.
- `archive/dev/JOURNAL-archived.md`: declined. It is the retired-route journal. This task measures a live consumer against a live residue. Not used.
- `archive/dev/JOURNAL.md`: declined. It is the archived per-episode journal. The history of this campaign is the task directories. Not used.
- `dev/ARCHIVE.md`: declined. This task does not retire a module. Not used.
- `archive/dev/ORCHESTRATION.md`: declined. It is the archived orchestrator rulebook. This task writes a probe and a report. Not used.
- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:13-14` "the one fact the bound consumes that is not yet delivered is the square law". Read. The archived counting chapter stops on the square law.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:335-336` "A canonical injection needs a well-order on the INJECTIONS, which is what `<_L` supplies classically". Read. Used: the pairing as DATA cannot be untruncated by selection, which is the `[LJ-1.391]` wall.
- `dev/literature/devlin-II5.md:413` "|L_α| = |α| for α ≥ ω". Read. Used: the consumer is Devlin's counting equation.
- `dev/literature/terms-2026-08.md`: declined. It is a terminology dossier for glossary renderings. Not used.
- `dev/literature/geology.md`: declined. It is a geology-sources dossier. Not used.
- `dev/literature/digest.md:241` "surjection g : α -> J_α^A when α is closed under Gödel pairing (SZ 1.17)". Read. Used: the classical bound of otp by α spends pairing-closure.
- `dev/literature/j-hierarchy.md:147-149` "if α is closed under the Gödel pairing function then otp(<^A_α) = α.". Read. Used in THE TWO BILLS: SZ 1.17 spends Gödel pairing to bound the order type.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root. I did not
set `GHCRTS`. No heap event. `pgrep` showed only
`scripts/ops/agda-watchdog.sh`, no Agda binary, before the run.

- Obligation as a hole, one run, exit 42, `UnsolvedInteractionMetas`
  at `Probe419.agda:99.21-25`: **0.96 s** real (`runs/hole-2.out`).
  Printed `Checking`. The only error is that hole. `from-two-hyps`
  elaborated; a type error in the composition would have appeared
  beside the hole and did not.
- Earlier in this directory, three green runs inhabited
  `upper-from-rank = from-two-hyps` and exited 0: 0.76 s, 0.74 s,
  0.74 s (`runs/green-{1,2,3}.out`). Those runs are the composition
  under the two hypotheses. They are not the obligation. The
  obligation is the hole.

Estimate for the Agda: about 12 code lines, a comparable of SHAPE from
`agents/tasks/LJ-1-413/Probe413.agda:106`. Measured, `comp-inj` is 3
non-blank lines and `from-two-hyps` is 14. Nothing is funded against
the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-419/`:

- `lj-1.419-report.md`, this report
- `review-of-bound-into-ord.md`, the D-10 obstruction
- `Probe419.agda`, the probe
- `runs/`, the Agda transcripts named above
