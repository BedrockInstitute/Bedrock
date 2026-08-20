# LJ-1.431 report: the arrow as DATA at the coded least cardinal

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-431/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-431/Probe431.agda`, at a
GENERIC L-element `a : S` with `oa : IsOrd (fst a)`, at a GENERIC
ordinal `γ` with `oγ : IsOrd γ`, and with ONE bare module hypothesis
`nonempty-coded`:

    arrow-at-kappaC : ⟪ fst a ⟫ ↪ ⟪ fst κC ⟫

`κC` is the coded selection on the ambient carrier, rebuilt in this
probe. The input is truncated. The output is not. No hypothesis is an
ambient injection.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. Nothing was written into `src/`.

## VERDICT

**GO.** The obligation typechecks
(`agents/tasks/LJ-1-431/Probe431.agda:133-134`, exit 0, median 1.60 s
on three forced rechecks) and it PASSes the program's witness meter
(`python3 scripts/pod/witness.py --code LJ-1-431 --brief
agents/tasks/LJ-1-431/LJ-1.431.md`, exit 0, 1.59 s, 0 UNRESOLVED of 1,
`probe_red=False`). `.venv/bin/python` is absent in this worktree. The
witness meter ran under `python3`. I added no dependency.

I did not write `review-of-arrow-at-kappaC.md`. The verdict is GO.

The device restates at a generic ordinal `γ`. It is not tied to
`stageBound`'s `β`. The two types meet with no repackaging:
`fst (snd selected)` is definitionally the truncated coded existence
at `κC`, and that is the input of `coded-to-arrow-at`. No ambient
injection sits in the telescope, truncated or otherwise.

This GO is at `κC`. It does not inhabit `kappa-arrow-data` at `κL`.
C-42: a measurement of one site does not measure the other. The
campaign residue named at
`agents/tasks/LJ-1-421/lj-1.421-report.md:60` is one untruncated
arrow at `κL a oa`. This dispatch does not discharge that residue.

## D-10: WHICH LINES OF Probe424.agda:80-100 MENTION β

Written before any Agda. C-42: `[LJ-1.424]` measured the device at
ONE bound. That measurement does not measure a different bound.

Predecessor GO, not NO-GO, not FALSE:
`agents/tasks/LJ-1-424/lj-1.424-report.md:23` reads "**GO.** The
obligation typechecks". The type that typechecked is at
`agents/tasks/LJ-1-424/Probe424.agda:91-95`. I take that type and
that verdict.

**LINES THAT MENTION `β` (the carrier, the order, the crossing).**

- `Probe424.agda:81` `Good4 : Mem (Lset β) → hProp (ℓ-suc ℓ)`.
  The carrier is `Mem (Lset β)`.
- `Probe424.agda:85` `∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁`.
  The truncated input is sited at `β`. `up` is `SiteBound.up`, typed
  at `Mem (Lset β)`.
- `Probe424.agda:86` `Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good4 F`.
  The selected member and the well-order are at `β`.
- `Probe424.agda:87` `leastOf (orderAt β oβ) lem Good4 h`.
  The call names `β` twice: the order and, through `Good4`, the
  carrier.
- `Probe424.agda:92` the same truncated input as `:85`.
- `Probe424.agda:94` `readL a b (up (fst chosen) , fst (snd chosen))`.
  `up` is again `SiteBound.up` at `β`.

`open SiteBound a` at `Probe424.agda:79` is how `β`, `oβ` and `up`
enter. `β` is `stageBound (fst a) (snd a) .fst`
(`src/L/Cardinal.lagda.md:165-166`).

**LINES IN :80-100 THAT ARE FREE OF `β`.**

- `Probe424.agda:82` the payload: `InjCode (up A) a b` and
  `isPropInjCode (up A) a b`. `InjCode` at
  `src/L/Cardinal.lagda.md:223-228` names no stage. `isPropInjCode`
  at `Probe424.agda:64-69` is generic in `F a b`.
- `Probe424.agda:91` the name `coded-to-arrow`.
- `Probe424.agda:93` the RESULT type `⟪ fst a ⟫ ↪ ⟪ fst b ⟫`.
  `_↪_` at `src/L/Cardinal.lagda.md:47-48` names no stage.
- `Probe424.agda:95-96` the `where` that feeds `chosen` to `readL`.

`readL` at `src/L/CantorBernstein.lagda.md:33-35` quantifies over a
bare `S` and names no stage. `orderAt` at
`src/L/Choice/Step.lagda.md:730-731` is already generic:
`(γ : S) → IsOrd γ → SWO (Mem (Lset γ))`. The crossing at
`src/L/Cardinal.lagda.md:171-172` is `up (x , m) = x , Lset→isL β oβ x m`,
and `Lset→isL` at `src/L/Constructible.lagda.md:395-396` is generic
in the ordinal.

**WHAT THE RESTATEMENT AT `γ` THEREFORE COSTS.**

The device body is `leastOf` plus `orderAt` plus `readL`. Nothing in
that body is `stageBound`-specific. The restatement replaces
`open SiteBound a` with a parameterized crossing `upγ` at a generic
ordinal `γ` with `oγ`. The carrier becomes `Mem (Lset γ)`. The order
becomes `orderAt γ oγ`. The crossing becomes
`upγ (x , m) = x , Lset→isL γ oγ x m`. The payload, the `isProp`
witness, and the result type do not move.

No Tarskian obstruction is in view: the statement does not claim an
injection into a smaller set. It reads a coded graph as a function.
No cardinality obstruction is in view at a generic pair. The target
is not the residue `[LJ-1.421]` named at `κL`. This task's target is
`κC`.

The restatement typechecked. The NO-GO (a term that still named
`stageBound`'s `β`) did not fire.

## 1. What was built

All in `agents/tasks/LJ-1-431/Probe431.agda`, module
`LJ-1-431.Probe431 {ℓ} (lem)`, inner
`module _ (a : S) (oa : IsOrd (fst a)) (γ : V ℓ) (oγ : IsOrd γ)`,
then a second inner module on `nonempty-coded`.

- `clause4`, `clause4-isProp`, `isPropInjCode`
  (`Probe431.agda:69-82`). Reconstruction of
  `Probe424.agda:57-70`. Generic in `F a b`. Names no stage.
- `upγ` (`:95-96`). The SiteBound crossing at a parameter `γ`.
  `Lset→isL γ oγ`. Not `stageBound`.
- `Good4` (`:98-99`). Four-conjunct `InjCode` as
  `hProp (ℓ-suc ℓ)`, now over `Mem (Lset γ)`.
- `coded-to-arrow-at` (`:101-106`). The W3 term. `readL a b` on
  `upγ (fst chosen)` and the four conjuncts. Generic in `b`.
- `hSucα`, `upα` (`:108-114`). The ambient crossing of
  `LeastCardInjL` at `a` (`src/L/Cardinal.lagda.md:72-80`),
  rebuilt, not imported from that module.
- `w` (`:116-118`). Sealed `ordSWO` on `⟪ sucV (fst a) ⟫`, the
  same seal as `src/L/Cardinal.lagda.md:90-92`.
- `CodedInjP'` (`:120-122`). Truncated coded existence at `γ`,
  range `upα d`.
- `selected` (`:127-128`). `leastOf w lem CodedInjP' nonempty-coded`.
  `nonempty-coded` is a module hypothesis. This probe does not
  inhabit it. `[LJ-1.429]` owes that existence. I did not import
  that task's probe. I did not copy a type out of its brief. I do
  not assert its statement.
- `κC` (`:130-131`). `upα (fst selected)`.
- `arrow-at-kappaC` (`:133-134`).
  `coded-to-arrow-at κC (fst (snd selected))`.

`kappaC-ord` is not a hypothesis and not a conclusion. `[LJ-1.430]`
owes it. This term does not need it.

I did not rebuild `Small`. I did not rebuild a coding primitive.
`readL` already carries that application
(`src/L/CantorBernstein.lagda.md:36-38`). Applying it cost one call.

## 2. W3: `coded-to-arrow-at`

**GO.** Typechecked ALONE, with the selection of step two omitted,
applied to a bare truncated hypothesis. Caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. The probe interface
was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-431/Probe431.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.62 | 404799488 |
| `runs/w3-2.out` / `w3-2.time` | 1.70 | 404799488 |
| `runs/w3-3.out` / `w3-3.time` | 1.65 | 404832256 |

Median wall **1.65 s**. Median peak RSS **404799488 bytes**. No heap
event.

The device restates at a bound that is not `stageBound`'s. No term
depended on `β`. The NO-GO did not fire.

## 3. Import cost of `L.CantorBernstein`

Plain wall figure, separate from W3. One run of the device with
`readL` and the `L.CantorBernstein` import omitted, `leastOf`
retained, result discarded (`runs/import-base.out` /
`import-base.time`): 1.66 s, RSS 404717568, exit 0.

W3's median with the import is 1.65 s. The delta is not a wall.
`L.CantorBernstein.agdai` and `L.GCH.agdai` were already present
under `_build/2.8.0/agda/src/L/`. I did not delete another
chapter's interface. Loading the compiled interface did not move
the figure. No heap event.

The chapter warns that an unsealed `Small` application exhausts an
8 GB heap (`src/L/InjChain.lagda.md:550-551`). That event did not
occur. `readL` carries the sealed application.

## 4. Step two: the selection and the join

**GO.** The two types meet with no repackaging. There is no
elaborator quote, because there was no mismatch.

`fst (snd selected)` at `Probe431.agda:134` has type
`⟨ CodedInjP' (fst selected) ⟩`, which is
`∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα (fst selected)) ∥₁`
(`Probe431.agda:120-122` and `:127-128`). `κC` is
`upα (fst selected)` (`:130-131`). That is definitionally the
input of `coded-to-arrow-at κC` (`:101-103`). The application
typechecks as written (`:134`).

Three forced rechecks of the full file, exit 0 every time, each
printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.60 | 393461760 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.64 | 393445376 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.60 | 393461760 |

Median wall **1.60 s**. Median peak RSS **393461760 bytes**. No heap
event. First full check after the join: 1.62 s, RSS 393445376
(`runs/full-1.out` / `full-1.time`), exit 0.

## 5. W2 (DD4)

The mathematics is written once at a generic carrier. `isPropInjCode`
is generic in `F a b`. `coded-to-arrow-at` sits in
`module _ (a : S) (oa : IsOrd (fst a)) (γ : V ℓ) (oγ : IsOrd γ)`
and names no cardinal, no band, no numeral and no `ω`. The device
does not know what `b` is. The selection instantiates `b` at `κC`.
Both proofs can share the device: the carrier is a pair of an
L-element and an ordinal, not a named cardinal.

`oa` is used only by the ambient crossing `upα` and the sealed
`w`. The device `coded-to-arrow-at` does not mention `oa`.

## 6. Which ordinal the arrow lands at, and what still stands

The arrow lands at `κC` (`Probe431.agda:130-134`): the least
member of the ambient carrier of `a` that admits a coded injection
from `a` with graph in `Lset γ`. It does not land at `κL`, the
ambient least cardinal of `LeastCardInjL`.

What still stands between the two:

- `nonempty-coded` is a hypothesis. `[LJ-1.429]` owes it. This
  dispatch does not inhabit it and does not assert it.
- `kappaC-ord` is owed by `[LJ-1.430]`. This dispatch does not
  assume it and does not need it.
- An untruncated arrow at `κL` remains the campaign residue
  (`agents/tasks/LJ-1-421/lj-1.421-report.md:60`). `[LJ-1.422]`
  refused that object at the ambient site. C-42: this GO does not
  move that refusal.
- Equality of `κC` and `κL` is not a theorem of this probe.

A GO here does not discharge that residue. It puts an untruncated
arrow at a coded ordinal in the tree. The widened bound of
`[LJ-1.429]` is usable: the device is no longer tied to
`stageBound`.

What resisted: nothing. The types matched. No weakening.

What the next brief needs: a producer of `nonempty-coded`, or a
ruling that the trophy may stay at `κC`. This term is the read-off
at the coded least cardinal. It is not the existence, and it is
not the ambient least cardinal.

Shape comparable, never a size comparable:
`agents/tasks/LJ-1-424/Probe424.agda:57-100` is the device with
its `isProp` witness. This probe is that block with `β` made a
parameter, plus one selection and one application. Nothing is
funded against the estimate.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`
  Read. `archive/dev/LJ-dispatch-index.md:1`
  quotes: # THE `LJ` DISPATCH INDEX, archived 2026-08-18
  Declined: archived dispatch rows. This task's live producer is
  `dev/pod/queue.toml`. The term does not consult a retired row.
- `archive/dev/JOURNAL-archived.md`
  Used. `archive/dev/JOURNAL-archived.md:1732`
  quotes: "plan rather than the target. The untruncated equivalence remains unavailable (T31's wall) and the"
  A GO on `_↪_` as data at `κC` does not move that wall. The door is
  an injection. It is not an equivalence.
- `dev/ARCHIVE.md`
  Read. `dev/ARCHIVE.md:1`
  quotes: # ARCHIVE.md: the archive registry
  Declined: not used. No module was retired. W4 does not apply.
- `archive/dev/JOURNAL.md`
  Read. `archive/dev/JOURNAL.md:1`
  quotes: # ARCHIVED 2026-08-20
  Declined: retired per-episode journal. The record of this task is
  this directory.
- `archive/dev/STATUS-archived.md`
  Read. `archive/dev/STATUS-archived.md:1`
  quotes: # STATUS-archived: the goal table of the internalization route
  Declined: archived goal table of a retired route. The live screen
  is `dev/pod/screen.toml`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`
  Used. `dev/literature/truncation-and-selection.md:146`
  quotes: "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`"
  and `dev/literature/truncation-and-selection.md:148`
  quotes: "index is a proposition. **A data payload does not come out.**"
  The device at `γ` has an hProp payload (`InjCode`). The coded
  selection on the ambient carrier has an hProp payload (truncated
  coded existence). Both come out. An ambient injection does not.
- `dev/literature/devlin-II5.md`
  Used. `dev/literature/devlin-II5.md:129`
  quotes: "ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))"
  That is the classical least-witness guard. `leastOf` is that guard
  (`src/L/WellOrder/Base.lagda.md:158-160`).
- `dev/literature/digest.md`
  Used. `dev/literature/digest.md:58`
  quotes: "- **Q4 (the canonical well-order).** Stage-first, then minimal producer"
  `orderAt` is the live stage-first order on members. It is generic
  in the ordinal (`src/L/Choice/Step.lagda.md:730`).
- `dev/literature/terms-2026-08.md`
  Read. `dev/literature/terms-2026-08.md:1`
  quotes: # The terminology dossier: fourteen renderings for the owner's ruling
  Declined: translation terms. This task writes no glossary entry.
- `dev/literature/geology.md`
  Read. `dev/literature/geology.md:1`
  quotes: # Geology dossier: set-theoretic geology sources and the five questions
  Declined: geology sources. This probe does not touch grounds or
  the mantle.
