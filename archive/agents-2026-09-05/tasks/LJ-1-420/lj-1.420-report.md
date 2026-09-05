# LJ-1.420 report: assemble the main chain into one term

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-420/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `chain-upper` in `agents/tasks/LJ-1-420/Probe420.agda`.
It is `L.StageCardinal`'s own `stage-card-upper`, reached by instantiating
that module with `[LJ-1.413]`'s pairing. One named hypothesis:
`amb-to-coded` at `[LJ-1.414]`'s delivered type.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`chain-upper` is the consumer's own delivered statement
(`src/L/StageCardinal.lagda.md:564-565`):

    stage-card-upper : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
                     → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫

Its truth at this generality is the consumer's claim, not a new one.

The hypothesis taken is `[LJ-1.414]`'s delivered type, cited at the probe,
never at a brief (`agents/tasks/LJ-1-414/Probe414.agda:134-139`):

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

It is not `[LJ-1.413]`'s hypothesis type
(`agents/tasks/LJ-1-413/Probe413.agda:232-236`), which concludes
`(IsCardinalL x → Empty.⊥)`.

`[LJ-1.414]`'s report is NO-GO on inhabiting that type
(`agents/tasks/LJ-1-414/lj-1.414-report.md:51`). The statement is not named
FALSE. It is not decidable in this tree
(`agents/tasks/LJ-1-414/lj-1.414-report.md:20`). This task takes the type
as a module parameter and does not inhabit it.

The conversion from the 414 conclusion to the 413 conclusion is the
definition of `IsCardinalL` (`src/L/Cardinal.lagda.md:230-233`): a code at
`d` refutes `IsCardinalL x`.

## VERDICT

**GO.** `chain-upper` typechecks
(`agents/tasks/LJ-1-420/Probe420.agda:97-99`, exit 0, median 1.66 s on
three forced rechecks) and PASSes the program's witness meter
(`scripts/pod/witness.py --code LJ-1-420 --brief
agents/tasks/LJ-1-420/LJ-1.420.md`, exit 0, 1.67 s, 0 UNRESOLVED of 1,
`probe_red=False`). It is `Upper.stage-card-upper` after the module is
instantiated with `[LJ-1.413]`'s `plugs-in`. The induction is not
restated. The unfolding join of the two `κL` seals was heap-safe. One
hypothesis remains: `amb-to-coded` at `[LJ-1.414]`'s delivered type.

## 1. W2

Everything is written once at a generic carrier. The module is generic in
`ℓ`. `α₀` and `oα₀` are the consumer's own parameters
(`src/L/StageCardinal.lagda.md:15-16`). `chain-upper` quantifies over a
generic `δ : V ℓ`. The imported terms and the conversion are generic in
their site. No site, no ordinal and no numeral is named anywhere in the
file except `ω`, which the consumer's own type names.

The counting bound lives once in `L.StageCardinal`. This file instantiates
that module. It does not copy the induction. W2 holds. There is no fixed
form to report.

W4 does not fire: no module was retired.

## 2. W3: `unfolding-cost`, first

**GO.** The widest unmeasured term was the join of the two `κL` seals.
`Probe406.agda:82` and `Probe413.agda:136` each declare an opaque `κL`.
Direct application reports unequal terms
(`dev/pod/audit-2026-08-20.md:132`). The probe is `unfolding-cost`
(`Probe420.agda:58-66`). Its type names 413's atom. Its body is 406's
`init-at-kappa`. One `unfolding` clause over both seals.

Stated and run alone, before pairing and `L.StageCardinal` were added.
Three forced rechecks, probe interface deleted before each run,
dependencies warm, caliber `-A64m -I0 -M8g`, one Agda process:

| run | wall s | peak RSS (bytes) | log |
|---|---|---|---|
| 1 | 1.81 | 419790848 | `runs/w3-1.out` |
| 2 | 1.53 | 419790848 | `runs/w3-2.out` |
| 3 | 1.53 | 419823616 | `runs/w3-3.out` |

Median wall **1.53 s**. Median peak RSS **419790848 bytes**. Exit 0 every
time. No heap event. `[LJ-1.398]`'s 8 GB wall was the transparent
`LeastCardInjL.κ` (`agents/tasks/LJ-1-398/lj-1.398-report.md:143-144`).
This unfolding of two already-sealed wrappers is not that style. It did
not transfer by analogy: it was measured here.

NINE non-blank code lines for `unfolding-cost`. The estimate for the
whole Agda was about 45 code lines, a comparable of SHAPE with
`[LJ-1.413]`'s hypothesis block at
`agents/tasks/LJ-1-413/Probe413.agda:219-232`. Nothing is funded against
the estimate.

## 3. The assembly

All in `agents/tasks/LJ-1-420/Probe420.agda`, module
`LJ-1-420.Probe420 {ℓ} (lem) (α₀) (oα₀)`.

Imported, not rebuilt:

| piece | source | role |
|---|---|---|
| `isPropInjCode` | `Probe401.agda:48` | proposition of `InjCode` |
| `code-as-data` | `Probe411.agda:82` | truncated code to data |
| `coded-descent` | `Probe412.agda:148` | descent target as data |
| `init-at-kappa` | `Probe406.agda:180` | `Init` at the sealed `κ` |
| `plugs-in` | `Probe413.agda:326` | pairing, the consumer parameter |

`Probe414` is not imported. It is a hole (`Probe414.agda:139`). The type
is restated as the module parameter `amb-to-coded`
(`Probe420.agda:76-80`).

`Probe407` is not imported. `[LJ-1.413]` restated that slice. The seals
that had to convert were 406 and 413.

The conversion `not-card-from-amb` (`Probe420.agda:83-89`) is not a
predecessor term. It is `IsCardinalL`'s own Pi
(`src/L/Cardinal.lagda.md:230-233`) applied to 414's conclusion. Body:
one line (`:89`).

The pairing (`:91-93`) is `P413.plugs-in` applied to `unfolding-cost`, to
412's `coded-descent` after 411 and 401, and to `not-card-from-amb`.
`module SC = StageCardinalMod lem α₀ oα₀ pairing` (`:95`).
`chain-upper` is `SC.Upper.stage-card-upper` (`:97-99`).

The consumer takes the pairing as a module parameter
(`src/L/StageCardinal.lagda.md:17`). The pairing exists before the
module opens. The output is the bare injection
(`src/L/StageCardinal.lagda.md:564`).

Measured size, non-blank code lines, comments excluded:

| piece | lines | site |
|---|---|---|
| `unfolding-cost` | 9 | `Probe420.agda:58-66` |
| `amb-to-coded` telescope | 5 | `:76-80` |
| `not-card-from-amb` | 7 | `:83-89` |
| `pairing` | 3 | `:91-93` |
| `module SC` | 1 | `:95` |
| `chain-upper` | 3 | `:97-99` |

28 code lines. The estimate was about 45. Comparables of SHAPE, not of
size.

## 4. Full-file runs

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before each timed run.

- First check after the assembly landed: 1.69 s, exit 0, peak RSS
  421183488 bytes. Printed `Checking`. `runs/full-1.out`.
- Three forced rechecks: 1.66 s, 1.66 s, 1.67 s. Peak RSS 421232640,
  421183488, 421167104 bytes. Median wall **1.66 s**. Median peak RSS
  **421183488 bytes**. Exit 0 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.67 s, 0 UNRESOLVED of 1,
  `probe_red=False`.

No heap event. The StageCardinal instantiation did not move the order of
magnitude against the W3-only file (median 1.53 s, 419790848 bytes).

## THE REMAINING BILL

`chain-upper` still carries **exactly one** hypothesis. It is
`amb-to-coded`. It is `[LJ-1.414]`'s delivered type, not a type this
assembly added.

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

Site: `agents/tasks/LJ-1-420/Probe420.agda:76-80`, copied from
`agents/tasks/LJ-1-414/Probe414.agda:134-139`. Hole at
`Probe414.agda:139`. Verdict there: NO-GO on inhabiting it, not FALSE
(`agents/tasks/LJ-1-414/lj-1.414-report.md:51`, `:20`).

It is `amb-to-coded`. It is not a second hypothesis. The conversion
`not-card-from-amb` is inhabited. `isPropInjCode`, `code-as-data`,
`coded-descent`, `init-at-kappa` and `plugs-in` are imported delivered
terms. No extra module parameter was forced.

`L ⊨ GCH`'s counting leg reduces, at every band ordinal, to this one
type. That is what `[LJ-2.5]` reads.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. It is a dispatch index. This task
  instantiates a live consumer.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the
  retired route". Declined. The retired-route journal does not bear on
  the seal join.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. The product of this task lives in
  this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry".
  Declined. This task does not retire a module.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the
  D series". Declined. The unfolding pattern used is the live one at
  `src/L/Cardinal.lagda.md:98`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:75`, read: "13.20
  (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a".
  Used: the remaining bill is a truncated ambient injection becoming a
  code. A cardinal inequality does not supply that code.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation
  Lemma and the GCH in L". Declined. This task instantiates a delivered
  consumer. It does not consult condensation.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier:
  fourteen renderings for the owner's ruling". Declined. No glossary
  work.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic
  geology sources and the five questions". Declined. Not geology.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review:
  the 119 pre-protocol entries". Declined. No glossary work.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import `Probe414` or `Probe407`.
- I did not rebuild `sq-data`, `init-at-kappa`, `coded-descent`,
  `code-as-data` or `isPropInjCode`.
- I did not restate the `StageCardinal` induction.
- I did not inhabit `amb-to-coded`. I did not weaken it.
- I did not write `review-of-chain-upper.md`. The verdict is GO.

## WHAT THE NEXT BRIEF NEEDS

The campaign's counting leg is one term, `chain-upper`, conditional on
`amb-to-coded` at `Probe414.agda:134-139`. HALF A remains unpaid
(`agents/tasks/LJ-1-414/lj-1.414-report.md:111-120`). A next brief that
wants the residue discharged must inhabit that type, or change the
target. This assembly does not price that.
