# LJ-1.423 report: the counting leg from ONE arrow, and the campaign's bill

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-423/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did
not set `GHCRTS`. One Agda process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-423/Probe423.agda`, at a
GENERIC band `α₀` with its ordinal certificate as module parameters:

    upper-from-arrow : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
                     → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫

The telescope must not hold `amb-to-coded`, `coded-descent` or
`IsCardinalL`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict. Nothing was written into `src/`.

## VERDICT

**GO, PROVISIONAL.** The obligation typechecks
(`agents/tasks/LJ-1-423/Probe423.agda:129-131`, exit 0, median 1.70 s on
three forced rechecks) and it PASSes the program's witness meter
(`scripts/pod/witness.py --code LJ-1-423 --brief
agents/tasks/LJ-1-423/LJ-1.423.md`, exit 0, 1.68 s, 0 UNRESOLVED of 1,
`probe_red=False`). The swapped pairing fits the consumer's parameter.
The telescope holds `descent-from-data` and `kappa-arrow-data` only. It
does not hold `amb-to-coded`, `coded-descent` or `IsCardinalL` (those
three strings occur only in comments, `Probe423.agda:14` and `:87-88`).

The return is provisional because neither supplier has delivered. I took
both types from their briefs, as the brief permits when a task has not
run. Neither report is NO-GO. Neither names its statement FALSE.

`[LJ-1.420]` has not run in this tree. I did not reuse an instantiation
that does not exist. I wrote the instantiation here.

## D-10: THE TELESCOPE, BEFORE ANY AGDA

`upper-from-arrow` restates the consumer's own delivered statement
(`src/L/StageCardinal.lagda.md:564-565`). Its truth is the consumer's
claim. What I checked is the telescope.

**`[LJ-1.421]` has not run.** This worktree has no
`agents/tasks/LJ-1-421/` directory. The sibling worktree
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-421/agents/tasks/LJ-1-421/`
holds only the brief. There is no `lj-1.421-report.md`. I took the type
from that brief, at the obligation:

    descent-from-data :
        (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

Cite: `.../LJ-1-421/agents/tasks/LJ-1-421/LJ-1.421.md:11-14`. Copied into
`Probe423.agda:92-95`.

**`[LJ-1.422]` has not delivered.** This worktree has no
`agents/tasks/LJ-1-422/` directory. The sibling worktree
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-422/agents/tasks/LJ-1-422/lj-1.422-report.md:5-6`
reads:

    ## VERDICT

    (unfilled)

That is not NO-GO. It does not name the statement FALSE. Status line
`:3` of the same file: "Status: IN PROGRESS. C-22: written early,
filled as answers land." I took the type from its brief:

    kappa-arrow-data :
        (a : S) (oa : IsOrd (fst a))
      → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

Cite: `.../LJ-1-422/agents/tasks/LJ-1-422/LJ-1.422.md:11-13`. Copied into
`Probe423.agda:96-98`.

Owner's ruling 2026-08-20, F1 and F3: I did not copy a supplier's BRIEF
type after that supplier's REPORT had refuted the statement. There is no
such report.

## 1. What was built

All in `agents/tasks/LJ-1-423/Probe423.agda`, module
`LJ-1-423.Probe423 {ℓ} (lem) (α₀) (oα₀)`.

- W3 first: `module Instantiation` (`:56-66`). Pairing is a module
  parameter, not a `postulate`. Instantiates `L.StageCardinal {ℓ} lem α₀
  oα₀ pairing` and reads `Upper.stage-card-upper`. Typechecked ALONE
  before the real pairing was added. `runs/w3-{1,2,3}.out`.
- Plumbing: sealed `κL` (`:73-75`), copied from
  `agents/tasks/LJ-1-413/Probe413.agda:136-137`, so the 422 brief type
  can name it. Not a hypothesis of `upper-from-arrow`.
- `band-ord` (`:79-82`), port of `Probe413.agda:199-202`.
- Two module hypotheses (`:91-98`): `descent-from-data` at 421's brief
  type, `kappa-arrow-data` at 422's brief type. `arrow-residue`
  (`:104`) names the second so the telescope carries the campaign's
  remaining arrow. The pairing body does not spend it:
  `descent-from-data`'s type already internalized it.
- `Goal`, `step`, `pairing` (`:106-125`). Finite case: contradiction.
  `ω` case: `squareω` transported. Infinite case: `descent-from-data`
  on the recursion's own IH. Then `∈-induction`, as
  `Probe413.agda:312` does.
- `module I = Instantiation pairing` (`:127`). `upper-from-arrow`
  (`:129-131`) is `I.stub-upper`.

`[LJ-1.413]`'s `sq-data` (`Probe413.agda:309-312`) and `plugs-in`
(`:326`) remain the shape. This file changes ONE branch of that
induction: the infinite case is `descent-from-data` instead of
`init-at-kappa` plus the coded detour.

## 2. W3: `instantiation-cost`

**GO.** Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda
process. Dependencies warm. The probe interface was deleted before
every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-423/Probe423.agdai`).

Stub instantiation ALONE, three forced rechecks, exit 0 every time,
each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.59 | 407470080 |
| `runs/w3-2.out` / `w3-2.time` | 1.56 | 407486464 |
| `runs/w3-3.out` / `w3-3.time` | 1.56 | 407470080 |

Median wall **1.56 s**. Median peak RSS **407470080 bytes** (388.6 MiB).
No heap event.

**Comparison with `[LJ-1.420]`.** `[LJ-1.420]` has not run. This
worktree has no `agents/tasks/LJ-1-420/` report and no number. I cannot
compare with a number that is not in the tree. The comparable that IS
in the tree is `[LJ-1.337]`'s consumer instantiation:
`agents/tasks/LJ-1-337/lj-1.337-report.md:17` records 1.720 seconds,
exit 0, for `stage-card-from-band` instantiating `L.StageCardinal` and
reading `stage-card-upper`. **The two agree**: 1.56 s here against
1.720 s there, same order, same module, no heap event.

Full file after the real pairing landed: first check 1.70 s, RSS
446709760 (`runs/full-1.out`). Three forced rechecks: 1.71 s, 1.70 s,
1.69 s, RSS 446693376 each (`runs/full-recheck-{1,2,3}.out`). Median
**1.70 s**. Exit 0 every time. No heap event.

`.venv/bin/python` is absent in this worktree. The witness meter ran
under `python3` (3.14.7). I added no dependency.

## 3. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `α₀` and `oα₀` are the consumer's own parameters. `upper-from-arrow`
quantifies over a generic `δ : V ℓ`. The two hypotheses are generic in
their site. No cardinal and no numeral is named except `ω`, which the
consumer's own type names.

The pairing is built once (`pairing`, `:121-125`) and fed to
`L.StageCardinal`. The counting statement is not restated. It is read
out of the consumer (`:131`).

## 4. The line a later task would change, and a `src/` landing

A later task would **not rewrite the body of** `L.StageCardinal`. The
consumer already computes the counting leg. What a landing discharges
is the pairing parameter at `src/L/StageCardinal.lagda.md:17-19`. The
one spend of that parameter is `:283`:

    module B = Bound α oα infα (sq α α∈suc infα)

The output it then exposes is `:564-565`:

    stage-card-upper : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
                     → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫

The live call site that still threads `sq` as a parameter is
`src/L/BoundedSubset.lagda.md:1397` (`module SC = L.StageCardinal {ℓ}
lem α ordα sq`). A `src/` landing would feed that site the pairing this
probe builds, once the two hypotheses are green in the tree.

**Cost of that landing, measured here, not guessed.** Instantiating
`L.StageCardinal` at a stub pairing is 1.56 s median, 388.6 MiB peak
RSS, caliber `-A64m -I0 -M8g`, no heap wall. The full file with the
real pairing is 1.70 s median, 426.0 MiB. The trophy case is
`src/Landmarks.lagda.md:1`. A theorem not wired into it is not landed.
This task wrote nothing into `src/`.

Estimate for the Agda: about 35 code lines, a comparable of SHAPE from
`Probe413.agda:309-312`. Measured, non-blank non-comment lines in
`Probe423.agda` are **76**. Nothing is funded against the estimate.

## WHAT LJ-1 STILL OWES

Every hypothesis `upper-from-arrow` carries, and what remains before
the counting leg could be written into `src/`.

| hypothesis | in this telescope | delivered green in `agents/tasks/`? | cite |
|---|---|---|---|
| `descent-from-data` | yes, `Probe423.agda:92-95` | **no**. `[LJ-1.421]` has not run. Type taken from its brief. Provisional. | sibling `LJ-1.421.md:11-14` |
| `kappa-arrow-data` | yes, `Probe423.agda:96-98` | **no**. `[LJ-1.422]` has no delivered verdict. Sibling report VERDICT unfilled (`lj-1.422-report.md:5-6`). Type taken from its brief. Provisional. | sibling `LJ-1.422.md:11-13` |
| `amb-to-coded` | **no** | hole, not refuted. `[LJ-1.414]` NO-GO on this name, GO on HALF B. `Probe414.agda:139` is `{!!}`. Report: "the statement is not proved and not refuted" (`lj-1.414-report.md:39`). Not in this telescope. | `Probe414.agda:134-139` |
| `coded-descent` | **no** | not in this telescope. 421's type is the question whether it is needed. | `Probe413.agda:226-231` (413's hypothesis, not 423's) |
| `IsCardinalL` | **no** | not in this telescope. | |
| `init-at-kappa` | **no** | **yes**, `[LJ-1.406]` GO (`lj-1.406-report.md:13-15`, `Probe406.agda:180-190`). 421's type internalizes the infinite case, including this, if 421 returns GO. | `Probe406.agda:180` |
| `sq-data` / consumer fit | rebuilt here as `pairing` | **yes** at `[LJ-1.413]`, GO (`lj-1.413-report.md:16-21`, `Probe413.agda:309-312` and `:326`). This task swapped one branch. | `Probe413.agda:326` |
| `κL` plumbing | defined here, not a hypothesis | sealed locally (`Probe423.agda:73-75`), same seal as 413. F10: three probes each sealed their own `κL`; joining seals is `[LJ-1.420]`'s measurement, and 420 has not run. | `Probe413.agda:136-137` |

**What remains before a `src/` landing.**

1. `[LJ-1.421]` must deliver `descent-from-data` green at the type copied
   here, or refuse it. Until then this GO is provisional.
2. `[LJ-1.422]` must deliver `kappa-arrow-data` green at the type copied
   here, or refuse it. Until then the "one named arrow" is a named
   hypothesis, not a term.
3. If both GO, the counting leg at every band ordinal reduces to that
   one arrow. A later task feeds `pairing` to
   `src/L/BoundedSubset.lagda.md:1397` and reads
   `src/L/StageCardinal.lagda.md:564`. It wires nothing until
   `src/Landmarks.lagda.md:1` names it.
4. If either is NO-GO, this route is closed and `[LJ-1.414]`'s bill
   stands: `amb-to-coded` at `Probe414.agda:134-139`, not proved and
   not refuted (`lj-1.414-report.md:39`).
5. Architecture remains a CANDIDATE (`dev/pod/screen.toml:10`). This
   measurement does not settle `[LJ-2.5]`.

The architecture is a CANDIDATE. Only a measurement at `[LJ-2.5]`
settles it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Also `:4`, read: "the task producer now, and the program-written transition log at". Declined for the assembly: the live producer is `dev/pod/queue.toml`. This probe does not consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:3`, read: "**Archived 2026-08-09**, when the owner ruled the two-tower bridge route and". Declined for the assembly: the pairing and the consumer live in the live tree.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined: not used. The live record of this task is this file.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined: W2 is carried by the slot file, not by this archive.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined: not used. D-10 is in `dev/LESSONS.md`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:134`, read: "### 1.4 5.4: the counting". Also `:137`, read: "> smallest M ≺ L_α such that X ⊆ M. For this M, |M| = max(|X|, ω).". The consumer's `stage-card-upper` is the counting leg this corollary spends. This task instantiates that consumer. It does not prove 5.4.
- `dev/literature/truncation-and-selection.md:75`, read: "13.20 (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a". Also `:76`, read: "truncated existence of an injection.** That is the HoTT Book's own definition,". That is why `κ-inj` is truncated at `src/L/Cardinal.lagda.md:133` and why `kappa-arrow-data` is DATA. This task takes the data form as a hypothesis. It does not untruncate.
- `dev/literature/digest.md:514`, read: section II.5 "The Condensation Lemma. The GCH in L" is in hand. Named so the trophy this counting leg serves is sourced. Declined for the assembly: the probe does not consult the digest's chain.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined: not used. Geology is not this counting leg.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined: not used. No glossary entry was added.
