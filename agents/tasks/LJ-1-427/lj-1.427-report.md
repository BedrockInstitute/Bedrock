# LJ-1.427 report: run the descent at the INTERNAL least cardinal, not the ambient one

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-427/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-427/Probe427.agda`, at a
GENERIC ordinal:

    descent-from-internal :
        (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

The descent target is the internal least cardinal `δᴸ`, not the ambient
`κL`. The telescope must not hold `kappa-arrow-data`, `amb-to-coded`,
`coded-descent` or `IsCardinalL`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`κL` is an ordinal by construction. It is a member of `sucV (fst α)`,
and `mem-ord` applies (`src/L/Cardinal.lagda.md:125-127`).

`δᴸ` is a member of `Lset β` (`src/L/Cardinal.lagda.md:249-254`).
`InternalLeastCard.Good` (`:239-240`) asks for a truncated coded
injection. It does not ask for `IsOrd`. A member of `Lset α` is
merely a member of `𝒟ₒ (Lset δ)` for some `δ ∈ α`
(`src/L/Constructible.lagda.md:336-337`). That is a definable
subset, not an ordinal.

The induction needs an ordinal at that position twice:

- trichotomy, `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`), used
  at `agents/tasks/LJ-1-421/Probe421.agda:185`
- Init's first conjunct (`src/L/Ordinal/SquareLaw.lagda.md:693`),
  filled by `κoL` at `agents/tasks/LJ-1-406/Probe406.agda:187`

Corrected target: `IsOrd (fst δᴸ)` is not delivered from
`internal-nonempty`. The swap as specified does not go through.
A corrected `Good` that added an ordinality conjunct would select
a different `δ`. That object is not the `δᴸ` this brief named.

`[LJ-1.424]` and `[LJ-1.425]` have not run. This worktree has no
`agents/tasks/LJ-1-424/` report and no `agents/tasks/LJ-1-425/`
report. The sibling worktrees hold only briefs. I took both types
from those briefs, as the brief permits when a task has not run.
Neither report is NO-GO. Neither names its statement FALSE. The
return is provisional on those two types. The W3 kill does not
depend on `coded-to-arrow`.

## VERDICT

**NO-GO.** `descent-from-internal` is not inhabited
(`agents/tasks/LJ-1-427/Probe427.agda:99-103`). The obstruction is
`review-of-descent-from-internal.md`, written for the branch
`no-go-stated`.

W3 `delta-is-ordinal` (`Probe427.agda:74-76`) is the type
`IsOrd (fst δᴸ)` with `internal-nonempty` as a bare module
hypothesis. The type is well-formed. The body is a hole. Agda
reports `UnsolvedInteractionMetas` at `:76` and at the obligation
`:103` (`runs/w3-recheck-2.out:2-6`, exit 42). No other error.

The property the ambient least cardinal carries that the internal
one does not: `IsOrd`, delivered at
`src/L/Cardinal.lagda.md:125-127` by `mem-ord` along membership
in `sucV (fst α)`. The internal selection is a member of
`Lset β` (`:249-254`) under a predicate that does not mention
`IsOrd` (`:239-240`).

This is not a universal negative. I did not prove that `δᴸ` fails
to be an ordinal in every model. I measured that this tree does
not deliver `IsOrd (fst δᴸ)` from `internal-nonempty`.

## 1. What was built

All in `agents/tasks/LJ-1-427/Probe427.agda`, module
`LJ-1-427.Probe427 {ℓ} (lem)`.

- W3, first: module `W3` (`:62-76`) with `κ`, `oκ`, and
  `internal-nonempty` at `[LJ-1.425]`'s brief type. `delta-is-ordinal`
  (`:74-76`) is a hole.
- The obligation `descent-from-internal` (`:99-103`) at the same
  type as `[LJ-1.421]`'s `descent-from-data`. Two module parameters:
  `coded-to-arrow` from `[LJ-1.424]`'s brief (`:87-91`),
  `internal-nonempty` from `[LJ-1.425]`'s brief (`:92-96`). The
  body is a hole. No `kappa-arrow-data`. No `amb-to-coded`. No
  `coded-descent`. No `IsCardinalL`. Those four strings occur only
  in comments (`:22-23`, `:82-83`).

I did not write the 421 induction with `δᴸ` in place of `κL`.
The brief forbids smuggling an ordinality hypothesis to make the
term green.

## 2. W3: `delta-is-ordinal`, first

**The type elaborates. The inhabitant is not delivered.**

`delta-is-ordinal` (`:74-76`) asks for

    IsOrd (fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty))

with `internal-nonempty` as the only extra hypothesis. The
conversion `nonempty = internal-nonempty` (`:70-72`) is
definitional: `⟨ Good δ ⟩` is the inner truncation. Agda accepted
that line. The hole at `:76` is the only remaining goal in `W3`.

Three forced rechecks, probe interface deleted, dependencies warm,
caliber `-A64m -I0 -M8g`, one Agda process:

| run | wall s | peak RSS (bytes) | exit |
|---|---|---|---|
| `runs/w3-recheck-1` | 2.03 | 395788288 | 42 |
| `runs/w3-recheck-2` | 1.66 | 395804672 | 42 |
| `runs/w3-recheck-3` | 1.67 | 395788288 | 42 |

Median wall **1.67 s**. Median peak RSS **395788288** bytes. Error
class `UnsolvedInteractionMetas` every time, at `:76` and `:103`.
No heap event.

The first check after the file landed: 1.60 s, exit 42, same error
(`runs/w3-1.out`, `runs/w3-1.time`).

Nothing was funded against the estimate of about 45 code lines.
The W3 fragment is two inhabited lines plus a hole.

## 3. The two uses that break

| use | what it needs | ambient supplier | internal status |
|---|---|---|---|
| trichotomy split | `IsOrd` on both arguments | `κoL` at `Probe421.agda:189` | not delivered |
| Init, conjunct 1 | `IsOrd α` | `κoL` at `Probe406.agda:187` | not delivered |

`ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`):

    ord-tri : (A : S) → IsOrd A → (B : S) → IsOrd B → Tri A B

`Init` (`src/L/Ordinal/SquareLaw.lagda.md:692-698`):

    Init α = IsOrd α × ⟨ ω ∈ˢ α ⟩ × (successor-closure) × (no-injection)

Both sites take the descent target as an ordinal. `δᴸ` does not
arrive as one.

## 4. Corrected `Good`, and it changes the object

If the descent needs `Good` to carry an ordinality conjunct, a
corrected predicate is:

    Good δ = ( ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁
             × IsOrd (fst (up δ)) )

`[LJ-1.403]` already wrote a stronger correction `Good⁺`
(`agents/tasks/LJ-1-403/Probe403.agda:46-52`): membership in `κ`,
infiniteness, and the code. Membership in an ordinal would give
`IsOrd` by `mem-ord`. That selected object is not the present
`δᴸ`. Adding a conjunct changes which `δ` is least: a non-ordinal
that admits a code and appears earlier in `orderAt` would win
under the present `Good` and lose under either correction.

I did not inhabit that corrected object. I did not write it into
`src/`.

## 5. Does `δ-min` give `κ-min-at`?

No.

`κ-min-at` (`src/L/Cardinal.lagda.md:140-141`):

    κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
             → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥

No member of `κ` by `∈` admits an ambient truncated injection
from `α`. `init-at-kappa` spends this at
`agents/tasks/LJ-1-406/Probe406.agda:116`.

`δ-min` (`src/L/Cardinal.lagda.md:261-263`):

    δ-min : (b : Mem (Lset β)) → ⟨ Good b ⟩
          → (SWO._<∙_ (orderAt β oβ) b δ-card → Empty.⊥)

No member of `Lset β` strictly below `δ-card` in the stage
well-order admits a code.

What is lost:

1. The comparison is `orderAt`, not `∈`.
2. The domain is `Mem (Lset β)`, not the members of the cardinal.
3. The forbidden witness is a code, not an ambient injection.

This is separate from W3. Even a `Good` that delivered `IsOrd`
would still not close Init's fourth conjunct from `δ-min`.

## 6. W2 and DD4

Everything is written once at a generic carrier. The module is
generic in `ℓ`. `W3` is generic in `κ`. `descent-from-internal` is
generic in `x`. No band, no cardinal and no numeral is named
anywhere in the file except `ω`, which the statement's own type
names. There is no fixed form to report.

W4 does not fire: no module was retired.

## 7. C-42

The refutation is at one site: `IsOrd (fst δᴸ)` from
`internal-nonempty`, `Probe427.agda:74-76`.

COUNT of `src/` consumers of `InternalLeastCard.Selected`: **0**.
`grep` over `src/` for `InternalLeastCard` returns one line, the
definition (`src/L/Cardinal.lagda.md:235`).

COUNT of `src/` sites whose `Good` selects a member of `Lset`
without an ordinality conjunct: **1**,
`src/L/Cardinal.lagda.md:239-240`.

COUNT of probes that treat `δᴸ` as an ordinal (trichotomy, Init,
or `IsOrd (fst δᴸ)`): **0** before this task. `[LJ-1.402]` uses
`δᴸ` as an injection target (`Probe402.agda:80`), not as an
ordinal. `[LJ-1.403]` switched to a different predicate `Good⁺`
and did not claim `IsOrd` of the unstrengthened `δᴸ`.

A cure funded against this site is a corrected `Good`, priced
against that one `src/` definition and against zero present
consumers.

## 8. What NO-GO earns for `[LJ-2.5]`

The two-tower candidate has two least-cardinal faces. The ambient
face is a member of `sucV` and inherits ordinality
(`src/L/Cardinal.lagda.md:125-127`). The internal face is a
member of `Lset β` under a coded-injection predicate
(`:239-240`, `:253-254`) and does not inherit ordinality. A
descent that splits on ordinal trichotomy and that runs `Init`
can use the first face as a target. It cannot use the second
face as written.

The later `src/` line a GO would have changed is
`src/L/StageCardinal.lagda.md:564`, `stage-card-upper`, the
counting leg. The consumer spends `sq` once, in the limit step
(`:283`). That line still waits. A `src/` landing of this swap
is not priced, because the swap did not close.

## WHAT LJ-1 STILL OWES

Every hypothesis `descent-from-internal` carries, with `file:line`,
and whether it is delivered.

| hypothesis | type from | delivered? |
|---|---|---|
| `IsOrd x`, `⟨ ω ∈ˢ x ⟩`, the IH | the obligation type itself (`Probe427.agda:99-102`) | the induction package, same as `[LJ-1.421]` |
| `coded-to-arrow` | `[LJ-1.424]` brief, copied at `Probe427.agda:87-91`. This worktree has no `agents/tasks/LJ-1-424/` | not run; not in `src/` |
| `internal-nonempty` | `[LJ-1.425]` brief, copied at `Probe427.agda:92-96`. This worktree has no `agents/tasks/LJ-1-425/` | not run; `InternalLeastCard.Selected` still takes it as a hypothesis (`src/L/Cardinal.lagda.md:243`) |
| `IsOrd (fst δᴸ)` | W3, this task (`Probe427.agda:74-76`) | **not delivered**. Ambient `oκ` is (`src/L/Cardinal.lagda.md:125-127`). |
| trichotomy at the target | `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`) | needs `IsOrd` on the target; not delivered |
| `Init` at the target | `src/L/Ordinal/SquareLaw.lagda.md:692-698` | conjunct 1 needs `IsOrd`; conjunct 2 needs `ω ∈`; conjunct 3 needs successor-closure; conjunct 4 spends `κ-min-at` (`src/L/Cardinal.lagda.md:140`), which `δ-min` (`:261`) does not give |
| `kappa-arrow-data` | `[LJ-1.421]` / `[LJ-1.422]` | **refused** (sibling `LJ-1-422` report, verdict **NO-GO** at `lj-1.422-report.md:15`). This task's point was to make it disappear. It does not disappear, because the internal target cannot stand in. |

What remains before the counting leg could be written into `src/`:

- `src/L/StageCardinal.lagda.md:283` still spends `sq` as a module
  parameter of `LimitStep`.
- `src/L/StageCardinal.lagda.md:564` is still the consumer's output,
  `stage-card-upper`.
- The ambient residue `kappa-arrow-data` is refused. The internal
  swap does not retire it.
- A corrected internal `Good` that carried ordinality would be a
  different object and a different dispatch. It is not this `δᴸ`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. The live producer is
  `dev/pod/queue.toml`. This probe does not consult the archived
  dispatch index.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. The retired-route journal is not this measurement.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived
  in full 2026-08-18". Declined. This task does not change a DD row.
- `archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules".
  Declined. How the loop is operated is not this measurement.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archive
  paths. This task does not retire a module.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Read for D-10 context on the coded witness. This task's kill is
  ordinality of `δᴸ`, not untruncation of the arrow.
- `dev/literature/truncation-and-selection.md:335`, read: "`ω`. **A
  canonical injection needs a well-order on the INJECTIONS, which is".
  Declined for the kill. A well-order on injections is `[LJ-1.422]`'s
  missing device. This task asks whether `δᴸ` is an ordinal.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L".
  Declined. Condensation codes a collapse of a hull. This task asks
  whether the internal least cardinal is an ordinal.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier:
  fourteen renderings for the owner's ruling". Not used. No glossary
  work in this task.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". Not used. This
  probe is the L-tower band step, not the rud-route architecture.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic
  geology sources and the five questions". Not used. Geology is not
  this measurement.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import `Probe421`, `Probe406`, `Probe402` or `Probe403`.
- I did not inhabit `IsOrd (fst δᴸ)`. I did not smuggle it as a
  hypothesis.
- I did not inhabit `descent-from-internal`.
- I did not write a universal negative: I did not say `δᴸ` cannot
  be an ordinal, and I did not say the swap is impossible at a
  corrected `Good`.
