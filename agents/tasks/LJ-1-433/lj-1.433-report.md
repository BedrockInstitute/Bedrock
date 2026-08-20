# LJ-1.433 report: below the ambient least cardinal, Init is FALSE

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-433/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-433/Probe433.agda`, at a
GENERIC ordinal:

    init-fails-below :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → Init x → Empty.⊥

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`Init` at `src/L/Ordinal/SquareLaw.lagda.md:692-698` is four conjuncts:

1. `IsOrd α` (`:693`).
2. `⟨ ω ∈ˢ α ⟩` (`:694`).
3. `((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)` (`:695`). Successor-closure
   of the index.
4. `((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩ → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫) → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)`
   (`:696-698`). No injection of the index into an infinite member's
   square.

This refutation consumes conjunct 3 as a hypothesis: it applies
successor-closure at the membership `⟨ fst κL ∈ˢ x ⟩` to obtain
`⟨ sucV κ ∈ˢ x ⟩`. It refutes conjunct 4: it builds the forbidden
injection of `⟪ x ⟫` into the square of `sucV κ` from the truncated
ambient arrow and `ord-emb`, then conjunct 4 returns `Empty.⊥`.

The statement is not false at the intended generality. `[LJ-1.406]` is
GO on `init-at-kappa` (`agents/tasks/LJ-1-406/lj-1.406-report.md:13-16`)
at the site `fst κL` itself. `[LJ-1.421]` is GO on `kappa-not-fin` and
on the four-projection seal (`agents/tasks/LJ-1-421/lj-1.421-report.md:51-58`,
`Probe421.agda:125-135` and `:164-180`). This task takes those GO
types. It does not inhabit a NO-GO type. It does not copy a type from
`[LJ-1.429]`, `[LJ-1.430]`, `[LJ-1.431]` or `[LJ-1.432]`.

Corrected target: none. Original target stands.

## VERDICT

**GO.** `init-fails-below` typechecks
(`agents/tasks/LJ-1-433/Probe433.agda:146-177`, exit 0, median 2.19 s
on three forced rechecks) and PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-433 --brief agents/tasks/LJ-1-433/LJ-1.433.md`, exit 0,
1.65 s, 0 UNRESOLVED of 1, `probe_red=False`).

`Init x` holds only when `x` is its own ambient least cardinal. This
leaves `descent-data` (`agents/tasks/LJ-1-421/Probe421.agda:111-118`) as
the only remaining producer of `sq` at a non-cardinal.

## 1. What was built

All in `agents/tasks/LJ-1-433/Probe433.agda`, module
`LJ-1-433.Probe433 {ℓ} (lem)`.

- `isL-ord`, sealed (`:53-55`). Same as `[LJ-1.421]`.
- `comp-inj` (`:57-59`) and `ord-emb` (`:63-72`). Rebuilt from
  `src/L/BoundedSubset.lagda.md:1365-1379`. `L.BoundedSubset` is not
  imported.
- The ambient least cardinal, sealed at the call site: `κL`, `κoL`,
  `κ∈sucL`, `κ-injL` (`:79-90`). Same four projections as
  `[LJ-1.421]` (`Probe421.agda:125-135`). This site does not re-measure
  the wall. `κ∈sucL` is sealed and not spent.
- `kappa-not-fin` (`:97-113`), rebuilt at
  `[LJ-1.421]`'s delivered type (`Probe421.agda:164-180`). The
  embedding of `ω` into `x` uses `ord-emb` in place of `mem-incl`.
  The type is the same. The truncated `κ-injL` is spent into
  `Empty.⊥`. Nothing untruncates.
- W3: `omega-in-suc-kappa` (`:121-138`).
- The obligation: `init-fails-below` (`:146-177`).

No module hypothesis. No `amb-to-coded`, no `coded-descent`, no
`IsCardinalL`. Those names occur only in this report.

## 2. W3: `omega-in-suc-kappa`, first

**GO.** The widest unmeasured term was `⟨ ω ∈ˢ sucV κ ⟩`.
`kappa-not-fin` refutes `⟨ κ ∈ˢ ω ⟩`. Trichotomy
(`src/L/Ordinal/Linear.lagda.md:136`) then leaves `⟨ ω ∈ˢ κ ⟩` or
`ω ≡ κ`. Both land in `⟨ ω ∈ˢ sucV κ ⟩`: the first by `∈sucV-inl`
(`src/V/Model.lagda.md:230`), the second by `self∈sucV`
(`src/V/Model.lagda.md:236`) after `subst`. The remaining trichotomy
case is `Empty.rec` of `kappa-not-fin`.

Stated and run alone, with the obligation omitted, before
`init-fails-below` was written. Three forced rechecks, probe interface
deleted, dependencies warm, caliber `-A64m -I0 -M8g`, one Agda
process:

| run | wall s | peak RSS bytes | log |
|---|---|---|---|
| 1 | 1.56 | 402751488 | `runs/w3-1.out` |
| 2 | 1.55 | 402751488 | `runs/w3-2.out` |
| 3 | 1.57 | 402751488 | `runs/w3-3.out` |

Median wall **1.56 s**. Median peak RSS **402751488 bytes**. Exit 0
every time. No heap event.

SEVENTEEN non-blank code lines for `omega-in-suc-kappa` (type plus
body). The estimate for the whole Agda was about 60 code lines, a
comparable of SHAPE with `[LJ-1.421]`'s seal plus `kappa-not-fin`.
Nothing is funded against the estimate.

P-l did not fire as a wall. The W3 type names `sucV` of the sealed
atom `κL`, as the brief wrote it. The elaborator did not unfold
`leastOf`.

## 3. The obligation

`init-fails-below` (`:146-177`) spends `Init x` as follows.

| step | supplier |
|---|---|
| `sucV κ` is an ordinal | `suc-ord` (`src/L/Ordinal.lagda.md:96`) at `κoL` |
| `⟨ sucV κ ∈ˢ x ⟩` | conjunct 3 of `Init x`, applied at `fst κ` and `κ∈x` (`:164`) |
| `⟨ ω ∈ˢ sucV κ ⟩` | `omega-in-suc-kappa` (`:166`) |
| `down : ⟪ x ⟫ ↪ ⟪ κ ⟫` | `PT.rec` on `κ-injL`, goal `Empty.⊥` (`:151`) |
| `e : ⟪ x ⟫ ↪ ⟪ sucV κ ⟫` | `comp-inj down (ord-emb κ (sucV κ) (suc-ord κoL) (self∈sucV κ))` (`:173`) |
| `Empty.⊥` | conjunct 4 of `Init x` at `β := sucV κ`, with `f m = (fst e m , fst e m)` and injectivity from `snd e` and `cong fst` (`:170-177`) |

The arrow stays truncated throughout. `PT.rec` spends `κ-injL` into a
proposition. Nothing untruncates.

**31 non-blank code lines** for `init-fails-below` (type plus body).
Nothing was weakened. Nothing failed to close.

## 4. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `init-fails-below` is generic in `x`. No band, no numeral and
no site is named anywhere in the file except `ω`, which is where
`Init`'s own statement and `kappa-not-fin` put it. There is no fixed
form to report.

W4 does not fire: no module was retired.

## 5. WHAT THIS DOES NOT MEASURE

This refutation measures ONE site: the ambient least cardinal of `x`,
selected by `LeastCardInjL` and sealed as `κL`
(`agents/tasks/LJ-1-433/Probe433.agda:80-81`,
`src/L/Cardinal.lagda.md:122-123`). It says `Init x` is false at that
site whenever `fst κL` is a proper member of `x`. It says nothing
about a coded selection. A different selection would use the coded
predicate `Good` at `src/L/Cardinal.lagda.md:239`:

    Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁

C-42: the next action is not a cure. It is the sweep. This report
does not count other sites.

It also says nothing about `Init` AT the least cardinal. That site is
paid (`agents/tasks/LJ-1-406/Probe406.agda:180-190`).

## 6. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first check, obligation omitted: 1.89 s, exit 0, peak RSS
  402800640 bytes.
- W3, three forced rechecks (probe interface deleted before each run,
  dependencies warm): 1.56 s, 1.55 s, 1.57 s. Median **1.56 s**.
  Median peak RSS **402751488 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/w3-{1,2,3}.out`.
- Full file, first check after the obligation landed: 2.18 s, exit 0,
  peak RSS 649265152 bytes. Printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 2.18 s, 2.19 s, 2.19 s. Median
  **2.19 s**. Median peak RSS **649281536 bytes**. Exit 0 every time.
  Each printed `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.65 s, 0 UNRESOLVED
  of 1, `probe_red=False`.
- No heap event.

The RSS rise from W3 to the full file is the import of
`L.Ordinal.SquareLaw` for `Init`. It is not a wall. The pane caliber
is 8 g.

## 7. What GO earns, and what the next brief needs

A GO is a refutation. `Init x` is false whenever the ambient least
cardinal of `x` is a proper member of `x`. Every route that hoped to
reach `sq x` at a non-cardinal `x` through an ambient initiality is
priced out. The brief names `[LJ-1.432]`'s open case as one such
route. I did not open that task. I did not write a descent. I did not
touch that split.

The remaining producer of `sq` at a non-cardinal is `descent-data`
(`agents/tasks/LJ-1-421/Probe421.agda:111-118`). That term still needs
the untruncated arrow. `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`) produces `sq` from `Init`,
and this measurement removes that producer below `κ`.

What the statement cost: 31 code lines for the obligation, 17 for
W3, the seal and `kappa-not-fin` copied. Median 2.19 s at the wide
caliber. The shape did not resist. Nothing was weakened. Nothing
failed to close.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. The live producer is
  `dev/pod/queue.toml`. This probe does not consult the archived
  dispatch index.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the
  retired route". Declined. This task measures `Init` below the
  ambient least cardinal. It does not consult the retired-route
  journal.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**,". Read to resolve the injected archive
  paths. This task does not retire a module.
- `archive/dev/STATUS-archived.md:1`, read: "# STATUS-archived: the goal
  table of the internalization route". Declined. This task does not
  consult the internalized-route goal table.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used to keep the arrow truncated: a cardinal inequality is a
  truncated injection, and `κ-injL` is spent by `PT.rec` into
  `Empty.⊥`.
- `dev/literature/truncation-and-selection.md:148`, read: "index is a
  proposition. **A data payload does not come out.**". Used to confirm
  that this refutation must not untruncate: the payload stays inside
  `PT.rec`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation
  Lemma and the GCH in L". Declined. Condensation codes a collapse of
  a hull. This task does not ask for a code.
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
- I did not import a probe of `[LJ-1.429]`, `[LJ-1.430]`, `[LJ-1.431]`
  or `[LJ-1.432]`. I did not copy a type out of any of their briefs.
- I did not write a descent. I did not touch `[LJ-1.432]`'s split.
- I did not write `review-of-init-fails-below.md`. The verdict is GO.
- I did not untruncate `κ-injL`.
