# LJ-1.436 report: stage-cardinal induction at a truncated conclusion

slot: `coder`. Written early as a skeleton and filled as answers landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-436/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-436/Probe436.agda`:

    step-trunc : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ) → P! α

ONE module hypothesis, the truncated square law at the type `[LJ-1.407]`
delivered (`agents/tasks/LJ-1-407/Probe407.agda:262-265`). Predecessor
report: **GO**, no residue (`agents/tasks/LJ-1-407/lj-1.407-report.md:18`).
I did not import that probe. I took the type from the probe that
typechecked, and the verdict from the report.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. Nothing was written into `src/`.

## VERDICT

**NO-GO.** The obstruction is `review-of-step-trunc.md`, written for
the branch `no-go-stated`. The truncation cannot pass through the Pi
that `limit-step` demands as data. W3 `branch-trunc` is stated and
run. Its finite case closed. Its first induction-hypothesis case
stops at `open-ih` (`Probe436.agda:202`), where `PT.rec` asks for
`isProp (⟪ Lset δ ⟫ ↪ ⟪ δ ⟫)`. The elaborator reports
`[UnsolvedInteractionMetas]` at `Probe436.agda:202.10-14`, exit 42.
`step-trunc` is left as a hole (`Probe436.agda:250`). I did not try
to inhabit it. The brief orders that only if W3 closes.

A GO would have ended the untruncation campaign. This is not a GO. I
do not claim the trophy. The trophy needs the consumer of the bound,
which `[LJ-1.434]` measures separately.

## D-10. THE TYPES, BEFORE ANY AGDA

**Type of `branch`**, `src/L/StageCardinal.lagda.md:534-536`:

    branch : (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
             (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P δ)
           → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫

**Type `limit-step` demands of its last argument**,
`src/L/StageCardinal.lagda.md:396-398`:

    ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)

The two types meet: `branch` returns exactly the family `limit-step`
takes. That family is a Pi of injections. An injection is a Sigma of a
function and an injectivity proof (`src/L/StageCardinal.lagda.md:221-222`
and `src/L/Cardinal.lagda.md:47-48`). It is not an hProp. The chapter's
own comment at `src/L/Cardinal.lagda.md:132` says the witness is still
not an hProp.

`P! δ`, after the three ordinal hypotheses, is

    ∥ Σ[ f ∈ (⟪ Lset δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ Lset δ ⟫) → f u ≡ f v → u ≡ v) ∥₁

That is a truncated injection. `PT.rec` may open it only if the goal is
an hProp.

**The truncation cannot pass through that Pi.** The Pi's codomain is
not an hProp, and `limit-step` demands the untruncated family as data.
A family of truncated values is not a truncated family. HoTT Book
3.8.1 has a truncated conclusion
(`dev/literature/truncation-and-selection.md:226`). If the goal that
consumes the selection is not a proposition, that axiom does not help
(`dev/literature/truncation-and-selection.md:229`).

## W2 (DD4)

Generic in `α`. The module takes `α₀` and `oα₀` as the chapter does
(`src/L/StageCardinal.lagda.md:15-16`). No band ordinal is named. No
extra infiniteness hypothesis is added. The infiniteness argument of
`branch-trunc` is the chapter's own `(⟨ α ∈ˢ ω ⟩ → Empty.⊥)`.

I did not instantiate `L.StageCardinal`. Opening that module demands
the untruncated pairing as a module parameter
(`src/L/StageCardinal.lagda.md:17-19`). The brief forbids pairing as
data. The plumbing that `branch` uses does not mention the motive, so
the probe copies `comp-inj`, `Emb`, `WOEmb` and `fin-inj` from the
chapter and does not take that parameter.

## WHO OWES WHAT

`[LJ-1.435]` owes a limit step that consumes a POINTWISE truncated
branch family. This worktree has no directory `agents/tasks/LJ-1-435/`.
There is no report to open, so there is no report to cite. The W3 term
failed. The repair is owed there.

## THE FIRST TERM THAT NEEDS DATA

`src/L/StageCardinal.lagda.md:550`, the first argument of `comp-inj`
in the ω-case of `branch.go`:

    (comp-inj (IH ω (subst (λ w → ⟨ w ∈ˢ α ⟩) e δ∈α) ω-ord ω∈suc (∈-irrefl ω))
              (WOEmb.ω-inj α oα infα))

The type it needs:

    ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫

which is `P ω` after the three ordinal hypotheses, not `P! ω`. The
finite case at `src/L/StageCardinal.lagda.md:548` does not read the
motive. It closed in the probe (`Probe436.agda:220`).

This named type is the deliverable to `[LJ-2.5]`, together with the
swap stated as `PiTruncSwap` (`Probe436.agda:239-243`):

    (α : S) (Y : ⟪ α ⟫ → Type ℓ)
    → ((m : ⟪ α ⟫) → ∥ Y m ∥₁)
    → ∥ ((m : ⟪ α ⟫) → Y m) ∥₁

`PiTruncSwap` is named, not postulated, and not inhabited. It does not
inhabit `branch-trunc`, because `branch-trunc` wants the untruncated
Pi. It would serve `step-trunc` if `limit-step` ran under `PT.rec`,
because `P! α` is an hProp.

## W3: `branch-trunc`

**NO-GO.** The brief named `branch-trunc` as the widest unmeasured
term. It is the chapter's `branch` (`src/L/StageCardinal.lagda.md:534-536`)
with the motive truncated and nothing else changed. Type:

    branch-trunc :
        (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
        (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ)
      → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫

Exact type used: `Probe436.agda:204-208`. The body follows the
chapter's `go` (`Probe436.agda:209-231`).

The finite case spends `fin-inj` and `WOEmb.ω-inj`. It does not read
`IH`. It closed.

The ω-case and the infinite case read `IH`. With `P!` that reading is
a truncation. `open-ih` (`Probe436.agda:194-202`) is the untruncation
those two cases spend. Its body is `PT.rec` into
`⟪ Lset δ ⟫ ↪ ⟪ δ ⟫`. The hole is

    goal : isProp (⟪ Lset δ ⟫ ↪ ⟪ δ ⟫)
    goal = {!!}

at `Probe436.agda:201-202`. The elaborator, W3-alone, three forced
rechecks, every time:

    [UnsolvedInteractionMetas]
    Probe436.agda:202.10-14

That is the only error of the W3-alone file. The Pi is in the way:
even one member that is not finite requires an untruncated injection,
and the target of `PT.rec` is not an hProp.

W3-alone, three forced rechecks, probe interface deleted before each
run (`_build/2.8.0/agda/agents/tasks/LJ-1-436/Probe436.agdai`),
caliber `-A64m -I0 -M8g`, one Agda process, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.10 | 307953664 |
| `runs/w3-2.out` / `w3-2.time` | 1.07 | 307953664 |
| `runs/w3-3.out` / `w3-3.time` | 1.10 | 307937280 |

Median wall **1.10 s**. Median peak RSS **307953664 bytes**. Exit 42
every time. No heap event.

## 1. What was built

All in `agents/tasks/LJ-1-436/Probe436.agda`, module
`LJ-1-436.Probe436 {ℓ} (lem) (α₀) (oα₀)`. No pairing as data. No
injection as data. No choice principle. No postulate.

- `P!` (`:64-67`), the chapter's motive with one truncation around
  its Sigma.
- `comp-inj` (`:80-82`), `Emb` (`:84-96`), `WOEmb` (`:98-109`),
  `fin-inj` (`:180-182`), copied from the chapter because opening
  `L.StageCardinal` would add the untruncated pairing.
- `open-ih` (`:194-202`), the untruncation the IH cases spend. Hole
  at `:202`.
- `branch-trunc` (`:204-231`), W3.
- `PiTruncSwap` (`:239-243`), named type, not inhabited.
- `step-trunc` (`:248-250`), the obligation as a hole.

## 3. Runs, caliber, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.
Dependencies warm. The probe interface was deleted before every kept
run.

Full file (W3 plus the named swap and the obligation hole), three
forced rechecks, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.10 | 307953664 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.09 | 307986432 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.09 | 307953664 |

Median wall **1.09 s**. Median peak RSS **307953664 bytes**. Exit 42
every time. The only errors are the two holes: `open-ih` at
`Probe436.agda:202.10-14` and `step-trunc` at
`Probe436.agda:250.14-18`. No heap event.

The brief's estimate for the Agda was about 70 code lines, a
comparable of SHAPE from `src/L/StageCardinal.lagda.md:530-566`.
Nothing is funded against that estimate. The W3 term plus `P!` plus
`open-ih` is the chapter's 37-line spine with a truncation. The
plumbing copy is what forbids opening `L.StageCardinal` without
pairing as data.

## WHAT NO-GO EARNS

This is the measurement `[LJ-2.5]` asks for. The one principle the
architecture needs, as a type, is `PiTruncSwap` (`Probe436.agda:239-243`):
a swap of a Pi and a truncation over the members of an ordinal.
Clause W1 says only a measurement changes the architecture. This is
that measurement.

The swap is not enough for `branch-trunc` as stated. `branch-trunc`
wants the family as data. The swap delivers a truncated family. The
repair that keeps the family truncated POINTWISE is owed at
`[LJ-1.435]`.

I did not weaken `P!`. I did not edit `src/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read, not used. Line 3:
  `**Status: ARCHIVED RECORD. It is never rewritten.**` The index is
  the retired PLAN section 11. This task is a live LJ-1 measurement.
- `archive/dev/JOURNAL-archived.md`: read, not used. Line 1:
  `# Archived journal: the retired route`. The retired-route journal
  does not record the truncated-motive induction.
- `archive/dev/JOURNAL.md`: read, not used. Line 1:
  `# ARCHIVED 2026-08-20`. It is a retired per-episode journal.
- `dev/ARCHIVE.md`: read, not used. Line 1:
  `# ARCHIVE.md: the archive registry`. No StageCardinal module is
  retired. This task writes no archival row.
- `archive/dev/DD-archived.md`: read, not used. Line 3:
  `**Status: ARCHIVED RECORD. Never rewritten, never deleted.**` W2 and
  W4 already bind from the slot file. The archived DD rows add no type.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: used. Line 223:
  `### 2.7 The axiom of choice does NOT give an untruncated selection`.
  Line 226: `(∏x ∥Y x∥) → ∥∏x Y x∥`. That is HoTT Book 3.8.1, the swap
  of a Pi and a truncation. The goal of `branch-trunc` is not a
  proposition, so that axiom does not inhabit it.
- `dev/literature/terms-2026-08.md`: read, not used. Line 1:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  No glossary entry is added.
- `dev/literature/devlin-II5.md`: read, not used. Line 1:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. The
  orthodox size proof is not the question. The question is whether a
  truncation passes through the chapter's Pi.
- `dev/literature/digest.md`: read, not used. Line 1:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  The rud route is not this measurement.
- `dev/literature/glossary-review-2026-08.md`: read, not used. Line 1:
  `# Glossary review: the 119 pre-protocol entries`. No glossary work.
