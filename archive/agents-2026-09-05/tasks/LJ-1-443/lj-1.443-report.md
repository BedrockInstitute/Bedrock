# LJ-1.443 report: state the campaign's one open statement ONCE, in the tree

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-443/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term `bounded-modulo-collect` in
`src/L/StageBound.lagda.md`, with `SqCollect` stated in that same
chapter.

## D-10, BEFORE ANY AGDA

The brief's first order is to open two reports
(`agents/tasks/LJ-1-443/LJ-1.443.md:27-34`).

Commands in this worktree:

    test -f agents/tasks/LJ-1-442/lj-1.442-report.md
    test -f agents/tasks/LJ-1-440/lj-1.440-report.md
    test -f src/L/StageBound.lagda.md
    test -f src/L/SquareLawClosed.lagda.md

Each path is absent. `git ls-files` of those four paths is empty at
this HEAD (`d81bfee9e9b726d04fd096242752a551964b52c2`,
`pod: admit LJ-1.443`). I cannot quote a VERDICT line from either
named report. I cannot quote a type either predecessor inhabited in
`src/`.

The brief says: if either file does not exist, or its verdict is not
`GO`, or the named master is not in the tree, write nothing and stop
(`LJ-1.443.md:29-34`). **All four of those happened for the
obligation.** The verdict test was not reached, because the files are
not here.

A predecessor taken as a hypothesis is the REPORT and never the brief
(`dev/pod/audit-2026-08-20.md:34`, quote: `F1 / F2. LJ-1.398 GO is hollow`;
`:41-42`, quote: `the brief, not the result`). I did not take the 443
brief's type as a delivered type. I did not inhabit it in `src/`.

The two sides the brief names as probes ARE in this tree. I quote them
here as types in probes, not as landed masters.

**Supply, as `[LJ-1.437]` delivered it.** VERDICT **GO** at
`agents/tasks/LJ-1-437/lj-1.437-report.md:16`. Type at
`agents/tasks/LJ-1-437/Probe437.agda:345-348`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

**Consumer, as `[LJ-1.434]` delivered it.** VERDICT **GO** at
`agents/tasks/LJ-1-434/lj-1.434-report.md:52`. Type at
`agents/tasks/LJ-1-434/Probe434.agda:127-128`:

    bounded-from-trunc : ∥ SqFam α ∥₁ → ⟨ x ∈ˢ Lset κ ⟩

with `SqFam` at `Probe434.agda:44-48`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

Neither probe is a master under `src/`. `src/Everything.lagda.md:375`
imports `L.Cardinal`. `src/Everything.lagda.md:393` imports
`L.BoundedSubset`. It does not import `L.StageBound` or
`L.SquareLawClosed`. The brief's claimed catalog seats at `:376` and
`:394` (`LJ-1.443.md:113-114`) are not those modules in this tree.

## VERDICT

**NO-GO** on `src/L/StageBound.lagda.md::bounded-modulo-collect`.
The premises named at `LJ-1.443.md:29-34` are not in this tree.
The obstruction is
`agents/tasks/LJ-1-443/review-of-bounded-modulo-collect.md`.
Agda over the named home is `agents/tasks/LJ-1-443/Probe443NoGo.agda:16`,
exit 42, class `[FileNotFound]` (`runs/nogo-1.out:5`).

**GO** on W3 `domains-meet`. The identity typechecks
(`agents/tasks/LJ-1-443/Probe443.agda:37-40`, exit 0, median 1.29 s
on three forced rechecks). The two spellings meet with no
repackaging.

This is not a refutation of `SqCollect`. The type was not inhabited
in `src/` and was not refuted. No postulate was added. No hole was
left in a live term. The NO-GO probe is one import of a module that
is not here.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`, quote: `One SRC collection after LJ-1, not after`).
This task is still LJ-1 work. It does not start that collection. It
does not start phase 3. No Boundary clause is in conflict with the
stop. `AGENTS.md:43` (quote: `A stop is a deliverable.`) is the rule
this return obeys. `AGENTS.md:69` (quote: `Write no mathematical prose until both trophies are proved in the tree.`)
is why the chapter was not invented.

## 1. What was written

- `agents/tasks/LJ-1-443/lj-1.443-report.md` (this file)
- `agents/tasks/LJ-1-443/review-of-bounded-modulo-collect.md`
- `agents/tasks/LJ-1-443/Probe443.agda` (W3 only)
- `agents/tasks/LJ-1-443/Probe443NoGo.agda` (the named home, absent)
- `agents/tasks/LJ-1-443/runs/w3-1.out` and `runs/w3-recheck-{1,2,3}.out`
- `agents/tasks/LJ-1-443/runs/nogo-1.out`

Not written:

- `src/L/StageBound.lagda.md`
- any edit of `src/Everything.lagda.md`
- any edit of `dev/ledger.toml`

## W2 (DD4)

The brief states W2 at `LJ-1.443.md:151`: `SqCollect` is written once,
generic in `α`. No term landed in `src/`. There is no fixed form to
report as a conflict.

The W3 term `domains-meet` is written once, generic in the module
parameter `α : V ℓ` (`Probe443.agda:28-29`). It names no band, no
numeral and no site. W2 holds on the probe.

W4 does not fire: no module was retired.

## W3, THE WIDEST UNMEASURED TERM

The brief named `domains-meet` as the identity between

    (δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁

and

    (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁

and ordered it typechecked ALONE with the obligation omitted from the
chapter.

The chapter `src/L/StageBound.lagda.md` is absent, so the identity
cannot be checked against that chapter. I wrote the identity as a
miniature against `V.Hierarchy` and `L.Ordinal.SquareLaw`, which are
in this tree. The obligation is omitted. The term is the identity
function (`Probe443.agda:40`).

**GO.** `agda --safe` exits 0. The first check printed `Checking`
(`runs/w3-1.out`: 1.49 s real, 348241920 bytes maximum RSS). Three
forced rechecks, probe interface removed before each run,
dependencies warm:

| run | wall s | maximum RSS bytes | exit |
|---|---|---|---|
| `runs/w3-recheck-1.out` | 1.29 | 348258304 | 0 |
| `runs/w3-recheck-2.out` | 1.28 | 348274688 | 0 |
| `runs/w3-recheck-3.out` | 1.30 | 348291072 | 0 |

Median wall **1.29 s**. Median peak RSS **348274688** bytes. Each
run printed `Checking`. Caliber `-A64m -I0 -M8g`, set on the pane,
untouched. One Agda process at a time. No heap event.

The brief estimated three lines and under one second on top of the
chapter's own cost. Measured 1.29 s for the miniature, with no
chapter present. I report the measured number, not the guess.

## THE NAMED HOME, IN AGDA

A W3-only return typechecks, so conjunct 1 holds and the runner's
`exit_code` is 0 (`scripts/pod/accept.py:462-463`). The GO branch
needs `obligations_delta_max = -1` (`LJ-1.443.md:205-207`). The
stated-NO-GO branch needs `exit_code = 42` (`LJ-1.443.md:227-229`).
Neither matches a green probe and an open obligation.

The brief's stop is a missing premise, not a conversion failure. I
wrote one import of the named home and ran it once, after W3, still
under the pane caliber, still one Agda process:

    open import L.StageBound

at `Probe443NoGo.agda:16`.

**NO-GO, measured.** `agda --safe` exits 42. The elaborator prints
`error: [FileNotFound]` at `Probe443NoGo.agda:16.1-25`
(`runs/nogo-1.out:5`). Quote of `:6-7`:

    Failed to find source of module L.StageBound in any of the
    following locations:

Quote of `:10-11`, the two seats under `src/` that were searched:

    /Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-443/src/L/StageBound.agda
    /Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-443/src/L/StageBound.lagda

Wall **0.22 s**. Peak RSS **116883456** bytes. Caliber
`-A64m -I0 -M8g`. No heap event. I did not rerun: a missing file is
not a conversion cost, and a second run would not be a recheck of a
green term.

`src/L/SquareLawClosed.lagda.md` is also absent. I did not start a
second Agda process to import it. The first failed test at
`LJ-1.443.md:29-31` is already enough to stop.

## WHAT THE JOIN COST

The join is the identity. I did not hide a conversion inside a
`subst`. The body is `domains-meet f = f` (`Probe443.agda:40`).

The two spellings that were joined:

| side | binder | membership | site |
|---|---|---|---|
| supply | `δ : V ℓ` | `⟨ δ ∈ sucV α₀ ⟩`, `⟨ δ ∈ ω ⟩` | `Probe437.agda:345-348` |
| consumer | `δ : S` | `⟨ δ ∈ˢ sucV α ⟩`, `⟨ δ ∈ˢ ω ⟩` | `Probe434.agda:44-48` |

At `src/V/Hierarchy.lagda.md:80-83`, the structure `𝒮ᵥ` sets
`S = V ℓ` and `_∈ˢ_ = _∈_`. Quote of `:80-83`:

    S      = V ℓ
    isSetS = setIsSet
    _≈ˢ_   = λ x y → (x ≡ y) , setIsSet x y
    _∈ˢ_   = _∈_

`L.Ordinal.SquareLaw` opens that same structure
(`src/L/Ordinal/SquareLaw.lagda.md:64`) and states `sq : S → Type ℓ`
(`src/L/Ordinal/SquareLaw.lagda.md:685`). The identity is therefore
the expected conversion, and Agda accepts it.

The two halves MEET. They do not sit in `src/` together. That is the
defect this task measured, and it is not a spelling defect.

## WHAT IS LEFT

As types, and only as types:

**`SqCollect`**, the statement the brief named and this task did not
land (`LJ-1.443.md:16-19`):

    SqCollect : S → Type (ℓ-suc ℓ)
    SqCollect α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ∥ SqFam α ∥₁

**The supply half, proved in a probe, not in `src/`:**
`sq-trunc-closed` at `agents/tasks/LJ-1-437/Probe437.agda:345-348`,
VERDICT GO at `agents/tasks/LJ-1-437/lj-1.437-report.md:16`.

**The consumer half, proved in a probe, not in `src/`:**
`bounded-from-trunc` at `agents/tasks/LJ-1-434/Probe434.agda:127-128`,
VERDICT GO at `agents/tasks/LJ-1-434/lj-1.434-report.md:52`.
`Distance` at `Probe434.agda:54-59` is the same shape as `SqCollect`
and is not inhabited there.

I do not claim the trophy. `src/Landmarks.lagda.md` was not touched.
I do not claim that `SqCollect` is false. Nothing in this tree refutes
it. What is missing is the two named reports and the two named masters.

The one site in `src/` that still demands the injection family as DATA
is `limit-step`'s last argument at `src/L/StageCardinal.lagda.md:397`.
The green refutation `pair-cross-refuted` is at
`agents/tasks/LJ-1-408/Probe408.agda:95-104`. I cite those two sites
because they are in this tree. I do not cite `[LJ-1.435]` or
`[LJ-1.436]` as a result: the brief forbids a report that this tree
cannot open (`LJ-1.443.md:126-129`).

## THE RATIO

Measured seconds for the W3 probe: median 1.29 s on three forced
rechecks (`runs/w3-recheck-{1,2,3}.out`).

Measured seconds for the NO-GO import: 0.22 s (`runs/nogo-1.out:18`).

In-fence line count of this task's write scope: 0. No `.lagda.md`
master was written. A raw `.agda` probe carries no fence. The ledger
does not count `src/Everything.lagda.md` here, and that file was not
edited.

The ratio bar is 0.0123 seconds per in-fence line. With divisor 0 the
bar has no rate to fire.

The brief's estimate of about 25 in-fence lines was not spent in
`src/`.

## SEQUENCING, FOR THE NEXT BRIEF

This worktree's HEAD is `d81bfee`
(`d81bfee9e9b726d04fd096242752a551964b52c2`, `pod: admit LJ-1.443`).

`git merge-base --is-ancestor a983bb7 HEAD` exits 1, so `a983bb7`
(`pod: LJ-1.442 done, row task-lj-1-442-go`) is not an ancestor of this
HEAD. Those paths are not in this worktree. I did not open that later
commit's report as the 442 premise. The brief named a path in the tree
I was given, and that path is absent.

`git ls-tree -r --name-only HEAD` returns no
`src/L/SquareLawClosed.lagda.md` and no
`agents/tasks/LJ-1-440/lj-1.440-report.md`. The 440 report and the
supply master are not on this HEAD.

Sibling worktrees exist on this machine. I did not open their files
as the 440 or 442 premise.

The next join brief can fire after a tree that contains all four named
paths at `LJ-1.443.md:29-34` is the tree the coder is given. Then D-10
can quote two VERDICT lines. Then the composition can be written in
the chapter. W3 says the two spellings already meet as the identity,
so the composition does not need a `subst` for the family telescope.

`.venv/bin/python` is absent in this worktree. I did not run
`scripts/pod/witness.py`. I did not run `make check`: the chapter did
not change. `AGENTS.md:75` (quote: `` `make check` is the gate before any commit. ``)
still binds the program, not a no-edit stop.

## WHAT GO WOULD HAVE EARNED, AND WHAT THIS NO-GO EARNS

A GO on the obligation would have put `SqCollect` in `src/` as one
type, with `bounded-modulo-collect` feeding the landed supply into it
and handing the result to the landed consumer, and a green
`make check` before and after. That did not happen. `[LJ-2.5]` still
has no typechecked term in this tree to rule on.

This NO-GO says the premises are not in the tree this task was given
(`LJ-1.443.md:27-34`). W3 says the join of the two spellings is free.
That is a fact the campaign needs before it joins anything.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `archive/dev/JOURNAL.md:1`. Quote:
  `# ARCHIVED 2026-08-20`. Declined, not used. The per-episode journal
  is retired. The history of this task is this directory.
- `archive/dev/LJ-dispatch-index.md`: read at
  `archive/dev/LJ-dispatch-index.md:1`. Quote:
  `DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This stop is a missing live report.
- `archive/dev/JOURNAL-archived.md`: read at
  `archive/dev/JOURNAL-archived.md:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The missing files are live task paths.
- `archive/dev/DD-archived.md`: read at `archive/dev/DD-archived.md:1`.
  Quote: `RULING SERIES, archived in full 2026-08-18`.
  Declined, not used. The stop rule is in the brief and in `AGENTS.md`.
- `archive/dev/DECISIONS-archived.md`: read at
  `archive/dev/DECISIONS-archived.md:1`. Quote:
  `# Archived decisions: the D series`. Declined, not used. No D-series
  row is the obstruction.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at
  `dev/literature/truncation-and-selection.md:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Also read at `:158`. Quote:
  `Theorem 16: "A type X has a constant endomap if and only if it has split`.
  Declined, not used. No truncation term was inhabited. Kraus Theorem 16
  is not reached.
- `dev/literature/devlin-II5.md`: read at
  `dev/literature/devlin-II5.md:1`. Quote:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. Declined,
  not used. This return does not consult II.5.
- `dev/literature/digest.md`: read at `dev/literature/digest.md:1`.
  Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/geology.md`: read at `dev/literature/geology.md:1`.
  Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not this obligation.
- `dev/literature/terms-2026-08.md`: read at
  `dev/literature/terms-2026-08.md:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not write in `src/`.
- I did not edit `dev/ledger.toml`.
- I did not run `make check`.
- I did not open `a983bb7`'s report as a substitute for
  `agents/tasks/LJ-1-442/lj-1.442-report.md`.
- I did not inhabit `SqCollect`.
- I did not inhabit `bounded-modulo-collect`.
- I did not postulate `SqCollect`.
- I did not leave a hole in a live term.
