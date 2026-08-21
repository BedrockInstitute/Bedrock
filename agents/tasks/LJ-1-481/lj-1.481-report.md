# LJ-1.481 report: HullClosedLset, uniqueness of the witness first

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-481/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-481/Probe481.agda`:

    HullClosedLset : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

where `M` is the definable hull, exactly as `src/L/BoundedSubset.lagda.md:903-914`
builds it. Land nothing in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## PREDECESSOR, READ FIRST

`[LJ-1.474]` is GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-474/lj-1.474-report.md:70`. Quote at `:72-75`:

> **GO.** `zero-code` typechecks. `lset-codes` typechecks. The witness
> meter reads `0 UNRESOLVED of 1`, `probe_red=False`
> (`runs/witness.out:1-2`). I did not add a hypothesis on `X`. I did not
> postulate. I did not inhabit `levelIn` or `lset-code`.

The delivered term is at `agents/tasks/LJ-1-474/Probe474.agda:124-125`.
I did not stop.

`[LJ-1.462]` states step 2 as a type and leaves it unbuilt
(`agents/tasks/LJ-1-462/Probe462.agda:136-138`). Its verdict is NO-GO at
D-10 step 3 (`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). That NO-GO
is not this task's type. I did not inhabit `levelIn`.

I did not read `[LJ-1.479]`. The brief forbids it.

## D-10, BEFORE ANY AGDA

`wit k ψ vs` is the witness of a satisfiable formula
(`src/L/Hull.lagda.md:73-74`). `search` is at `:79-81`. `val` at a
`wit` is that search, or junk (`:88-91`). A witness satisfies ψ. It is
`Lset y` only if ψ pins that set uniquely.

`Lset-only` at `src/L/Hierarchy.lagda.md:334-335`:

    Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
              → fst (lookup w γ) ≡ Lset (fst (lookup b γ))

It does give uniqueness. The unique value is `Lset` of the argument.
It spends `IsOrd` on the argument slot.

`Lset-defines` at `src/L/Hierarchy.lagda.md:646-648` spends `IsOrd` too.
Without `IsOrd`, the graph need not hold of `Lset y`, and `Sat` of
`wit` may fail. Then `val` is junk (`src/L/Hull.lagda.md:90-91`).

Where does `IsOrd` come from at a hull member `y`? It has no source.

- `⟨ y ∈ˢ M ⟩` reads back as a code (`src/L/Hull.lagda.md:337-339`):
  `hull-member` returns `∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁`.
- `Code` has constructors `base` and `wit` only (`:72-74`).
- `Hull⊆L` (`:330-334`) places a hull member in `Lset α`. It does not
  place it among the ordinals.
- The obligation type at `agents/tasks/LJ-1-462/Probe462.agda:136-138`
  carries no `IsOrd`.

The brief forbids an ordinality hypothesis on `y`. Adding one changes
the statement `levelIn` needs.

Corrected target beside the original: uniqueness of the packaged
graph's witness as `Lset y` holds at an ordinal and does not hold at a
hull member. The `feed` then `inHull` join does not inhabit
`HullClosedLset` as stated.

## VERDICT

**NO-GO at uniqueness of the witness.** `pins` typechecks from
`Lset-only`. `IsOrd` has no source at a hull member. The obligation
term `HullClosedLset` is not written. Witness meter: 1 UNRESOLVED of 1,
`probe_red=False` (`runs/witness.out:1-2`).

This is an obstruction of the `feed` then `inHull` route. It is not a
refutation of `HullClosedLset`. I did not build a term of the
negation.

The NO-GO is stated in
`agents/tasks/LJ-1-481/review-of-HullClosedLset.md`. That file is the
critic's input. It does not close the task.

## W2 (DD4)

The mathematics is written once at a generic carrier. `pins` is generic
in the environment (`Probe481.agda:53-57`). `HullStage` is generic in
`lam` and `X` (`:88-91`). Uniqueness instantiates at the class carrier
`𝒮ʟ`. The hull instantiates at `𝒮ᵥ`. No ordinal is fixed. No second
copy at a concrete stage. The conflict the clause names did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-481/Probe481.agda`, module
`LJ-1-481.Probe481 {ℓ} (lem)`.

- W3: `pins = Lset-only` (`:53-57`). Same term as
  `agents/tasks/LJ-1-458/Probe458.agda:62-66`. Site of the adequacy:
  `src/L/Hierarchy.lagda.md:334-335`.
- W3: `pins-at-most-one` (`:62-70`). Two environments that satisfy the
  graph at the same ordinal argument have the same value. Built from
  `pins`.
- D-10 correction beside the original: `pins-no-ord` (`:75-79`). Same
  type as `Probe458.agda:69-73`. Stated. Unbuilt.
- Telescope `HullStage` (`:88-98`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. The module keyword is at
  `:903`. Line `:916` is `module Condense`, and it is not copied.
  `M = H.T.Hull`.
- `OrdFromHull` (`:105-106`). The missing `IsOrd` source. Unbuilt.
- Predecessor step 2 restated as `ClosedLset` (`:111-113`). Unbuilt.
  Not a term named `HullClosedLset`.
- `JoinNeedsOrd` (`:119-120`): the type `OrdFromHull → ClosedLset`.
  Unbuilt as a term of that type.

Measured non-blank non-comment lines: 57. Total lines: 120. The brief
estimate was about 150 lines, of which the obligation is about 25.
Nothing is funded against the estimate. Uniqueness failed. The task
stopped at that point. I did not rebuild `[LJ-1.474]`'s `lset-codes`.

## STEP ONE, W3

**Uniqueness holds at an ordinal and has no source at a hull member.**

`pins` (`Probe481.agda:53-57`) is `Lset-only`. It is the type the
brief named from `src/L/Hierarchy.lagda.md:334-335`. Inhabited. The
obligation is omitted.

`pins-at-most-one` (`:62-70`) is "at most one satisfier at a given
index", from `pins`. Inhabited.

`pins-no-ord` (`:75-79`) is the same uniqueness without `IsOrd`.
Unbuilt. `[LJ-1.458]` left the same stronger type unbuilt
(`Probe458.agda:69-73`). I did not inhabit it. I did not postulate.

`IsOrd` at a hull member has no source. `OrdFromHull`
(`Probe481.agda:105-106`) records that. Unbuilt. `hull-member`
(`src/L/Hull.lagda.md:337-339`) returns a `Code`. `Hull⊆L`
(`:330-334`) places the member in `Lset α`. `Code` has `base` and
`wit` only (`:72-74`).

Three forced rechecks of the W3-only file (`pins` and
`pins-at-most-one`, obligation omitted), `_build` interface removed
before each, dependencies warm, caliber `-A64m -I0 -M8g`, one Agda
process. Exit 0 every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.74 | 378388480 |
| `runs/w3-2.out` / `w3-2.time` | 1.67 | 378388480 |
| `runs/w3-3.out` / `w3-3.time` | 1.63 | 366493696 |

Median wall **1.67 s**. Median peak RSS **378388480 bytes**. No heap
event. The first green W3-only check `runs/w3-0.out` was 1.71 s and
378421248 bytes, also exit 0. It is not one of the three forced
rechecks. The brief estimate for W3 was about 12 lines and under 15
seconds. The measured median is under that estimate.

## STEP TWO, THE OBLIGATION

Omitted. Uniqueness failed. The obligation is not inhabited. A
truncated conclusion was not written. I did not add `IsOrd` on `y`.
I did not postulate. I did not rebuild `lset-codes`. I did not apply
`inHull`.

Step 4 was not touched. `[LJ-1.477]` remains a critic-upheld NO-GO
(`agents/tasks/LJ-1-477/review-of-LJ-1-477-1.md:6`).

## WHAT LEVELIN STILL OWES

Four steps from `[LJ-1.462]`. I do not claim `levelIn`.

1. Step 1 is built. `step1 = C.πX-member` at
   `agents/tasks/LJ-1-462/Probe462.agda:133-134`. Type at `:129-131`.
2. Step 2 is unbuilt. The type is `HullClosedLset` at
   `Probe462.agda:136-138`. This task restates it as `ClosedLset` at
   `Probe481.agda:111-113` and does not inhabit it. This is a stated
   NO-GO.
3. Step 3's codes are GO. `lset-codes` at
   `agents/tasks/LJ-1-474/Probe474.agda:124-125`. The value equation
   `lset-code` at `Probe462.agda:109-111` is still unbuilt. This
   task's uniqueness measurement is why: `wit`'s value is `Lset y`
   only with `IsOrd`, which a hull member does not carry.
4. Step 4 is a critic-upheld NO-GO on the computation-law route.
   `[LJ-1.477]` verdict at
   `agents/tasks/LJ-1-477/lj-1.477-report.md:97`. Critic:
   `agents/tasks/LJ-1-477/review-of-LJ-1-477-1.md:6`, `verdict: upheld`.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense` (`src/L/BoundedSubset.lagda.md:917`).

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.67 s**,
  **378388480 bytes**. Exit 0.
- Full file, three forced rechecks. The D-10 types are in the file.
  The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.43 | 468664320 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.45 | 468680704 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.54 | 468697088 |

Median wall **2.45 s**. Median peak RSS **468680704 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the D-10 types were added, `runs/full-0.out` /
`full-0.time`, was 2.91 s and 468680704 bytes, also exit 0. It is not
one of the three forced rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.71 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `HullClosedLset` is not in scope. That is the intended NO-GO
  reading.

## 3. What NO-GO earns, and what is still owed

A NO-GO says the witness is not the set. `[LJ-1.474]`'s codes buy
less than they look. They produce a `Vec Code`. They do not produce
a code whose value is `Lset y` at a hull member. The hull route
needs uniqueness, with a source for `IsOrd`, before `feed` then
`inHull` can close step 2.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `HullClosedLset`.
- It does not inhabit `OrdFromHull`.
- It does not inhabit `pins-no-ord`.
- It does not inhabit `levelIn`.
- It does not refute `HullClosedLset`.
- It does not add `IsOrd` on `y`.
- It does not rebuild `lset-codes`.
- It does not touch step 4.
- It does not pay `cover`.
- It does not edit `src/`.

C-42: this is not a refutation. I did not search the tree for a false
shape.

`[LJ-1.462]` measured that `Lset-only` is at the class carrier and
`wit` searches in `TermAlgebra` over the stage
(`agents/tasks/LJ-1-462/lj-1.462-report.md:273-277`). That meeting is
still unmeasured.
Even with `IsOrd`, the join is not free. This task did not time it.

## 4. What the next brief needs

- Do not send `HullClosedLset` down `feed` then `inHull` as if
  `lset-codes` already pinned the value. They did not.
- `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` is uniqueness at
  an ordinal. Site of the inhabited form: `Probe481.agda:53-57`.
- `IsOrd` has no source at `⟨ y ∈ˢ M ⟩`. `OrdFromHull` at
  `Probe481.agda:105-106` is that gap as a type.
- Do not add `IsOrd` on `y` to inhabit step 2. The brief of this
  task forbade it: the hull carries none, and adding one changes the
  statement `levelIn` needs.
- `[LJ-1.474]`'s `lset-codes` at `Probe474.agda:124-125` still
  stands. Do not order those codes again.
- Step 4 remains a critic-upheld NO-GO on the computation-law route.
  Do not reopen that route as if this task had moved it.
- What the statement cost: 57 non-blank non-comment lines, W3 median
  1.67 s, full median 2.45 s, peak RSS 468697088 bytes on the kept
  rechecks. What the shape resisted: `IsOrd` at a hull member. What
  I had to weaken: nothing of the obligation. The obligation is
  omitted. What I could not close: `HullClosedLset`, `OrdFromHull`,
  `pins-no-ord`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4. W4
  did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ pins `v = L_γ`. That is the LST analogue of uniqueness.
  This tree's analogue is `Lset-only`, and it spends `IsOrd`. Devlin
  writes the biconditional at an ordinal index γ. A hull member is
  not that index.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. `search` picks a least satisfier. The gap is
  not truncation. The gap is that the satisfier is `Lset y` only
  with `IsOrd`.
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
- I did not inhabit `HullClosedLset`, `OrdFromHull` or `levelIn`.
- I did not add a `Code` constructor.
- I did not postulate. I did not add `IsOrd` on `y`.
- I did not rebuild `lset-codes`.
- I did not touch step 4.
- I did not pay `cover`.
- I did not hide the uniqueness gap in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-481/`:

- `lj-1.481-report.md`, this report
- `Probe481.agda`, W3 uniqueness and the D-10 types
- `review-of-HullClosedLset.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
