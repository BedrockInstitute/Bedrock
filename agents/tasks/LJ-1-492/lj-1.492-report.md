# LJ-1.492 report: the hull's own closure, CoverWitnessesInHull

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-492/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-492/Probe492.agda`:

    CoverWitnessesInHull :
        (y : S) → ⟨ y ∈ˢ M ⟩
      → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

from `H.T.closed`, not from `wit`. The type is taken from
`[LJ-1.484]`'s probe at `agents/tasks/LJ-1-484/Probe484.agda:123-126`,
never from this brief. Land nothing in `src/`.

W3 first, the type the brief names:

    coverFo : (yc : Code) → Formula Code 1

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## WHICH PREMISE MOVED

`[LJ-1.487]` is a critic-upheld NO-GO. Heading `## VERDICT` at
`agents/tasks/LJ-1-487/lj-1.487-report.md:170`. Quote at `:172-175`:

> **NO-GO at CoverWitnessesInHull, after W3 closed.** W3 is GO:
> `wit` names an ordinal at `isOrdFo`. The covering formula
> packages and feeds to `wit`. The obligation term is not written.

I did not inhabit a term via `wit`. I opened `closed`. I did not take
`levelIn` as a hypothesis. I did not inhabit `cover`.

`[LJ-1.484]` built `ambient-level` at
`agents/tasks/LJ-1-484/Probe484.agda:88-90`. I take that delivered
type. I rebuild the term. I do not import a probe.

`[LJ-1.160]` measured that the hull is not transitive
(`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). That measurement
still stands.

## D-10, BEFORE ANY AGDA

`closed` takes `Formula Code 1`
(`src/L/Hull.lagda.md:120-122`). The formula must say of `γ`: `γ` is
an ordinal and `y ∈ Lset γ`, with `y` as a `Code` constant. Each
piece, at `file:line`:

1. **Ordinal predicate.** `[LJ-1.487]`'s `φord` at
   `agents/tasks/LJ-1-487/Probe487.agda:79-80` is `isOrdFo {K = ⊥* {ℓ}}
   {n = 1} zero`. The generic spelling is at `:52-55`, the same as
   `isOrdAt` at `src/L/BoundedSubset.lagda.md:795-798`. Instantiated
   at `K = Code`, `n = 1`, this is `Formula Code 1`. No constants.
   Arity one is free.

2. **Level formula.** `LsetGraphAt` at
   `src/L/Coding/Sequence.lagda.md:349`, type
   `∀ {n} → Fin n → Fin n → Formula S n`, with `S` the carrier of
   `𝒮ʟ` (`src/L/Coding/Sequence.lagda.md:59`). It is not generic in
   `K`. `[LJ-1.458]` found it delivered
   (`agents/tasks/LJ-1-458/lj-1.458-report.md:71`). `[LJ-1.474]` is GO
   on codes for its constants
   (`agents/tasks/LJ-1-474/lj-1.474-report.md:70`). The arity-two
   instance `LsetGraphAt {n = 2} zero (suc zero)` is the graph of
   `Lset` at value slot `0` and argument slot `1`.

3. **`y`'s code.** `[LJ-1.484]`'s step 1, `code-of` at
   `agents/tasks/LJ-1-484/Probe484.agda:68-69`, is `H.hull-member`.
   Site: `src/L/Hull.lagda.md:337-339`. Type:
   `(y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁`.
   The constant `con yc` is that code.

**Can the conjunction form at arity one?** Yes, as syntax. `y` is a
constant, not a free variable. The shape is `coverFoGen` at
`Probe492.agda:57-61`. `isOrdFo` at `n = 1` is `Formula Code 1`.
The inner formula after `∃̇` is `Formula Code 2` (bound `v` at `0`,
original `γ` at `1`). `mapFo` at
`src/FOL/Manipulation/Relabelling.lagda.md:54-56` sends
`Formula CS.S 2` to `Formula Code 2`. `con yc ∈̇ var zero` is
`Formula Code 1` after the existential. The conjunction is
`Formula Code 1`. Nothing blocks the arity. W3 measured this.

**What `closed` still needs after the formula forms.** `closed` at
`src/L/Hull.lagda.md:120-122` takes an ambient witness of type
`∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁`, with `S𝒮` the stage carrier
`SL` (`src/L/Hull.lagda.md:155-156`, `:323`). `[LJ-1.484]`'s
`ambient-level` at `Probe484.agda:88-90` has type
`∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁`. Those
types do not match. The conversion is STAGE satisfaction of the
graph. Adequacy `Lset-defines` / `Lset-only` is at `𝒮ʟ`
(`src/L/Hierarchy.lagda.md:646-648` and `:334-335`). `⊨c` is at
`AbsL.𝒮M`. The graph is not Δ₀ (`GraphAt` is an unbounded `∃̇` at
`src/L/Coding/Sequence.lagda.md:292`). Δ₀ transfer
(`src/L/Absoluteness.lagda.md:122-123`) does not move it. I did not
add an elementarity hypothesis. That conversion did not close.
`closed` is not enough.

## W8, LITERATURE, BEFORE ANY AGDA

The orthodox argument, `dev/literature/devlin-II5.md:107-108`: the
reverse inclusion transfers `∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)` from `L_α`
to `X` by Σ₁-elementarity. `closed` is the hull's Tarski-Vaught
criterion. It transfers STAGE satisfaction into the hull. It does
not transfer a meta-level covering into STAGE satisfaction. Devlin
does not identify those two steps. I do not stop as a literature
NO-GO before W3.

## PREDECESSOR TYPES

- `[LJ-1.487]` is NO-GO at `CoverWitnessesInHull`
  (`agents/tasks/LJ-1-487/lj-1.487-report.md:170`). The statement is
  not named FALSE. This task inhabits the same type via `closed`.
- `[LJ-1.484]` is NO-GO at D-10 step 4
  (`agents/tasks/LJ-1-484/lj-1.484-report.md:114`). It built
  `ambient-level` at `Probe484.agda:88-90`. I take that type.
- `[LJ-1.462]` is NO-GO at D-10 step 3 for `levelIn`
  (`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). The statement is
  not named FALSE. This task does not inhabit `levelIn`.
- `[LJ-1.474]` is GO on codes for the level formula's constants
  (`agents/tasks/LJ-1-474/lj-1.474-report.md:70`).
- `[LJ-1.458]` is GO on the level formula
  (`agents/tasks/LJ-1-458/lj-1.458-report.md:71`).
- `[LJ-1.160]` measured that the hull is not transitive
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`).

## VERDICT

**NO-GO at CoverWitnessesInHull, after W3 closed and `closed` opened.**
W3 is GO: the formula at arity one typechecks. `closed` is applied
at that formula. The conversion from `ambient-level` to STAGE
satisfaction of `coverFo` is unbuilt. The obligation term is not
written. Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

This is an obstruction of the conversion, not a refutation of the
type. I did not build a term of the negation. The NO-GO is stated
in `agents/tasks/LJ-1-492/review-of-CoverWitnessesInHull.md`. That
file is the critic's input. It does not close the task.

**The hull's own closure does not reach its own consumer.** `closed`
transfers STAGE satisfaction of `Formula Code 1` into the hull. The
consumer's covering is a meta-level fact. Those are not the same
hypothesis.

## WHAT COVER STILL OWES

Restate of `[LJ-1.484]`'s four steps, this one marked. I do not
claim `cover`.

1. **code-of.** BUILT, by `[LJ-1.484]`, rebuilt here at
   `Probe492.agda:132-133` as `H.hull-member`. Site:
   `src/L/Hull.lagda.md:337-339`.

2. **StageBoundOfCode.** UNBUILT. Wrong shape. A `Code` does not
   carry an ordinal (`src/L/Hull.lagda.md:72-74`). Still wrong.
   This step does not supply `CoverWitnessesInHull`.

3. **ambient-cover / ambient-level.** BUILT, by `[LJ-1.484]`,
   rebuilt here at `Probe492.agda:137-151`. The index is in `lam`,
   not in `M`. Still not `cover`. `pack-index` at `:157-158` puts
   that index in `Lset lam`. That is STAGE membership, not hull
   membership.

4. **CoverWitnessesInHull.** UNBUILT. This task. The type is at
   `Probe492.agda:216-219`. The formula forms (`coverFo` at
   `:124-125`). `closed` is opened (`closed-at-cover` at
   `:191-195`). `isOrdFo` at `⊨c` is both directions (`:162-186`).
   `StageSatOfCover` at `:205-209` is the missing conversion. No
   term of the obligation type.

`cover` stays unbuilt. It is not a join. Steps 5 and 6 of
`[LJ-1.484]` stay as they were. Step 7 stays unbuilt. `levelIn`
stays an unpaid sibling.

## DOES THIS REACH levelIn

`closed` at `coverFo`, given `StageSatOfCover`, would inhabit
`CoverWitnessesInHull`:
`(y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁`.
That type is not `[LJ-1.481]`'s `ClosedLset`
`(y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩` at
`agents/tasks/LJ-1-481/Probe481.agda:111-113`, and it is not
`OrdFromHull` `(y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y` at `:105-106`:
`closed` at `coverFo` produces `IsOrd` of a covering index, not
`IsOrd` of the hull member `y`.

`closed` does not bear on `[LJ-1.489]`'s `PiCommuteD`
`(y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)` at
`agents/tasks/LJ-1-489/Probe489.agda:139-141`: `closed` does not
mention `π` or `𝒟ₒ`, and it does not transfer satisfaction along
the collapse. `levelIn` still needs a new decomposition. This
application is not that decomposition. I did not attempt either.

## W2 (DD4)

The mathematics is written once at a generic carrier. `isOrdFo` is
generic in `K` (`Probe492.agda:48-51`). `coverFoGen` is generic in
`K` (`:57-61`). Instantiation is at `Code` inside the hull
telescope (`coverFo` at `:124-125`). `succFo` and `numeralFo` are
generic in `K` (`:81-91`). The module is generic in `ℓ`. `lam`,
`X` and the limit hypotheses stay parameters. No ordinal is fixed.
No second copy at a concrete stage. The conflict the clause names
did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-492/Probe492.agda`, module
`LJ-1-492.Probe492 {ℓ} (lem)`.

- Telescope `HullStage` (`:97-100`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. Nothing below
  `module Condense` is copied. `M = H.T.Hull`. `levelIn` is not a
  parameter. `cover` is not a parameter.
- `isOrdFo`, generic in `K` (`:48-51`).
- `coverFoGen`, generic in `K` (`:57-61`). `mapFo` of
  `LsetGraphAt {n = 2} zero (suc zero)` plus `con yc ∈̇ var zero`.
- Decoder `tagOf` / `ck` / `lset-emb` (`:67-78`, `:118-122`),
  rebuilt from `[LJ-1.474]`, not imported. `wit` names numeral
  codes for the graph's constants. `wit` is not the covering
  witness.
- W3 inhabited: `coverFo` (`:124-125`).
- `code-of` (`:132-133`), `ambient-cover` / `ambient-level`
  (`:137-151`), rebuilt from `[LJ-1.484]`.
- `pack-index` (`:157-158`).
- `isOrdFo-out` (`:162-179`) and `isOrdFo-in` (`:181-186`) at `⊨c`.
- `closed-at-cover` (`:191-195`): `closed (coverFo yc)`.
- `StageSatOfCover` (`:205-209`). Unbuilt. The conversion.
- Obligation as type: `CoverWitnessesInHull` (`:216-219`).
  Unbuilt. No term of that type.

Measured non-blank non-comment lines: 128. Total lines: 219. The
brief estimate was about 170 lines, of which the obligation is
about 45. Nothing is funded against the estimate.

## STEP ONE, W3

**The formula at arity one forms.** `coverFo`
(`Probe492.agda:124-125`) is the brief's type, inhabited. The
obligation is omitted in the W3-only file. `y` enters as
`con yc`. The ordinal conjunct is `isOrdFo {K = Code} {n = 1}
zero`. The level conjunct is `mapFo lset-emb (LsetGraphAt {n = 2}
zero (suc zero))` under one existential, with `y ∈ v`.

This is not `[LJ-1.487]`'s `φord`. That formula had no parameters.
C-42: a parameter-free formula is not this one, and this run does
not fund against `[LJ-1.487]`'s W3.

Three forced rechecks of the W3-only file (`coverFo` only,
obligation omitted), `_build` interface removed before each,
dependencies warm, caliber `-A64m -I0 -M8g`, one Agda process.
Exit 0 every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.35 | 472301568 |
| `runs/w3-2.out` / `w3-2.time` | 2.13 | 472317952 |
| `runs/w3-3.out` / `w3-3.time` | 2.14 | 472334336 |

Median wall **2.14 s**. Median peak RSS **472317952 bytes**. No heap
event. The first green W3-only check `runs/w3-0.out` was 3.09 s and
472285184 bytes, also exit 0. It is not one of the three forced
rechecks. The brief estimate for W3 was about 20 lines and under
25 seconds. The measured median is under that estimate.

## STEP TWO, THE OBLIGATION

Omitted as a term. `CoverWitnessesInHull` is a `Type` at
`Probe492.agda:216-219`. `closed` is opened. A truncated conclusion
was not written from an unbuilt conversion. `levelIn` was not
added as a hypothesis. `cover` was not added as a hypothesis.
`wit` was not used to name a covering index.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency
warm, from the repository root. The probe interface was deleted
before every kept run.

- W3, three forced rechecks: see the table above. Median
  **2.14 s**, **472317952 bytes**. Exit 0.
- Full file, three forced rechecks. W3, `closed-at-cover`,
  `ambient-level`, `isOrdFo` at `⊨c`, and the D-10 types are in
  the file. The obligation is omitted as a term.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.81 | 508936192 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.71 | 483704832 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.98 | 461881344 |

Median wall **2.81 s**. Median peak RSS **483704832 bytes**.
Exit 0 every time. Each printed `Checking`. No heap event.
The first green full check `runs/full-0.out` was 3.11 s and
508854272 bytes, also exit 0. It is not one of the three forced
rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.74 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `CoverWitnessesInHull` is a `Type` inside `HullStage`. That is
  the intended NO-GO reading. The worktree has no `.venv`. The
  meter ran under `/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

## 3. What NO-GO earns, and what is still owed

NO-GO names what `closed` lacks. The formula at arity one forms.
`closed` is the hull's Tarski-Vaught criterion and it is applied
at that formula. It does not take `ambient-level` as its
hypothesis. The missing object is `StageSatOfCover`: STAGE
satisfaction of the level graph at `Formula Code 1`. Adequacy of
the graph is at `𝒮ʟ`. `⊨c` is at `AbsL.𝒮M`. Those semantics do
not meet. That is the first measurement of what the condensation
front owes beyond the hull's own closure.

What this task does not settle:

- It does not inhabit `CoverWitnessesInHull`.
- It does not inhabit `cover`.
- It does not inhabit `levelIn`.
- It does not refute `CoverWitnessesInHull`.
- It does not inhabit `StageSatOfCover`.
- It does not re-measure `[LJ-1.474]` at `coverFo`. C-42.
- It does not edit `src/`.

## 4. What the next brief needs

- Do not order `coverFo` again. The formula at arity one forms.
- Do not order `code-of` or `ambient-level` again. `[LJ-1.484]`
  built them. This task rebuilt them.
- Do not order `isOrdFo-in` / `isOrdFo-out` at `⊨c` again. Both
  closed. They are Δ₀. They are not the graph.
- Do not order a covering index from `wit`. `[LJ-1.487]` measured
  that route.
- The unpaid object is still `CoverWitnessesInHull`. A brief that
  sends `ambient-level` through `closed` must fund STAGE
  satisfaction of `coverFo` at `AbsL.𝒮M`, which is
  `StageSatOfCover` at `Probe492.agda:205-209`. Adequacy of
  `LsetGraphAt` at `𝒮ʟ` is not that fact.
- A brief that takes the elementarity route must inhabit
  `M ≺_{Σ₁} L_lam` at `Formula Code` (or `coverFo`) at this
  telescope, or `Lset lam ≺_{Σ₁} L` at the language of the graph.
  `closed` is not that fact.
- Do not take `levelIn` as a hypothesis of a `cover` probe.
- `levelIn` needs a new decomposition. See `## DOES THIS REACH
  levelIn`.
- What the statement cost: 128 non-blank non-comment lines, W3
  median 2.14 s, full median 2.81 s, peak RSS 508936192 bytes
  on the kept rechecks. What the shape resisted: STAGE
  satisfaction of the mapped level graph. What I had to weaken:
  nothing of the obligation. What I could not close:
  `CoverWitnessesInHull`.

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
  Also read at `:107`. Quote:
  `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the`.
  Also read at `:108`. Quote:
  `statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally`.
  Used: `CoverWitnessesInHull` is that reverse-inclusion transfer
  of the covering witnesses into the hull. Φ is the LST analogue.
  The orthodox argument uses Σ₁-elementarity of X in L_α. `closed`
  is the hull's Tarski-Vaught criterion. It transfers STAGE
  satisfaction into the hull. It does not transfer a meta-level
  covering into STAGE satisfaction of Φ. Devlin does not identify
  those two steps.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a formula at arity one. It is not a
  truncation question. The conclusion of the obligation is already
  truncated once.
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
- I did not inhabit `CoverWitnessesInHull` or `cover`.
- I did not take `levelIn` as a hypothesis.
- I did not postulate. I did not weaken `γ ∈ M`.
- I did not import a probe.
- I did not use `wit` to name a covering index.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-492/`:

- `lj-1.492-report.md`, this report
- `Probe492.agda`, W3, `closed-at-cover`, and the D-10 types
- `review-of-CoverWitnessesInHull.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
