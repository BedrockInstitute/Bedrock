# LJ-1.482 report: is the carved rank a code, and does it reach a limit

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-482/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `rank-coded` in
`agents/tasks/LJ-1-482/Probe482.agda`. Land nothing in `src/`.

## PREDECESSORS, READ BEFORE ANY AGDA

1. `[LJ-1.478]` verdict, `agents/tasks/LJ-1-478/lj-1.478-report.md:150`:
   "**GO.** W3 typechecks `rankFo : (Q a : S) → Formula S 1`"
   Delivered terms, `agents/tasks/LJ-1-478/Probe478.agda:105-124`:
   `rank-graph`, `rank-graph-out`, `rank-graph-in`. The report records
   "I did not claim `InjCode`" at `:156`. The report is not NO-GO. It
   does not name the statement FALSE. I take those types. I rebuild
   the body. I do not import a probe.

2. `[LJ-1.460]` verdict, `agents/tasks/LJ-1-460/lj-1.460-report.md:110`:
   "**GO.** The obligation typechecks"
   Delivered type, `agents/tasks/LJ-1-460/Probe460.agda:73-76`:
   `shift-coded`. Body at `:81-82` packs `SG.sv , SG.dm , SG.ij , SG.ran`.
   The same packing now sits in `src/` at
   `src/L/Absorption.lagda.md:619-620`. The report is not NO-GO.
   C-42: that packing does not transfer. I re-measure the four
   conjuncts at the rank carve.

Neither report is NO-GO on the statement this brief names. I do not
stop on a predecessor. I stop on D-10 below.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`InjCode` is four conjuncts, `src/L/Cardinal.lagda.md:223-228`. Only
the fourth names the codomain `b`. `[LJ-1.460]` packed four
`ShiftGraph` exports (`src/L/Absorption.lagda.md:452-498`, opened
publicly at `:605-606`) because that carve was built to serve
`InjCode`. `[LJ-1.478]`'s carve was built to serve a rank description.
Its delivered readings are the unique `SetOf` and the two unpackings
of that field (`Probe478.agda:105-124`). They are not the four
conjuncts.

The four, and the delivered reading that would have to supply each:

1. **svAt** (`src/L/Cardinal.lagda.md:225`):
   `⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩`.
   Supplier asked of 478: none. `rank-graph-out`
   (`Probe478.agda:111-116`) does not mention uniqueness of the
   second component. `ShiftGraph` got `sv` from `pair-out` and
   `Fo.val-cong` (`src/L/Absorption.lagda.md:453-465`). 478 exports
   neither.

2. **domAt** (`src/L/Cardinal.lagda.md:226`):
   `⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩`.
   Supplier asked of 478: none for totality. `rankFo` contains
   `var (suc zero) ∈̇ con a` (`Probe478.agda:90`). That is the first
   component in `a`, after a reading 478 did not deliver. The other
   direction is: every member of `a` has a pair in the graph.
   `rank-graph-in` (`Probe478.agda:118-124`) needs `z ∈ˢ bnd`. `bnd`
   is a parameter. Existence of approximating functions is the
   adequacy `[LJ-1.475]` left as a separate bridge
   (`agents/tasks/LJ-1-475/lj-1.475-report.md:236-253`).

3. **injAt** (`src/L/Cardinal.lagda.md:227`):
   `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩`.
   Supplier asked of 478: none. `[LJ-1.417]`'s `rank-inj` is at a
   generic `SWO` (`agents/tasks/LJ-1-417/Probe417.agda:60`). 478's
   `Q` is a set. `[LJ-1.475]` recorded that bridging `Q` as a set
   to an `SWO` is a separate price
   (`agents/tasks/LJ-1-475/lj-1.475-report.md:249-250`).

4. **range** (`src/L/Cardinal.lagda.md:228`):
   `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩`.
   Supplier asked of 478: none. `rank-graph-out`
   (`Probe478.agda:111-116`) supplies `z ∈ˢ bnd` and satisfaction
   of `rankFo`. That is membership of the PAIR in the bound, not
   membership of `y` in `b`. This is the W3 site.

No conjunct has a supplier at `file:line` in 478's delivered
readings. I do not inhabit the brief's type. I do not add a
hypothesis to close a conjunct. I do not postulate. I write
`review-of-rank-coded.md`. That file does not close the task.

Corrected target, beside the original: the four conjuncts over a
carve that already exports them, as `[LJ-1.460]` packed
`ShiftGraph` and as `src/L/Absorption.lagda.md:619-620` packs them
now. The rank carve is not that carve. A later brief that wants a
rank code must first supply, as types, the bound, the well-order
reading of `Q`, and the adequacy `[LJ-1.475]` deferred.

## VERDICT

**NO-GO.** W3 typechecks `from-out`
(`Probe482.agda:125-132`, exit 0, median 1.55 s on three forced
rechecks). It does not inhabit the fourth conjunct. A false close
that treated pair-in-bound as `y ∈ b` is `[UnequalTerms]`
(`runs/w3-false-close.out:2-8`, exit 42). The obligation name has
no term. The witness meter reports `1 UNRESOLVED of 1`,
`probe_red=False` (`runs/witness.out:1-2`). I wrote
`review-of-rank-coded.md`. I did not postulate. I did not inhabit
`bnd`. I did not claim `InjCode`. I did not claim `Residue`. I did
not claim anything about limits.

The exact type that remains unbuilt, so the next brief can quote
it without opening a hole, is at `Probe482.agda:149-152`:

    RankCoded =
        (Q a bnd b : S)
      → InjCode (fst (rank-graph Q a bnd)) a b

I rebuilt `[LJ-1.478]`'s carve at its delivered type
(`Probe482.agda:89-108`). I did not take the readings as module
hypotheses. I did not import a probe.

## 1. W3: `from-out`, first

**GO as a reading. NO-GO as the fourth conjunct.** Typechecked
ALONE, with the obligation omitted. Caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. The probe interface was
deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-482/Probe482.agdai`).

`from-out` (`Probe482.agda:125-132`) applies `rank-graph-out` at
the coded pair, after the same `prʟ-fst` transport `pair-out` uses
at `src/L/Absorption.lagda.md:435`. The conclusion is
`⟨ prʟ x y ∈ˢ bnd ⟩ × ⟨ (prʟ x y ∷ []) ⊨ rankFo Q a ⟩`. That is
the PAIR in the bound, and sat. It is not `⟨ fst y ∈ fst b ⟩`.

`RangeClause` (`Probe482.agda:136-140`) is the fourth conjunct as
the brief named it. No term.

A false close `range-clause-false b x y h = from-out x y h .fst`
failed with `[UnequalTerms]` (`runs/w3-false-close.out:2-8`):
`fst (pairʟ (pairʟ x x) (pairʟ x y)) != fst y`. The pair is not
the second component. That inhabitant was then removed. The green
file does not keep it.

The brief guessed that the clause might need the bound to be an
ordinal containing every rank. That is not the shape. `bnd` is a
pair-bound (`lj-1.478-report.md:62-80`). The missing condition is
that the second component of a pair in the graph lies in `b`.
`PairBound.below` at `src/L/InjChain.lagda.md:299-300` is the other
direction: members of `D` and `C` yield a pair in `bnd`. It does
not read a pair in `bnd` back to a member of `C`. I did not add
that converse. I did not add a condition on `b`.

ESTIMATE for W3 was about 14 lines and under 20 seconds. MEASURED:
`from-out` is 8 lines. `RangeClause` is 5. The W3-only file
typechecked. Comparables of shape, not of size. Nothing is funded
against the estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`. The W3-only file ended at `RangeClause`. It did
not import `InjCode` and did not name `RankCoded`.

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 1.87 | 339492864 | `runs/w3-2.out` |
| w3-3 | 1.55 | 339492864 | `runs/w3-3.out` |
| w3-4 | 1.54 | 339509248 | `runs/w3-4.out` |

Median wall **1.55 s**. Peak RSS **339509248** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.93 s and
339558400 bytes, also exit 0. It is not one of the three forced
rechecks. The false close `runs/w3-false-close.out` was 1.96 s,
exit 42, and is not a price.

The conjunct is not reachable from `rank-graph-out` alone. The
task stops at W3 for the fourth conjunct. D-10 already stopped the
other three.

## 2. The inhabitant `rank-coded`

Not built. `RankCoded` is a type (`Probe482.agda:149-152`). There
is no term named `rank-coded`. See `review-of-rank-coded.md`.

After W3 was green I added the type and the `InjCode` import. I
did not inhabit it. I did not import `LJ-1-478.Probe478` or
`LJ-1-460.Probe460`. I did not pack four exports the carve does
not have.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 2.25 | 376799232 | `runs/full-2.out` |
| full-3 | 2.17 | 390905856 | `runs/full-3.out` |
| full-4 | 2.22 | 377913344 | `runs/full-4.out` |

Median wall **2.22 s**. Peak RSS **390905856** bytes. Exit 0 every
time. No heap event. The first full check `runs/full-1.out` was
2.18 s and 390938624 bytes, also exit 0. It is not one of the
three forced rechecks.

ESTIMATE for the Agda was about 160 lines, of which the obligation
is about 45. MEASURED: 97 non-blank non-comment lines in the full
probe, of which `RankCoded` is 4 lines and has no body.
Comparables of shape, not of size. Nothing is funded against the
estimate.

The witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-482 --brief agents/tasks/LJ-1-482/LJ-1.482.md`) reports
`1 UNRESOLVED of 1`, 1.86 s, `probe_red=False`, exit 1
(`runs/witness.out:1-3`). This worktree has no `.venv`. The meter
ran under the parent venv. I added no dependency.

## 3. W2

The terms are generic in the carrier `S`. I rebuild `[LJ-1.478]`'s
`rankFo` once at slots and instantiate `Q` and `a` as constants. I
did not write a fixed form. No deadline asked for a fixed form. W2
holds for what was written. The conflict the clause names did not
arise.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

This NO-GO measures ONE site: the four `InjCode` conjuncts over
`[LJ-1.478]`'s carved rank graph. It is not a refutation of the
type. I did not build a term of the negation. C-42's refutation
sweep does not fire. The count of the shape, a code of a rank
graph, is still owed as a search:

- `src/`: 0 hits for `rank-graph`. 0 hits for `rankFo`. 0 hits for
  `rank-coded`.
- `InjCode` in `src/` sits at the definition
  (`src/L/Cardinal.lagda.md:223`), at `InjL`
  (`src/L/GCH.lagda.md:38`), at `shift-coded`
  (`src/L/Absorption.lagda.md:611-626`), and at `readL`
  (`src/L/CantorBernstein.lagda.md:33`). Count of this exact carve
  as a code in `src/`: **0**.
- The shift code is a different site. `[LJ-1.464]` measured that
  the shift route cannot reach a limit
  (`agents/tasks/LJ-1-464/lj-1.464-report.md:91`). That
  measurement does not transfer.

## WHAT A CODE HERE WOULD REACH

Do not claim a limit. Do not claim `Residue`. The types that would
still be needed to get a coded injection at a LIMIT stage, and
that this task does not inhabit:

1. `[LJ-1.418]`'s instantiation, `agents/tasks/LJ-1-418/Probe418.agda:64-66`:

       stage-into-bound : (α : S) → IsOrd α
                        → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))

   At a limit ordinal this is an untruncated ambient injection of
   the stage into an ordinal. It is not `InjCode`. There is no
   band and no infiniteness (`agents/tasks/LJ-1-418/lj-1.418-report.md:18-23`).

2. The bound `bnd`, still a parameter. The device that would name
   it is `PairBound a C` (`src/L/InjChain.lagda.md:276-297`), with
   `C` the `β` of (1) and `a` the stage as an `S`. `[LJ-1.478]`
   did not inhabit `bnd`. This task does not inhabit `bnd`.
   `PairBound.below` (`:299-300`) is not a reading of the second
   component out of the bound.

3. A set `Q` that is the order of that stage, so `rankFo Q a`
   describes the rank of that order. `carry-at-generic`
   (`Probe418.agda:50-51`) is an `SWO` on the stage. Bridging that
   `SWO` to a set `Q` is the price `[LJ-1.475]` recorded
   (`lj-1.475-report.md:249-250`).

4. Adequacy of `rankFo` to `swo-rank`: `(z ∷ []) ⊨ rankFo Q a`
   iff `z` is the pair of a member of `a` and that member's rank.
   `[LJ-1.475]` left that bridge
   (`lj-1.475-report.md:236-253`). `[LJ-1.417]`'s `swo-into-ord`
   (`Probe417.agda:80`) is the untruncated ambient injection from
   that rank. It is not `InjCode`.

5. Then the four conjuncts over that carve, packed as
   `src/L/Absorption.lagda.md:619-620` packs `ShiftGraph`'s
   exports. The rank carve does not export them today.

`Residue` at `agents/tasks/LJ-1-447/Probe447.agda:208-210` is not
any of those types. This report does not claim it.

I do not price these types from this task's seconds.

## WHAT THE NEXT BRIEF NEEDS

- `from-out` typechecks (`Probe482.agda:125-132`). It is
  `rank-graph-out` at the coded pair. It supplies pair-in-bound,
  not `y ∈ b`.
- `RangeClause` (`Probe482.agda:136-140`) and `RankCoded`
  (`Probe482.agda:149-152`) are types. They have no terms.
- No conjunct of `InjCode` has a supplier in `[LJ-1.478]`'s
  delivered readings. The carve serves a description. It does not
  serve a code. The two need different bounds: a pair-bound for
  the description, and a condition that ranks land in `b` for the
  code.
- Do not add a hypothesis to close a conjunct. Do not postulate
  the bound. Do not transfer `[LJ-1.460]`'s packing by analogy.
  Re-measure each conjunct at a carve that exports it, or fund
  the bound, the well-order reading of `Q`, and adequacy first.
- Do not claim a limit. Do not claim `Residue`. Those questions
  wait on a code, and the code waits on the types in
  `## WHAT A CODE HERE WOULD REACH`.
- Do not rebuild `rank-formula`. Take `Q` and `a` as parameters,
  as this probe did.
- Do not reuse `[LJ-1.418]` as this `bnd`. That injection is at a
  stage, not at a set `Q`.

What the statement cost: 97 non-blank non-comment lines, W3 median
1.55 s, full-file median 2.22 s, peak RSS 390905856 bytes. What
the shape resisted: every conjunct. What I had to weaken: nothing,
because I did not inhabit the type. What I could not close: all
four conjuncts. The range clause is the one W3 measured.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:3`
  "**Status: ARCHIVED RECORD. It is never rewritten.** These are the 464 dispatch rows"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether `rank-graph-out` supplies `InjCode`.
- `archive/dev/JOURNAL-archived.md:1229`
  "raw material at all (no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used. That archived journal records the absence of rank
  theory in the retired route. `[LJ-1.416]` filled the rank as DATA.
  `[LJ-1.475]` filled the object-language formula. `[LJ-1.478]`
  filled the SET half. This task measured that the CODE half is
  still absent: a carved description is not `InjCode`.
- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired. Every agent task already keeps its"
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `dev/ARCHIVE.md:1`
  "# ARCHIVE.md: the archive registry"
  Declined. Not used. No module was retired, so no row is written.
- `archive/dev/DD-archived.md:3`
  "**Status: ARCHIVED RECORD. Never rewritten, never deleted.** These are the 20 `DD` rows"
  Declined. Not used. The archived D series does not bear on
  whether the rank carve is a code.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to
  SELECT a least witness. This task does not select. It asks
  whether a carved rank description is already a code. It is not.
- `dev/literature/truncation-and-selection.md:68`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. The rank graph is not that device. Internal's order
  is the well-order side. The rank is a recursion on that order,
  now a set at a named bound, and still not a code.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the order type of the WHOLE order. A rank
  code would be the GRAPH of ranks of members, not that single
  ordinal. This task does not land that graph as `InjCode`.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. `[LJ-1.475]`
  described the RANK of that order. `[LJ-1.478]` made that
  description a set. This task measured that the set is not a
  code until the four conjuncts have suppliers.
- `dev/literature/glossary-review-2026-08.md:1`
  "Glossary review: the 119 pre-protocol entries"
  Declined. Not used. It reviews glossary entries. It does not
  bear on a rank-graph code.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when each run started.

- W3 first check, `runs/w3-1.out`: 1.93 s real, 339558400 bytes
  RSS, printed `Checking LJ-1-482.Probe482`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-482/Probe482.agdai`:
  1.87 s, 1.55 s, 1.54 s. Median **1.55 s**. Peak RSS
  **339509248** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).
- False close, `runs/w3-false-close.out`: 1.96 s real, exit 42,
  `[UnequalTerms]` at the then-current `Probe482.agda:146`. Not a
  price.
- Full-file first check, `runs/full-1.out`: 2.18 s real,
  390938624 bytes RSS, printed `Checking LJ-1-482.Probe482`,
  exit 0.
- Three forced rechecks after `rm` of the same interface:
  2.25 s, 2.17 s, 2.22 s. Median **2.22 s**. Peak RSS
  **390905856** bytes. Exit 0 every time
  (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`).
- Witness meter, `runs/witness.out`: 1.86 s, `1 UNRESOLVED of 1`,
  `probe_red=False`, exit 1.

Estimate for the Agda was about 160 lines for the whole
obligation. MEASURED 97 non-blank non-comment lines, no
inhabitant of `rank-coded`. Nothing is funded against the
estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-482/`:

- `lj-1.482-report.md`, this report
- `Probe482.agda`, W3 `from-out` then `RankCoded` as a type
- `review-of-rank-coded.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
