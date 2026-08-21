# LJ-1.490 report: the fourth conjunct, at the delivered bound

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-490/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term `rank-coded` in
`agents/tasks/LJ-1-490/Probe490.agda`, the four `InjCode` conjuncts
over the rank carve, with the bound taken from `[LJ-1.486]`'s
delivered term. Land nothing in `src/`.

## PREDECESSORS, READ BEFORE ANY AGDA

1. `[LJ-1.486]` verdict, `agents/tasks/LJ-1-486/lj-1.486-report.md:162`:
   "**GO.** W3 typechecks `fits`"
   Delivered term, `agents/tasks/LJ-1-486/Probe486.agda:169-194`:
   `rank-bound : (a : S) (oa : IsOrd (fst a)) → Σ[ bnd ∈ S ] ...`.
   The bound is `PairBound a C .bnd`, a bounding STAGE. `C`, the
   bounding ordinal, is sealed behind `PB`. The report is GO. I take
   that type. I rebuild the body. I do not import a probe.

2. `[LJ-1.482]` verdict, `agents/tasks/LJ-1-482/lj-1.482-report.md:99`:
   "**NO-GO.** W3 typechecks `from-out`"
   The critic upheld it. The false close is at
   `agents/tasks/LJ-1-482/runs/w3-false-close.out:2-8`. The report is
   a stated NO-GO on the fourth conjunct. This brief names the bound
   that 482 lacked, so I do not stop on the predecessor. I rebuild the
   range clause at the delivered bound and measure it.

3. `[LJ-1.478]` verdict, `agents/tasks/LJ-1-478/lj-1.478-report.md:150`:
   "**GO.** W3 typechecks `rankFo : (Q a : S) → Formula S 1`"
   Delivered terms, `agents/tasks/LJ-1-478/Probe478.agda:105-124`:
   `rank-graph`, `rank-graph-out`, `rank-graph-in`. I take those
   types. I rebuild the carve. I do not import a probe.

4. `[LJ-1.418]` verdict, `agents/tasks/LJ-1-418/lj-1.418-report.md:23-24`:
   "The term is an untruncated injection from every stage into some
   ordinal. There is no pairing in the telescope. There is no `Init`,
   no band and no infiniteness."
   Delivered term, `agents/tasks/LJ-1-418/Probe418.agda:64-66`:
   `stage-into-bound`. This task does not take the limit
   instantiation. It is named in `## WHAT A LIMIT WOULD NOW COST`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`[LJ-1.482]`'s false close,
`agents/tasks/LJ-1-482/runs/w3-false-close.out:4-8`, is
`[UnequalTerms]`: `fst (prʟ (prʟ x x) (prʟ x y)) != fst y`. The pair
in the bound is not the second component. That is what the bound
lacked: a reading of the second component out of the bound.

One line: the bound now supplies the delivered set that holds the rank
pairs (a bounding stage), which `[LJ-1.482]` left a free parameter; it
is still a bounding stage, not the codomain ordinal, so the range
clause still does not close.

The bound `[LJ-1.486]` delivers is `PairBound a C .bnd`, a bounding
STAGE (`LsetS β' oβ'`). It holds the rank pairs. It is still a
bounding stage, not the codomain ordinal `C`. So the bound supplies
the SET that holds the pairs, which 482 left a free parameter, but it
does not supply the READING that the second component of a pair in the
carve is a member of `C`.

The finding, per the brief: `PairBound`'s membership (a pair in a
bounding stage) is not the codomain membership `InjCode` wants
(`fst y ∈ C`). The bound serves the carve, not the code. The two need
different sets: a bounding stage for the carve, and the bounding
ordinal for the code. That is worth more than the obligation, so I
state it and stop.

## VERDICT

**NO-GO.** W3 typechecks `from-out` (the reading) and the
`range-clause` type, exit 0. The range clause does not inhabit: a
close that treats the pair-in-bound as the second-component-in-codomain
is `[UnequalTerms]` (`runs/w3-false-close.out`, exit 42). The
obligation name `rank-coded` has no term. The witness meter reports
`1 UNRESOLVED of 1`, `probe_red=False` (`runs/witness.out`, exit 1).
I wrote `review-of-rank-coded.md`. I did not postulate. I did not add
a hypothesis to close a conjunct. I did not claim `InjCode`. I did not
claim a limit. I did not claim `Residue`.

The exact type that remains unbuilt is `RankCoded` at `Probe490.agda`
(the four conjuncts over the delivered carve):

    RankCoded : Type (ℓ-suc ℓ)
    RankCoded =
        (Q a : S) (oa : IsOrd (fst a)) (b : S)
      → InjCode (fst (rank-graph Q a (fst (rank-bound a oa)))) a b

The W3 found the range clause wants `b = C` (the bounding ordinal), so
the telescope changes from a free `b` to `b = C` when the adequacy
lands. See `## WHAT A LIMIT WOULD NOW COST`.

## 1. W3: the range clause, first

**NO-GO as the fourth conjunct.** Typechecked ALONE, with the other
three conjuncts and the obligation omitted. Caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. The probe interface was
deleted before every kept recheck.

`from-out` (`Probe490.agda:262-268`) applies `rank-graph-out` at the
coded pair, after the same `prʟ-fst` transport 482 used. The
conclusion, at `Probe490.agda:266`, is `⟨ prʟ x y ∈ˢ bnd ⟩ ×
⟨ (prʟ x y ∷ []) ⊨ rankFo Q a ⟩`. That is the PAIR in the bounding
stage, and satisfaction of `rankFo`. It is not `⟨ fst y ∈ fst C ⟩`.

`range-clause` (`Probe490.agda:276-279`) is the fourth conjunct at the
delivered bound: `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ →
⟨ fst y ∈ fst B.C ⟩`, with `G = rank-graph Q a bnd` and `bnd` the
delivered bound, `fst (rank-bound a oa)`. No term.

How I get from one to the other, at `file:line`: I do not. At
`Probe490.agda:266`, `from-out` supplies a pair in the bounding STAGE
`bnd` (a weak membership, a stage below the ordinal `bnd` names) and
satisfaction of `rankFo`. At `Probe490.agda:278`, the clause wants the
SECOND component in the bounding ORDINAL `C`. The bridge is the
adequacy of `rankFo` to `swo-rank`: reading the second component of a
pair in the carve back as a member of `C`. `[LJ-1.475]` left that
adequacy (`lj-1.475-report.md:236-253`); this task does not build it.
It does not transfer from the forward `PairBound.below` (a member and
a rank yield a pair in the bound), which is the other direction.

And it needs `b = C`, `[LJ-1.417]`'s bounding ordinal: the codomain is
`C` (`Probe490.agda:217`), the ordinal that holds the ranks. `b` is
determined by `a` and `oa`, not free.

The false close, `range-clause-false x y h = from-out x y h .fst`,
returns the pair-in-bound as the codomain membership. It is
`[UnequalTerms]` (`runs/w3-false-close.out`, exit 42): the bounding
stage

    fst (prʟ x y) ∈ fst (StageBound.bnd ... (PairBound.pw ... a C))

is not equal to the truncated second-component-in-codomain

    ∥ ... (i ≡ fst y) ∥₁

The bounding stage and the bounding ordinal are different sets. `b` is
determined, not free: the codomain is `C`, the bounding ordinal of the
rank. The obligation's telescope changes from a free `b` to `b = C`.

ESTIMATE for W3 was about 16 lines and under 25 seconds. MEASURED:
`from-out` is 6 lines, `range-clause` is 4. The W3 file typechecked.
Comparables of shape, not of size. Nothing is funded against the
estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 2.23 | 425132032 | `runs/w3-2.out` |
| w3-3 | 1.90 | 425197568 | `runs/w3-3.out` |
| w3-4 | 1.90 | 425132032 | `runs/w3-4.out` |

Median wall **1.90 s**. Peak RSS **425197568** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.89 s and
413401088 bytes, also exit 0. It is not one of the three forced
rechecks.

## 2. The inhabitant `rank-coded`

Not built. `RankCoded` is a type (`Probe490.agda`). There is no term
named `rank-coded`. See `review-of-rank-coded.md`.

Three forced rechecks of the full file (with `RankCoded`), probe
interface deleted, dependencies warm, exit 0 every time:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 1.81 | 405241856 | `runs/full-2.out` |
| full-3 | 1.82 | 405241856 | `runs/full-3.out` |
| full-4 | 1.80 | 405241856 | `runs/full-4.out` |

Median wall **1.81 s**. Peak RSS **405241856** bytes. Exit 0 every
time. No heap event. The first full check `runs/full-1.out` was 1.90
s and 423886848 bytes, also exit 0. It is not one of the three forced
rechecks.

ESTIMATE for the Agda was about 180 lines, of which the obligation is
about 50. MEASURED: the probe carries the carve, the rank, the bound
and the W3; `RankCoded` is 4 lines and has no body. Comparables of
shape, not of size. Nothing is funded against the estimate.

## 3. W2

The terms are generic in the carrier `S`. I rebuild `[LJ-1.478]`'s
`rankFo` once at slots and instantiate `Q` and `a` as constants. The
rank is generic in `A` and `w`. The bound is generic in two `𝒮ʟ`-sets.
I did not write a fixed form. No deadline asked for a fixed form. W2
holds for what was written. The conflict the clause names did not
arise.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

This NO-GO measures ONE site: the range clause (the fourth `InjCode`
conjunct) over the rank carve at the delivered bound. It is not a
refutation of the whole obligation. C-42's refutation sweep does not
fire. The count of the shape, a rank-graph range clause, is still owed
as a search:

- `src/`: 0 hits for `rank-graph`. 0 hits for `rankFo`. 0 hits for
  `rank-coded`. 0 hits for `rank-bound`.
- `PairBound` in `src/` sits at the definition
  (`src/L/InjChain.lagda.md:276`), at a comment (`:192`), and at
  `Comp` (`:327`). Count of this exact instantiation, a range clause
  over a rank carve, in `src/`: **0**.
- The shift code is a different site. `src/L/CodedShift.lagda.md:40-52`
  packs four `ShiftGraph` exports. That carve was built to serve
  `InjCode`; the rank carve was built to serve a description. C-42
  forbids the transfer.

## WHAT A LIMIT WOULD NOW COST

Do not claim a limit. Do not claim `Residue`. This task measured the
range clause at an ORDINAL carrier and found it wants the adequacy of
`rankFo` to `swo-rank`. The types that would still be needed to get a
coded injection at a LIMIT stage, and that this task does not inhabit:

1. `[LJ-1.418]`'s instantiation,
   `agents/tasks/LJ-1-418/Probe418.agda:64-66`:

       stage-into-bound : (α : S) → IsOrd α
                        → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))

   At a limit ordinal this is an untruncated ambient injection of the
   stage into an ordinal. It is not `InjCode`. There is no band and no
   infiniteness.

2. The bound at a limit. The well-order is `carry-at-generic`
   (`agents/tasks/LJ-1-418/Probe418.agda:50-51`), not the ordinal
   well-order `OrdSWO` this task rebuilt. The bound device is
   `PairBound (Lset α) C` at the limit stage, with `C` the bounding
   ordinal of the rank at `carry-at-generic`. This task rebuilt the
   bound at an ordinal; it does not inhabit it at a limit.

3. The range clause at a limit: the fourth conjunct over the limit
   carve, `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G-limit ⟩ →
   ⟨ fst y ∈ fst C-limit ⟩`, with `G-limit` the carve at the limit
   stage and `C-limit` the bound at a limit. This task found the
   ordinal instance wants the adequacy; the limit instance wants the
   same adequacy with the limit carve and the limit bound. It is a
   NO-GO at an ordinal, so a fortiori at a limit.

4. Adequacy of `rankFo` to `swo-rank`, which `[LJ-1.475]` left
   (`lj-1.475-report.md:236-253`): `(z ∷ a ∷ []) ⊨ rankFo Q a` iff
   `z` is the pair of a member of `a` and `swo-rank` of that member.
   It needs a well-order from the set `Q`, which the formula does not
   read as `SWO`.

I do not price these types from this task's seconds.

## WHAT THE NEXT BRIEF NEEDS

- `from-out` typechecks (`Probe490.agda`, the reading). It supplies a
  pair in the bounding stage and satisfaction of `rankFo`. It does not
  supply the second component in `C`.
- `range-clause` is a type (`Probe490.agda`). It has no term. The
  codomain is `C`, the bounding ordinal, so `b` is determined.
- The other three conjuncts (`svAt`, `domAt`, `injAt`) read the graph
  as a function, which also reads the second component of a pair in the
  carve. They want the same adequacy of `rankFo` to `swo-rank`. This
  task did not measure them (the W3 is the fourth); this is a shape
  observation, not a price. The brief's premise that three were
  already reachable at `[LJ-1.482]` is not supported by this
  measurement.
- The range clause wants the adequacy of `rankFo` to `swo-rank`, which
  `[LJ-1.475]` left. Fund that bridge first. Then the second component
  of a pair in the carve is a member of `C`, and the range clause
  closes.
- `PairBound.below` is the forward direction (a member and a rank
  yield a pair in the bound). The range clause wants the converse (a
  pair in the bound yields a member of `C`). The converse is not
  `below`.
- Do not add a hypothesis to close a conjunct. Do not postulate the
  bound. Do not transfer `[LJ-1.460]`'s packing by analogy.
- Do not claim a limit. Do not claim `Residue`. Those questions wait
  on a code, and the code waits on the types in
  `## WHAT A LIMIT WOULD NOW COST`.
- Do not rebuild `rank-formula`. Take `Q` and `a` as parameters, as
  this probe did.
- Do not reuse `[LJ-1.418]` as this `bnd`. That injection is at a
  stage, not at a set `Q`.

What the statement cost: the probe carries the carve, the rank, the
bound and the W3; W3 median 1.90 s, full-file median 1.81 s, peak RSS
425197568 bytes. What the shape resisted: the fourth conjunct, again.
What I had to weaken: nothing, because I did not inhabit the type.
What I could not close: the range clause, the fourth conjunct, for
want of the adequacy of `rankFo` to `swo-rank`. The bound is the
carve's set, not the code's codomain.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:3` Declined. Not used. It is a
  dispatch index. It does not bear on whether the bound is the
  codomain.
- `archive/dev/JOURNAL-archived.md:1229`
  "raw material at all (no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used as context. The archived journal records the absence of
  rank theory in the retired route. `[LJ-1.475]` filled the object-
  language half. `[LJ-1.486]` filled the bound. This task measured
  that the bound is the carve's set, not the code's codomain.
- `archive/dev/JOURNAL.md:3` Declined. Not used. The per-episode
  journal is retired. The history of this campaign is the task
  directories.
- `dev/ARCHIVE.md:1` Declined. Not used. No module was retired, so no
  row is written.
- `archive/dev/DD-archived.md:3` Declined. Not used. The archived D
  series does not bear on whether the bound is the codomain.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "Requirement: a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to SELECT
  a least witness. This task does not select. It asks whether a pair
  in a bounding stage is a member of the bounding ordinal. It is not,
  without the adequacy.
- `dev/literature/truncation-and-selection.md:68`
  "**The selection device is a definable well-order plus a universal guard.** The"
  Read. Used. The rank bound is not that device. The bound is a
  bounding stage, not a selection. The range clause is not a
  selection.
- `dev/literature/terms-2026-08.md:230`
  "**Sense.** The ordinal a well-order collapses to: \"the order type of the"
  Read. Used. That is the order type of the WHOLE order. The bound is
  a bounding stage of the rank pairs, not that single ordinal. The
  codomain is the bounding ordinal of the rank, a different set.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. `[LJ-1.416]` defined
  the RANK of that order as data. This task measured that the bound
  holds the rank pairs but is not their codomain.
- `dev/literature/glossary-review-2026-08.md:1` Declined. Not used.
  It reviews glossary entries. It does not bear on a rank-graph range
  clause.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root. I did not
set `GHCRTS`. No heap event. No other Agda compiler was live when each
run started.

- W3 first check, `runs/w3-1.out`: 1.89 s real, 413401088 bytes RSS,
  exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-490/Probe490.agdai`: 2.23 s,
  1.90 s, 1.90 s. Median **1.90 s**. Peak RSS **425197568** bytes.
  Exit 0 every time (`runs/w3-2.out`, `runs/w3-3.out`,
  `runs/w3-4.out`).
- False close, `runs/w3-false-close.out`: exit 42, `[UnequalTerms]`.
  The error line was in a temporary addition of
  `range-clause-false`; the green probe does not keep it. Not a price.
- Full-file first check, `runs/full-1.out`: 1.90 s real, 423886848
  bytes RSS, exit 0.
- Three forced rechecks after `rm` of the same interface: 1.81 s,
  1.82 s, 1.80 s. Median **1.81 s**. Peak RSS **405241856** bytes.
  Exit 0 every time (`runs/full-2.out`, `runs/full-3.out`,
  `runs/full-4.out`).
- Witness meter, `runs/witness.out`: 1.95 s, `1 UNRESOLVED of 1`,
  `probe_red=False`, exit 1.

Estimate for the Agda was about 180 lines. MEASURED: the probe carries
the carve, the rank, the bound and the W3, with `RankCoded` a 4-line
type and no body. Nothing is funded against the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-490/`:

- `lj-1.490-report.md`, this report
- `Probe490.agda`, the carve, the rank, the bound, W3 `from-out` and
  `range-clause`, `RankCoded` as a type
- `review-of-rank-coded.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
