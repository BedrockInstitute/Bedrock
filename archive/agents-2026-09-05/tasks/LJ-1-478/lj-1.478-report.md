# LJ-1.478 report: carve the rank, at the formula two reports set up

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-478/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `rank-graph` in
`agents/tasks/LJ-1-478/Probe478.agda`. Land nothing in `src/`.

## PREDECESSORS, READ BEFORE ANY AGDA

1. `[LJ-1.475]` verdict, `agents/tasks/LJ-1-475/lj-1.475-report.md:107`:
   "**GO.** W3 typechecks `fn-clause : Formula S 3`"
   Delivered type, `agents/tasks/LJ-1-475/Probe475.agda:95`:
   `rank-formula : (Q : S) → Formula S 2`
   The report names `rankFo` and `rank-graph` at
   `agents/tasks/LJ-1-475/lj-1.475-report.md:209-216`. Pinning is the
   RelCond move at `:219-220`. The bound is not delivered at this `Q`,
   at `:225`. The report is not NO-GO. It does not name the statement
   FALSE. I take those types. I rebuild the body. I do not import a
   probe.

2. `[LJ-1.471]` verdict, `agents/tasks/LJ-1-471/lj-1.471-report.md:111`:
   "**GO.** W3 typechecks `hasSeparationL bnd (orderFo R P B C C₀)`"
   Delivered type, `agents/tasks/LJ-1-471/Probe471.agda:90-94`:
   `order-as-set` at a named parameter bound. The carve SHAPE is that
   type. The bound survey is at `:46`. C-42: that survey does not
   transfer. I re-measure the rank bound at its own site.

3. `[LJ-1.454]` verdict, `agents/tasks/LJ-1-454/lj-1.454-report.md:178-180`:
   first inhabit the formula, then carve. This task is the carve.

None of these reports is NO-GO on the carve this brief names.

## D-10, BEFORE ANY AGDA

`[LJ-1.475]` pinned `Q` with `con`. Pin `a` the same way. Written as
a type, before any Agda:

```
rankFo : (Q a : S) → Formula S 1
```

`a` is free at a Term position, `_∈̇_`, not at a `Fin` slot. `con a`
is the pin. If that pin reduces the arity, separation can eat the
formula. If it does not, that is the finding and the task stops.

`bnd` is a parameter. I do not inhabit it. I do not postulate it.

See `## WHERE THE BOUND COMES FROM` below. That list is the finding
this D-10 asks for. No delivered term in `src/` is already the
pair-bound of a member of `a` and that member's rank in `Q`. The
device that would supply it is `PairBound a β`
(`src/L/InjChain.lagda.md:276-297`) at a rank-bound `β`. This task
does not instantiate it.

The target that CAN be true at this generality is the carve at a
named parameter: `hasSeparationL bnd (rankFo Q a)`. The target that
would be false is a bound invented here.

## WHERE THE BOUND COMES FROM

The formula talks about pairs `(m , r)`: `m` is a member of `a`, and
`r` is the rank of `m` in the order `Q`
(`Probe475.agda:95-103`, `Probe478.agda:85-93`). The second component
is an ordinal, not a member of `a`. Every candidate below is a
delivered term in `src/`. C-42: `[LJ-1.471]` measured the ORDER bound
at Internal's `B`. That measurement does not transfer. I re-measure
here.

1. `PairBound` at `src/L/InjChain.lagda.md:276`. Generic in two sets
   `D` and `C`. Its `bnd` at `:296` holds every pair of a member of
   `D` with a member of `C` (`:299-300`). Instantiated at `a β` it
   would hold every pair of a member of `a` with a member of `β`.
   **The device fits, if `β` bounds the ranks.** This task does not
   instantiate it. `[LJ-1.471]` fitted `PairBound B B`. That instance
   does not fit here: both components of an order-pair live in `B`;
   the second component of a rank-pair does not live in `a`.

2. `StageBound` at `src/L/InjChain.lagda.md:75`. Generic in a small
   index `I` and a family `g : I → S`. Its `bnd` at `:92-93` is
   `LsetS β oβ`. **The engine fits.** The caller must supply `I` and
   `g`. `PairBound` is that caller for two sets. No caller in `src/`
   instantiates it at a member of `a` paired with that member's rank
   in a set `Q`.

3. `smallDom` at `src/L/Recursion.lagda.md:133`. Generic in a small
   type `X` and a family `f : X → S`. Same engine as `StageBound`
   (`boundingOrd` then `LsetS`). **The engine fits.** Same gap: no
   instantiation at this pair family.

4. `boundingOrd` at `src/L/Ordinal.lagda.md:154-155`. Bounds a small
   family of ordinals by one ordinal. **Fits as a bound on the RANGE
   of ranks, not as `bnd`.** Pair-bound is a set of pairs. This term
   is an ordinal. `PairBound` would consume such a `β`. The family it
   needs is the rank function. `swo-rank` supplies that family at an
   `SWO`, not at a set `Q` (`agents/tasks/LJ-1-416/Probe416.agda:105`).
   It is not in `src/`.

5. `pairsAt` at `src/L/Choice/Before.lagda.md:179-181`. Pairs of
   members of `finiteStage n`. **Does not fit.** The rank is an
   ordinal. The obligation is generic in `a`.

6. `pairsBound` at `src/L/Choice/Limit.lagda.md:418`. Pairs of
   `Limit`, that is members of `Lset ω`. **Does not fit.** Same
   reason: generic `a`, and the rank is not a limit-stage member.

7. `bound` at `src/L/Choice/Table.lagda.md:656-665`. Pairs of members
   of `Lset α`, confined further to `Related α`. **Does not fit.** The
   obligation is generic in `a`.

8. `InclGraph`'s `SB.bnd` at `src/L/InjChain.lagda.md:584-589`. The
   family is `dg m = prʟ (toD m) (toD m)`, identity pairs. **Does not
   fit.** The rank graph is not the identity graph.

9. `ShiftGraph`'s `SB.bnd` at `src/L/Absorption.lagda.md:591-594`. The
   family is the graph of a shift. **Does not fit.**

10. `orderL` at `src/L/Choice/Order.lagda.md:693-694`. The order as an
    element of the model. **Does not fit as `bnd`.** It is already a
    carved order, not a pair-bound for `rankFo`.

11. `relAt` at `src/L/Choice/Before.lagda.md:229-233`. Already the
    carved finite-stage relation. **Does not fit as `bnd`.**

12. `codeOrder` at `src/L/Choice/Limit.lagda.md:608`. Already the
    carved limit-stage order. **Does not fit as `bnd`.**

13. `rank` at `src/L/Rank.lagda.md:92-93`. The cumulative-hierarchy
    rank, sealed. **Does not fit.** It is V-rank, not the well-order
    rank of a set `Q`, and it is not a pair-bound.

14. `[LJ-1.417]`'s `swo-into-ord` at
    `agents/tasks/LJ-1-417/Probe417.agda:80`. An ordinal bound for the
    ranks of a generic `SWO A`. **Not in `src/`.** Not at a set `Q`.
    Bridging `Q` as a set to an `SWO` is a separate price.
    `[LJ-1.418]` instantiates that injection at every stage
    (`agents/tasks/LJ-1-418/lj-1.418-report.md:18-23`). That is still
    a stage, not this `Q`.

**None of these is a delivered inhabitant of the bound for pairs of a
member of `a` and that member's rank in `Q`.** The parameter is the
right shape. Instantiating `PairBound a β` is the next brief's whole
target, if a consumer must name the bound rather than take it. First
it must name `β`. `[LJ-1.471]`'s `PairBound B B` does not transfer.

## VERDICT

**GO.** W3 typechecks `rankFo : (Q a : S) → Formula S 1`
(`Probe478.agda:85-93`). Pinning `a` as `con a` reduces the arity.
Separation accepts this formula. `rank-graph` inhabits the unique
`SetOf` of that carve (`Probe478.agda:105-109`). Both directions read
back (`Probe478.agda:111-124`). Exit 0. No heap event. I did not write
`review-of-rank-graph.md`. I did not postulate. I did not inhabit
`bnd`. I did not claim `InjCode`
(`src/L/Cardinal.lagda.md:223-228`). I did not claim `Residue`. I did
not claim anything about limits.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

P-l (`dev/LESSONS.md:2357`): the type is over the generic carrier
`S`. It does not name a transparent stage presentation.

D-26 (`dev/LESSONS.md:1735`): this task does not well-order a tower
stage. It carves with a formula `[LJ-1.475]` already wrote.

## 1. W3: `rankFo`, first

**GO.** Pinning `a` needs only `con`. It does not need a second
`∃̇ (var zero ≐ con a)` binder.

Stated as `rankFo : (Q a : S) → Formula S 1` (`Probe478.agda:85-93`).
`rank-formula Q` is `Formula S 2` with free env `(z ∷ a ∷ [])`. `a`
occurs in Term position as `var (s4 zero)` after the pin of `Q` and
two binders (`Probe475.agda:100`). Replacing that variable by `con a`
drops `a` from the free env. The remaining indices do not shift:
`a` sat after `z`, so `z` stays at the same slot. `Q` still needs the
RelCond pin-binder, because `fnAt` and `assignAt` take `Fin` slots.
The obligation was omitted from that file.

ESTIMATE for W3 was about 6 lines and under 15 seconds. MEASURED:
`rankFo` is 9 lines. The W3-only file typechecked. Comparables of
shape, not of size. Nothing is funded against the estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 1.01 | 311902208 | `runs/w3-2.out` |
| w3-3 | 1.16 | 311902208 | `runs/w3-3.out` |
| w3-4 | 1.00 | 311918592 | `runs/w3-4.out` |

Median wall **1.01 s**. Peak RSS **311918592** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.21 s and
311869440 bytes, also exit 0. It is not one of the three forced
rechecks.

## 2. The inhabitant `rank-graph`

`rank-graph` is `Probe478.agda:105-109`. It is one
`hasSeparationL` at the named `bnd` and `rankFo`:

- helpers `fnAt`, `assignAt`, `supAt` rebuilt at `[LJ-1.475]`'s
  delivered constructors (`Probe478.agda:55-76`, from
  `Probe475.agda:51-80`)
- one pin `var zero ≐ con Q`
- `a` pinned as `con a` in Term position
- three binders `m`, `r`, `f`
- after those the env is `0 = f, 1 = r, 2 = m, 3 = Q', 4 = z`
- `hasSeparationL bnd (rankFo Q a) .fst` is the unique `SetOf`

Both readings unpack that field, as `order-as-set` did
(`Probe471.agda:96-109`):

- `rank-graph-out` (`Probe478.agda:111-116`)
- `rank-graph-in` (`Probe478.agda:118-124`)

I did not rebuild `order-as-set`. I did not import a probe. I did
not postulate. I did not inhabit `bnd`. I did not write a code.

ESTIMATE for the Agda was about 140 lines, of which the obligation
is about 30. MEASURED: 74 non-blank non-comment lines in the full
probe, of which `rank-graph` is 5 lines (`Probe478.agda:105-109`).
Comparables of shape, not of size. Nothing is funded against the
estimate.

Three forced rechecks of the full file, same caliber, one Agda
process at a time, interface removed:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 0.99 | 333168640 | `runs/full-2.out` |
| full-3 | 1.01 | 333168640 | `runs/full-3.out` |
| full-4 | 1.02 | 333168640 | `runs/full-4.out` |

Median wall **1.01 s**. Peak RSS **333168640** bytes. Exit 0 every
time. No heap event. The first check `runs/full-1.out` was 1.02 s
and 333168640 bytes, also exit 0. It is not one of the three forced
rechecks.

## 3. W2

The terms are generic in the carrier `S`. `fnAt`, `assignAt` and
`supAt` are written once at slots. `rankFo` instantiates `Q` and `a`
as constants, `Q` by one pin-binder and `a` by `con`. They name no
stage, no cardinal, no numeral, and no `Lset`. I did not write a
fixed form. W2 holds for what was written. No deadline asked for a
fixed form.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

`[LJ-1.475]` measured ONE site: whether the rank of an order carried
as a set has a `Formula S 2`. That site is GO. This task is the
carve of that formula, after one more pin. It is not that inventory.

Sweep of THIS shape, a carved `Formula S 1` rank graph over a named
bound:

- `src/`: 0 hits for `rank-graph`. 0 hits for `rankFo`.
- `src/`: 0 hits for `swo-rank`. 0 hits for `rank-formula`.
- Live carves of a `Formula S 1` with constants in Term position:
  `relAt` at `src/L/Choice/Before.lagda.md:232`, `codeOrder` at
  `src/L/Choice/Limit.lagda.md:608`, `tableAt`'s `sep` at
  `src/L/Choice/Table.lagda.md:785`, `order-as-set` in a probe.
  None consumes `rankFo`. Count of this exact carve in `src/`:
  **0**.

The `[LJ-1.471]` bound survey is a different shape (pairs of members
of `B`). This sweep does not re-price it. The re-measurement is
`## WHERE THE BOUND COMES FROM`.

## WHAT THE NEXT BRIEF NEEDS

- `rankFo : (Q a : S) → Formula S 1` typechecks
  (`Probe478.agda:85-93`). Pinning `a` is `con a` in Term position.
  It does not need a second RelCond binder.
- `rank-graph : (Q a bnd : S) → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G) ≡
  ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))` typechecks
  (`Probe478.agda:105-109`). Both readings typecheck
  (`Probe478.agda:111-124`).
- The bound is still a parameter. No delivered term in `src/` is the
  pair-bound of a member of `a` and that member's rank in `Q`. The
  device that would name it is `PairBound a β`
  (`src/L/InjChain.lagda.md:276-297`). Re-measure that instantiation.
  Do not postulate the bound. Do not transfer `[LJ-1.471]`'s
  `PairBound B B`.
- Do not claim `InjCode`. A carved graph is a set. `InjCode` is four
  conjuncts (`src/L/Cardinal.lagda.md:223-228`). This task delivers
  none of them.
- Do not claim `Residue`. Do not claim anything about limits. Those
  questions are now askable. Asking is a later brief.
- Do not send adequacy as part of a code. `[LJ-1.475]` left adequacy
  as a separate bridge from approximating functions to `swo-rank`
  (`agents/tasks/LJ-1-475/lj-1.475-report.md:236-253`).
- Do not rebuild `rank-formula`. Take `Q` and `a` as parameters, as
  this probe did.
- Do not reuse `[LJ-1.418]` as this `bnd`. That injection is at a
  stage (`agents/tasks/LJ-1-418/lj-1.418-report.md:18-23`), not at
  a set `Q`.

What the statement cost: 74 non-blank non-comment lines, W3 median
1.01 s, full-file median 1.01 s, peak RSS 333168640 bytes. What
the shape resisted: nothing of the pin, and nothing of the
separation. What I had to weaken: nothing. What I could not close:
an inhabitant of `bnd`. The parameter is the right shape.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`
  "THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether `hasSeparationL` accepts `rankFo`.
- `archive/dev/JOURNAL-archived.md:1229`
  "raw material at all (no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used. That archived journal records the absence of rank
  theory in the retired route. `[LJ-1.416]` filled the rank as DATA.
  `[LJ-1.475]` filled the object-language formula. This task fills
  the SET half of that absence, as a carved graph at a named bound.
- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired."
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used. The retired `L.WellOrder.Tree` is a well-order, not a
  pair-bound and not a rank-graph carve. No retired module turns a
  rank formula into a set by one separation. This task does not
  retire a module.
- `archive/dev/DD-archived.md:1`
  "THE `DD` RULING SERIES, archived in full 2026-08-18"
  Declined. Not used. The archived D series does not bear on the
  carve of `rankFo`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to
  SELECT a least witness. This task does not select. It carves the
  rank of an order that is already a set, over a parameter bound.
- `dev/literature/truncation-and-selection.md:67`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. The rank graph is not that device. Internal's order
  is the well-order side. The rank is a recursion on that order,
  now a set at a named bound.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the order type of the WHOLE order. This carve
  is the GRAPH of ranks of members, not that single ordinal.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. This formula
  describes the RANK of that order, and this carve makes that
  description a set.
- `dev/literature/glossary-review-2026-08.md:1`
  "Glossary review: the 119 pre-protocol entries"
  Declined. Not used. It reviews glossary entries. It does not
  bear on a rank-graph carve.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when the first run started.

- W3 first check, `runs/w3-1.out`: 1.21 s real, 311869440 bytes
  RSS, printed `Checking LJ-1-478.Probe478`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-478/Probe478.agdai`:
  1.01 s, 1.16 s, 1.00 s. Median **1.01 s**. Peak RSS
  **311918592** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).
- Full-file first check, `runs/full-1.out`: 1.02 s real,
  333168640 bytes RSS, printed `Checking LJ-1-478.Probe478`,
  exit 0.
- Three forced rechecks after `rm` of the same interface:
  0.99 s, 1.01 s, 1.02 s. Median **1.01 s**. Peak RSS
  **333168640** bytes. Exit 0 every time
  (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`).

Estimate for the Agda was about 140 lines for the whole
obligation. MEASURED 74 non-blank non-comment lines. Nothing is
funded against the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched. No `review-of-*.md`.

New files, all in `agents/tasks/LJ-1-478/`:

- `lj-1.478-report.md`, this report
- `Probe478.agda`, W3 `rankFo` then `rank-graph`
- `runs/`, the Agda transcripts named above
