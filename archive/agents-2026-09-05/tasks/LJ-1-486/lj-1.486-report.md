# LJ-1.486 report: the bound the rank carve has never had

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-486/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `rank-bound` in
`agents/tasks/LJ-1-486/Probe486.agda`. Land nothing in `src/`.

## PREDECESSORS, READ BEFORE ANY AGDA

1. `[LJ-1.482]` verdict, `agents/tasks/LJ-1-482/lj-1.482-report.md:99`:
   "**NO-GO.** W3 typechecks `from-out`"
   The critic upheld it, `agents/tasks/LJ-1-482/review-of-LJ-1-482-1.md:14`:
   "The NO-GO stands."
   Quoted in full under `## WHAT A CODE HERE WOULD REACH` below.
   The report names the device `PairBound a C` at `:264-267`.
   The report is a stated NO-GO. The slot clause that would stop on a
   predecessor NO-GO does not fire on the statement this brief names:
   this brief does not inhabit `rank-coded`. It inhabits the bound
   that 482 named and did not build.

2. `[LJ-1.478]` verdict, `agents/tasks/LJ-1-478/lj-1.478-report.md:150`:
   "**GO.** W3 typechecks `rankFo : (Q a : S) → Formula S 1`"
   `bnd` stayed a parameter. I do not import that probe. I do not
   carve.

3. `[LJ-1.416]` verdict, `agents/tasks/LJ-1-416/lj-1.416-report.md:15`:
   "**GO.** The obligation typechecks."
   Delivered type, `agents/tasks/LJ-1-416/Probe416.agda:105-106`:
   `swo-rank : {A : Type ℓ} (w : SWO A) → A → S` with `S` from `𝒮ᵥ`.
   The report is not NO-GO. I take that type. I rebuild the body.
   I do not import a probe.

4. `[LJ-1.417]` verdict, `agents/tasks/LJ-1-417/lj-1.417-report.md:19`:
   "**GO.** The obligation typechecks"
   Delivered type, `agents/tasks/LJ-1-417/Probe417.agda:80`:
   `swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))`
   under the module telescope `:44-51`. The report is not NO-GO.
   I take the bounding ordinal as `boundingOrd` on the rebuilt rank,
   the pack at `Probe417.agda:83-89`. Rebuilt. Not a module
   hypothesis. The injection `A ↪ ⟪ β ⟫` is not spent.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## WHAT A CODE HERE WOULD REACH

Quoted from `[LJ-1.482]`, `agents/tasks/LJ-1-482/lj-1.482-report.md:249-286`,
as this brief requires. The verdict there is a stated NO-GO (`:99`).
I write.

> Do not claim a limit. Do not claim `Residue`. The types that would
> still be needed to get a coded injection at a LIMIT stage, and
> that this task does not inhabit:
>
> 1. `[LJ-1.418]`'s instantiation, `agents/tasks/LJ-1-418/Probe418.agda:64-66`:
>
>        stage-into-bound : (α : S) → IsOrd α
>                         → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))
>
>    At a limit ordinal this is an untruncated ambient injection of
>    the stage into an ordinal. It is not `InjCode`. There is no
>    band and no infiniteness (`agents/tasks/LJ-1-418/lj-1.418-report.md:18-23`).
>
> 2. The bound `bnd`, still a parameter. The device that would name
>    it is `PairBound a C` (`src/L/InjChain.lagda.md:276-297`), with
>    `C` the `β` of (1) and `a` the stage as an `S`. `[LJ-1.478]`
>    did not inhabit `bnd`. This task does not inhabit `bnd`.
>    `PairBound.below` (`:299-300`) is not a reading of the second
>    component out of the bound.
>
> 3. A set `Q` that is the order of that stage, so `rankFo Q a`
>    describes the rank of that order. `carry-at-generic`
>    (`Probe418.agda:50-51`) is an `SWO` on the stage. Bridging that
>    `SWO` to a set `Q` is the price `[LJ-1.475]` recorded
>    (`lj-1.475-report.md:249-250`).
>
> 4. Adequacy of `rankFo` to `swo-rank`: `(z ∷ []) ⊨ rankFo Q a`
>    iff `z` is the pair of a member of `a` and that member's rank.
>    `[LJ-1.475]` left that bridge
>    (`lj-1.475-report.md:236-253`). `[LJ-1.417]`'s `swo-into-ord`
>    (`Probe417.agda:80`) is the untruncated ambient injection from
>    that rank. It is not `InjCode`.
>
> 5. Then the four conjuncts over that carve, packed as
>    `src/L/Absorption.lagda.md:619-620` packs `ShiftGraph`'s
>    exports. The rank carve does not export them today.

This task inhabits item 2's bound, at an ordinal carrier. It does not
inhabit 1, 3, 4 or 5. It does not claim a limit. It does not claim
`Residue`. It does not carve. It does not build any `InjCode` conjunct.

## D-10, BEFORE ANY AGDA

`PairBound` at `src/L/InjChain.lagda.md:276-277` is

    module PairBound (D C : S) where

with `S` from `𝒮ʟ` (`src/L/InjChain.lagda.md:53`). Its `below` at
`:299-300` is

    below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
          → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩

Two `𝒮ʟ`-sets. The pair is a member of `D` with a member of `C`.

`[LJ-1.417]`'s `swo-into-ord` at `Probe417.agda:80-88` packs
`boundingOrd A swo-rank swo-rank-ord`. The first component is a
`V`-ordinal `β`. The third says every rank is a member of `β`.
A pair `pr m r` with `m ∈ a` and `r ∈ β` is exactly `PairBound a C`
at `C` whose first projection is that `β`.

What `PairBound` needs that this telescope does not give, at
`file:line`:

1. `C : S` as an `𝒮ʟ`-set. `[LJ-1.417]` supplies `β : S` from
   `𝒮ᵥ` (`Probe417.agda:84-85`, `S` opened from `𝒮ᵥ` at `:37`).
   `𝒮ʟ = 𝒮ᵥ ↾ isL` (`src/L/Constructible.lagda.md:410-411`), so
   `C` is `(β , isL β)`. The rank does not wrap `β`. The wrap is
   `isL-ord` at `src/L/SquareLawClosed.lagda.md:51-52`. Rebuilt,
   `opaque`, at `Probe486.agda:116-118`. SquareLawClosed takes
   extra parameters `(α₀ , oα₀)` (`:19-20`), so it is not an
   import. I do not postulate.

2. The well-order `w` that `swo-rank w m` names. `[LJ-1.416]`'s
   type is `{A : Type ℓ} (w : SWO A) → A → S`
   (`Probe416.agda:105-106`). The brief's telescope is
   `(a : S) (oa : IsOrd (fst a))`. `oa` supplies `OrdSWO` on
   `⟪ fst a ⟫` (`src/L/StageCardinal.lagda.md:228-264`). Rebuilt
   at `Probe486.agda:125-161`. PairBound does not need `w`. The
   conclusion of `rank-bound` does.

3. The conversion of `m : S` to the carrier `A`. `swo-rank` wants
   `A`. `fiber` at `src/V/Presentation.lagda.md:34-35` sends
   `⟨ fst m ∈ fst a ⟩` to `⟪ fst a ⟫`. The brief wrote
   `swo-rank w m` with `m : S`. That does not form. The type that
   typechecks is at `Probe486.agda:169-175`.

`PairBound` does not want `IsOrd` of `D`. The `oa` in the telescope
is for `w`, not for the bound device.

The brief said: if `PairBound` wants something the rank does not
supply, name it and STOP. The wrap `isL-ord` is that thing. It is
delivered. I do not stop. I rebuild it. I do not postulate.

The brief's `⟨ fst m ∈ˢ fst a ⟩` does not form at `𝒮ʟ`: `_∈ˢ_`
there wants two `S`. PairBound.below spells `⟨ fst m ∈ fst a ⟩`.
Restriction makes `⟨ m ∈ˢ a ⟩` the same membership
(`src/FOL/ZFStructure.lagda.md:149`). I take PairBound's spelling.

Corrected target, beside the original: the type at
`Probe486.agda:169-175`. The original sketch has a free `w` and
applies `swo-rank` to an `S`. The corrected type binds `mx` so
`fiber` can send it, and takes `w` from `oa` via `OrdSWO`.

## VERDICT

**GO.** W3 typechecks `fits` (`Probe486.agda:66-67`, exit 0, median
1.62 s on three forced rechecks). The arities match: `PairBound`
takes two `𝒮ʟ`-sets, and the rank's pairs are a member of `a` with
a member of `β`. `rank-bound` inhabits the bound
(`Probe486.agda:169-194`). Exit 0. No heap event. The witness meter
reports `0 UNRESOLVED of 1`, `probe_red=False`
(`runs/witness.out:1-2`). I did not write `review-of-rank-bound.md`.
I did not postulate. I did not carve. I did not claim `InjCode`
(`src/L/Cardinal.lagda.md:223-228`). I did not claim `Residue`. I
did not claim anything about limits.

P-l (`dev/LESSONS.md:2357`): the type is over `𝒮ʟ`'s `S` and a
generic small carrier. It does not name a transparent stage
presentation.

D-26 (`dev/LESSONS.md:1735`): this task does not well-order a tower
stage. `OrdSWO` is the ordinal's own membership order, rebuilt at
the delivered type. The rank is Acc recursion on that order.

## 1. W3: `fits`, first

**GO.** Typechecked ALONE, with the obligation omitted. Caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process. The
probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-486/Probe486.agdai`).

`fits` (`Probe486.agda:66-67`) is `PairBound.bnd` at generic
`a C : S`. The body of `rank-bound` is omitted. Rank is omitted.
InjCode is omitted.

The brief guessed that `PairBound` was built for `InclGraph`, whose
pairs are `(x , x)` at one set. That is not the site.
`InclGraph` uses `StageBound` with identity pairs
(`src/L/InjChain.lagda.md:584-589`). `PairBound` is the two-set
device, spent by `Comp` at `:327`. The rank's pairs are `(m , rank m)`
across two sets. C-42: the identity-pair site does not transfer.
The two-set arity is the one that matches. That is the finding.

ESTIMATE for W3 was about 8 lines and under 15 seconds. MEASURED:
`fits` is 2 lines inside a 4-line module. The W3-only file
typechecked. Comparables of shape, not of size. Nothing is funded
against the estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`. The W3-only file ended at `fits`.

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 1.68 | 396591104 | `runs/w3-2.out` |
| w3-3 | 1.62 | 396623872 | `runs/w3-3.out` |
| w3-4 | 1.59 | 396640256 | `runs/w3-4.out` |

Median wall **1.62 s**. Peak RSS **396640256** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.75 s and
396623872 bytes, also exit 0. It is not one of the three forced
rechecks.

## 2. The inhabitant `rank-bound`

`rank-bound` is `Probe486.agda:169-194`. Body:

- `w = OrdSWO.w (fst a) oa` (`:178`)
- `pack = boundingOrd ⟪ fst a ⟫ (swo-rank w) (swo-rank-ord w)`
  (`:179`), the pack `[LJ-1.417]` used at `Probe417.agda:83`
- `C = β , isL-ord β oβ` (`:182-183`)
- `module PB = PairBound a C` (`:184`)
- `below` applies `PB.below` at the fibre of `m` and the rank
  packaged by `isL-trans` (`:187-194`)

`swo-rank` and `swo-rank-ord` are rebuilt at `[LJ-1.416]`'s type
(`Probe486.agda:74-108`, from `Probe416.agda:49-78`).
`swo-rank-mono` is not rebuilt. `boundingOrd` does not spend it.

The injection of `swo-into-ord` is not spent. The bound needs
membership of each rank in `β`, which is `pack .snd .snd`.

I did not import `LJ-1-416.Probe416` or `LJ-1-417.Probe417`. I did
not import `L.SquareLawClosed` or `L.StageCardinal`. I did not
postulate.

ESTIMATE for the Agda was about 130 lines, of which the obligation
is about 25. MEASURED: 117 non-blank non-comment lines in the full
probe, of which `rank-bound` is 26 lines (`:169-194`). Comparables
of shape, not of size. Nothing is funded against the estimate.

The witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-486 --brief agents/tasks/LJ-1-486/LJ-1.486.md`) reports
`0 UNRESOLVED of 1`, 1.89 s, `probe_red=False`, exit 0
(`runs/witness.out:1-2`). This worktree has no `.venv`. The meter
ran under the parent venv. I added no dependency.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 1.82 | 386252800 | `runs/full-2.out` |
| full-3 | 2.02 | 368328704 | `runs/full-3.out` |
| full-4 | 1.91 | 386220032 | `runs/full-4.out` |

Median wall **1.91 s**. Peak RSS **386252800** bytes. Exit 0 every
time. No heap event. The first full check `runs/full-1.out` was
2.25 s and 386220032 bytes, also exit 0. It is not one of the
three forced rechecks. The import miss `runs/full-fail-import.out`
was 2.17 s, exit 42, `[NotInScope]` on `sucV`. Not a price. The
import was then `InfinitySet.sucV`. The green file keeps that.

## 3. W2

The rank is generic in the carrier `A` and in `w`. `PairBound` is
generic in two `𝒮ʟ`-sets. Instantiation at the ordinal `a` and the
wrapped `β` is one instance. I did not write a fixed form. No
deadline asked for a fixed form. W2 holds for what was written.
The conflict the clause names did not arise.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

This GO measures ONE site: `PairBound a C` at an ordinal `a` with
`C` the wrapped bounding ordinal of `swo-rank` on `OrdSWO`. It is
not a refutation. C-42's refutation sweep does not fire. The count
of the shape, a rank pair-bound, is still owed as a search:

- `src/`: 0 hits for `rank-bound`. 0 hits for `rank-graph`. 0 hits
  for `rankFo`.
- `PairBound` in `src/` sits at the definition
  (`src/L/InjChain.lagda.md:276`), at a comment (`:192`), and at
  `Comp` (`:327`). Count of this exact instantiation, rank pairs
  at an ordinal, in `src/`: **0**.
- The `Comp` instance is a different site. `[LJ-1.409]` used
  `PairBound a c` as a trim bound
  (`agents/tasks/LJ-1-409/Probe409.agda:61`). That measurement
  does not transfer.

## WHAT THE FOURTH CONJUNCT NOW COSTS

Do not close it. The next brief must be written against this bound.

`InjCode`'s fourth conjunct, `src/L/Cardinal.lagda.md:228`:

    (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

`[LJ-1.482]`'s `from-out` (`Probe482.agda:125-132`) still supplies
`prʟ x y ∈ˢ bnd` and sat of `rankFo`. It does not supply
`fst y ∈ fst b`. A false close that treated pair-in-bound as
`y ∈ b` is `[UnequalTerms]`
(`agents/tasks/LJ-1-482/runs/w3-false-close.out:2-8`).

The bound this task names is `fst (rank-bound a oa)`. Its `C` is
the wrapped `β`. If a later code takes `b = C`, the range clause
asks that the second component of a pair in the graph is a member
of `β`.

`PairBound.below` (`src/L/InjChain.lagda.md:299-300`) is the other
direction: members of `D` and `C` yield a pair in `bnd`. It does
not read a pair in `bnd` back to a member of `C`. That converse is
still not delivered. `[LJ-1.482]` recorded this at
`lj-1.482-report.md:148-151`. Re-measured here: `rank-bound`'s
`below` spends `PB.below` (`Probe486.agda:187`). It does not spend
a converse.

A close of the range clause still needs:

1. The carve `[LJ-1.478]` already has, at this `bnd`.
2. Adequacy of `rankFo` to `swo-rank`, which `[LJ-1.475]` left
   (`lj-1.475-report.md:236-253`): a pair in the graph is a member
   paired with that member's rank.
3. Then `y` is a rank, and `memβ` puts it in `β`, so in `b` if
   `b = C`.

(2) is not this bound. I did not inhabit it. I did not add it as a
hypothesis.

The other three conjuncts still have no supplier in `[LJ-1.478]`'s
readings. The bound unblocks `rank-graph-in`'s `z ∈ˢ bnd` premise
(`Probe478.agda:118-124`). It does not supply uniqueness, totality
of approximating functions, or injectivity at a set `Q`.

## WHAT THE NEXT BRIEF NEEDS

- `fits` typechecks (`Probe486.agda:66-67`). `PairBound a C` is the
  rank's two-set telescope.
- `rank-bound` typechecks (`Probe486.agda:169-194`). The named set
  is `PB.bnd` at `C = (β , isL-ord β oβ)` with `β` from
  `boundingOrd` on the rebuilt rank.
- The carrier is an ordinal: `oa : IsOrd (fst a)` supplies `w` via
  `OrdSWO`. `[LJ-1.478]`'s carve is generic in `a : S`. A bound at
  a STAGE, as 482 named at `lj-1.482-report.md:264-267` (`a` the
  stage, `C` the `β` of `stage-into-bound`), needs `w` from
  `carry-at-generic` (`Probe418.agda:50-51`) and `a` as
  `Lset α` packaged as an `𝒮ʟ`-set. That is not this term. Do not
  transfer this ordinal instance by analogy. Re-measure at the
  stage.
- Do not close the fourth conjunct from `PairBound.below`. Name
  adequacy, or name a converse of `below`, or take `b = C` and
  prove `y` is a rank.
- Do not import a probe. Rebuild, or take as a module hypothesis,
  the rank at `[LJ-1.416]`'s type.
- Do not claim a limit. Do not claim `Residue`. Those questions
  wait on a code, and the code waits on the types in
  `## WHAT A CODE HERE WOULD REACH`, of which item 2 is now a set.

What the statement cost: 117 non-blank non-comment lines, W3 median
1.62 s, full-file median 1.91 s, peak RSS 396640256 bytes. What
the shape resisted: the brief's free `w` and `swo-rank w m` with
`m : S`. What I had to weaken: the membership spelling, and the
fibre of `m`. What I could not close: the fourth conjunct. I did
not try.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:3`
  "**Status: ARCHIVED RECORD. It is never rewritten.** These are the 464 dispatch rows"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether `PairBound a C` holds rank pairs.
- `archive/dev/JOURNAL-archived.md:1229`
  "raw material at all (no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used. That archived journal records the absence of rank
  theory in the retired route. `[LJ-1.416]` filled the rank as DATA.
  `[LJ-1.417]` bounded it by an ordinal. This task filled the pair
  bound of a member with that rank, as a set.
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
  whether `PairBound` reaches the rank.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to
  SELECT a least witness. This task does not select. It names the
  set of pairs of a member and its rank.
- `dev/literature/truncation-and-selection.md:68`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. The rank bound is not that device. Internal's order
  is the well-order side. The bound is a pair-set, not a selection.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the order type of the WHOLE order. This bound
  is the GRAPH of ranks of members, inside `PairBound a β`, not
  that single ordinal.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. `[LJ-1.416]`
  defined the RANK of that order as data. This task put the pairs
  of member and rank into a named set.
- `dev/literature/glossary-review-2026-08.md:1`
  "Glossary review: the 119 pre-protocol entries"
  Declined. Not used. It reviews glossary entries. It does not
  bear on a rank pair-bound.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when each run started.

- W3 first check, `runs/w3-1.out`: 1.75 s real, 396623872 bytes
  RSS, printed `Checking LJ-1-486.Probe486`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-486/Probe486.agdai`:
  1.68 s, 1.62 s, 1.59 s. Median **1.62 s**. Peak RSS
  **396640256** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).
- Import miss, `runs/full-fail-import.out`: 2.17 s real, exit 42,
  `[NotInScope]` on `sucV` at the then-current
  `Probe486.agda:116`. Not a price.
- Full-file first check, `runs/full-1.out`: 2.25 s real,
  386220032 bytes RSS, printed `Checking LJ-1-486.Probe486`,
  exit 0.
- Three forced rechecks after `rm` of the same interface:
  1.82 s, 2.02 s, 1.91 s. Median **1.91 s**. Peak RSS
  **386252800** bytes. Exit 0 every time
  (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`).
- Witness meter, `runs/witness.out`: 1.89 s, `0 UNRESOLVED of 1`,
  `probe_red=False`, exit 0.

Estimate for the Agda was about 130 lines for the whole
obligation. MEASURED 117 non-blank non-comment lines, inhabitant
of `rank-bound` present. Nothing is funded against the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-486/`:

- `lj-1.486-report.md`, this report
- `Probe486.agda`, W3 `fits` then `rank-bound`
- `runs/`, the Agda transcripts named above
