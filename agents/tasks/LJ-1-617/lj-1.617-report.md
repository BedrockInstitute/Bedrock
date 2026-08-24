# LJ-1.617 report: does the bill ever need the pairing at module grain

## HEAD

head_slot: coder
machine: shared
task: LJ-1.617
obligation: agents/tasks/LJ-1-617/Probe617.agda::site-grain-suffices
verdict: DELIVERED, GO.  The term `site-grain-suffices` is in the probe
(`Probe617.agda:500-502`) and the probe is GREEN: `runs/final-1.out`
cold at 2.20 s, `runs/final-2.out` warm at 1.05 s and
`runs/final-3.out` warm at 0.96 s, all exit 0, all postdating the last
edit.  The hypothesis is ingredient (iii) at the SITE: one binary
function at one alpha, with its injectivity.  The conclusion is the
exact type of `code-inj` (`src/L/BoundedSubset.lagda.md:1512-1513`),
the bill's only consumer of the pairing's proof-only demand.  Nothing
landed in `src/`.  The probe carries no hole and no postulate.  The
scope's `review-of-site-grain.md` is NOT written: that name is the stop
path, the obligation is discharged, so no stop is stated.  No commit,
no push.  `git status` shows only `agents/tasks/LJ-1-617/` as new.

The brief asked the coder to measure, not to agree.  The measurement
agrees with the brief.  The bill pays in the site grain.  The circle at
module grain is real but it binds a demand that nothing in the tree
makes.

This report was a skeleton before the probe was written and was filled
as each answer landed (C-22).

## W3: THE COUNT OF SPEND SITES, MEASURED FIRST

Two greps, before any Agda, under the two-minute cap the brief set.  No
counting command carries `head`; every number below is from `grep -c`
or `wc -l`.

- Applications of the PRODUCT `sq` at an ordinal in `src/`: exactly
  TWO.  `grep -rnE "\bsq α " src/` returns five lines.  Three of them
  are the FIBER type of `L.Ordinal.SquareLaw`, which is a different
  `sq` (the naming hazard `[LJ-1.604]` recorded).  Two are the product
  applied: `src/L/StageCardinal.lagda.md:283` and
  `src/L/BoundedSubset.lagda.md:1410`.
- Instantiations of `L.StageCardinal` in `src/`: exactly ONE
  (`grep -rn "= L.StageCardinal" src/ | wc -l` gives 1), at
  `src/L/BoundedSubset.lagda.md:1397`.
- The token `SqParam` in `src/`: ZERO files.
- The token `SqParam` in the live probes: ten files.  Every one carries
  it as the ABSTRACT module parameter of a probe (LJ-1-594 definition
  and use, LJ-1-604, LJ-1-605, LJ-1-613 and 613's four floor files).
  No probe applies it at a concrete ordinal.
- Uses of `stage-card-upper` at an ordinal in `src/`: five lines total,
  ONE of them a use: `src/L/BoundedSubset.lagda.md:1513`, at
  `γ = α`, the enclosing module's own alpha.

## EVERY SPEND SITE

Each row is the product `sq : (δ : S) -> δ in sucV α -> inf δ ->
fiber at δ` being bound, passed, or applied.  The last column is the
ordinal the site spends the pairing AT.

| file:line | what happens | the alpha it spends at |
|---|---|---|
| `src/L/StageCardinal.lagda.md:17` | the product is BOUND, module telescope, base `α₀` | none yet |
| `src/L/StageCardinal.lagda.md:283` | the product is APPLIED, inside `LimitStep`: `module B = Bound α oα infα (sq α α∈suc infα)` | the step's own alpha.  `stage-card-upper = ∈-induction step` (`:566`) sends `step` (`:562`) into `limit-step` at every member of the descent, so this alpha RANGES over every infinite ordinal of the band below the target |
| `src/L/BoundedSubset.lagda.md:1388` | the product is BOUND, `BoundedSubsetAt` telescope; an inline copy of `SqParam α` | none yet |
| `src/L/BoundedSubset.lagda.md:1397` | the product is PASSED wholesale: `module SC = L.StageCardinal {ℓ} lem α ordα sq`; the sole instantiation in `src/` | none yet |
| `src/L/BoundedSubset.lagda.md:1410` | the product is APPLIED: `SC.Bound α ordα α∉ω (sq α (self∈sucV α) α∉ω)` | ONE alpha, the module's own |
| `src/L/BoundedSubset.lagda.md:1513` | the product's proof-only demand is consumed at one point: `code-inj = comp-inj absorbs (stage-card-upper α ordα (self∈sucV α) α∉ω)` | ONE alpha, the same as `:1410` |
| `src/L/StageBound.lagda.md:28-31` | `SqFam α`, a copy of the product type | none yet |
| `src/L/StageBound.lagda.md:67` and `:75` | the product is BOUND and PASSED into `Devlin55.BoundedSubsetAt`; this is `:1397` reached again | none yet |
| `src/L/StageBound.lagda.md:100` and `:126-131` | the product as a HYPOTHESIS of the recorded residue (`SqCollect` codomain, `bounded-from-data` domain) | the band below the module alpha |

Fiber-type consumers in `src/`, for completeness, since the token `sq`
names both objects: `SquareLaw` supplies the fiber at the initial
ordinals (`:953`, `:960`), `InjChain:184` supplies it at omega,
`SquareLawClosed` carries the truncated family (`:325-328`), and
`StageBound:17` imports it.  None of these spends the product.

COUNT: the product is applied at an ordinal at exactly TWO lines of
`src/`.  One, `BoundedSubset:1410`, spends it at ONE fixed alpha.  The
other, `StageCardinal:283`, spends it at a RANGING alpha because the
proof of `stage-card-upper` is an `∈-induction`, not because any
consumer asked for a ranging value: the sole consumer of that induction
reads the result at `γ = α` and nowhere else (`BoundedSubset:1513`).

## WHICH GRAIN THE BILL PAYS IN

The bill pays in the SITE grain, and the circle at module grain does
not bind it.  Four measurements carry this, and each is a term or a
count in this return.  First, the count above: only two lines of `src/`
apply the product at an ordinal, and only one of them fixes a concrete
alpha, the module's own at `BoundedSubset:1410`.  Second, the band spend
at `StageCardinal:283` is PROOF-INTERNAL: it exists because `Upper`'s
predicate `P` fixes the injection's TARGET at each step's own ordinal
(`src/L/StageCardinal.lagda.md:530-532`), which forces each step to
count its formulas at that ordinal and hence to pair there.  The probe
replaces that predicate with `Q γ = ... ↪ ⟪ α ⟫`, the same induction
with the target FIXED at the site alpha, and the pairing is then
consumed at the site only.  Third, the probe INHABITS the discharge:
`site-grain-suffices` takes the site fiber plus `absorbs` and lands
`code-inj`'s exact type, and every other `SC.` use inside
`BoundedSubsetAt` is sq-free in content (`OrdSWO` at `:1518` and
`:1528`, `stage-card-lower` at `:1581`; the probe rebuilds the ordinal
well-order from importable pieces and never touches the product).
Fourth, the orientation row `family-gives-site` is the tree's own
application at `:1410`: the product gives the site fiber, so the site
hypothesis is strictly the weaker one, and the weaker one suffices.
The circle stands as measured, `[LJ-1.605]` and `[LJ-1.607]` are not
refuted: `SqParam α₀` is still the stronger object and any future
consumer that wants stage cardinality at MANY ordinals through one
supply would still face it.  No such consumer exists in this tree
today.  The bill's whole demand on ingredient (iii) is one fiber at one
alpha.

## WHAT THE PROBE BUILDS

`Probe617.agda`, 502 lines, seven sections, all inside the module
telescope `(lem, α, oα, α∉ω, iii)` where `iii` states the site fiber
inline.

- Section 2, `SiteBound` (`:126-245`): the tree's own `Bound`
  (`src/L/StageCardinal.lagda.md:64-219`) copied verbatim at a generic
  carrier.  The copy is proof-text faithful; the module name differs.
  It exists only because the original sits inside the `sq` telescope,
  and `Bound` itself never uses the product: it takes ONE pairing at
  its own beta.
- Section 3, `SiteOrdSWO` (`:254-297`): the tree's own `OrdSWO`
  (`src/L/StageCardinal.lagda.md:228-271`) copied verbatim at a generic
  carrier, for the same reason.  Its content uses no `sq`.
- Section 4, `SiteStep` (`:313-455`): the tree's own `LimitStep`
  (`src/L/StageCardinal.lagda.md:277-394`) with ONE change of shape.
  The counting and packing carrier is the fixed site alpha, not the
  step's own.  The member index `m` lives in `⟪ γ ⟫` and is embedded
  into `⟪ α ⟫` by `emb` before packing.  The composed hypothesis is
  supplied per member by the `∈-induction`, not by `branch`.
- Section 5 (`:457-477`): the predicate `Q`, the step, and
  `site-stage-card = ∈-induction step`, plus `site-leg-α`, the bill's
  own reading at `γ = α`.
- Section 6 (`:479-487`): `family-gives-site`, the orientation row.
- Section 7 (`:489-502`): the obligation, three lines, one composition
  with `comp-inj`.

Two consequences of the restructure, both measured by green rows: the
probe imports NO `L.Choice.Finite` (the tree's omega base `FinInj` and
`Tally` exist to inject finite stages into their own ordinal; with the
target fixed at alpha the one step covers them), and `Q γ` carries NO
per-step infinity hypothesis, only `IsOrd γ` and `γ ∈ sucV α`.

## PREMISES CHECKED

- Premise 1 HOLDS: one instantiation, count 1, at
  `src/L/BoundedSubset.lagda.md:1397`.
- Premise 2 HOLDS: the Π-bound at `:1388`.
- Premise 3 HOLDS: the spend at `:1410` at one alpha.
- Premise 4 HOLDS: `absorbs` at `:1392`.
- Premise 5 HOLDS: `[LJ-1.604]` priced the two grains and found
  different objects, the product strictly stronger; the
  smallest-of-the-five claim is verified at
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:143`.
- Premise 6 HOLDS WITH AN OFFSET: the cited `:90` is the section head
  `## THE RULING FOR THE OWNER`; the NO-GO text it heads is at
  `agents/tasks/LJ-1-605/review-of-uniform-pairing.md:91-93`.
- Premise 7 HAS A DEFECT IN ITS BASIS: `agents/tasks/LJ-1-607/` does
  not exist in THIS worktree, and `git log --all` over that path is
  empty, so the cited `lj-1.607-report.md:173` is not reachable here.
  The deliverables exist UNTRACKED in the main tree at
  `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-607/`; I read
  `lj-1.607-report.md:173-184` there (section `IS THE CIRCLE CLOSED`)
  and `Probe607.agda:228` (`the-circle : Untruncation → SqParam α₀`).
  This task does not rest on that type, so the defect is recorded and
  the task proceeds.  The next dispatch into this worktree that DOES
  need `[LJ-1.607]` will need the owner to commit it.
- Premise 8 HOLDS: `agents/tasks/LJ-1-588/Probe588.agda:424` is
  `gch-from-restricted-row4 :`.
- Premise 9 HOLDS WITH A MISATTRIBUTION: `Probe585.agda:163` holds
  `Row4Restricted`, the restricted row's TYPE.  The width-principle
  SENTENCE the brief quotes is recorded at
  `agents/tasks/LJ-1-588/Probe588.agda:89-91`, "a hypothesis about it
  may be stated at every α₀ without being stated more widely than the
  function".  Both files verify the substance.
- Premise 10 HOLDS: `agents/tasks/LJ-1-613/Probe613.agda:137`.
- Premises 11 and 12 HOLD at `AGENTS.md:45` and `AGENTS.md:43`.
- Premise 13 HOLDS WITH AN OFFSET: the make-check bullet head is at
  `AGENTS.md:75`; `:74` is the tail of the previous bullet.

## THE FLOOR, THE CAPS, THE RUN LEDGER

The caliber on every run is the program's `-A64m -I0 -M2g`, read from
the pane and recorded inside each `.out` file.  I did not set `GHCRTS`
at any point.  One Agda process at a time.  Caps, which I set and
report: two minutes for the W3 greps (they took seconds), 300 s for
every Agda run.  No run reached a cap.  No run hit the heap cap.  The
floor was measured BEFORE the proof, per the owner's ruling of
2026-08-23: the hard row `h-inj` holed, everything else present and
green, 1.70 s.  The frame is the whole price.

| run | what | exit | price |
|---|---|---|---|
| `runs/floor-1.out` | my structure error: a definition before the module header broke name inference | 42 | 0.29 s |
| `runs/floor-2.out` | my import error: `⟪_⟫↪` not imported | 42 | 1.41 s |
| `runs/floor-3.out` | my import error: `PathP` not imported | 42 | 1.10 s |
| `runs/floor-4.out` | my transcription slip in `e-pair` (a dropped comma, type line) | 42 | 1.27 s |
| `runs/floor-5.out` | the same slip in the value line | 42 | 1.57 s |
| `runs/floor-6.out` | THE FLOOR: `h-inj` holed, exactly one unsolved meta at `:412`, no other diagnostic | 42 | 1.70 s |
| `runs/final-1.out` | delivered, cold | 0 | 2.20 s |
| `runs/final-2.out` | warm | 0 | 1.05 s |
| `runs/final-3.out` | warm | 0 | 0.96 s |

Sizes: the probe is 502 lines, of which 112 are full-line comments.
The two verbatim copies cost about 164 lines (`SiteBound` about 120,
`SiteOrdSWO` about 44).  The new mathematics, `SiteStep`, is about 143
lines.  The obligation term is 3 lines.  The brief estimated about 140
probe lines with about 35 for the obligation; the estimate priced the
new mathematics roughly right and did not price the copies, which exist
only because `Bound` and `OrdSWO` sit behind the product telescope in
`src/`.  Comparables are of SHAPE only.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean; `lint-prose.py --check`
exit 0 on this report; `grep` for `postulate`, `TERMINATING` and `{!`
over the probe returns nothing at code level; no em dash in any file of
this scope.  `make check` not run: it is the commit gate and nothing
here commits.  The ratio bar cannot fire: the write scope carries no
agda fence, so the in-fence count is 0.

## WHAT THE NEXT BRIEF NEEDS

1. **The demand side is settled by a term.**  Any brief that funds a
   supply for ingredient (iii) at this bill should name the FIBER AT
   ALPHA, not the product.  `[LJ-1.618]`'s site-level build is the
   right shape for exactly this reason: one definable pairing at one
   alpha would close the bill's fifth ingredient outright.
2. **The circle questions survive, narrowed.**  `SqParam α₀` is still
   the stronger object and the untruncation route to it is still walled
   by `[LJ-1.605]` and `[LJ-1.607]`.  What this task removes is the
   bill's NEED for that object.  If a later consumer genuinely wants
   stage cardinality at many ordinals from one supply, the circle
   becomes live again; none exists today.
3. **The ideal W2 form is now on record.**  `Bound` and `OrdSWO` are
   site-grain in shape and sit behind a product-grain telescope for no
   reason their own text uses.  A later `src/` pass that lifts them out
   of `L.StageCardinal`'s telescope deletes both copies of this probe's
   sections 2 and 3, and `StageBound`'s `SqFam` interfaces reduce to
   the site grain at the same time.  That pass is a `src/` change and
   this brief forbade it.
4. **What the shape resisted: nothing.**  One induction predicate
   change, no wall, no restructure.  The `h-inj` adaptation (the `emb`
   split) typechecked on the first fill.  What I had to weaken:
   nothing; the statement was taken whole, and the induction hypothesis
   came out STRONGER than the tree's (no per-step infinity).  What is
   not closed: the probe builds no pairing, per the brief, and lands
   nothing in `src/`, per the brief.

## W2 AND W4

**W2.**  The probe writes the mathematics once at generic carriers
(`SiteBound β`, `SiteOrdSWO β`) and instantiates both at the site, so
the same rows serve any future site.  The statement is made at the
chapter's own generic telescope `(lem, α, oα, α∉ω, iii)`.  Nothing
landed in `src/`, so no fixed-form chapter was written and no deadline
conflict arose.  The copies exist because the tree's own generic
carriers are trapped behind the product telescope; item 3 above names
the cure.

**W4.**  No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`.  The ideal form of this
measurement written fresh today is the probe as it stands; I did not
pay for a worse shape first and then compare.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:192`: "| LJ-1.116 | At which alpha
  does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is
  every infinite ordinal below alpha; the site is omega. Init is false
  at omega and at successors |".  This row is the recorded demand-side
  half of the W3 count, and its "generic demand" clause is exactly what
  this task re-measured as PROOF-INTERNAL rather than demanded.  Also
  read and used: `:183` (`[LJ-1.107]`, non-initial honest `sq`
  unconstructible), `:187` (`[LJ-1.111]`, truncated chain green), `:190`
  (`[LJ-1.114]`, truncation threading walls), `:193` (`[LJ-1.117]`, the
  band restriction landed).
- **`archive/dev/JOURNAL.md` DECLINED.**  `archive/dev/JOURNAL.md:1`:
  "# ARCHIVED 2026-08-20".  A retired journal; the demand measurements
  this task used live in the live task directories and the dispatch
  index above.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired
  route".  The retired route's journal does not measure the fiber or
  the band.
- **`archive/dev/DD-archived.md` DECLINED.**
  `archive/dev/DD-archived.md:1`: "# THE `DD` RULING SERIES, archived
  in full 2026-08-18".  The rulings that bind this task were in the
  standing instructions; no decision history was needed.
- **`archive/dev/DECISIONS-archived.md` DECLINED.**
  `archive/dev/DECISIONS-archived.md:1`: "# Archived decisions: the D
  series".  Same reason as `DD-archived.md`.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:413`: "|L_α| = |α| for α ≥ ω (`dev2.txt:117`,
  `dev2.txt:200-240`) is consumed at".  The classical theorem consumes
  the size equation at EVERY infinite level, which is the product
  grain; the classical PROOF therefore walks the band, the same shape
  as `Upper`'s induction.  This task's finding is the complementary
  one: a SINGLE reading of that equation, which is all the bill takes,
  is payable at the site grain, by the probe's term.
- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:146`: "**The constraint
  the route carries: `P` must be `hProp`-valued.** So `leastOf`".  This
  is why the probe KEEPS `leastOf` over a rebuilt ordinal well-order
  instead of extracting the packed witness: the witness Σ is data, not
  a prop, and the canonical selection with its membership proof is what
  makes `h` a function at all.  The probe's `SiteStep` follows the
  tree's own selection, at the site grain.
- **`dev/literature/digest.md` DECLINED.**  `dev/literature/digest.md:1`:
  "# Digest: the orthodox form of the rud route, pinned from the
  collected literature".  No rud-route question arose; the measurement
  is inside one chapter's parameter grain.
- **`dev/literature/geology.md` DECLINED.**
  `dev/literature/geology.md:1`: "# Geology dossier: set-theoretic
  geology sources and the five questions".  No layering question arose.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.**
  `dev/literature/level-formula-slot-roles.md:1`: "# The level-hood
  formula: arity, what it binds, what stays free".  This task fixes no
  Levy grade and no level slot; the fiber type at the site carries
  none.
