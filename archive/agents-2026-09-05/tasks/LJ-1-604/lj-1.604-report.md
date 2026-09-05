# LJ-1.604 report: is ingredient (iii) the same object as `sq`

## HEAD

head_slot: coder
machine: shared
task: LJ-1.604
obligation: agents/tasks/LJ-1-604/Probe604.agda::third-is-sq
verdict: DELIVERED. The term `third-is-sq` is in the probe and the probe is
GREEN (`runs/final-4.out`, `runs/final-6.out`, `runs/final-7.out`, exit 0,
all three postdating the last edit). The brief allowed two disjuncts, the
equivalence or "the term that shows they are different objects". The
measurement picked the second: **THEY ARE DIFFERENT OBJECTS, AND `sq` IS THE
STRONGER ONE.**

The report was a skeleton before the probe was written and was filled as each
answer landed (C-22). Nothing landed in `src/`. No hole and no postulate is
in the probe. No row puts `step`, `branch` or `stage-card-upper` into a
conversion problem. The scope's `review-of-third-is-sq.md` is NOT written:
that name is the stop path, the obligation is discharged, so no stop is
stated. No commit, no push.

## THE ANSWER IN ONE PARAGRAPH

Ingredient (iii) at a site is ONE FIBER: one binary function on the members
of one ordinal, with its injectivity. `sq` is the PRODUCT of that fiber over
every site of the band `δ ∈ sucV α₀, δ ∉ ω`, and the product carries nothing
else: no coherence between two sites, no uniformity, no definability. The
proof of the product identity is `refl`
(`the-parameter-is-the-product`, `Probe604.agda:160-164`). The parameter gives
the ingredient at every site by application; the ingredient at one site gives
nothing toward the parameter, because the only route back runs through the
whole band. The two do not even share a universe: the fiber is a `Type ℓ`, the
parameter is a `Type (ℓ-suc ℓ)`. The resemblance the brief suspected is the
same shape `[LJ-1.585]` broke: the side conditions and the hidden `∀` are the
difference.

## W3: THE TWO IN ONE FILE, TYPE ONLY

`runs/W3.agda` was written FIRST and typechecked ALONE, as ordered. GREEN:
`runs/w3-1.out` cold at 1.52 s, `runs/w3-2.out` warm at 1.65 s, under the
2-minute cap I set and report. It states the two types, imports `SqParam`
from `[LJ-1.594]`'s green transcription and does not restate it, and carries
the two conversion rows that prove the fiber transcription: `site-gets`
(`runs/W3.agda:50-52`) and `sq-is-product` (`runs/W3.agda:57-61`). The widest
unmeasured term is measured: the two objects coexist in one file at a cost of
1.52 s cold.

## THE TWO OBJECTS

| | ingredient (iii) at one site | `sq`, the module parameter |
|---|---|---|
| type | `Ing3 α` (probe, `Probe604.agda` section 0), which IS the tree's own `sq` type, `src/L/Ordinal/SquareLaw.lagda.md:685-688`, by `refl` (`ing3-is-the-law-sq`, `Probe604.agda:117-118`) | `SqParam α₀`, `[LJ-1.594]`'s checked transcription of `src/L/StageCardinal.lagda.md:17-19` |
| carrier | the members of ONE α fixed by the site (`fst (sq α α∈suc infα)` is the name `[LJ-1.594]`'s table row gives it, `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:42`) | every δ of the band, `δ : V ℓ` |
| arity | one binary package: `⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫` plus injectivity | a `Π` over the band INTO that same package |
| side conditions | the site's own `α ∈ sucV α₀` and `α ∉ ω`, fixed, not quantified (`src/L/StageCardinal.lagda.md:277`) | the same two conditions, per δ, as arguments (`src/L/StageCardinal.lagda.md:17-18`) |
| universe | `Type ℓ` | `Type (ℓ-suc ℓ)` |
| where spent | the class-pred value equation, `B.pair m (cnt m φ) ≡ y` (`src/L/StageCardinal.lagda.md:322`), and `h-inj`'s split, `B.pair-inj` (`:382`) | one use in the whole module: `module B = Bound α oα infα (sq α α∈suc infα)` (`:283`), inside `LimitStep`, reached at every infinite member of the descent |

One correction to the table's source: the site spends BOTH halves of the
fiber. The row's name `fst (sq α α∈suc infα)` names the value half; `h-inj`
splits packed values with `B.pair-inj`, which is `snd` of the same fiber
(`src/L/StageCardinal.lagda.md:71-75`). The probe re-derives it from `snd`
(`pair-inj-from-the-second-half`, `Probe604.agda:125-135`), so the claim is a
term.

## THE TERM

`third-is-sq` (`Probe604.agda:180-186`) carries both directions of the brief's
`↔`, each with the hypothesis it actually needs:

- the forward component applies the parameter at the site;
- the backward component takes the ingredient at EVERY site of the band, and
  by the product identity that hypothesis IS the parameter.

So the type itself shows the difference: no map from the one fiber to the
family is on offer anywhere in it. The two supporting rows are
`family-gives-ingredient` (`:153-156`), the cheap direction, and
`the-parameter-is-the-product` (`:160-164`), `refl`, which is the bridge and
the whole content of the resemblance. A third row ties the fiber to the law
chapter's own name (`ing3-is-the-law-sq`, `:117-118`), and a fourth supplies
the fiber without the parameter at initial ordinals
(`initial-ordinals-have-the-fiber`, `:234-235`, from
`src/L/Ordinal/SquareLaw.lagda.md:960-961`).

This is not a refutation of anything: the target family stays true, `V = L`
gives it (`[LJ-1.594]`, `vl→target`), and no row here touches that. The
nonexistence of a fiber-to-family map is read off the priced converse, in
`[LJ-1.585]`'s discipline: the missing direction's exact price is a term, and
the tree's stock of that price is measured in the next section.

## THE DEMAND: THE MODULE SPENDS THE PRODUCT

Two live predecessors measured this before the brief asked:

- `[LJ-1.116]` (`agents/tasks/LJ-1-116/lj-1.116-report.md`, section 1) read
  the trace: `stage-card-upper` is `∈-induction step`
  (`src/L/StageCardinal.lagda.md:566`); `step` calls `limit-step` (`:562`);
  `limit-step` applies `sq` at its own α (`:283`); the branch at a finite
  member never demands `sq` (`:548`), at ω and at every infinite member it
  descends (`:549-556`). Generic demand: every infinite ordinal δ below α.
- `[LJ-1.117]` (`agents/tasks/LJ-1-117/lj-1.117-report.md`, section 1) landed
  the band: the parameter is stated exactly on `δ ∈ sucV α₀`.

So the four arrivals of the brief sit at two grains, and both grains are
correct at their own site: `[LJ-1.597]`'s value equation
`fst (sq α α∈suc infα) (m , cnt m φ) ≡ y` names the FIBER at one step;
`[LJ-1.594]`'s route 2, "give `L.StageCardinal` a definable pairing instead
of `sq`", names the PRODUCT. `[LJ-1.594]`'s `DefPairing`
(`agents/tasks/LJ-1-594/Probe594.agda:199-210`) states the definability of
ONE fiber and therefore covers exactly one site of route 2's demand.

## WHAT (iii) COSTS IF THEY ARE ONE

They are not one, so the section answers at both grains. At ONE site the
ingredient costs one binary function with its injectivity, and I agree with
`[LJ-1.594]` that it is the smallest of that site's five
(`agents/tasks/LJ-1.594/review-of-pairing-suffices.md:143`): (iv) at the same
site costs the whole injection below it and (v) a coded copy of the syntax.
At MODULE grain "the pairing" costs the product over every infinite ordinal
of the band, and nobody has priced that product as a product. The product
carries no coherence (`the-parameter-is-the-product` is `refl` over a bare
`Π` into a `Σ`), so one uniform supply discharges every fiber at once, and
the tree already holds two such supplies: the honest fiber at ω
(`squareω : sq ω`, `src/L/InjChain.lagda.md:184-185`, machine-checked by
`[LJ-1.116]` section 4) and the fiber at every initial ordinal
(`via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961`). The hole is
the non-initial band: `[LJ-1.107]` measured that the truncated witness cannot
give an honest fiber there, and `[LJ-1.114]` measured that threading
truncation into `Upper` walls (`archive/dev/LJ-dispatch-index.md:183`, `:190`).
The truncated square law holds at every infinite ordinal with no choice
(`[LJ-1.111]`, `archive/dev/LJ-dispatch-index.md:187`), and it does not
untruncated into the family, for the law's own reason: a data payload does
not come out of `leastOf`
(`dev/literature/truncation-and-selection.md:146-148`).

**WHICH IS STRONGER: `sq`, strictly.** A later brief that targets "the
pairing" must name its grain. At the fiber grain, one definable pairing at
one α discharges `[LJ-1.597]`'s value equation at that α and nothing else. At
the product grain, the target is `SqParam α₀`, and the campaign's known
supplies (ω, initial ordinals) leave the non-initial band open.

## PREMISES CHECKED

- Premise 3, "`sq` is a pairing ... and nothing else", is FALSE as stated and
  the falsity is the finding: `src/L/StageCardinal.lagda.md:17-19` is a `Π`
  over the band into the pairing package, with two side conditions per site.
  The brief's own warning was right to check the side conditions first.
- Premise 4's basis is NOT IN THIS TREE: `agents/tasks/LJ-1-572/` does not
  exist, `git ls-files` returns nothing for it, and `find` outside `_build`
  finds nothing. The `[LJ-1.572]` arrival is therefore carried on this
  report's other three verifications and on the brief's word.
- Premises 1 and 2 hold with a line offset: "(iii) is the hypothesis" is at
  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md:82` (brief said `:79`,
  a section head), and "the smallest of the five" is at `:143` (brief said
  `:138`, the list head).
- Premises 5, 6, 7, 8, 9, 10 verified at their cited lines:
  `src/L/StageCardinal.lagda.md:283`;
  `agents/tasks/LJ-1-585/Probe585.agda:163`;
  `agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40`;
  `agents/tasks/LJ-1-601/lj-1.601-report.md:1`;
  `agents/tasks/LJ-1-568/Probe568.agda:377`;
  `src/L/Axioms/Full.lagda.md:144`.

## THE FLOOR, THE CAPS, THE RUN LEDGER

The caliber on every run is the program's `-A64m -I0 -M2g`, read from the pane
and recorded inside each `.out` file. I did not set `GHCRTS` at any point. One
Agda process at a time. Caps, which I set and report: 120 s for every W3 run,
300 s for the floor and every final run. No run reached a cap. No run hit the
heap cap.

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, cold | 0 | 1.52 s |
| `runs/w3-2.out` | W3 alone, warm | 0 | 1.65 s |
| `runs/floor-1.out` | my hole-syntax error, no measurement | 42 | 1.85 s |
| `runs/floor-2.out` | the floor: obligation body as the only hole, every other row green | 42 | 2.25 s |
| `runs/final-1.out` | obligation filled, cold | 0 | 1.66 s |
| `runs/final-2.out` | warm | 0 | 1.53 s |
| `runs/final-3.out` | warm | 0 | 1.55 s |
| `runs/w3-3.out` | W3 after its citation fix | 0 | 1.96 s |
| `runs/final-4.out` | probe after its citation fix, cold | 0 | 1.77 s |
| `runs/final-5.out` | signal death, no Agda diagnostics | 1 | 0.48 s |
| `runs/final-6.out` | identical input, next process | 0 | 1.74 s |
| `runs/final-7.out` | warm | 0 | 1.52 s |

The floor is the frame: 2.25 s with the obligation holed, 1.66 s delivered
cold, so the obligation's assembly costs nothing and the frame is the whole
price. `floor-1` is my error (`{}` is not a hole in Agda 2.8; `{! !}` is),
one edit fixed it. `final-5` is a machine transient in `[LJ-1.601]`'s
recorded class: `time: command terminated abnormally`, `time: signal:
Invalid argument`, at 0.48 s with no scope error, no unsolved meta and no RTS
heap message, on a machine at load 4.43 with 422 MB of swap free. Nothing was
restructured for it. The identical input passed as the next process
(`final-6`), and the delivered content has three green runs postdating the
last edit (`final-4`, `final-6`, `final-7`).

Sizes: the probe is 268 lines of which about 60 are code, and the obligation
is 7 (`Probe604.agda:180-186`); W3 is 61 lines. The brief estimated about 130
probe lines with about 30 for the obligation; the comment blocks are the
excess, and comparables are of SHAPE only.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean; `lint-prose.py --check` exit 0
on this report; `grep` for `postulate`, `TERMINATING` and `{!` over the probe
and W3 returns nothing; no em dash in any file of this scope. `make check`
not run: it is the commit gate and nothing here commits.

## WHAT THE NEXT BRIEF NEEDS

1. **Name the grain.** "The pairing" now has two measured meanings. The
   bridge is `the-parameter-is-the-product` (`Probe604.agda:160-164`), and a
   brief that targets the parameter should say PRODUCT, a brief that targets
   one step's value equation should say FIBER AT α.
2. **The naming hazard is real and now recorded:** the tree has two objects
   called `sq`, the parameter (`src/L/StageCardinal.lagda.md:17-19`) and the
   fiber type (`src/L/Ordinal/SquareLaw.lagda.md:685-688`). They are related
   by product and application and they are not one object. The probe's
   `Ing3` is the fiber under a third name, chosen to keep the two apart.
3. **A definable pairing at ONE site is not a route to the parameter.**
   `[LJ-1.594]`'s `DefPairing` is one fiber's definability. Route 2 at the
   product grain needs the non-initial band, where the tree's honest supplies
   stop (`[LJ-1.107]`, `[LJ-1.114]`).
4. **What the shape resisted: nothing.** No wall, no restructure, one
   syntax error of mine, one machine transient. What I had to weaken:
   nothing. The statement was taken whole and the second disjunct was
   inhabited whole.

## W2 AND W4

**W2.** The probe is stated once at the chapter's own generic telescope
`{ℓ} lem α₀ oα₀ sq`, and every row is at a generic site or over the whole
band; any consumer of either trophy instantiates the same rows. Nothing
landed in `src/`, so no fixed-form chapter was written and no deadline
conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is untouched
and nothing moved to `archive/`. The ideal form of this measurement written
fresh today is the probe as it stands; I did not pay for a worse shape first
and then compare.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:192`: "| LJ-1.116 | At which alpha does
  Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is every
  infinite ordinal below alpha; the site is omega. Init is false at omega and
  at successors |". Also read and used: `:183` (`[LJ-1.107]`, non-initial
  honest `sq` unconstructible), `:187` (`[LJ-1.111]`, truncated chain green),
  `:190` (`[LJ-1.114]`, truncation threading walls), `:193` (`[LJ-1.117]`,
  the band restriction). These rows are the recorded demand-side half of this
  task's answer.
- **`archive/dev/JOURNAL.md` DECLINED.** `archive/dev/JOURNAL.md:1`: "#
  ARCHIVED 2026-08-20". A retired journal; the demand measurements this task
  used live in the live task directories LJ-1-116 and LJ-1-117, read whole.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired
  route". The retired route's journal does not measure the fiber or the band.
- **`dev/ARCHIVE.md` DECLINED.** `dev/ARCHIVE.md:1`: "# ARCHIVE.md: the
  archive registry". This task retires no module, so no row was written and
  none was consulted beyond the first line.
- **`archive/dev/DD-archived.md` DECLINED.**
  `archive/dev/DD-archived.md:1`: "# THE `DD` RULING SERIES, archived in full
  2026-08-18". The rulings that bind this task were in the standing
  instructions; no decision history was needed.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:413`: "|L_α| = |α| for α ≥ ω (`dev2.txt:117`,
  `dev2.txt:200-240`) is consumed at". The classical theorem consumes the
  size equation at EVERY infinite level, which is the product grain; the
  classical source agrees with the module's demand set as `[LJ-1.116]` read
  it.
- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:146`: "**The constraint the
  route carries: `P` must be `hProp`-valued.** So `leastOf`". With `:147-148`
  this is the law behind why the truncated square law at every infinite
  ordinal does not untruncated into the parameter's family.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** This task fixes
  no Levy grade and no level slot; the pairing type at `src/L/StageCardinal
  .lagda.md:17-19` carries none.
- **`dev/literature/geology.md` DECLINED.** No layering question arose; the
  measurement is a type comparison inside one chapter's parameter.
- **`dev/literature/terms-2026-08.md` DECLINED.** A terminology dossier; this
  return adds no glossary entry, per the Boundary's two-dispatch rule.
