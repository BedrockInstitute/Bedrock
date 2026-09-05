# LJ-1.605 report: one uniform pairing, because the product carries no coherence

## HEAD

head_slot: coder
machine: shared
task: LJ-1.605
obligation: agents/tasks/LJ-1-605/Probe605.agda::uniform-pairing
verdict: NO-GO. The NO-GO is a ruling: the uniform supply IS the square
law at the band, by a `refl` identity of types, and the campaign has
forbidden the dispatch that would build it. The statement is at
`agents/tasks/LJ-1-605/review-of-uniform-pairing.md`.

The report was a plan before the Agda and was filled as each answer
landed (C-22). Nothing landed in `src/`. No hole and no postulate is in
the probe. No row puts `step`, `branch` or `stage-card-upper` into a
conversion problem (`[LJ-1.584]`). No commit, no push.

## THE ANSWER IN ONE PARAGRAPH

The brief's premise holds and it is the trap: because the product
carries no coherence, the obligation is ONE construction applied
fiberwise, and that construction, at the module grain, is the square
law at every infinite ordinal of the band. The no-coherence identity is
`refl` (`no-coherence-at-this-site`, `Probe605.agda:84-88`, re-proving
`[LJ-1.604]`'s measurement at its own site), so a term of `SqParam α₀`
is definitionally a family of untruncated pairings at every site of the
band, and the fiber is the law chapter's `sq` itself. The tree holds
three supplies: untruncated at ω (`squareω`), untruncated at the
initial ordinals (`via-col-square`), and truncated at the whole band
(`sq-trunc-closed`), all re-ascribed at the band fiber in
`runs/W3.agda`. The missing direction, from the truncated band supply
to the obligation, is named as a type (`missing-direction-type`,
`Probe605.agda:177-181`) and the tree holds no term of it: the payload
is data, the threading of the truncation into the live consumer is the
wall of `[LJ-1.114]`, the square law reduces to B9 at
`[LJ-1.593]`, and B9 is NO-GO at `[LJ-1.533]`. `[LJ-1.593]` forbids a
fourth square-law dispatch, and building the uniform pairing would be
exactly that. The brief ordered: that NO-GO goes to the mathematician
as a ruling, not to a fifth attempt.

## W3: DOES THE TREE HAVE AN ORDINAL PAIRING

Ordered FIRST, by grep, before any file was written. The grep was
`grep -rn "× ⟪\|→ ⟪ δ ⟫" src/L/` with the square and pairing keywords,
under a two-minute cap, and it found FOUR objects with the square
shape. Three are supplies and one is a consumer:

| object | what it is | home |
|---|---|---|
| `squareω : sq ω` | the honest pairing at ω, order route, zero arithmetic | `src/L/InjChain.lagda.md:184-185` |
| `via-col-square : (δ : S) → Init δ → sq δ` | untruncated at the initial ordinals, only | `src/L/Ordinal/SquareLaw.lagda.md:960-961` |
| `sq-trunc-closed` | TRUNCATED at the whole band, an `∈-induction` | `src/L/SquareLawClosed.lagda.md:325-328` |
| the `sq` parameter of `BoundedSubsetAt` | a module PARAMETER, a consumer of a supply | `src/L/BoundedSubset.lagda.md:1386-1390` |

So the tree has ordinal pairings, but at restricted sites and, at the
band grain, only truncated. There is no uniform untruncated supply,
which is the object this brief asked about. `runs/W3.agda` re-ascribes
the three supplies at the band fiber, TYPE ONLY (rows `fiber-identity`,
`supply-ω`, `supply-init`, `supply-band-truncated`), and it
typechecked ALONE, GREEN, `runs/w3-1.out` 6.87 s cold and
`runs/w3-2.out` 1.81 s warm, cap 120 s, before `Probe605.agda` was
written.

## THE NO-COHERENCE CHECK

**CONFIRMED, at `file:line`.** The brief's D-10 order was to re-check
`[LJ-1.604]`'s claim that `the-parameter-is-the-product` is `refl`
over a bare `Π` into a `Σ`. It is: the row is at
`agents/tasks/LJ-1-604/Probe604.agda:160-164`, its body is `refl`
(`:164`), and its statement is the identity of `SqParam α₀` with the
bare product over the band of the fiber, a product with no coherence
between two sites and no uniformity. A measured cure does not transfer
by analogy, so this probe re-proved the row at its own site as a term
of its own: `no-coherence-at-this-site`
(`agents/tasks/LJ-1-605/Probe605.agda:84-88`), again `refl`, with the
fiber named by the law chapter's own `sq`
(`src/L/Ordinal/SquareLaw.lagda.md:685-688`), which is definitionally
the same fiber as the one at
`src/L/StageCardinal.lagda.md:17-19`. The shape of the brief stands:
one uniform supply, if it existed, would discharge every fiber at
once. The measurement that follows prices the supply itself.

## THE GAP

The tree's stock at the band, in `runs/W3.agda`:

- untruncated at ω: one site, `supply-ω`;
- untruncated at the initial ordinals: the sites with `Init δ`,
  `supply-init`; the chapter's prose states the restriction, the
  extraction wall, at `src/L/Ordinal/SquareLaw.lagda.md:14-17`;
- truncated at every site of the band: `supply-band-truncated`, with
  the truncation in the type.

The sites the untruncated stock leaves open are exactly the non-initial
ordinals of the band. The measurements that the tree holds nothing
untruncated there:

- `[LJ-1.107]`, PARTIAL, initial ordinals only; the non-initial case
  needs an injection the truncated least-of witness cannot give
  (`archive/dev/LJ-dispatch-index.md:183`);
- `[LJ-1.111]`, the truncated square law holds at every infinite
  ordinal, no choice, and the cheap cure is NO
  (`archive/dev/LJ-dispatch-index.md:187`): "Truncated sq holds at
  EVERY infinite ordinal, no choice. The cheap cure is NO; threading
  costs about 350 lines";
- `[LJ-1.114]`, WALL, route level: the live consumer needs ONE honest
  injection and two truncation eliminations collide; reverted; the
  cause is proved (`archive/dev/LJ-dispatch-index.md:190`).

And the type-level law behind all three: the payload a pairing is,
data, does not come out of a truncated selection
(`dev/literature/truncation-and-selection.md:146-148`), and the exact
necessary-and-sufficient criterion for lifting the truncation is the
`splitSup` form, which is a choice principle over a family, not a
construction the tree holds (same file, section 2.4).

The reduction side: the square law at the campaign's own spelling
reduces to B9, one way only (`square-from-b9`,
`agents/tasks/LJ-1-593/Probe593.agda:532-533`); B9, `StageCountedCoded`
(`agents/tasks/LJ-1-564/Probe564.agda:127-130`), is NO-GO at
`[LJ-1.533]`, whose review carries the generator argument: an
L-element set is produced by exactly two generators, separation and
replacement, and nothing codes an arbitrary ambient injection
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:107-111`: the
only two generators of an L-element set are `hasSeparationL` and
`hasReplacementL`, and both take a `Formula` in their type).

The funding side: `agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`
states, "DO NOT FUND THE SQUARE LAW AGAIN. A fourth dispatch on this
object buys nothing that is not in this file."

## WHAT THE ROUTE NOW WANTS

Of `[LJ-1.594]`'s five ingredients of `class-pred`
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:38-44`), the
count after this task. This task discharged NOTHING, so the count is
the predecessor count plus one measurement:

| ingredient | status | paid by |
|---|---|---|
| (i) `D`, the definable power set | PAID, internal | `[LJ-1.594]`, `D-at-the-site`, `Probe594.agda:227-234` |
| (ii) the least-element selection | PAID, internal | `[LJ-1.594]`, `h-is-leastOf`, `Probe594.agda:305-317` |
| (iii) the pairing | UNPAID. Still the hypothesis. This task measured it at the product grain: it IS the square law at the band, the tree holds it untruncated at ω and at the initial ordinals and truncated at the band, and the dispatch that would build the rest is forbidden at `[LJ-1.593]` with B9 NO-GO behind it at `[LJ-1.533]` | `[LJ-1.594]` names it; `[LJ-1.605]` prices it and stops |
| (iv) `ih m`, the injection at the stage below | PAID in PART. The finite base has a formula: the graph of `finite-stage-inj` (`src/L/StageCardinal.lagda.md:485`) is definable in the internalization shape, `finite-base-measured` (`[LJ-1.601]`, GO). The limit and induction part is not paid: `[LJ-1.594]` measured the target as the induction hypothesis itself, one stage down | `[LJ-1.601]` for the finite base; the rest remains |
| (v) the meta syntax the existential ranges over | PAID at this carrier: `keyS` at `A := LsetS δ oδ`, `key-at-stage` (`[LJ-1.600]`, GO, `Probe600.agda:129-130`) | `[LJ-1.600]` |

Count: three paid whole, one paid in part, one unpaid. No discharge is
read into anything not inhabited: this task wrote no term of the
obligation, and the row it does write, `untruncated-buys-truncated`
(`Probe605.agda:157-161`), is the inhabited direction only, from a
hypothetical supply to the truncated supply it would imply.

## D-10: THE TARGET'S TRUTH

The target is not false. Classical set theory proves that at every
infinite ordinal the square is in bijection with the ordinal, and the
endpoint is L ⊨ ZFC. The NO-GO is therefore not a truth statement and
not a falsehood: it is a dispatch-count and a funding statement about
the tree, with the correction recorded beside the target: the
obligation, at the module grain, is the square law at the band, and
that is the object the campaign has already measured four times
(`[LJ-1.107]`, `[LJ-1.111]`, `[LJ-1.114]`, `[LJ-1.593]`).

## THE FLOOR, THE CAPS, THE RUN LEDGER

Caliber on every run: the program's `-A64m -I0 -M2g`, read from the
pane and recorded inside each `.out`. I did not set `GHCRTS` at any
point. One Agda process at a time. Caps I set and report: 120 s for
every W3 run, 300 s for every probe run. No run reached a cap. No run
hit the heap cap (largest peak 616 MB against a 2 g heap).

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, cold (re-elaborates `L.SquareLawClosed`, `L.Absorption`, `L.InjChain`) | 0 | 6.87 s |
| `runs/w3-2.out` | W3 alone, warm | 0 | 1.81 s |
| `runs/w3-neg-1.out` | negative control: one planted error at W3's `supply-ω` row | 42 | 1.76 s, at `W3.agda:71` and nowhere else |
| `runs/final-1.out` | the probe, cold | 0 | 2.03 s |
| `runs/final-2.out` | the probe, warm | 0 | 1.79 s |
| `runs/final-3.out` | the probe, warm | 0 | 1.77 s |
| `runs/w3-3.out` | W3 after the negative control was reverted | 0 | 1.81 s |

Two events on record. First: my first W3 run exited 42 in 0.83 s with
"Not in scope: `ℓ`": I had placed the `ℓ`-dependent opens at the file
top instead of the module body, as `[LJ-1.604]` does. One edit fixed
it; that `.out` was overwritten by the green `w3-1`. Second: the
negative control, `w3-neg-1`, planted `supply-ω = λ _ → refl` and the
checker died at exactly that row, `W3.agda:71`, so the checker is
live; the file was reverted and `w3-3` is green.

Sizes: the probe is 240 lines, of which the two terms are 2 and 1
lines of body and the rest is the measurement in comments; W3 is 96
lines with four rows. The brief estimated about 200 probe lines with
about 50 for the obligation. The obligation has no body, because the
NO-GO forbids inhabiting its type, and comparables are of SHAPE.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean; `lint-prose.py --check`
exit 0 on this report; `grep` for `postulate` and `{!` over the probe
and W3 returns nothing; no em dash in any file of this scope.
`make check` not run: it is the commit gate and nothing here commits.
The ratio bar cannot fire: the probe is a raw `.agda` file and counts
0 in-fence lines.

## W2 AND W4

**W2.** The probe is stated once at the chapter's own generic
telescope `{ℓ} lem α₀ oα₀`, and every row is at a generic α₀ or at a
generic site of its band; any consumer of either trophy instantiates
the same rows. Nothing landed in `src/`, so no fixed-form chapter was
written and no deadline conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the probe as it stands: the no-
coherence row, the three re-ascribed supplies, the named missing
direction, and the count. I did not pay for a worse shape first and
then compare.

## WHAT THE SHAPE RESISTED

The shape resisted only at the funding, not at the typecheck. Every
row elaborated; the frame prices at 2 s. What I had to weaken:
nothing; the brief's type was taken whole and found to be the object
the campaign has already ruled. What I could not close: the missing
direction, `missing-direction-type`, by the wall of `[LJ-1.114]` and
the B9 NO-GO of `[LJ-1.533]`, and I did not attempt it because
`[LJ-1.593]` forbids the dispatch that would be it.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:183`: "| LJ-1.107 | sq at every
  infinite ordinal | PARTIAL: initial ordinals only | The non-initial
  case needs an injection the truncated least-of witness cannot give:
  the inject type is not a prop |". Also read and used:
  `:187` ("| LJ-1.111 | Can Devlin55 take the TRUNCATED sq? | TRUNCATED
  CHAIN GREEN | Truncated sq holds at EVERY infinite ordinal, no
  choice. ...") and `:190` ("| LJ-1.114 | Thread the truncation from
  StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs
  ONE honest injection; two truncation eliminations collide. Reverted;
  the cause is proved |"). These three rows are the demand-side count
  this report's section THE GAP stands on.
- **`archive/dev/JOURNAL.md` DECLINED.**
  `archive/dev/JOURNAL.md:1`: "# ARCHIVED 2026-08-20". A retired
  journal; the measurements this task uses live in the live task
  directories and the dispatch index, both read.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the
  retired route". The retired route's journal does not measure the
  band or the square law at the module grain.
- **`dev/ARCHIVE.md` DECLINED.**
  `dev/ARCHIVE.md:1`: "# ARCHIVE.md: the archive registry". This task
  retires no module, so no row was written and none was consulted
  beyond the first line.
- **`archive/dev/DECISIONS-archived.md` DECLINED.**
  `archive/dev/DECISIONS-archived.md:1`: "# Archived decisions: the D
  series". The rulings that bind this task, R-42 and the square-law
  funding rule, are cited at their own homes in the report.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:146`: "**The constraint
  the route carries: `P` must be `hProp`-valued.** So `leastOf`". With
  `:147-148` ("delivers the least INDEX untruncated, and any payload
  it delivers with the index is a proposition. **A data payload does
  not come out.**") this is the law behind the missing direction: a
  pairing is a data payload, and the band supply is truncated. The
  `splitSup` criterion in section 2.4 of the same file is the exact
  form of the lifting question the tree cannot answer, and the report
  cites it as such.
- **`dev/literature/devlin-II5.md` DECLINED.** Not read for this task:
  the product-grain consumption of the classical theorem was already
  measured and cited at its own line in `[LJ-1.604]`
  (`agents/tasks/LJ-1-604/lj-1.604-report.md`), and this report
  reuses that measurement.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** This task
  fixes no level slot and no Levy grade; the obligation's type
  `SqParam α₀` carries neither.
- **`dev/literature/digest.md` DECLINED.** The digest is about the
  orthodox form of the rud route; no rud-form question arose in this
  measurement.
- **`dev/literature/geology.md` DECLINED.** No layering question arose;
  the measurement is a type comparison inside one chapter's parameter.
