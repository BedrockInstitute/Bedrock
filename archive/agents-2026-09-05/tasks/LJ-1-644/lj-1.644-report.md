# [LJ-1.644] report: the bill's kappa is a chosen site EXACTLY WHEN it is an ambient cardinal AND it has a predecessor, so the route is a LOOP and a limit cardinal breaks it

## HEAD

head_slot: coder
machine: shared
task: LJ-1.644
obligation: agents/tasks/LJ-1-644/Probe644.agda::kappa-is-chosen
verdict: **GO on the obligation, NEGATIVE on the campaign question.**

The term typechecks with the final file in place: `runs/final-3.out`,
`EXIT=0`, 2.77 s, 773.1 MB peak, under the 300 s cap, and it postdates
the last edit of `Probe644.agda` (`.out` mtime 1787706475, source mtime
1787706472). The second file, `runs/S6.agda`, is green in its final
shape at `runs/s6-d.out`, `EXIT=0`, 2.59 s, 692.9 MB (`.out` mtime
1787706452, source mtime 1787706449).

- caliber on every run: `GHCRTS=[-A64m -I0 -M2g]`, which the program set
  on this pane and every `.out` records. I did not set it and never
  raised it.
- one Agda process at a time; no parallelism anywhere in this dispatch.
- no hole, no postulate, no `TERMINATING`, no hole-escape in either
  file. Nothing lands in `src/`. No commit, no push. `git status` shows
  only `agents/tasks/LJ-1-644/` as new.
- gates run from the tree root while working: `check-probes` clean
  (9739 tracked files, no probe outside `agents/tasks/`, no generated
  file), `check-fences` clean (103 masters), `lint-agda` exit 0.
- ledger ratio bar: both files are raw `.agda`, not `.lagda.md` masters,
  so the in-fence divisor is 0 and the bar cannot fire on them.
- this report was a skeleton on disk before any Agda ran and was filled
  as each answer landed (C-22).

**I did NOT write `review-of-kappa-is-chosen.md`, and that is a decision.**
My clause says a `review-of-*.md` is how a coder states a NO-GO, and a
NO-GO means the brief's type was not inhabited. **This brief's type is a
disjunction in prose**: "the statement that `fst κ` IS the `θ` that
`cardAboveAt` chooses at some `a`, **or the term naming the one input
that statement needs**". I inhabited the second disjunct, and the
negative half is carried in the telescope of the term itself rather than
in a prose file. `[LJ-1.640]` returned the identical shape at the
identical kind of brief and stated the same reason
(agents/tasks/LJ-1-640/lj-1.640-report.md:26-31). **The negative is the
whole point of this report and it is in the next section, not buried.**

## THE ANSWER IN ONE LINE

`fst κ` is a site `cardAboveAt` chooses **exactly when two things hold
at once**: `fst κ` is an **ambient** cardinal, and `fst κ` has a
**predecessor**. `chosen⟺` (`Probe644.agda:169-181`) proves both
directions. **Neither direction spends `IsCardinalL` and neither spends
`κ ∉ ω`.**

So the route is a **loop**, and it also **fails outright at a limit
cardinal**:

1. What a chosen site BUYS at the bill's site is `IsCardinal (fst κ)`
   (`chosen→amb`, `Probe644.agda:81-83`). That is the join defect's
   whole want.
2. What pinning the bill's site as a chosen site COSTS is
   `IsCardinal (fst κ)` **and** `Predecessor κ`
   (`pred+amb→chosen`, `Probe644.agda:113-143`).
3. The first cost is the payoff. `route-is-circular`
   (`Probe644.agda:183-187`) is that loop written as one term:
   `IsCardinal (fst κ) → IsCardinal (fst κ)`.
4. The second cost is **not an artefact of my proof**. A chosen site
   FORCES a predecessor: `chosen→pred` (`Probe644.agda:90-98`) reads one
   straight out of the producer. So `Predecessor κ` is what the route
   IS, not how I happened to prove it.

**And `Predecessor κ` is FALSE at a limit cardinal.** It says some
`a ∈ κ` absorbs every member of `κ`, that is, `fst κ` is the Hartogs
ordinal of `a`, that is, `κ` is a SUCCESSOR cardinal. The bill does not
give that: `GCHStatement` (src/L/GCH.lagda.md:60-64) quantifies over
every `κ` with `IsOrd (fst κ)`, `IsCardinalL κ` and `κ ∉ ω` and nothing
else, so `κ` ranges over the limit cardinals too, and at each of those
no `a` exists.

**Therefore the bill's `κ` is NOT reachable as a chosen site.** By the
brief's own words that is the stop worth having, and what to do about it
is your call: the bill must be restated, or the crossing must be bought
somewhere else.

## WHY `a := κ` DOES NOT SAVE IT, AND WHY [LJ-1.640] IS NOT A PRECEDENT HERE

`[LJ-1.640]` closed its converse by instantiating the producer **at the
bill's own site**: `amb→least-at-self` (agents/tasks/LJ-1-640/Probe640.agda:106-110)
takes `a := κ` and `κL κ oκ ≡ κ` follows.

**That move is structurally blocked for `cardAboveAt`**, and the reason
is one component of its output type. `cardAboveAt` returns
`⟨ a ∈ˢ θ ⟩` (src/L/CardinalAbove.lagda.md:207): **the chosen site is
STRICTLY above `a`.** So `a := fst κ` gives `fst κ ∈ θ`, and `θ ≡ fst κ`
would give `fst κ ∈ fst κ`. The witness `a` must come from strictly
below the bill's site, and nothing in the bill hands one down.

This is the measured difference between the two producers, and it is why
`[LJ-1.640]`'s cure does not transfer here by analogy.

## THE TERMS

`agents/tasks/LJ-1-644/Probe644.agda` is 218 lines, 103 of them code.
`agents/tasks/LJ-1-644/runs/S6.agda` is 73 lines, 38 of them code.

| row | what it states | evidence |
|---|---|---|
| `NoInjAt` | `cardAboveAt`'s untruncated Hartogs input, named | `Probe644.agda:52-53` |
| `ChosenSite` | `fst κ` IS the `θ` the producer chooses at some `a` | `Probe644.agda:55-58` |
| `Predecessor` | some `a ∈ κ` absorbs every member of `κ` | `Probe644.agda:60-64` |
| `chosen→amb` | **the payoff**: a chosen site gives ambient cardinality at the bill's site | `Probe644.agda:81-83` |
| `chosen→pred` | **the necessity**: a chosen site FORCES a predecessor | `Probe644.agda:90-98` |
| `pred+amb→chosen` | **the cost**: both inputs together do pin the site | `Probe644.agda:113-143` |
| `kappa-is-chosen` | **THE OBLIGATION**, in the form that names its inputs | `Probe644.agda:158-163` |
| `chosen⟺` | the biconditional, both directions in one type | `Probe644.agda:169-181` |
| `route-is-circular` | the loop, as a term | `Probe644.agda:183-187` |
| `free-chosen-above` | what IS free: a chosen site above ANY ordinal, no hypothesis, truncated | `Probe644.agda:205-217` |

### How `pred+amb→chosen` spends its two inputs

The bound `γ` costs nothing: `fst κ` is its own bound, and the single
fact `cardAboveAt` asks of it, that it does not inject into `a`, is the
ambient cardinality applied to `a ∈ κ` (`Probe644.agda:118-119`). The
equality `θ ≡ fst κ` is then trichotomy at the two sites, one witness
per losing leg (`Probe644.agda:133-143`):

- `θ ∈ κ`: the predecessor clause injects `θ` into `a`, and `θ` is
  inside the bound, so the separation puts `θ` into `θ`; `∈-irrefl`
  closes it.
- `κ ∈ θ`: the separation's own clause `θ-inj`
  (src/L/CardinalAbove.lagda.md:136) injects `κ` into `a`, and ambient
  cardinality refuses exactly that.

Both legs are one line each. **The mathematics here is cheap. The
inputs are the whole price.**

## THE OTHER HALF: WHAT THE TREE DOES SUPPLY FOR FREE

The tree is **not** short of ambient cardinals. It is short of one **at
a site handed in**. `free-chosen-above` (`Probe644.agda:205-217`) shows
that above ANY ordinal the tree hands over an L-element that is a chosen
site AND carries `IsCardinal`, with **no hypothesis beyond ordinality**,
because `noInjOrd` (src/L/CardinalAbove.lagda.md:575) discharges
`cardAboveAt`'s one external input.

**Its only price is the truncation.**

So if you restate the bill to run at the PRODUCER's site rather than at
its own, the ambient half is already paid and this row is the term that
pays it. That is your call, not mine; I record that the option is
costed.

## THE C-42 SWEEP: WHO PRODUCES `Predecessor` IN `src/`

**Nobody.** `grep -rn "Predecessor\|predecessor" src/` returns **26
lines across 7 files** and **not one is a cardinal predecessor**. Every
hit is the ORDINAL or numeral predecessor, which is a different notion:

| file | lines | what the hits are |
|---|---|---|
| src/L/Choice/Before.lagda.md | 11 | the numeral predecessor of the choice chapter |
| src/L/Choice/Stage.lagda.md | 7 | the predecessor of a least STAGE |
| src/Everything.lagda.md | 3 | the powerset-of-the-predecessor remark, :268 |
| src/L/Axioms/Numerals.lagda.md | 2 | the numeral axiom's prose, :192-193 |
| src/L/CardinalAbove.lagda.md | 1 | :458, a point of an image with no preimage |
| src/L/Choice/Step.lagda.md | 1 | :105, the numeral predecessor again |
| src/L/Choice/Limit.lagda.md | 1 | :736, a comparison with two earlier chapters |

**One of them is worth naming so it is not mistaken for a producer.**
src/L/Choice/Stage.lagda.md:144-157 carries "The predecessor of a least
stage" and states at :154-155 that "being the predecessor of a given
ordinal is a proposition, which is what lets a merely-existing
predecessor be read as a definite one". That is the ORDINAL predecessor,
not the cardinal one, so it produces nothing for `Predecessor κ`. **It
is worth reading anyway if you take the restatement option**, because it
is the tree's own worked example of turning a merely-existing witness
into a definite one, which is the shape the truncation question in
section 6 has.

The nearest named thing is `SuccCardL` (src/L/GCH.lagda.md:46-52), and
it is the **wrong direction and the wrong predicate**: it says `δ` is
the successor of `κ` above `κ`, in the CODED predicate `IsCardinalL`,
and `GCHStatement` demands it as a CONCLUSION (src/L/GCH.lagda.md:65-68),
never supplies it as a hypothesis.

**So the second input has zero producers in the tree, and the count is
zero before any cure is priced.**

## THE MEASUREMENT THAT COST THE MOST, AND IT IS A LAW

`runs/final-2.out` walled: 600 s, `EXIT=142`, 2.6 GB RSS, killed by the
wall cap with section 6 inside `Probe644.agda`. **I restructured in the
same dispatch and isolated it in `runs/S6.agda`, one variant per run:**

| variant | what changed | run | result |
|---|---|---|---|
| A | `ordL` on the raw package, no equality | `runs/s6-a.out` | 2.66 s, `EXIT=0` |
| B | A plus the `ChosenSite` conjunct (`refl`) | `runs/s6-b.out` | 2.64 s, `EXIT=0` |
| C | B, but ambient cardinality read back through `subst IsCardinal e` | `runs/s6-c.out` | 240 s, `EXIT=142` |
| D | A and B fused, the surviving shape | `runs/s6-d.out` | 2.59 s, `EXIT=0` |

**Neither `ordL` nor the equality is the cost.** `subst IsCardinal e`
**at a CONCRETE separation site** is. `IsCardinal θ` unfolds to a
Π-type over `⟪ θ ⟫`, so under `--cubical` `subst` is a `transp` across
that family; with `θ` a literal `SEPAREE` term the elaborator transports
across the whole separation set instead of across a variable.

**2.66 s against more than 240 s, at one `subst`.** The cure is not to
transport: the producer already hands the fact over at its own site, so
take it there and let the equality carry only what has no other source.
`Probe644.agda:205-217` obeys that, and the warning sits at the row it
binds (`Probe644.agda:69-79`).

**Note the asymmetry, because it is what makes this trap quiet.**
`chosen→amb` is CHEAP at a variable `e` and was green in `final-1.out`
at 2.81 s. It only walls when APPLIED at a concrete site. A row can be
green in the file that defines it and unusable at its only real
argument.

I have not measured whether this generalises past `IsCardinal` at a
`SEPAREE`, and the Boundary says a measured cure does not transfer by
analogy, so I am not proposing a `dev/LESSONS.md` entry on one site.
**If you want it as a law, the next dispatch should re-measure it at a
second site.** That is my recommendation, not a finding.

## THE FLOOR, MEASURED BEFORE THE PROOFS

Per the coder clause, the frame was priced first with the three real
bodies as holes: `runs/floor-1.out`, 4.13 s, 715.7 MB, `EXIT=42` with
the three interaction holes as the only failures. Every type stood at
that point, including `ChosenSite`, `Predecessor`, the obligation's
shape, and the reduction of `fst (cardAboveAt a oa h)` through
`module Sep`. **The frame was never the problem here, and the three
proof bodies then landed green on the first attempt** (`final-1.out`,
2.81 s). The wall came later and from section 6 alone.

## W3: THE WIDEST UNMEASURED TERM

The brief named it: "Whether `IsCardinalL κ` plus ordinality pins
`fst κ` against a chosen `θ`." Estimate 70 to 140 lines.

**ANSWERED, AND THE ANSWER IS NO. `IsCardinalL κ` plus ordinality pins
nothing.** Both hypotheses are dead in every body of this probe;
`kappa-is-chosen` carries them and never mentions either
(`Probe644.agda:158-163`), exactly as `noInjOrd→CardAboveLᵀ` reports of
the same two (src/L/CardinalAbove.lagda.md:225-226). What pins the site
is the AMBIENT predicate plus a predecessor, and the bill supplies
neither.

**Measured cost: 103 code lines in a 218-line probe, plus 38 code lines
in a 73-line isolation file.** Against the 70-to-140 estimate that is
inside the band for the obligation file. The estimate did not price the
isolation file, and nothing in the brief could have: it exists because
of the `subst` wall, which was not visible before it was paid.

## WHAT THE NEXT BRIEF NEEDS FROM ME

1. **Do not queue another attempt at pinning the bill's site against a
   producer's chosen site.** Three producers were censused by
   `[LJ-1.643]`, `[LJ-1.640]` measured the first two, and this dispatch
   measured the third. All three choose their own site, and for
   `cardAboveAt` the choice is provably strictly above any `a` you hand
   it, so the bill's site is out of reach by the shape of the output
   type and not by a missing lemma.
2. **The two live options are yours to rule between.** Restate the bill
   to run at the producer's site, where `free-chosen-above` already pays
   the ambient half up to a truncation; or buy `IsCardinal (fst κ)` at
   the named site, which is `[LJ-1.533]`'s `AmbToCodeᵀ` crossing and
   `[LJ-1.615]`'s shelve.
3. **If you restate, the truncation is the one open price** and I have
   not measured whether it can be stripped. `dev/literature/truncation-and-selection.md`
   gives the exact condition; nothing in this dispatch tested it at this
   site.
4. **If you take the restatement, the successor-cardinal question comes
   back anyway**, because `GCHStatement` must PRODUCE `SuccCardL δ κ`
   (src/L/GCH.lagda.md:65-68) and `free-chosen-above` gives a cardinal
   above `κ`, not the LEAST one. I did not price that gap.

## ARCHIVE USED

- **archive/dev/LJ-dispatch-index.md**: READ, and it is the one archive
  hit that bore on this dispatch. `archive/dev/LJ-dispatch-index.md:170`
  reads: `| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |`.
  It is the row `src/L/CardinalAbove.lagda.md` itself cites when it
  explains why the current Hartogs construction needs no order types,
  and it confirms that the 1058-line ambient Hartogs of the retired
  route ALSO stated `IsCardinal` locally rather than at a site handed
  in. The defect this dispatch measured is older than this file.
- **archive/dev/JOURNAL-archived.md**: not read. It is 4280 lines of
  dated narrative from the retired route; the Boundary says a live
  document carries no history, and nothing in this task turns on when
  something happened.
- **dev/ARCHIVE.md**: surveyed and declined.
  `grep -n "Cardinal\|cardinal" dev/ARCHIVE.md` returns nothing, so no
  retired module bears on the cardinal question. No W4 move arises from
  this dispatch either: I retired no module.
- **archive/dev/DD-archived.md**: not read. 38 lines, and the `DD`
  series is set aside in this form by amendment A7; no `DD` row binds
  this task.
- **archive/dev/JOURNAL.md**: not read, for the same reason as
  `JOURNAL-archived.md`.

## LITERATURE USED

- **dev/literature/truncation-and-selection.md**: READ, and it is
  cited above as the open price on the restatement option.
  `dev/literature/truncation-and-selection.md:183` reads:
  `And the condition is not only sufficient:`, and the lines under it
  give the exact condition for a map out of `∥ A ∥₁` into a set. That
  is the condition anyone stripping `free-chosen-above`'s truncation
  must meet. **I did not test it at this site and I claim nothing about
  it.** The file's line 243 also reads:
  `first-order ZF. **In classical first-order logic, existential elimination`,
  which is why the classical Hartogs argument reads as free and this one
  does not.
- **dev/literature/devlin-II5.md**: not read. It digests Devlin II.5,
  the Condensation Lemma and the GCH proof; this dispatch touched no
  condensation step and no stage bound, only the cardinal predicate at
  one site.
- **dev/literature/digest.md**: not read. It pins the orthodox rud
  route; nothing in this task chooses between towers.
- **dev/literature/devlin-errata.md**: not read. No step of this
  dispatch follows a Devlin proof, so no erratum could apply.
- **dev/literature/terms-2026-08.md**: declined. It is a terminology
  dossier for the owner's naming ruling. I added no `dev/glossary.toml`
  entry and named no new term for translation.
