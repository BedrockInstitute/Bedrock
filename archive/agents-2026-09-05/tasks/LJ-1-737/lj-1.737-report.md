# LJ-1.737 return: table-sat under closedω

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: PARK, not GO and not NO-GO.** The obligation is not
discharged and not refuted. The probe is green and delivers the closedω
arithmetic the whole route stands on, plus the conclusion-side placement
that the 724-SPLIT scope could not give. Two tree debts block the
satisfaction; both are measured with `file:line`, and neither is
probe-sized. The target itself is TRUE (D-10 truth-price below), so a
NO-GO would be a false measurement and is not filed.

## What the obligation is

`table-sat` at `[LJ-1.698]`'s `Carved` frame (`Probe698.agda:107-123`), with
the SPLIT scope hypothesis `x+2 < γ` replaced by `closedω γ`
(`src/L/Ordinal/StageArith.lagda.md:81-82`):

    table-sat : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
                (clγ : closedω γ)
                (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
              → ⟨ ω ∈ˢ γ ⟩
            → ⟨ pr x (Lset x) ∈ˢ carved ⟩

## Route, and where it stands

`carved` is sealed, so the only leg in is `imageIn` (`carveSat`,
`src/L/Axioms/Separation.lagda.md:163-168`): membership in `carved` is
satisfaction of `φᵣ` at the pair's environment. The 724-SPLIT refutation
died on the DefAt membrane: relativized to `A = Lset γ`, the reading's raw
quantifiers demand every witness INSIDE `Lset γ`. `closedω γ` absorbs every
finite block above a member, so each witness places iff it is built at a
finite iterate over a member. The witness list, at env `(xᶜ ∷ pairS)`:

- the recording witness `c₀ = xᶜ` (hypothesis `x ∈ˢ γ`),
- the value slot `z' = (Lset x , isL)`: `Lset x ∈ˢ Lset γ` by `Lset-self`
  plus Section 1's `suc∈γ`,
- the tower graph `f` below `x` (`hierL x` up to `Lset-only`),
- the step's witnesses `c' ∈ x`, `w' = Lset c'`,
  `d' = 𝒟ₒ (Lset c') = Lset (sucV c')` by `Lset-suc`,
- DefAt's code and graph (`keyS`/`Sat` over the value; the tag atoms'
  numerals sit at `ω`, and `⟨ ω ∈ˢ γ ⟩` is a hypothesis).

## Legs closed (all green in `Probe737.agda`)

- `Closer.no-succ`: `closedω γ` is never a successor. `γ = sucV x` with
  `x ∈ˢ γ` would put `+ω x` inside `sucV x`, and `+ω x` is neither below
  nor equal to `x` (`+ω-mem`, transitivity, `∈-irrefl`). This leg is NEW:
  without it, every successor step of the absorption kit dies at the
  `suc∈or≡` equality branch.
- `Closer.suc∈γ` / `iter∈γ`: every finite iterate of a member is a member.
- `Closer.block∈Lγ`: anything in a finite iterate's stage is in
  `Lset γ` (`Lset-mono` along `+ω-iter`, then StageArith's `boundCloses`,
  `src/L/Ordinal/StageArith.lagda.md:86-89`).
- `Underω.pair-in-Lγω`: `pr x (Lset x) ∈ˢ Lset γ` from `x ∈ˢ γ` ALONE.
  [LJ-1.724-SPLIT] needed `x+2 < γ` as a scope hypothesis
  (`Probe724Split.agda`, `pair-in-Lγ`); closedω derives it (`x²∈γ`), so
  the pair's conclusion-side placement now holds for EVERY member.

## The two debts that block the satisfaction

1. **The tower graph's stage.** The graph witness must be an L-element in
   `Lset γ`. Carving the recording relativized to `Lset x` at
   `mkBoundedFo ψᵣ`'s own stage fails: that stage is unbounded, and
   bounding it needs a constant-tracking induction over the recording's
   atom unfolding. The tag atoms carry `con (numeralL k)` constants
   (`src/L/Coding/CodeSet.lagda.md:135-136`,
   `src/L/Coding/Model.lagda.md:585-587`), so the unfolding's constant
   set is not uniform, and the per-constant leaf bound cannot be stated
   without tracking which constants occur. Neither the converse rank leg
   (`rank z < α ∧ isL z → z ∈ˢ Lset α`) nor any replacement-image finite
   stage bound exists in `src/` (`rank-Lset` at
   `src/L/Ordinal/Stages.lagda.md:190-191` is the forward direction only).
2. **The DefAt-witness placement.** The step body's DefAt conjunct, once
   relativized, demands its code and graph INSIDE `Lset γ`. Nothing in
   `src/` places `keyS`/`Sat` witnesses at a controlled stage:
   `EnvSet`'s `stageFor` bounds are `boundingOrd` sups of least-stages
   (`src/L/Coding/EnvSet.lagda.md:85-99`), uncontrolled, and StageArith's
   own header comment ("the code set over the carrier at δ sits at stage
   δ+ω", `src/L/Ordinal/StageArith.lagda.md:76-80`) is narrative only.
   `boundCloses` waits for exactly the leg that would supply it; no
   chapter supplies it yet. My probe's `runs/` history confirms this was
   the wall the SPLIT refutation actually lived behind, now seen from the
   GO side.

## D-10 truth-price

The target is TRUE at the intended generality. Every witness the
A-restricted reading demands has rank finite over a member of `γ`, and
`closedω` absorbs each finite block (Section 1 is that statement in Agda).
The wall is the tree's missing placement legs, not the statement: NO-GO is
therefore not filed, because "which membrane still fails at closedω" has
the answer "none; the legs to build the witnesses are missing".

## What the next brief needs

- A chapter-sized leg: `codes-at-stage` or equivalent, placing the coding
  of a formula over a carrier at a finite iterate of the carrier's stage
  (Devlin II.5's promise StageArith's header already makes). Debt (ii)
  dies with it, and debt (i)'s induction gets its uniform numeral leaf.
- Alternatively, a `occurs-in` constant-tracking metalemma over `Formula`,
  which makes `mkBoundedFo`'s stage bound by syntax induction.
- The A21 probe the SPLIT critic named (construct the Step-membrane
  witnesses inside `Lset γ`) is blocked by the same debt (ii); pricing it
  before the leg lands would wall the same way.

## Runs (wide caliber, pane GHCRTS, one Agda process per run)

- `runs/s1-green-1.out`: probe with Section 1 + final hole, rc 42
  (unsolved interaction meta at the obligation hole only), 2.07 s.
- `runs/final-green-1.out`: final full file, rc 0, empty transcript
  (no warnings), 2.0 s warm. Cold floor with the 724-SPLIT/698 import
  chain: 49.8 s, measured once at skeleton stage.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-737
    check-survey-quotes: LJ-1-737 FAILS the survey duty:
      no-heading: the return carries no ARCHIVE USED section
      unanswered: the return never names archive/dev/DD-archived.md
      unanswered: the return never names archive/dev/ORCHESTRATION.md
      unanswered: the return never names archive/dev/PLAN-archived.md
      unanswered: the return never names archive/dev/STATUS-archived.md
      unanswered: the return never names archive/dev/TASKS-archived.md
      no-lit-heading: the brief cites dev/literature/ and the return carries no LITERATURE USED section

    A return names every path the program injected, and quotes one line read per
    file: the quote must occur AT the cited line in the cited file. A written
    decline is compliance.

(The paste above is the mid-run output while the report was still a
skeleton; the blocks below answer it.)

## W2 answer

The brief's W2 (write the mathematics once at a generic carrier and
instantiate it) is answered in the shape: Section 1's `Closer` is written
once, generic in `(γ, oγ, hγ, clγ)`, and Section 2's `Underω` instantiates
it; `Frame`'s `pair-in-Lγ` from [LJ-1.724-SPLIT] is reused rather than
re-written. The follow-up that pays the two debts should keep the same
discipline: one tower module generic in the base ordinal, instantiated at
`x` for the graph and at `γ` for the frame. No deadline forced a fixed
form here.

## ARCHIVE USED

- `archive/dev/DD-archived.md:30`: "A return carries an ARCHIVE USED
  section naming what it actually read and what it took from each item, at
  `file:line`." READ. This row is the mechanism this block runs under, so
  it is the one archived record this return uses.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch and landing
  are the program's business; this return writes files and reports.
- `archive/dev/PLAN-archived.md`: declined, not read. The park disposition
  follows the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is the 724-SPLIT review and probe, both
  live in the tree and cited at `file:line` above.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  return adds no glossary term and cites none.
- `dev/literature/devlin-errata.md`: declined, not read. The debts are
  measured inside the tree's own codings, not in the primary text.
- `dev/literature/rudimentary-functions.md`: declined, not read. Debt (ii)
  is a placement leg in this tree's own chapters; the digest would not
  change the `file:line` evidence.
- `dev/literature/primary-sources.md`: declined, not read. No fetched text
  backs any step of this return.
- `dev/literature/formalizations-landscape.md`: declined, not read. The
  route and its blocking legs are internal to `src/` and cited above.
