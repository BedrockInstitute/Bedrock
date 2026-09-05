# [LJ-1.638] report: the above-omega half reduces to conjunct 4 alone, and the C-42 sweep finds conjunct 4 a second route that is already green in src/

## HEAD

head_slot: coder
machine: shared
task: LJ-1.638
obligation: agents/tasks/LJ-1-638/Probe638.agda::above-half-needs-c4
verdict: GO. The term typechecks and is green: `runs/final-4.out`,
exit 0, 3.44 s, 779.2 MB peak, under the 300 s cap, and it postdates the
last edit of both source files (`Probe638.agda` mtime 1787677725,
`runs/C3.agda` mtime 1787677489, run mtime 1787677735). The caliber on
every run is the program's `GHCRTS=[-A64m -I0 -M2g]`, read from the pane
and recorded in every `.out`. I did not set it. One Agda process ran at
a time. No hole and no postulate stand in either final file. Nothing was
written under `src/`. No commit, no push. `git status` shows only
`agents/tasks/LJ-1-638/` as new.

The brief asked for one term and it is delivered. Conjunct 4 stayed a
hypothesis, as the brief required, and no row of this task builds it.

**The task's own W3 is GO and the answer is stronger than the brief
expected: `c3-payable` composes with NO re-proof at all**, through one
line of order that the brief did not name. **The C-42 sweep that the
LAWS block makes mandatory earned the finding that matters most: `src/`
already carries an `Init` assembly at another site, and its conjunct 4
is paid by a route `[LJ-1.629]` never priced.**

This report was a skeleton before any Agda ran and was filled as each
answer landed (C-22).

## THE PREDECESSOR'S NO-GO, AND WHY IT DOES NOT BITE HERE

The coder's standing clause says to take the type from the predecessor's
probe and the verdict from its report, and to stop if the report names
the statement FALSE. `[LJ-1.629]`'s verdict IS NO-GO. I checked it
before I wrote any Agda, and it does not bite, for one reason stated as
a term:

`[LJ-1.629]` refuted `SiteIsInit` (`agents/tasks/LJ-1-629/Probe629.agda:84-88`),
whose second hypothesis is the bill's trophy clause
`⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥`. Its falsifier `target-false`
(`Probe629.agda:138-139`) runs at `κ := ωʟ`, a site that clause ADMITS.
**This obligation's second hypothesis is `⟨ ω ∈ˢ fst κ ⟩` instead, and
that hypothesis is uninhabited at `κ := ωʟ`**: the row is `no-ω-site`,
`agents/tasks/LJ-1-638/Probe638.agda:179-180`. The refuted site is not
admitted here, so no term of this file inhabits the refuted type, and
`target-false` cannot be run against `above-half-needs-c4`.

The respell is the one `[LJ-1.629]`'s own report proposed as the cure
(`agents/tasks/LJ-1-629/lj-1.629-report.md:183-192`), and `[LJ-1.635]`
turned it into a split rather than a bill edit
(`agents/tasks/LJ-1-635/Probe635.agda:90-104`). **The module hypotheses
this task consumes are the types the predecessor DELIVERED, taken by
import and not by copy**: conjunct 4's type is `Init4` from
`[LJ-1.629]`'s alone-typechecked W3 (`agents/tasks/LJ-1-629/runs/W3.agda:62-67`),
and conjunct 3 is the green `c3-payable` (`agents/tasks/LJ-1-629/Probe629.agda:227-233`).
Neither is re-spelled anywhere in this task, so neither can drift.

## W3: DOES `c3-payable` COMPOSE AT THIS FRAME WITHOUT RE-PROOF

`agents/tasks/LJ-1-638/runs/C3.agda` was written first and typechecked
ALONE: `runs/w3-2.out`, exit 0, 3.46 s, 755.4 MB peak, under the 120 s
cap. (`runs/w3-1.out` is the same file green at 24.95 s and 2284.7 MB:
that run built the `L.BoundedSubset` and `LJ-1-629.Probe629` interfaces
cold, and the difference between the two runs is the interface build and
not the term. `runs/w3-3.out` is green again at 3.68 s after a
comment-only edit.)

**GO, and the price is ZERO re-proof.** `c3-payable` names four
hypotheses; three are this frame's own, and the fourth is the bill's
trophy clause, which this frame does not have. **One line of order
supplies it**: `above→∉ω`, `agents/tasks/LJ-1-638/runs/C3.agda:83-84`.
An ordinal that has `ω` as a member is not itself a member of `ω`,
because `ω` is transitive (`ω-ord`, and `IsOrd`'s first component is
`isTransV`, `src/L/Constructible.lagda.md:142`, whose shape is
`src/FOL/ZFStructure.lagda.md:116-118`) and regularity forbids `ω ∈ ω`
(`∈-irrefl`, `src/V/Hierarchy.lagda.md:155`). So `c3-at-frame`
(`runs/C3.agda:92-96`) is ONE application of `c3-payable`, and conjunct 3
transfers whole.

**What this measures beyond the brief's question: the respelled frame is
a STRENGTHENING and not a sideways move.** The strictly-above hypothesis
implies the trophy clause. Every row `[LJ-1.629]` proved under the
trophy clause is therefore still available at the split's above-ω half,
without re-measurement. The brief's estimate was 40 to 90 lines with the
basis "`[LJ-1.629]`'s own rows are 70 lines and this composes them"
(`agents/tasks/LJ-1-629/lj-1.629-report.md:166`). **The estimate priced
re-proof. The measurement is that no re-proof was needed**: the whole
obligation path is 15 lines of Agda (`above→∉ω` 2, `c3-at-frame` 4,
`four-gives-init` 3, `above-half-needs-c4` 6). The two files are 96 and
225 lines because the discipline notes are part of the deliverable.

## THE TERM

`agents/tasks/LJ-1-638/Probe638.agda` is 225 lines and carries five
sections. `agents/tasks/LJ-1-638/runs/C3.agda` is 96 lines.

| row | what | evidence |
|---|---|---|
| `above→∉ω` | strictly above `ω` implies the bill's trophy clause | `runs/C3.agda:83-84` |
| `c3-at-frame` | conjunct 3 at this frame, from `[LJ-1.629]`'s row by one application | `runs/C3.agda:92-96` |
| `Closed` | conjunct 3's type, copied letter for letter from `src/L/Ordinal/SquareLaw.lagda.md:695` | `Probe638.agda:105-106` |
| `four-gives-init` | the four conjuncts BUILD `Init`, which pins `Init4` as the chapter's own fourth conjunct in the build direction | `Probe638.agda:108-110` |
| `above-half-needs-c4` | THE OBLIGATION, stated as the brief names it | `Probe638.agda:129-134` |
| `AboveFrame` | the shape of `[LJ-1.635]`'s above-ω half with its conclusion left open | `Probe638.agda:154-156` |
| `above-c4→sq` | THE PAYOFF: conjunct 4 across the half buys the square law at every site of the half | `Probe638.agda:158-162` |
| `no-ω-site` | the falsifier's site is not admitted here | `Probe638.agda:179-180` |
| `c4-from-min` | what the C-42 sweep earned, re-measured at a generic site | `Probe638.agda:212-225` |

**The obligation's spelling against the brief's.** The brief writes
`(κ : S)`; the probe writes `(κ : SL.S)`, which is the SAME carrier
under a name that cannot be confused with the ambient one. `IsCardinalL`
and `fst κ` both demand the `𝒮ʟ` carrier, and this is `[LJ-1.635]`'s own
spelling for the above-omega half's site (`agents/tasks/LJ-1-635/Probe635.agda:59`
opens `S` from `𝒮ʟ`, and `:92` is the half). This file follows
`[LJ-1.629]`'s convention instead, because it consumes `[LJ-1.629]`'s
rows: `S` is ambient (`𝒮ᵥ`) and `SL.S` is `𝒮ʟ`'s
(`agents/tasks/LJ-1-629/Probe629.agda:69-70`). The two names denote one
type. The brief's `<conjunct 4 of Init at fst κ>` is `W3629.Init4 (fst κ)`,
pinned to the chapter in both directions as the next paragraph but one
explains.

**The three free conjuncts, and where each comes from.**

| # | conjunct at `fst κ` | source at THIS frame |
|---|---|---|
| 1 | `IsOrd (fst κ)` | the frame's own first hypothesis, verbatim (`[LJ-1.629]`'s `c1-given`, `Probe629.agda:109-111`) |
| 2 | `⟨ ω ∈ˢ fst κ ⟩` | the frame's own third hypothesis, VERBATIM. Conjunct 2 IS the strictly-above hypothesis (`src/L/Ordinal/SquareLaw.lagda.md:694`) |
| 3 | successor closure | `[LJ-1.629]`'s `c3-payable`, composed by `runs/C3.agda` with no re-proof |
| 4 | the non-injection | THE HYPOTHESIS. Not built. This is the whole remaining debt of the above-ω half |

**`four-gives-init` is what makes the anti-drift claim a measurement and
not a promise.** `Init4` (`agents/tasks/LJ-1-629/runs/W3.agda:62-67`) is
`[LJ-1.629]`'s letter-for-letter copy of the chapter's fourth conjunct.
`init-gives-4` (`W3.agda:69-70`) already pinned the projection
direction. `four-gives-init` typechecks only if `Init4` is that conjunct
up to definitional equality in the BUILD direction as well, so the copy
and the chapter cannot drift apart in either direction.

**`above-c4→sq` is `[LJ-1.629]`'s `route` restated at the corrected
frame.** There (`Probe629.agda:292-295`) the premise was the refuted
`SiteIsInit` and the row measured a route whose premise was false. Here
the premise is `AboveFrame` of conjunct 4 alone, the falsification is
gone, and the row says exactly what the campaign buys if it pays
conjunct 4 across the half: `sq (fst κ)` at every site of the half,
through the chapter's own theorem (`via-col-square`,
`src/L/Ordinal/SquareLaw.lagda.md:960-961`).

## C-42: THE SWEEP, AND WHAT IT FOUND

C-42 says a refutation measures ONE site and never measures how far the
same shape extends, so the next action is the sweep and the COUNT comes
before any cure is priced. `[LJ-1.629]` refuted `Init` at the bill's
site. Here is the count.

**PRODUCERS of `Init` in `src/`: exactly ONE.**
`grep -rn "→ Init \|Init (fst" src/` outside the defining chapter
returns a single line: `src/L/SquareLawClosed.lagda.md:171`, the
conclusion of `init-at-kappa` (`:166-176`).

**CONSUMERS of `Init` in `src/`: three, all inside the defining
chapter.** `module Initial` (`src/L/Ordinal/SquareLaw.lagda.md:938`),
`via-col-square` (`:960-961`) and `via-col-truncated` (`:963-964`).

**SITES where the shape "`Init` demanded at an ordinal" occurs: three,
and TWO of them already route around the refuted case.**

| site | what the tree does there |
|---|---|
| `ω` | `src/L/InjChain.lagda.md:104` states the refutation in a comment and routes around it: "The base at ω is not initial (`Init ω` needs `⟨ ω ∈ˢ ω ⟩`, refuted by `∈-irrefl`), so the three hypotheses are supplied at ω directly" through `InitialCore` (`InjChain.lagda.md:171`) |
| `fst (κL a oa)` | `src/L/SquareLawClosed.lagda.md:166-176` BUILDS `Init` there, with conjunct 2 as a hypothesis |
| `fst κ`, the bill's site | this task: three conjuncts free, conjunct 4 open |

**So the refuted shape is NOT spread through the tree.** `[LJ-1.629]`'s
falsification names the only place the campaign was about to walk into
it, and the chapter had already walked around the same wall at `ω` by
the same move `[LJ-1.635]` later made at the bill: supply the site
directly instead of asking `Init` for it. No cure needs funding against
an unknown count.

**THE SWEEP'S REAL PAYOFF: conjunct 4 has a second route, and it is
already green.** `clause4-at-kappa` (`src/L/SquareLawClosed.lagda.md:96-115`)
pays conjunct 4 at the least-cardinal site from two things:
MINIMALITY at the site (`κ-min-atL`, `:86-89`: no member of the site
admits an injection from `a`) plus `∥ sq β ∥₁` at every infinite member,
which that chapter's recursion supplies as an induction hypothesis.
**Neither ambient `IsCardinal` at the site nor `BandBelow` appears in
it.** `[LJ-1.629]` priced conjunct 4 as needing exactly those two
(`agents/tasks/LJ-1-629/lj-1.629-report.md:59`), and that pricing is
correct for the route it measured; it is not the only route.

Because a measured cure does not transfer by analogy, I re-measured the
`src/` argument at its own site rather than citing it. `c4-from-min`
(`Probe638.agda:212-225`) is that argument at an ARBITRARY site and an
ARBITRARY injected type. **It does not discharge conjunct 4**: all three
of its hypotheses stay open. It measures that the route is
site-generic, so the bill's site can consume it the moment a future task
supplies minimality there.

**A second, smaller find, reported and not hidden.** `above→∉ω`
(`runs/C3.agda:83-84`) is `inf-member` (`src/L/SquareLawClosed.lagda.md:60-61`)
letter for letter: same statement, same body. I did not import it,
because it sits inside a module parameterized by `(α₀ : V ℓ) (oα₀ : IsOrd α₀)`
(`src/L/SquareLawClosed.lagda.md:19-20`) that its own body never uses,
so reaching it costs an invented `α₀` and that chapter's whole frame for
one line of order. The duplication is a defect of PLACEMENT, not of
either copy. The cure is one line long and it is the mathematician's
call: lift `inf-member` to `L.Ordinal`, where both sites reach it
without a parameter.

## THE FLOOR, THE CAPS, THE RUN LEDGER

Caliber on every run: `GHCRTS=[-A64m -I0 -M2g]`, set by the program on
this pane. Caps, which I set and report: 120 s for the alone W3 runs,
300 s for every other run. No run reached a cap. **No heap wall
occurred**, so the owner's restructure ruling of 2026-08-23 was not
engaged.

**The floor was measured before the proof, per the owner's ruling of
2026-08-23**: the probe ran first with a hole in each of its three
bodies. `runs/floor-1.out` is that run, exit 42 with exactly three
unsolved interaction metas and NO type error on any statement, at
3.38 s and 772.4 MB. **The obligation body costs nothing on top of the
frame**: the holed floor is 3.38 s and the green obligation is 3.30 s,
which is inside run-to-run noise. This is not a heavy object, and the
frame, not the term, is what the price measures. The imports were kept
to the facts these rows actually use, per the same ruling.

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3 ALONE, cold; builds the `L.BoundedSubset` and `LJ-1-629.Probe629` interfaces | 0 | 24.95 s, 2284.7 MB |
| `runs/w3-2.out` | W3 ALONE, warm | 0 | 3.46 s, 755.4 MB |
| `runs/floor-1.out` | THE FLOOR: the frame and all four statements, three bodies holed | 42 | 3.38 s, 772.4 MB |
| `runs/final-1.out` | the obligation, the assembly and the payoff, real bodies | 0 | 3.30 s, 778.8 MB |
| `runs/final-2.out` | green with the C-42 row `c4-from-min` added | 0 | 3.84 s, 779.2 MB |
| `runs/w3-3.out` | W3 ALONE again, after the comment-only duplication note | 0 | 3.68 s, 758.9 MB |
| `runs/final-3.out` | green after the W3 note; superseded by a comment-only citation fix | 0 | 3.52 s, 777.3 MB |
| `runs/final-4.out` | GREEN, postdating the last edit of both files | 0 | 3.44 s, 779.2 MB |

**Every run that was meant to be green was green on its first attempt.**
The only non-zero exit in this ledger is the floor run, and its three
holes are why. No code was ever re-run unchanged.

Sizes: `Probe638.agda` is 225 lines, of which the obligation is 6
(`:129-134`); `runs/C3.agda` is 96 lines, of which the W3 term is 5
(`:92-96`). The Agda on the obligation's whole path is 15 lines.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean (9680 tracked files, no
probe outside `agents/tasks/` and no generated file);
`scripts/gate/lint-prose.py --check` exit 0 on this report; `grep` for
`postulate`, `TERMINATING` and `{!` over both `.agda` files returns
nothing; no em dash in any file of this scope. `make check` not run: it
is the commit gate and nothing here commits. **The ratio bar cannot
fire**: the write scope carries no `.lagda.md` master, so the in-fence
line count is 0 and the bar's divisor is fact 7 of the write scope.

## WHAT THE NEXT BRIEF NEEDS

1. **The above-ω half is now ONE named conjunct wide, and the type is
   written.** It is
   `AboveFrame (λ κ → Init4 (fst κ))`, `Probe638.agda:154-159`, and
   `above-c4→sq` says what paying it buys. Nothing else stands between
   the above-ω half and `sq` at its sites.
2. **PRICE `c4-from-min`'s MINIMALITY HYPOTHESIS AT THE BILL'S SITE
   BEFORE PRICING `BandBelow` AGAIN.** This is the sweep's finding and
   it is the cheapest open question this task leaves. `src/` pays
   conjunct 4 from minimality plus a descending `sq` induction
   hypothesis, with no ambient cardinal at the site and no band
   (`src/L/SquareLawClosed.lagda.md:96-115`, re-measured generically at
   `Probe638.agda:212-225`). `[LJ-1.629]`'s pricing
   (`lj-1.629-report.md:59`) measured a different route and is not
   wrong; it is not the only route. The open question is whether
   `IsCardinalL κ` yields minimality at `fst κ` in the ambient sense
   `c4-from-min` wants, and D-10 says to price that TRUTH before
   dispatching its proof.
3. **`inf-member` is trapped in a parameterized module and should be
   lifted.** `src/L/SquareLawClosed.lagda.md:60-61`, inside a module
   parameterized by `(α₀ , oα₀)` its body never uses. Two sites now
   carry the same line. This is a one-line placement fix and it is the
   mathematician's call, not mine.
4. **The shape to keep, and one shape to stop paying for.** Keep the
   import-not-copy discipline for a predecessor's delivered type: this
   task re-spelled NOTHING from `[LJ-1.629]` and so had no drift to
   check. Keep the alone-typechecked W3 file: it caught the whole
   answer before the probe frame existed. **Stop assuming a
   predecessor's NO-GO closes a statement**: `[LJ-1.629]`'s NO-GO is
   about the type its own report names, and one hypothesis separates
   that type from this one. The separating term is `no-ω-site`
   (`Probe638.agda:179-180`), six characters of proof.
5. **What was weakened: nothing.** The statement is the brief's, with
   the brief's own hypothesis list and the chapter's own conclusion.
   **What is not closed: conjunct 4, deliberately**, as the brief
   required.

## PREMISES CHECKED

- Premise 1 HOLDS: `agents/tasks/LJ-1-635/lj-1.635-report.md:70` is
  "**It is, and the term is `above-half-misses-ω`, which is
  `∈-irrefl ω`.**" The split is forced by an order fact.
- Premise 2 HOLDS WITH AN OFFSET: the cited `Probe629.agda:224` is a
  clause of `c3-triω`, an ingredient. `c1-given` is at
  `agents/tasks/LJ-1-629/Probe629.agda:109-111` and `c3-payable` is at
  `:227-233`. Both are green rows and both were used.
- Premise 3 HOLDS WITH AN OFFSET OF ONE: the cited
  `src/L/Ordinal/SquareLaw.lagda.md:693` is conjunct 1, `Init α = IsOrd α`.
  Conjunct 2, `× ⟨ ω ∈ˢ α ⟩`, is `:694`. The claim itself is exact:
  conjunct 2 IS the strictly-above hypothesis, verbatim.
- Premise 4 HOLDS: `agents/tasks/LJ-1-629/lj-1.629-report.md:59` is the
  conjunct-4 row, "MISSING at the stated grain", naming ambient
  `IsCardinal` at the site plus `BandBelow`. **It holds as a statement
  about the route `[LJ-1.629]` measured, and this task's C-42 sweep
  finds a second route that needs neither.** See the C-42 section.
- The brief's `Init` citation HOLDS: `Init` is
  `src/L/Ordinal/SquareLaw.lagda.md:692-698`, four conjuncts.
- The brief's W3 estimate is ANSWERED AND WAS HIGH: 40 to 90 lines
  estimated, 15 lines of Agda measured, because no re-proof was needed.

## THE LAWS THE BRIEF BOUND ME TO

- **D-10** (price the truth of a recorded residue before pricing its
  proof). Applied twice. First to the predecessor's NO-GO: I priced
  whether the refuted statement IS this statement before writing any
  Agda, and the answer is a term (`no-ω-site`). Second to the sweep's
  find: item 2 of "what the next brief needs" asks for the TRUTH of
  minimality at the bill's site to be priced before its proof is
  dispatched.
- **C-22** (write the deliverable incrementally). This report was a
  skeleton on disk before the first Agda run and was filled section by
  section as each answer landed.
- **P-l** (a statement may be ABOUT a concrete stage without dragging
  that stage's presentation into its type). Held throughout, and it is
  visible in the price. No type in either file names a transparent
  presentation: `Init4` and `Init` quantify over an ambient site, and
  `fst κ` is left as an atom. The frame costs 3.38 s and the terms cost
  nothing on top of it.
- **D-26** (a well-founded key on a tower needs generation data, or it
  needs syntax). NOT ENGAGED. No row of this task well-orders a stage
  or builds a key; the task composes four conjuncts of an order
  predicate.
- **C-42** (a refutation measures the site it names, never how far that
  site extends). Answered in full in its own section above, with the
  count before any cure: one producer of `Init` in `src/`, three
  consumers, three sites, two of which already route around the refuted
  case.

## W2 AND W4

**W2.** Every row is written at a generic carrier and instantiated, so
both future proofs share the code. `Closed` and `four-gives-init` are
stated at an ARBITRARY ambient `α`, not at the site, so any future site
consumes them unchanged. `AboveFrame` is stated at an ARBITRARY
conclusion, so it is the shape of `[LJ-1.635]`'s half
(`AboveFrame (Concl zf)`), of this task's supply
(`AboveFrame (λ κ → Init4 (fst κ))`) and of the payoff
(`AboveFrame (λ κ → sq (fst κ))`) with one definition. `c4-from-min` is
stated at an arbitrary site AND an arbitrary injected type, which is
strictly more general than the `src/` argument it re-measures. Nothing
landed in `src/`, so no fixed-form chapter was written and no deadline
conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the two files as they stand: one
alone-typechecked W3 carrying the order bridge and the composed
conjunct, one probe carrying the assembly, the obligation, the payoff
and the sweep's row. I did not pay for a worse shape first: every run
meant to be green was green on its first attempt, so this return has no
walled shape to compare against. The one PLACEMENT defect this task
found is in `src/` and not in this task's own files: `inf-member` at
`src/L/SquareLawClosed.lagda.md:60-61`, priced above at one line.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:192`: "| LJ-1.116 | At which alpha
  does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is
  every infinite ordinal below alpha; the site is omega. Init is false
  at omega and at successors |". Both predecessors cite this row. This
  task uses it as the OLDEST member of the C-42 sweep's site list: the
  "false at omega" half is what `src/L/InjChain.lagda.md:104` routes
  around, what `[LJ-1.629]` re-measured at the bill's site, and what
  `no-ω-site` re-measures here. Three independent measurements of one
  order fact, and the sweep's count says there is no fourth site.
- **`archive/dev/JOURNAL.md` DECLINED.** `archive/dev/JOURNAL.md:1`:
  "# ARCHIVED 2026-08-20". A retired journal. The facts this task used
  are in the live task directories, in `src/` and in the dispatch index
  above, all of which the sweep read directly.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired
  route". The retired route's journal measures nothing about `Init` at
  the split's above-omega half.
- **`archive/dev/TASKS-archived.md` DECLINED.**
  `archive/dev/TASKS-archived.md:1`: "# Archived task index: the
  `L3.32-T` series". A closed task index from another series. This
  task's predecessors are `[LJ-1.629]` and `[LJ-1.635]`, both live in
  `agents/tasks/`.
- **`dev/ARCHIVE.md` DECLINED.** `dev/ARCHIVE.md:1`: "# ARCHIVE.md: the
  archive registry". No module was retired by this task, so the registry
  was not used. W4 above says the same.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:413`: "|L_α| = |α| for α ≥ ω
  (`dev2.txt:117`, `dev2.txt:200-240`) is consumed at". This is the
  classical arithmetic behind conjunct 4's TRUTH at an infinite cardinal
  site, and it is why this task states conjunct 4 as a hypothesis rather
  than as a doubt: the conjunct is true at every site of the above-omega
  half, and what the campaign owes is its SUPPLY. The sweep's finding is
  about that supply and not about the truth.
- **`dev/literature/devlin-II5.md:502` ALSO READ.** "| 5.5-5.6: P(κ) ⊆
  L_{κ⁺}, GCH | 13.20: P^L(ω_α) ⊂ L_{ω_{α+1}}, |L_{ω_{α+1}}| = ℵ_{α+1}
  (`jech13.txt:762-779`) | AGREES |". `[LJ-1.635]` used this row to show
  the textbook runs ONE uniform argument indexed by α and does not split
  at ω. This task is the above-omega half of that split, so the row is
  the reason the half exists as a separate object at all.
- **`dev/literature/truncation-and-selection.md` DECLINED.**
  `dev/literature/truncation-and-selection.md:1`: "# Truncation and
  selection: how the two literatures pick a witness". This task picks no
  witness. `c4-from-min` consumes a truncated `∥ sq β ∥₁` through
  `PT.rec` into `Empty.⊥`, which is a proposition, so no selection
  question arises.
- **`dev/literature/terms-2026-08.md` DECLINED.**
  `dev/literature/terms-2026-08.md:1`: "# The terminology dossier:
  fourteen renderings for the owner's ruling". No terminology question
  arose; this task used the tree's own names throughout.
- **`dev/literature/digest.md` DECLINED.** `dev/literature/digest.md:1`:
  "# Digest: the orthodox form of the rud route, pinned from the
  collected literature". No rud-route question arose; the task composes
  four conjuncts of `Init`.
- **`dev/literature/geology.md` DECLINED.**
  `dev/literature/geology.md:1`: "# Geology dossier: set-theoretic
  geology sources and the five questions". No layering or inner-model
  question arose.
