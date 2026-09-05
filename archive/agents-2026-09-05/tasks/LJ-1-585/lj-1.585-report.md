# [LJ-1.585] Are rows 1 and 4 the same missing formula?

**THE ANSWER IS NO, AND THE BRIEF ASKED ME TO MEASURE IT AND NOT TO AGREE.**
The two type signatures are not one object. They are not even two objects at two
pairs: they are two objects at THREE pairs, and section `THE TWO PAIRS` below
names each one at `file:line`.

**THE OBLIGATION IS INHABITED.** `one-formula-two-rows`
(`agents/tasks/LJ-1-585/Probe585.agda:444-454`) is the brief's second form: "the
term that says which and why". The witness meter resolves it, 0 UNRESOLVED of 1,
11.86 s.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`runs/final-1.out` to
`runs/final-3.out`). It carries NO hole and NO postulate under `--safe`, so
every row in it is a measurement. Nothing landed in `src/`. No formula was
built. Neither row was built. `Def` is a hypothesis from the first line to the
last.

**READ THE `go` BRANCH WITH THIS SENTENCE BESIDE IT.** The brief says "A GO
MEANS `[LJ-1.584]` PAYS TWO ROWS AND THE BILL DROPS TO THREE". The obligation is
delivered, so the meter reads -1 and the row matches. **THE BILL DOES NOT DROP
TO THREE.** One payment clears one row at most, and the row it clears is not
row 4 either.


## W3, WRITTEN FIRST AND TYPECHECKED ALONE

`agents/tasks/LJ-1-585/runs/W3.agda`, TYPE ONLY, two runs, exit 0:
`runs/w3-1.out` (COLD, 130.82 s, 2,921,021,440 bytes peak RSS) and
`runs/w3-2.out` (WARM, 3.34 s).

**THE TWO STATEMENTS DO SIT IN ONE FILE. THE PRICE IS THAT THE FILE CARRIES TWO
PARAMETER SETS AND NEITHER STATEMENT USES THE OTHER'S.** Row 4 lives at
`{ℓ} (lem)` alone (`agents/tasks/LJ-1-523/Probe523.agda:15`). The hypothesis
drags `L.StageCardinal`'s three parameters α₀, oα₀ and sq
(`src/L/StageCardinal.lagda.md:15-19`). Row 1's residue drags
`Devlin55.BoundedSubsetAt`'s seventeen (`src/L/BoundedSubset.lagda.md:1385-1395`)
plus `Co`'s two (`:1555-1558`).

The brief estimated about 20 lines and under 2 minutes. The slice is 130 lines
and 130.82 s cold. **The overrun is the finding and not an overrun of the
estimate's shape**: the residue cannot be NAMED without the whole site
telescope, and writing that telescope is most of the file.


## THE TWO PAIRS

The brief asked for two. **THERE ARE THREE, AND THE THIRD IS THE ONE THE BRIEF'S
READING NEEDED.**

| # | What | The pair | Evidence |
|---|---|---|---|
| 1 | Row 4, `StageCountedCoded` | `(Lset d , d)`. ONE ordinal, twice | `agents/tasks/LJ-1-523/Probe523.agda:258-261`, measured at `Probe585.agda:110-112` |
| 2 | Row 1's residue, `Leg2Coded` | `(Lset β , α)`. TWO ordinals | `agents/tasks/LJ-1-580/Probe580.agda:296-297`, identified at `:311-317`, re-ascribed at `Probe585.agda:364-367` |
| 3 | The site's own `stage-card-upper` | `(Lset α , α)`. ONE ordinal, twice, and it is α | `src/L/BoundedSubset.lagda.md:1512-1513`, measured at `Probe585.agda:358-359` |

**THEY DO NOT UNIFY, AND THE ELABORATOR SAYS SO IN ONE LINE.**
`row1-at-the-diagonal-is-row4` (`Probe585.agda:135-137`) is `refl`: row 1's shape
at `a := b` IS row 4's shape. So the two shapes agree EXACTLY when the two
ordinals agree, and nothing weaker does it.

**AND THE SITE BINDS β AND α SEPARATELY.** β is `Cn.condenses .fst`
(`src/L/BoundedSubset.lagda.md:1562-1563`), α is the module's own parameter
(`agents/tasks/LJ-1-580/Probe580.agda:121`). The site delivers `β ∈ κ`
(`src/L/BoundedSubset.lagda.md:1594`) and `α ∈ κ`, and NO relation between the
two. `beta-is-not-alpha-by-any-row-of-the-site` (`Probe585.agda:336-338`) is
those two memberships and nothing more. That is everything the site knows about
the two ordinals together.

**THE THIRD PAIR IS WHERE THE BRIEF'S READING BREAKS.** `stage-card-upper` is
the ambient injection the brief names, and at the site it is applied at ONE
argument, which is α: `code-inj = comp-inj absorbs (stage-card-upper α ...)`
(`src/L/BoundedSubset.lagda.md:1512-1513`). So the ambient injection at the site
is `⟪ Lset α ⟫ ↪ ⟪ α ⟫` (`Probe585.agda:358-359`), and the residue asks for
`(Lset β , α)`. The ambient object the brief calls "the same object" is at the
diagonal, and the residue is not.

**AND THE TOWER IS NOT THE SAME TOWER EITHER.**
`Devlin55.BoundedSubsetAt` builds its own `L.StageCardinal` at ITS α
(`src/L/BoundedSubset.lagda.md:1397`), so the site's `stage-card-upper` takes
`γ ∈ sucV α`. The hypothesis of this task is stated at α₀, this file's own tower
parameter. `site-tower-is-alpha` (`Probe585.agda:347-350`) is that type,
ascribed. **`Def at stage-card-upper` at α₀ is not even ABOUT the function the
site applies.**


## HOW MANY ROWS ONE FORMULA BUYS

**ONE AT MOST, AND NOT ROW 4.** Never two.

### Row 4: bought only in the restricted form

`def→row4-restricted : DefAtSCU → Row4Restricted` (`Probe585.agda:172-173`).
That is the implication's name. It is not new work: it is
`[LJ-1.568]`'s `no-free-lunch-at-B9` (`agents/tasks/LJ-1-568/Probe568.agda:454-463`)
at `H := Def`, IMPORTED.

`Row4Restricted` (`Probe585.agda:163-166`) is row 4 with `stage-card-upper`'s own
two side conditions, `δ ∈ sucV α₀` and `δ ∉ ω`
(`src/L/StageCardinal.lagda.md:564-566`), and with nothing else changed. **THE
HYPOTHESIS CANNOT BE STATED MORE WIDELY THAN THE FUNCTION IT IS ABOUT.** Where
the two conditions fail, `stage-card-upper` has no value, so `Def` at it has no
statement.

### And the restricted form is not row 4

`StageCountedCoded` carries no side condition. It quantifies over EVERY
`δ : SL.S` with `IsOrd (fst δ)` (`Probe523.agda:258-261`).

- One direction holds and it is the cheap one: `full→restricted`
  (`Probe585.agda:188-189`).
- The other direction needs the two conditions at every ordinal:
  `restricted+conditions→full` (`Probe585.agda:194-205`). That term is the price,
  written out, with the two transports as `Σ≡Prop` over `isL`.
- **AND THAT PRICE IS NOT PAYABLE.** `side-conditions-are-false`
  (`Probe585.agda:219-226`) refutes the supply at δ := 0, from `#∈ω`
  (`src/L/Ordinal.lagda.md:248-249`), which puts every numeral IN ω.

**WHAT THAT DOES AND DOES NOT SAY.** It does NOT refute row 4. It says that
`Def at stage-card-upper` does not reach row 4 by this route, because the
hypothesis is not even STATED at a finite δ. `[LJ-1.533]` says in its own words
that it "did not prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ"
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55`), and this file
does not prove it either.

### Row 1's residue: not bought, and what stands in the way is named

Two rows, both at ANY pair of L-ordinals, so neither is an accident of the site:

- `row4+gap→row1` (`Probe585.agda:245-257`). Row 4 at b, PLUS a code for
  `b ↪ a`, gives row 1's shape. `Comp` (`src/L/InjChain.lagda.md:314-433`),
  IMPORTED.
- `row1→gap` (`Probe585.agda:267-279`). Row 1's shape gives the code for
  `b ↪ a` back, with NO row 4 at all, because `b ⊆ Lset b` is an inclusion
  (`src/L/StageCardinal.lagda.md:193-195`) and `InclGraph`
  (`src/L/InjChain.lagda.md:575-598`) codes those.

**SO ROW 1's RESIDUE IS NOT A SECOND INSTANCE OF ROW 4. IT IS ROW 4 COMPOSED
WITH `[LJ-1.580]`'s OWN UNPAID OBLIGATION, AND IT IMPLIES THAT OBLIGATION ON ITS
OWN.** At the site: `row4-in-full-still-wants-the-gap`
(`Probe585.agda:410-413`) takes row 4 IN FULL and still asks for the gap.
`the-two-routes-have-one-type` (`Probe585.agda:418-420`) pairs this file's
general route with `[LJ-1.580]`'s own `leg2-coded→at-β`
(`agents/tasks/LJ-1-580/Probe580.agda:245`), so the general rows are not
neighbours of the site's statement.

`gap-is-580s-obligation` (`Probe585.agda:386-389`) is `refl`:
`BetaIntoAlphaCoded` is the gap with the ambient injection to its left.

**THE HONEST BOUNDARY, AND I STATE IT BECAUSE THE BRIEF ORDERED ME NOT TO READ A
DISCHARGE INTO ANYTHING I DID NOT INHABIT.** This file does NOT prove
`Def at stage-card-upper → row 1's residue` false. What it proves is that a term
of that type would discharge `InjL βᴸ αᴸ`, which is `[LJ-1.580]`'s obligation,
through `row1→gap`. `[LJ-1.580]` measured that the route through `β↪α` cannot
deliver it, because that route computes through `absorbs`
(`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40`). **A proof of row
1's residue is therefore not a corollary of anything about row 4. It is a new
producer of a code at an off-diagonal pair.**


## W2, ANSWERED

The brief did not state W2. I answer it because the slot file requires the
answer in the return.

**W2 IS KEPT AND IT IS THE FILE'S SHAPE.** The mathematics is written ONCE at a
generic carrier. `Row4Shape`, `Row1Shape` and `Gap` are stated at an arbitrary
pair of L-ordinals (`Probe585.agda:122-129`), and the two implications hold
there (`Probe585.agda:245-257`, `:267-279`). Section 4 (`Probe585.agda:296-420`)
instantiates. Nothing in the generic half mentions the bounded-subset site, and
nothing in section 4 restates a statement of the generic half.


## WHAT THE STATEMENT COST, AND WHAT RESISTED

- **THE FRAME COST MOST OF THE FILE.** 454 lines, of which the obligation is 11
  (`Probe585.agda:444-454`) and the site telescope is 22
  (`Probe585.agda:296-309` and `:314-321`). The brief estimated about 130 lines with about 30
  for the obligation. The obligation is SMALLER than the estimate and the file is
  3.5 times bigger, and both numbers have the same cause: the residue cannot be
  NAMED without `Devlin55.BoundedSubsetAt`'s nineteen parameters.
- **ONE RED RUN AND IT WAS SCOPE, NOT MATHEMATICS.** `runs/red-1.out`, exit 42,
  `[NotInScope] C580.αᴸ`. `αᴸ` is bound in `Site` and not in `CoAt`
  (`agents/tasks/LJ-1-580/Probe580.agda:140-141`). One `sed` fixed it.
- **NOTHING ELSE RESISTED.** No transport failed, no universe rose, no `refl`
  was expensive. `[LJ-1.580]` measured that a `refl` across the hull costs 96
  seconds (`agents/tasks/LJ-1-580/Probe580.agda:187`); this file writes
  no such `refl`, and its two `refl`s (`Probe585.agda:137`, `:389`) are both at
  the level of type formers.
- **I WEAKENED NOTHING.** The obligation is the brief's own second form, and the
  brief offered it.

## WHAT I COULD NOT CLOSE

1. **I did not refute `Def at stage-card-upper → row 1's residue`.** See the
   honest boundary above. I measured what such a term would discharge.
2. **I did not price row 4's truth at a finite δ.** `[LJ-1.533]` left it open
   and this file leaves it open. It is now the sharper question, because
   `side-conditions-are-false` (`Probe585.agda:219-226`) proves the formula
   route cannot reach those δ at all.


## ONE THING THE NEXT BRIEF SHOULD KNOW, AND IT IS A DEFECT IN A PREDECESSOR

`[LJ-1.580]` says "`grep -rn "isL (Lset" src/` returns nothing, so this shape is
not in the tree" (`agents/tasks/LJ-1-580/Probe580.agda:98-99`) and rebuilds it
as `Lset-isL` (`:104-109`). **THE SHAPE IS IN THE TREE AND IT LANDED ON
2026-07-25.** `isL-Lset : (β : V ℓ) → IsOrd β → ⟨ isL (Lset β) ⟩` is at
`src/L/Axioms/Basic.lagda.md:156`, wrapped as `LsetS` at `:160-161`, and
`git log -L 156,157:src/L/Axioms/Basic.lagda.md` names commit `711c151e`,
`[L3.0.1]`, dated 2026-07-25. `grep -rn "isL (Lset" src/` returns that line
today. This file uses `LsetS` throughout and `shape-is-the-residue`
(`Probe585.agda:374-381`) is the one line that reconciles the two proofs, which
agree because `isL` is an hProp.


## RUNS

| Run | What | Result | Peak RSS (bytes) |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, TYPE ONLY, typechecked ALONE as ordered, COLD | GREEN, 130.82 s | 2,921,021,440 |
| `runs/w3-2.out` | the same file, WARM | GREEN, 3.34 s | 735,526,912 |
| `runs/red-1.out` | the probe, first attempt | RED, exit 42, `[NotInScope] C580.αᴸ` | 860,078,080 |
| `runs/final-1.out` | the file as it stands, interface removed | GREEN, 15.50 s | 2,580,774,912 |
| `runs/final-2.out` | the same file, interface removed again | GREEN, 16.81 s | 2,580,348,928 |
| `runs/final-3.out` | the same file, WARM | GREEN, 3.71 s | 712,458,240 |

CALIBER. `GHCRTS="-A64m -I0 -M8g"`, set by the program on this pane. I did not
set it. One Agda process at a time. No heap wall.

The witness meter: `witness.py --brief agents/tasks/LJ-1-585/LJ-1.585.md`,
0 UNRESOLVED of 1, 11.86 s, `probe_red=False`.


## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED.** Line 379:
  `| LJ-1.324 | Transplant stage-card-upper | REFUTED, THE FIRST INGREDIENT IS THE GOAL. DD25 review not needed: it closes a lead and funds nothing | The generic engine survives, tower-blind |`
  This is the campaign's earlier measurement that `stage-card-upper` does not
  move to a new site by transplant, and "tower-blind" is the same fact this task
  re-measured at `Probe585.agda:347-350`: the site builds its own tower.
- `archive/dev/JOURNAL.md`. **NOT READ.** Declined. `grep -n` for
  `StageCounted`, `stage-card`, `InjL`, `B9`, `1.533` and `1.523` returns
  nothing in its 1,378 lines, and the Boundary says a live document carries no
  history, so a journal cannot carry a type.
- `archive/dev/JOURNAL-archived.md`. **NOT READ.** Declined. The same grep
  returns two hits, both of them the digit string `1533` inside a token count
  (`:3024`, `:3117`), and neither is about this task's objects.
- `dev/ARCHIVE.md`. **NOT READ.** Declined. The same grep returns nothing in its
  299 lines. This task retires no module, so W4 has no work here.
- `archive/dev/DD-archived.md`. **NOT READ.** Declined. 38 lines, and the same
  grep returns nothing. The `DD` series is set aside in this form by amendment
  A7.


## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED, AND IT CONFIRMS THE
  MEASUREMENT.** Line 281: `(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact`
  and line 282: `|γ| = |α| < κ with κ a cardinal implies γ < κ (\`dev2.txt:1372-1384\`).`
  **THE CLASSICAL ARGUMENT GETS `|γ| = |α|` AND NOT `γ = α`.** It then uses
  `γ < κ` to place `L_γ ⊆ L_κ`. That is the same two-ordinal shape this task
  measured at `Probe585.agda:333-338`, from the other side. Line 413 also states
  the size equation for `α ≥ ω` only: `|L_α| = |α| for α ≥ ω (\`dev2.txt:117\`, \`dev2.txt:200-240\`) is consumed at`.
  **THE CLASSICAL STATEMENT CARRIES THE INFINITY CONDITION THAT ROW 4 DROPS**,
  which is what `side-conditions-are-false` (`Probe585.agda:219-226`) prices.
- `dev/literature/truncation-and-selection.md`. **READ AND USED, ONE LINE.**
  Line 72: `### 1.5 The classical conclusion is proposition-valued, and this matters`.
  `InjL` is a truncated `InjCode` (`src/L/GCH.lagda.md:37-38`), so both
  compositions of section 3 are `PT.map` and `PT.map2`
  (`Probe585.agda:248`, `:270`) and neither needs a choice. The file's rule is
  why that is free here.
- `dev/literature/digest.md`. **NOT READ.** Declined. It pins the orthodox form
  of the rud route. This task is inside the `Def` tower and takes no position on
  the crossing.
- `dev/literature/geology.md`. **NOT READ.** Declined. Set-theoretic geology is
  `[L6]`'s corpus and has no bearing on a coded injection at one pair.
- `dev/literature/level-formula-slot-roles.md`. **NOT READ.** Declined. This
  task writes no formula and numbers no variable. `Def` is a hypothesis
  throughout, and the brief forbade building the formula.


## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT FUND A TASK THAT PAYS TWO ROWS WITH ONE FORMULA.** The bill stays at
   five rows.
2. **ROW 1's ROUTE NEEDS A CODE FOR AN INJECTION THAT IS NOT AN INCLUSION, AT AN
   OFF-DIAGONAL PAIR. AND `[LJ-1.580]`'s PRODUCER COUNT IS A GREP ARTEFACT.**
   That review says "`src/` has exactly TWO `InjCode` producers and both deliver
   the single shape" (`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:105`).
   Re-grepped at today's tree: `grep -rn "InjCode" src/` names
   `src/L/Absorption.lagda.md:625-626` and `src/L/CodedShift.lagda.md:51-52`,
   both at `InjCode F (sucʟ γ) γ`, and the same grep returns NOTHING in
   `src/L/InjChain.lagda.md`. **BUT `InjChain` PRODUCES CODES AND THE GREP CANNOT
   SEE THEM**, because `InclGraph` (`src/L/InjChain.lagda.md:575-598`) and `Comp`
   (`:314-433`) deliver the four conjuncts and never name the type. This task's
   own `row1→gap` (`Probe585.agda:267-279`) builds an `InjCode` out of
   `InclGraph`'s four fields at an OFF-DIAGONAL pair, and it typechecks. So the
   tree can already code an inclusion anywhere, and a composite of an inclusion
   with an existing code anywhere. **WHAT IT CANNOT CODE IS AN INJECTION THAT IS
   NEITHER.** Row 1's residue is one of those, and a diagonal stage bound does
   not become one, whatever formula pays for the diagonal.
3. **ROW 4's OWN QUESTION MOVED.** It is no longer "find the formula". It is
   "is row 4 true at a finite δ, and if not, what is row 4's corrected target".
   D-10 says to price the truth of a recorded residue before pricing its proof,
   and `side-conditions-are-false` (`Probe585.agda:219-226`) shows the formula
   route stops exactly where that question starts.
4. **`[LJ-1.584]` IS NOT AFFECTED BY THIS TASK.** This brief took its formula as
   a hypothesis and never read its value. Whatever `[LJ-1.584]` delivers, it
   buys `Row4Restricted` (`Probe585.agda:172-173`) and no more.
