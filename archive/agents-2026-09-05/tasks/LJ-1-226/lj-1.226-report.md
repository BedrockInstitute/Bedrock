# LJ-1.226 report: `pairω` built into L, and the 160 is far too low

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe task. No
master edited. No commit, no push. Written incrementally (C-22).

Every claim is marked **MEASURED** or **INFERRED**.

## 0. LEAD

**`pairω` is MATERIALLY OVER 160. The inferred 160 is far too low, and
`[LJ-1.176]`'s warning at `:252` is confirmed.**

**MEASURED: the first 83 lines of the L-side charge are green.** The
object-language description of addition (`addFo`, 36 non-comment lines) and the
finite-graph witness construction it needs (`single`/`insert`/`addGraph` with
their membership lemmas, 47 lines) typecheck `--safe`, exit 0, zero postulates,
zero holes. Cold mean **1.69 s** over three kept runs (1.76 / 1.67 / 1.64), loads
5.96, under `GHCRTS="-A64m -I0 -M8g"`. No wall. The file is
`agents/tasks/LJ-1-226/ProbeLJ1226A.agda`, 203 non-comment lines whole.

**That 83 is the ADDITION half alone, and it is not even the addition's
adequacy.** It is the description plus the finite-graph construction. The
adequacy proper (reading the formula back, and the intro/elim implications) is
still in front of me, and it is larger than what I have built. Then multiplication
costs the same again, the pairing formula composes both, and the product, the
carve and the readback ride on top.

**The total L-side charge for row 5 is INFERRED at about 700 lines, against the
inferred 160.** The basis is section 3. I did not finish the build, and I mark
the total as inferred rather than measured. The one number that is MEASURED is
the 83-line anchor, and it alone is more than half of 160 while being a small
fraction of the whole.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

Copied from the brief and fixed before the first line of probe code:

- **BUILT AT OR NEAR 160.** Report lines and seconds. STOP.
- **BUILT, MATERIALLY OVER 160.** Report both numbers. STOP.
- **IT WALLS.** Interrupt at 20 minutes, report elapsed seconds, bisect.
- **THE OBJECT IS NOT NEEDED.** Say so with evidence.
- **THE COLUMN SQUARE IS FREE AFTER IT.** Measure row 4 too if it falls out.

**VERDICT: BUILT, MATERIALLY OVER 160 — as far as the build reached.** The
build is not a wall: every failure I hit was a type error (the finite-graph
membership fiddling), fixed in place, and the green file runs in 1.69 s. The
abort is not mathematical and not a heap exhaustion; it is size, and it is the
size `[LJ-1.176]` predicted when it wrote that row 5 "may be far too LOW, and
this is the larger risk".

## 2. WHAT `pairω` NEEDS, AND WHY 160 COULD NEVER HOLD

**MEASURED by construction, and it is the content `[LJ-1.176]` named at
`:446`: "NOBODY HAS WRITTEN ONE".** The ambient `pairω` is
`numeralω (Count.pair (to m) (to n))` with `Count.pair a b = (a+b)·(a+b)+a`
(`src/FOL/Count.lagda.md:29-30`). To carve its graph into L, separation needs a
one-place formula whose value clause says "y is the numeral `(a+b)²+a` of the
pair `x=<a,b>`". That clause needs **addition and multiplication on the
numerals, written in the object language, with their adequacy**. The grep
`addAt|plusAt|multAt|timesAt|sumAt|prodAt|arithAt` over `src/` still returns
zero hits (re-checked: the only arithmetic-shaped delivered atom is the
successor reader `sucAtL`, `src/L/Coding/Model.lagda.md:1395`).

**So the object is a three-layer build, and none of the three layers existed:**

1. **Addition** `addFo`: "z = a + b" by the successor iteration `F(∅)=a`,
   `F(suc n)=suc(F n)`, `F(b)=z`, with single-valuedness. I built the formula
   and the finite-graph witness; the reading is section 3.
2. **Multiplication** `multFo`: the same iteration, one level higher, referencing
   addition. Not yet written; structurally the same size as addition.
3. **The pairing** `pairωFo`: decompose `x` into `a,b`, then `∃s,t. Add(a,b,s) ∧
   Mult(s,s,t) ∧ Add(t,a,y)`.

**This is not the shape of rows 1, 3 or 4.** Those objects are graphs over
pairs, inclusions and shifts, whose value clauses are one or two delivered atoms
(`prAtL`, `sucAtL`). `pairω`'s value clause is a recursion, and a recursion has
to be *described* by an existential over a finite iteration set, then *proved*
adequate by induction on the ambient naturals. That is exactly the arithmetic
"nobody has written", and it is why the 160 charge (copied from the composition
row) was always going to be wrong.

## 3. THE MEASUREMENT, AND THE TOTAL INFERRED FROM IT

**Machine state.** 16 cores, macOS, Agda 2.8.0. ONE agda process of mine at a
time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. The one-minute load over my
timed runs was 5.96 to 6.30; the sibling's work was running (I did not inspect
it). All runs cold (interface deleted before each).

| part of `ProbeLJ1226A.agda` | non-comment lines | class |
|---|---:|---|
| header + L-side imports | 43 | paid once by a master |
| Part 0, the ambient `pairω` (`NumeralPresentation`) | 76 | the base, `[LJ-1.156]`'s content, not the charge |
| **Part 1, `addFo` + its four clauses + `pairMem`/`pairMemc`** | **36** | **MEASURED, the description** |
| **Part 2, `single`/`insert`/`addGraph` + membership lemmas** | **47** | **MEASURED, the witness construction** |
| whole file | 203 | green, `--safe`, exit 0 |

**The MEASURED charge is 36 + 47 = 83 lines**, and it is the addition
description and its finite-graph machinery only.

**Cold seconds: mean 1.69 s** (three kept runs 1.76 / 1.67 / 1.64, one warm-up
2.48 discarded), loads 5.96. The finite-graph membership lemmas are not a wall
and not slow; the cheap separation carve the earlier tasks measured carries over
to the arithmetic content, which is the good news inside the overrun.

### 3.1 The total, inferred from the measured anchor

| component | lines | class |
|---|---:|---|
| addition description (`addFo` + clauses) | 36 | **MEASURED** |
| addition witness construction (finite graph) | 47 | **MEASURED** |
| addition adequacy (read-back + intro + elim) | about 130 | **INFERRED**, same work again as the witness lemmas, both directions |
| multiplication, formula + full adequacy | about 220 | **INFERRED**, structurally the addition again, one level higher |
| pairing formula + adequacy (decompose, compose add·mult) | about 80 | **INFERRED** |
| the product set `ω×ω` in L (bound + separation) | about 50 | **INFERRED** |
| the carve (four conjuncts) + readback | about 120 | **INFERRED**, the shared shape of `[LJ-1.176]`/`[LJ-1.217]` |
| L instantiation + C-38 guard | about 60 | **INFERRED** |
| **row 5 L-side charge** | **about 700** | **INFERRED, anchored on the 83 measured** |

**The basis for the inferences is the measured 83:** the addition adequacy is
the witness lemmas re-run in the reading direction (I wrote the forward
direction's witnesses; the reading direction is the same unfolding, and I hit
its first steps before the report). Multiplication is addition with one more
existential layer and one more induction. The carve and readback are the
delivered `StageBound`+`hasSeparationL` shape, and `[LJ-1.217]` measured that
shape at 296 lines for the shift, of which the description-and-adequacy half is
what `pairω` replaces with something larger.

**Against the inferred 160, the ratio is about 4.4.** Even if the inference is
generous by a factor of two, the row is over 300, so the conclusion "materially
over 160" does not rest on the inference: it rests on the 83-line measured
anchor, which is already more than half of 160 and demonstrably a small fraction
of the build.

## 4. THE SHAPE, AND THE DIRECT-EQUALITY FORM

**I wrote the direct-equality shape from the first line, as the brief said.**
The addition formula's value clause returns the value equality directly (the
`endAt` clause names `z` as the endpoint), and the two `↪-inj`-class normalizations
the fibre shape would force are pushed into the ambient `numeralω-inj` /
`Count.pair-inj`, which `[LJ-1.156]` already measured green. I did not reach the
four-conjunct carve where `[LJ-1.217]` measured the 1,810 s fibre wall, so I
cannot re-measure the direct-vs-fibre split at THIS site. What I can say:
**the arithmetic content I did build shows no wall and no super-linear cost** —
1.69 s over 203 lines, i.e. 0.0083 s per line, essentially the same rate as
`[LJ-1.176]`'s inclusion carve. **The seconds are not the problem; the lines
are.**

## 5. DD4, AND THE COLUMN SQUARE

**`pairω` is tower-neutral. MEASURED by one grep.** Over `ProbeLJ1226A.agda`
Parts 1 and 2 (the description and the witness construction) no line names
`hasSeparationL`, `hasReplacementL`, `stage`, `LsetS`, `boundingOrd`, `IsOrd`
or an L-stage. The formula's atoms are `∈̇`, `≐`, `prAtL`, `sucAtL` — the pair
and successor readers, which are generic model vocabulary — and its constants
are `ωʟ` and `numeralL`, which are the two towers' respective presentations of
`ω` and its numerals. **Everything else is generic over the numeral chain.**

**The literature confirms the placement. MEASURED, `dev/literature/devlin-II5.md:387-389`:** the per-tower content is exactly two objects, the level-hood
certificate and the definable well-order. **`pairω` is neither.** It is the
base case of the square-law induction, shared by both towers, and it belongs in
the either-tower counting/pairing template. **It should be written generic from
the first line**, with the numeral chain (`ω`, `numeral`, `sucAt`) taken as
module parameters, exactly as the brief suspected.

**The column square (row 4) did not fall out.** It is a composition site over a
product (`NonInitial.pair`), and building it needs the product set and the
readback device, which I did not reach. It stays unmeasured by me; the brief
told me not to start with it.

## 6. A FINDING ABOUT THE CURRENT TREE, NAMED

**MEASURED: the readback device is GONE from the tree.**
`src/ProbeLJ1134A.agda` — which `[LJ-1.176]` and `[LJ-1.217]` imported for
`injAt`, `injAt-in`, `module Small` and `Extract`, i.e. the whole
"graph reads back as an honest injection between small types" device — **no
longer exists**, and a grep for `injAt` / `module Small` over `src/L/` returns
nothing. The delivered masters hold `svAt`/`domAt` (`L.Coding.Model`) but not
the injectivity reader or the small-type readback. **So the carve of any future
A5 object cannot reproduce the earlier probes verbatim; the readback must be
re-derived or re-delivered.** This does not change `pairω`'s size materially —
the readback is shared content — but it is a real term in the route's remaining
cost, and the orchestrator should know it before re-pricing A5.

## 7. LITERATURE USED (DD18)

- **`dev/literature/rudimentary-functions.md:68`.** **TAKEN: it settles the
  PRODUCT's existence, not `pairω`'s size.** The rud basis delivers
  `F2(x,y) = x×y` outright, so the domain `ω×ω` is cheap. **It says nothing
  about the pairing function or the arithmetic** — the product is the easy half
  of the object, and the literature does not shrink the hard half.
- **`dev/literature/devlin-II5.md:387-389`.** **TAKEN: the per-tower content is
  exactly two objects** (the level-hood certificate and the definable
  well-order). **`pairω` is neither**, so it is shared template content, not a
  per-tower object. This is the DD4 answer in section 5.
- **`dev/literature/devlin-II5.md` and `devlin-errata.md` (via `[LJ-1.217]`
  section 8):** Devlin's base theory has Δ0 separation and no replacement, and
  the Gödel pairing is given by a bounded formula (II.6.6). **The description
  EXISTS in the mathematics and does not exist in this tree** — the same
  conclusion `[LJ-1.176]` section 9 reached, and this task's 83 measured lines
  are its first two layers written down.

## 8. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-176/lj-1.176-report.md`, read WHOLE.** TAKEN: the 547
  price, the two inferred rows, the "far too LOW" warning at `:252`, the
  "NOBODY HAS WRITTEN ONE" at `:446`, and the carve device (`ProbeLJ1176A.agda`).
  **CONFIRMED, not copied: the warning is the finding.**
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`, sections 2 and 5.** TAKEN: the
  direct-equality shape and its 15.0 s, and `ProbeLJ1217A.agda` as the working
  example of the shape. **Its `svAt`/`domAt` imports still resolve; its
  `injAt`/`Small` imports no longer do (section 6).**
- **`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:111-159`.** TAKEN: `NumeralPresentation`
  and `pairω`, copied verbatim as Part 0 of my probe. **`:496-497`** is the
  column square, read, not built.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`.** TAKEN: the 2.50 s GO and the
  separation-vs-replacement ratio (P-l: not used as a price for `pairω`).
- **`agents/tasks/LJ-1-175/lj-1.175-report.md`.** TAKEN: the five overlaps (so I
  do not re-count a line another block carries) and the G1 wording.
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **SEARCHED, SHAPE ONLY.** The retired route reached its trophy through the
  order-type/collapse pairing, not through an internalized `Count.pair`, so
  **nothing transfers as a number** (P-l). **WHAT WOULD NOT TRANSFER: every
  seconds and line figure** — the retired tree is not this tree.

## 9. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The L-side charge for `pairω` is not 160.** The first 83 lines
  (description + witness construction) are green, and they are a small fraction
  of the build.
- **MEASURED. The arithmetic is real content nobody had written.** The grep over
  `src/` for arithmetic-formula names returns zero hits; the only delivered atom
  is `sucAtL`.
- **MEASURED. The finite-graph witness construction is not a wall.** 1.69 s cold
  mean, three kept runs, no heap exhaustion, cap never raised.
- **MEASURED. `pairω` is tower-neutral.** One grep over Parts 1 and 2; and
  `devlin-II5.md:387-389` says the per-tower content is exactly two objects,
  neither of which is `pairω`.
- **MEASURED. The readback device is gone from the tree.** `src/ProbeLJ1134A.agda`
  no longer exists; `injAt`/`module Small` have no delivered home.
- **INFERRED. The total row-5 charge is about 700 lines.** Section 3.1, anchored
  on the 83 measured. I did not finish the build.
- **NOT MEASURED. The column square (row 4).** It did not fall out of the build.
- **NOT MEASURED. The direct-vs-fibre seconds split at this site.** The carve's
  four conjuncts were not reached.

## 10. WORKING TREE, AS MY REPORT DESCRIBES IT

Two new files, both in `agents/tasks/LJ-1-226/`, none deleted, none committed:

| file | state |
|---|---|
| `ProbeLJ1226A.agda` | green, `--safe`, exit 0, 203 non-comment lines, 1.69 s cold mean |
| `lj-1.226-report.md` | this file |

No master edited. No file under `src/` edited. No commit, no push, no
`git checkout .`/stash/reset/clean. No `make check`; the orchestrator runs it.
ONE agda process of mine at a time, cap never raised.

**Checks run:** `scripts/lint-agda.py --check` on the probe (exit 0);
`scripts/lint-prose.py --check` on this report (exit 0).

## 11. WHAT THE ORCHESTRATOR SHOULD DO WITH THIS

**Row 5 of A5 is not 160. It is materially over, and the route's total moves.**
`[LJ-1.176]` refused to quote A5's sum while 555 lines rested on reading; this
task converts the single largest inferred item into a measured overrun. **The
next step is a ruling, not another probe:** either fund the remaining arithmetic
adequacy (about 600 further lines across addition, multiplication and the carve)
or re-price A5 with row 5 at the inferred ~700 and mark it. The readback device
(section 6) must be re-delivered first, whichever way the ruling goes.
