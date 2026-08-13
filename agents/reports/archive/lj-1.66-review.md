# LJ-1.66 review (DD25 adversarial)

Status: COMPLETE. Written incrementally per C-22. Read-only for `src/`.
ASD-STE100. This report is `_build/lj-1.66-review.md`.
No commit, no push, no edit under `src/`.

**I RAN NO AGDA.** `LJ-1.67`'s agda process was live on
`src/L/Condensation.lagda.md` for the whole review (PID 92544, observed at
load 4.29). C-12 caps concurrency and `check-ratio.py` refuses beside a live
process. Every figure below comes from the cited reports, from the ledger,
from `git show HEAD`, or from `grep`/`awk` over the working tree. No load
average is reported, because I measured nothing.

## 0. VERDICT: SPLIT

**UPHOLD the two measured negatives. OVERTURN the conclusion drawn from
them.**

| part of the return | verdict |
|---|---|
| 1.016 s per `EnvSet` application | **UPHOLD as a decision, not as a precision figure.** The instrument under-reports and its exact value is soft, but a second, independent number in the same report corroborates the order. The 0.05 s abort line is crossed by 12x to 20x on every reading. |
| +10.88 s hoist regression | **UPHOLD.** Every confound I can find points the safe way. |
| "the applications are not hoistable without a statement change" | **UPHOLD as written.** It is a correct statement about the hoist shape that was tried. |
| **"the lever is dead"** | **OVERTURN.** One shape of the lever was tried: ADD a layer at each site. The opposite shape was never considered: REMOVE copied surface from each site. Section 4.1 gives it, with a code count, and it is the D-30 shape that measured 5.45x elsewhere in this wing. |
| **"the residual is 2.33 s"** (the campaign's framing, not the return's) | **OVERTURN.** The campaign's own recorded band is 2.33 to 3.75 s, and the bar it is measured against rests on ONE un-repeated pass with no recorded spread. Section 5. |

**The brief did NOT cause the stop.** Three separate clauses stopped it, and
the return named the statement-change cure anyway. The brief's real defect is
different and is in section 3.

**EXTENSION VERDICT on `LJ-1.67` (added after it returned): SPLIT.** Its
+2.82 s is sound and I uphold it. But its section 2 denies that it added a
module layer, and its own code shows three module applications where there
were two, so the denial is **MEASURED FALSE**. `LJ-1.67` is therefore not an
independent sixth failure: it is the **fourth measurement of one mechanism**.
The `LJ-1.67` brief prescribed that mechanism in its own words, so **that
brief did cause its outcome** (section E.2). Section E.1 gives the law the
four failures support, and it names the one class nobody has tested. Section
E.6 gives the updated standing verdict, and section E.6.1 gives the finding
that outranks the whole residual question.

---

## 1. Q1. Is 1.016 s per application sound?

### 1.1 The instrument does what the return says it does

**Does an unused module application still elaborate? YES. INFERRED**, from
Agda's semantics, at high confidence. `module E' = EnvSet ...` is a
declaration, not an expression. Agda creates one new definition for every
definition in the applied module, with the type obtained by substituting the
arguments, and it does this while checking the enclosing declaration block.
Agda performs no dead-declaration elimination. So an unused copy pays the
instantiation cost, which is the cost the probe set out to price.

**I cannot confirm the report's word "let-bound".** Section 1 of the return
says "unused let-bound module applications"
(`_build/lj-1.66-report.md:31-32`). The tree is reverted, so the spelling is
gone. Whether the copies sat in a `let` or in a `where` does not change the
conclusion above: both elaborate.

### 1.2 The direction of the error is UNDER-report, which is the safe direction

**A used application costs MORE than an unused one. INFERRED.** A used site
additionally pays conversion checking when `E'.out` meets the row's goal
type. The probe's copies pay only the instantiation half. So 1.016 s is a
**lower bound** on the marginal cost of a real site, and 18.29 s is a floor,
not a ceiling. That strengthens the return's decision rather than weakening
it.

Two further biases, both toward under-report:

- The six copies sat in **three** proof bodies, two per body, so they shared
  a local context that the eighteen real sites, spread over nine row modules,
  each establish separately. **INFERRED.**
- The copies were verbatim duplicates of the application beside them, so
  their argument expressions were re-elaborated in an identical context.
  **INFERRED**, and I know of no memoization in Agda 2.8.0 that would let
  them share elaboration with the original.

### 1.3 Three real weaknesses in the number, none of which move the decision

1. **The depth mix does not match the population. MEASURED** from the site
   list. The eighteen real sites are 2 at `{5 + m}`, 10 at `{6 + m}` and 6 at
   `{7 + m}` (verified by `grep`, section 1.5). The probe put 2 at each
   depth. It therefore over-weights `{5 + m}` (33 percent against 11) and
   under-weights `{6 + m}` (33 percent against 56). If cost rises with stack
   depth, and the `lookup` mechanism says it should, **the sign of this bias
   is not determined** and the report does not mention it.
2. **Marginal is not average. INFERRED.** The probe measured the cost of
   applications 19 to 24. The claim `18 x 1.016 = 18.29 s` requires the cost
   per application to be flat from 1 to 18. Nothing measured that.
3. **Rows are known to differ.** The campaign's own table prices a "row-level
   cure of the three hot rows" at a ~1.3 s ceiling, so rows are not uniform.
   A per-site mean taken at three host rows is not the population mean.
   **INFERRED.**

### 1.4 The corroboration the return had and did not use

The return holds a **second, independent** measurement of the same physical
quantity, and never compares the two.

The hoist added one module-copy layer at each of the eighteen sites and cost
**+10.88 s**, which is **0.604 s per site** for one layer of `EnvSet`-shaped
copies at a concrete stack (`_build/lj-1.66-report.md:94`). The probe says
one layer of `EnvSet` copies at a concrete stack costs **1.016 s**
(`:50`).

**Two instruments, different sites, different spellings, same quantity, and
they agree within a factor of 1.7. MEASURED**, by arithmetic over the
return's own table. That is the strongest single piece of support for the
1.016 s figure, and it should be in the report.

**So the honest family price is a RANGE, 10.9 s to 18.3 s, not a point.**
Every value in it is 5x to 8x the residual. The decision the number was
bought for does not depend on which end is right.

### 1.5 An error in the diagnosis that the brief corrected without knowing it

`_build/diag-dd24-residual.md:66-68` reports "33 inner module applications
inside proof bodies: `EnvSet` **15** times, AtomLeaf 4, BndLeaf 4, ImpLeaf 2,
PropAgree 2, ExistAgree 1". **Its own itemization sums to 28, not 33.**

I counted the restored working tree, band `:2720-5101`:

| applied module | count |
|---|---:|
| `EnvSet` | **18** |
| `BndLeaf` | 4 |
| `AtomLeaf` | 4 |
| `PropAgree` | 2 |
| `Leaf` | 2 |
| `ImpLeaf` | 2 |
| `ExistAgree` | 1 |
| **total** | **33** |

**MEASURED** (`awk` over `src/L/Condensation.lagda.md:2720-5101`;
`grep -c "= EnvSet"` returns 18 in the working tree and 18 at
`git show HEAD`).

So the diagnosis's headline 33 is right, its `EnvSet` count of 15 is wrong,
and it omits `Leaf`. **The brief's 18 is correct and the return's 18 is
correct.** I raise this only because the campaign treats
`diag-dd24-residual.md` as its map, and `LJ-1.65` already measured one of its
recommendations false. This is a second countable error in the same document.

### 1.6 A false finding I built and then withdrew

At 10:05 I counted 17 `EnvSet` applications and was ready to report that the
brief's 18 was wrong. It was not. `LJ-1.67` was mid-edit: the tree carried
6,400 in-fence lines and a diff stat of 978/90, against `LJ-1.66`'s
dispatch-start 6,390 and 956/79. At 10:13 `LJ-1.67` reverted and both figures
returned to 6,390 and 956/79, with 18 applications. **MEASURED** (file
mtimes, `git diff --stat`, `ledger.count`). I record the near-miss because a
count taken beside a live dispatch is a count of somebody else's tree.

**Q1 answer: the number is sound enough for the decision it was bought for,
its true value is a range of 10.9 to 18.3 s, and the campaign must stop
quoting 18.29 s as a point figure.**

---

## 2. Q2. Is the +10.88 s regression correct on its own numbers?

**UPHELD. I find no confound that could reverse the sign.**

- **Effect against spread. MEASURED.** Baseline 100.386 / 100.302 / 99.611;
  hoist 111.086 / 110.763 / 111.093. The ranges do not overlap and the gap
  between the worst baseline run and the best hoist run is 10.38 s. No
  three-run spread in this campaign approaches that: the largest recorded
  single-module spread is 1.5 to 1.7 s (`_build/lj-1.65-report.md:13-26`).
- **Load points the SAFE way. MEASURED**, and the return does not claim this
  credit. The hoist ran at load 3.6 to 4.7; the baseline ran at 3.1 to 5.7
  (`_build/lj-1.66-report.md:44-48`). The hoist ran at the **narrower and
  quieter** band, so if load biased anything it made the hoist look faster.
  The measured regression is therefore conservative.
- **One unverified item: run order.** The report does not say whether the six
  probe copies were removed before the hoist runs. If they were not, the
  correct comparator is 106.196 s and the hoist delta is +4.79 s, not
  +10.88 s. The report's own text implies removal ("the only proof-body edit
  was the module-binding spelling", `:88-90`) and negative 4 states the tree
  returned to 6,390 lines. **INFERRED that they were removed.** Both readings
  are regressions, so the verdict survives either way; only the magnitude is
  at risk.
- **Blocked runs, not interleaved. INFERRED** from the table's shape. A
  monotone drift in machine state over the session would confound blocked
  runs. A 10.88 s drift on a 100 s base is implausible, so this does not
  decide anything, but interleaving costs nothing and should be the caliber.

**Q2 answer: correct. The direction is safe against every confound I can
identify, and the +10.88 s magnitude carries one unverified assumption about
run order.**

---

## 3. Q3. Did the brief cause the stop?

**No. The clause you suspect was not load-bearing, and the return did not
miss the cure. The brief has a different defect, and it cost a measurement.**

### 3.1 The suspected clause was the third of three stops

Your DD4 section says "If a hoist forces a statement change, stop and report
it" (`_build/briefs/LJ-1.66.md:137`). Two earlier clauses already ended the
dispatch:

- "**STOP after the hoist's measurement** whichever way it goes"
  (`_build/briefs/LJ-1.66.md:95-96`).
- "**Any measured regression**: revert it and stop" (`:97`).

The hoist regressed. Clause two fired on its own. Removing the DD4 sentence
would have changed nothing.

### 3.2 The return did NOT stop one step short of the answer

It named the cure. Twice.

- Section 5: "A hoist that genuinely reduced the application count to three
  would need the rows' stack variables at module level, which is a statement
  change" (`_build/lj-1.66-report.md:119-122`).
- Negative 5: "A statement-level restructuring (moving the rows' stack
  variables into module telescopes) would recover the 18.3 s: **INFERRED, NOT
  MEASURED**" (`:152-155`).

That is your `LJ-1.67` hypothesis, written in the return, correctly
classified. The brief cost you the **price** of the move, never the idea. And
paying for that price was outside the two-measurement budget the brief set on
purpose, per D-1.

### 3.3 The brief's REAL defect: a false premise, and a GO gate that could not see it

The brief asserts a structural fact as given:

> "The eighteen applications take **three distinct depths only** ... The slot
> arguments **look identical** within each depth. **So eighteen applications
> could become three**" (`_build/briefs/LJ-1.66.md:72-76`).

Section 4 of the return measured that false: the slot numerals are identical,
the environments and the site facts are not
(`_build/lj-1.66-report.md:84-90`). **Once that is known, the hoist is known
in advance to ADD a layer instead of removing one**, which is the exact
mechanism the return then writes down at `:96-102`.

But the GO gate keyed on ONE term only: "Unit cost 0.05 s or more: attempt
the hoist" (`_build/briefs/LJ-1.66.md:95`). The gate could not see its own
premise fail. So the agent, correctly following a pre-fixed criterion,
measured a hoist whose failure was derivable from the finding it had just
made.

**The cure is a two-part gate.** A brief that funds a cure on a structural
premise must gate on BOTH the cost term and the premise:

> GO only if (a) the unit cost is 0.05 s or more AND (b) the applications
> genuinely collapse. **Verify (b) by reading the sites BEFORE you build
> anything.** If (b) fails, report which term failed and stop; that is a
> full deliverable.

**The cost of the defect: three cold runs, about 5.5 minutes of Agda plus
build time.** The consolation is real: module-application hoisting is now
measured false at two sites instead of one, and that is a finding the
campaign can cite. I call this a **modest** brief defect, not the cause of
the negative.

### 3.4 One thing the brief did right, against your own record

The brief handed the agent every prior measurement and said "Do not re-run
any of those" (`_build/briefs/LJ-1.66.md:24-37`), and it demanded MEASURED or
INFERRED on every negative. The return complied on both. Your recorded
failure mode is that briefs transmit assumptions agents cannot contradict.
Here the agent **did** contradict the brief's structural assumption, in
writing, in section 4. The classification discipline is working.

---

## 4. Q4. Cures the return missed

### 4.1 THE ONE THAT MATTERS: cut what each application COPIES

**This is the shape nobody has tried, and it is the opposite of every shape
that has failed.**

Every failed move ADDED something at the site: a seal (+1.61 s), a shared
frame (+17.23 s), an alias (+3.29 s), a depth frame (+10.88 s). The move
below REMOVES content from the site.

**The code fact, MEASURED** (`src/L/Condensation.lagda.md:2761-2900`, by
`grep`). `EnvSet` exports **sixteen** definitions:

`φB`, `φ`, `app3`, `app3'`, `app2`, `bnd→over`, `over→bnd`, `out`, `back`,
`memE-bnd`, `memE-at`, `t0eq`, `t1eq`, `t0K`, `keyK`, `num1K`.

A module application copies **every one of them** at the site's arguments.

**What the eighteen sites actually use, MEASURED**
(`grep -oE "E'\.[a-zA-Z0-9'→-]+"` over the whole master):

| export | uses |
|---|---:|
| `E'.out` | 9 |
| `E'.back` | 9 |
| `E'.memE-bnd` | 9 |
| **every other export** | **0** |

**Three of sixteen exports are reached. Thirteen are copied eighteen times
and used never.**

That is D-30 exactly (`dev/LESSONS.md:3255`): "look for sections with NO
consumer at all ... they cost their full check time and return nothing". D-30
measured **5.45x on seconds** by that move, on `src/L/StageCardinal` in this
same wing, and the report notes "One module decided the wing"
(`dev/LESSONS.md:3268-3280`). D-30 was applied to a whole module. **It has
never been applied INSIDE an applied module.**

**The shape.** Keep the implementation in a module that no site applies, and
give the sites a thin face carrying only the three reached definitions:

```agda
module EnvSetImpl {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : ...) (arSubK : ...) (envInK : ...) where
  -- φB, φ, app3, app3', app2, bnd→over, over→bnd, t0eq, t1eq,
  -- t0K, keyK, num1K, memE-at  ... unchanged

module EnvSet {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : ...) (arSubK : ...) (envInK : ...) where
  out      = EnvSetImpl.out      E ar B K γ entryK arSubK envInK
  back     = EnvSetImpl.back     E ar B K γ entryK arSubK envInK
  memE-bnd = EnvSetImpl.memE-bnd E ar B K γ entryK arSubK envInK
```

The three lines in the face are **term applications, not module
applications**, so they copy nothing. Each of the eighteen sites then copies
three definitions instead of sixteen.

**Why this is not the +10.88 s shape.** The frame added a layer *between* the
site and `EnvSet`, so each site paid for two layers of copies. This adds no
layer: the site still performs exactly one module application, and that
application has less to copy.

**Projected saving, INFERRED, and the inference is stated so it can be
refuted.** If the per-application cost scales with the number of copied
definitions, the unit falls from 1.016 s to about 3/16 of it, and eighteen
sites return roughly 14.9 s. At one quarter of that projection it still
clears the residual four times over. **This is a hypothesis about a scaling
law, not a price.**

**And it is cheap to price, with the instrument LJ-1.66 already built.** Add
N = 6 applications of the thin face at the same three depths, measure cold
three runs each side, divide by N, and compare the unit against 1.016 s. No
site is touched, no statement changes, and the answer is a ratio rather than
an absolute, so the load caveat matters less. **Abort if the thin face's unit
cost is not at least 0.3 s below 1.016 s.**

**Risks to name in the brief.**
- The three faces' types still mention `envSetB` / `envSetAt` at the site's
  stack, so the reduction those types force is NOT removed. The move prices
  the copy count, never the reduction. If the whole 1.016 s sits in three
  definitions rather than sixteen, the move returns nothing, and the probe
  above says so for the price of one measurement.
- P-h (`dev/LESSONS.md:174`) forbids turning walk parameters into function
  parameters. **This move does not do that.** Both layers stay
  module-parameterized; only the face's three bodies are term applications.

### 4.2 The other five wing modules hold nothing. MEASURED, and it closes that question

Your sub-question "does any wing module I have not examined have recoverable
mass" has a measured answer, from your own gate run
(`_build/briefs/LJ-1.64.md:26-33`):

| module | lines | seconds | rate |
|---|---:|---:|---:|
| `src/V/Collapse.lagda.md` | 335 | 0.96 | 0.0029 |
| `src/L/Hull.lagda.md` | 431 | 2.67 | 0.0062 |
| `src/V/Presentation.lagda.md` | 18 | 0.64 | 0.0357 OVER |
| `src/FOL/Count.lagda.md` | 620 | 1.65 | 0.0027 |
| `src/L/StageCardinal.lagda.md` | 475 | 2.09 | 0.0044 |
| `src/L/Condensation.lagda.md` | 6,390 | 99.45 | 0.0156 OVER |

**The five non-Condensation modules hold 8.01 s in total, against a 23.89 s
share of the ceiling. They run 15.88 s UNDER. They are the wing's subsidy,
not its cost.** Even reducing all five to zero seconds is arithmetically
impossible to exceed 8.01 s, and every second removed from them also removes
nothing from the denominator. **Do not fund a search there.**

### 4.3 Module fission: NO-GO by arithmetic. Do not spend a dispatch

Splitting `L.Condensation` looks attractive and is not. The gate sums module
**slices**, each timed cold with warm dependencies, and the ledger measured
what that costs: "the 73 AC masters timed one at a time sum to **193.85 s**
against the same tree's **133.70 s** cold ... timing modules separately
re-pays a fixed cost 73 times over, chiefly loading each module's dependency
interfaces" (`dev/ledger.toml:2579-2585`). **MEASURED.**

The wing's own table prices that floor directly: `V/Presentation` is 18 lines
and costs **0.64 s**, which `_build/briefs/LJ-1.44.md:22` calls the
"module-load floor". **Every module added to the wing costs at least about
0.6 s of pure loading and adds no lines.** `L.Condensation`'s dependency
closure is far larger than `V/Presentation`'s, so a split pays more than
0.6 s. **Fission raises the aggregate. INFERRED, from two measured figures.**

### 4.4 Adding cheap lines: legitimate, and the wiring will NOT do it

You asked whether "close 2.33 s" is the right target given the pending
wiring. The ratio does improve when cheap lines land, and that is what the
bar is designed to reward. **The arithmetic is against you.**

To close the gap by adding X lines at marginal rate r:
`X >= 2.33 / (0.012716 - r)`. At r = 0.008 it needs 494 lines; at r = 0.0104
it needs 1,000.

But the campaign has **measured** the pending wiring's class:
**0.045 to 0.047 s per line** (`_build/lj-1.62-report.md:87-88`, cited at
`_build/diag-dd24-residual.md:171-173`). That is **3.6x the bar**. At
0.046 s/line each wiring line adds 0.0333 s of overage:

| wiring lines | residual after |
|---:|---:|
| 0 | 2.33 s |
| 250 | 10.7 s |
| 500 | 19.0 s |
| 1,000 | 35.6 s |

**So "close 2.33 s" is the wrong target, but in the PESSIMISTIC direction,
not the optimistic one.** The wing's problem is not a 2.33 s residual on
delivered code. It is that the remaining work is projected to arrive at 3.6x
the bar. **The controllable quantity is the marginal rate of the work not yet
written, and no brief in this phase has set a rate budget on it.**
**Recommendation: every remaining GCH build brief carries a marginal-rate
line, "this block must land at or below 0.0127 s per in-fence line", and
reports its own rate.** That is DD24 enforced where it can still be steered.

The 0.045 to 0.047 figure is the chain's marginal class, and P-l
(`dev/LESSONS.md:2305`) says a rate does not transfer by analogy. **So the
first thing a wiring brief must do is measure its own block's rate on the
first 200 lines and stop if it exceeds the budget.**

### 4.5 On your mechanism reading, and on what LJ-1.67 has built

You asked whether your reading of the mechanism is right. **Half of it is,
and the code `LJ-1.67` wrote does not test the half that matters.**

**First, a measured law points against your reading.** P-t
(`dev/LESSONS.md:2601`) is titled "The content class follows the FORMULA, not
the carrier", and it says: "It is **not** whether the carrier is concrete or
variable. It is whether the object-language FORMULA is a built tree or a
telescope hypothesis." Its measurement is the exact move you propose: "the
campaign spent two days reading 0.297 as 'the carrier is concrete' ... and
looked for a cure by moving to a variable carrier. `[T240]` then measured a
variable carrier at 0.297 anyway." `EnvSet` builds two formula trees, `φB`
and `φ` (`src/L/Condensation.lagda.md:2770-2774`). P-t predicts that
abstracting the stack leaves the expensive object in place. **Your own
diagnosis reached the same conclusion for `PropAgree`:** "the environment is
a module VARIABLE, so P-n's 'concrete carrier' wording does not describe it;
P-t does" (`_build/diag-dd24-residual.md:85-87`).

Your counter-evidence is `[LJ-1.25]`'s 12.8x at a different site. **P-l
forbids exactly that transfer**, and you were right to buy a measurement
rather than assume. I do not overturn the hypothesis; I record that a
measured law of this repository predicts against it.

**Second, and this is the load-bearing observation.** At 10:05 I read
`LJ-1.67`'s in-flight `NegAgree`. It had built:

```agda
module NegEnv (γ' : S ^ (6 + m)) (entryK' ...) (arSubK' ...) (envInK' ...) where
  module E' = EnvSet {6 + m} zero ... γ' entryK' arSubK' envInK'
```

and then, inside the lambda in `out`:

```agda
module N = NegEnv (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) entryK (arSubK ya yc a ar c) ...
```

**That is `LJ-1.66`'s frame, moved from file scope to row scope.** The
intermediate module takes the stack abstractly; the site instantiates it at
the concrete cons-stack. The concrete substitution and its `lookup`
reductions still happen at the site, on copies of the same definitions. The
abstract layer is added, not substituted.

The counts confirm it: HEAD's `NegAgree` has **two** `EnvSet` applications at
the concrete stack, one in `out` and one in `back`
(`git show HEAD:src/L/Condensation.lagda.md`, lines 3559 and 3586). The
in-flight version had **one** `EnvSet` application at the abstract stack plus
**two** `NegEnv` applications at the concrete stack: three module
applications where there were two. **MEASURED** (`awk` over the tree at
10:05, which reported `2 NegEnv`).

`LJ-1.66` priced this shape: one added layer costs **0.604 s per site**.
**PREDICTION, INFERRED: the shape as built regresses by roughly 0.5 to
1.0 s at this row and cannot reach its 1.0 s saving gate.**

**Corroboration, and it is only that.** At 10:13 the working tree returned to
6,390 in-fence lines, diff stat 956/79, and 18 `EnvSet` applications, with
`NegEnv` gone. **MEASURED** (file mtime, `git diff --stat`,
`grep -c "= EnvSet"`). `LJ-1.67` reverted. **Why it reverted is
`LJ-1.67`'s to report, not mine to infer.**

**What would actually test your hypothesis** is what your own return named:
state the row's `out` and `back` AT an abstract stack, so that the concrete
cons-stack never appears at the row. That is the statement change. An
intermediate module does not achieve it, because the intermediate is
instantiated at the concrete stack anyway.

---

## 5. Q5. Is the residual closable, or must the owner rule?

**My answer: the residual as stated is not a firm number, and the campaign
should stop funding cures against it until the instrument is priced. That
costs about ten minutes.**

### 5.1 The residual is a band, not a point, and the campaign already knows

Four readings of the wing aggregate exist at the same 8,269-line tree:
**107.48, 108.27, 108.47, 108.90 s**
(`_build/briefs/LJ-1.64.md:32`; `_build/lj-1.63-report.md:192-194`;
`_build/lj-1.64-report.md:86`). Spread 1.42 s.

Against the 105.15 s ceiling that is a residual of **2.33 to 3.75 s**. Your
own brief said so: "take the residual as 2.33 to 3.75 s"
(`_build/briefs/LJ-1.64.md:36-38`). **The 2.33 s in the brief you gave me is
the lowest of four readings, quoted as a point.** MEASURED.

### 5.2 The BAR rests on one un-repeated pass, and nobody has priced its spread

The bar is `ac_baseline_module_rate x tolerance = 0.011057 x 1.15 =
0.012716` (`dev/ledger.toml:2590`, `:2810`).

`check-ratio.py --recalibrate` calls `measure(targets, cold=True, ...)`, and
`measure` times each master **exactly once** (`scripts/check-ratio.py:118-123`,
`:155`). There is no repeat and no mean. **MEASURED**, by reading the code.
**No spread for 0.011057 is recorded anywhere.**

The ledger admits the gap itself, about the tolerance: "THE TOLERANCE IS A
CHOICE, NOT A MEASUREMENT ... WHAT WOULD MAKE IT A MEASUREMENT: time the
delivered AC wing module by module and set the tolerance from its own
observed spread. That costs a per-module pass over 75 masters and **nobody
has paid for it**" (`dev/ledger.toml:2802-2809`).

**Scale.** A 1 percent error in the baseline moves the ceiling by
`8,269 x 0.011057 x 0.01 x 1.15 = 1.05 s`. The campaign's own recorded
run-to-run noise band for this instrument is **5 to 10 percent**
(`_build/briefs/LJ-1.44.md:37-40`; `_build/lj-1.48-report.md:170-171`), and
its tightest single-module three-run spreads are 0.5 to 1.8 percent. **At the
tight end the ceiling moves +/- 1.9 s. At the loose end it moves +/- 10 s.**

**In both cases the movement is at least as large as the residual being
hunted, and nine cure dispatches have been funded against it.**

### 5.3 One caution against over-reading this, which I put in because I nearly did

The ledger's comment block above the field is **stale**. It describes
`0.011472 / 16,897 lines / 193.85 s`, superseded on 2026-08-11 by
`0.011057 / 17,081 lines / 188.86 s` (commit `f48ffd7`). I first read the two
as two runs of one quantity and computed a 3.75 percent instrument spread.
**That reading is wrong and I withdraw it**: the two ran over different
trees, 184 lines apart.

**What survives, and it is enough.** The tree GREW by 184 lines and the slice
sum FELL by 4.99 s. Nothing in the record explains a growing tree getting
5 s cheaper. Some part of that 2.6 percent is run-to-run variation, and no
measurement separates it from real change. **INFERRED.**

### 5.4 The caliber's structural bias FAVOURS the wing, so do not argue unfairness

The slice caliber re-pays a per-module load floor of about 0.6 s (section
4.3). The AC baseline pays it 73 times over 17,081 lines; the wing pays it 6
times over 8,269 lines. **The baseline is therefore inflated by fixed cost
far more per line than the wing is, which RAISES the bar and helps the wing.**
**INFERRED**, from two measured figures. The wing is judged leniently by the
caliber and is still over. Any appeal that the gate is unfair to the wing is
not supportable, and I looked for one.

### 5.5 What I would need to be sure, and it is cheap

**Run `check-ratio.py --recalibrate` three times on one quiet tree and record
the spread.** One pass costs about 190 s of Agda plus per-invocation
overhead; three passes are roughly ten minutes on a quiet machine. Compare
that against nine cure dispatches. Then:

- If the three passes agree inside about 0.5 percent, the bar is firm, the
  residual is real at 2.33 to 3.75 s, and section 4.1's cure is the move to
  fund.
- If they spread by 2 percent or more, **the residual is inside the
  instrument**, and the honest report to the owner is that the wing is at the
  bar and cannot be said to be over it. That is a ruling the owner should
  make on evidence, not a wall.

**So my answer to your standing question is neither of your two options.**
The residual is probably closable by section 4.1's cure IF the copy-count
scaling law holds, and that is one measurement away. But the prior question
is whether there is a residual to close. **Price the instrument first.** It
is the cheapest unmeasured term in the whole campaign, and DD8 says the
widest unmeasured term is what turns a projection into a price.

---

## 6. DD4

**For each cure I recommend, what the J tower inherits and whether sharing
falls.**

- **Section 4.1, the thin face on `EnvSet`. Sharing is UNCHANGED and the
  generic surface improves.** `EnvSet` stays one generic artifact over
  abstract slot positions `E ar B K` at a frame `γ`, exactly as its own
  comment claims: "one copy serves every frame layout and **both towers**"
  (`src/L/Condensation.lagda.md:2757-2758`). The split is packaging: the
  implementation module holds the same code, the face names the three
  consumed results. The J tower applies the same face at its own frames and
  inherits both layers. **Nothing becomes J-specific and nothing is
  duplicated.** No sharing is traded for seconds here, which is why I rank it
  above every alternative.
- **Section 4.4, a marginal-rate budget on the remaining wiring. DD4-positive
  by construction.** A block that must land at or below 0.0127 s per line is
  a block that must stay parameterized, and parameterized content is the
  content both towers share. P-m puts parameterized work at 0.010 to 0.013
  and instantiation at 0.22. **The rate budget and DD4 push the same way**,
  which is worth saying in the brief: a block written generic passes the
  budget, and a block written for L alone at a concrete carrier does not.
- **Section 4.3, module fission. REJECTED, and it would have been
  DD4-neutral.**
- **The statement change `LJ-1.67` is chasing.** If it is ever built as a
  genuine abstract-stack statement, **say in that brief whether the J tower's
  rows can be stated at the same abstract stack.** If only L's rows can, the
  move buys seconds by making the row statements L-specific, and that is a
  DD4 trade that must be surfaced to the owner rather than absorbed. I flag
  it; I do not price it.

---

## 7. WHAT I DID NOT ANSWER

- **Whether the six probe copies were removed before the hoist runs.** The
  tree is reverted and no log survives. INFERRED only (section 2).
- **Whether the per-application cost scales with copied-definition count.**
  This is the load-bearing inference under section 4.1's projection. It is
  a hypothesis and I could not measure it: `LJ-1.67` held the Agda slot.
- **The true reproducibility of the wing gate and of the AC baseline.** Not
  recorded anywhere (section 5.2). This is the gap that decides Q5, and it is
  unmeasured today.
- **Why `LJ-1.67` reverted at 10:13.** Observed, not explained. Its own
  report is the authority.

---

---

# EXTENSION: `LJ-1.67` under the same review

Added after `LJ-1.67` returned. Its verdict: the row-level abstract-stack
module at `NegAgree` measured **+2.82 s** and was reverted
(`_build/lj-1.67-report.md:8-14`).

**I RAN NO AGDA FOR THE EXTENSION EITHER.** No agda process is live now
(`pgrep -x agda` empty), and the coordinator permitted a measurement. I
declined, for two reasons. First, my brief keeps `src/` read-only, and the
decisive measurement (section E.5) requires editing
`src/L/Condensation.lagda.md`. Second, P-h's own provenance records that this
class does not reproduce outside the file: "the isolated machinery did NOT
reproduce the wall in any standalone parameterization; only the real-file
context did, so bisects for this class must run in situ"
(`dev/LESSONS.md:194-197`). A `src/ProbeDD25R*.agda` miniature would return a
number I could not trust. **The tree is verified untouched: diff stat 956/79,
18 `EnvSet` applications. MEASURED.**

## E.0. Verdict on `LJ-1.67`

**UPHOLD the measurement. OVERTURN one structural claim inside it, and
overturn the conclusion the campaign is drawing from the six failures.**

The +2.82 s is sound: disjoint ranges, 3.2x the spread, load biased against
GO. I attack none of it.

**But `LJ-1.67` section 2 states: "no module-application layer was added on
top of `EnvSet` (this is not a third hoist; it is the same `EnvSet`
application moved to an abstract stack)"
(`_build/lj-1.67-report.md:78-81`). That claim is FALSE, and the report's own
code refutes it.** MEASURED, by counting module applications in the report's
own two code blocks (`:52-65`, `:71-74`):

| | module applications at `NegAgree` |
|---|---:|
| before | 2 (`module E' = EnvSet ...` in `out`, and in `back`) |
| after | 3 (`module E' = EnvSet ...` inside `NegEnv`, plus `module N = NegEnv ...` in `out` and in `back`) |

`NegEnv` is a module that the two sites apply, and `EnvSet` is applied inside
it. **That is a layer on top of `EnvSet`.** The report contradicts itself:
section 5 concedes "the added module layer is pure overhead at this site"
(`:113-115`). Section 5 is right and section 2 is wrong.

**Why this matters more than a wording slip.** If `LJ-1.67` is an independent
test of a new idea, the campaign has six independent failures and should
conclude the wall is real. If `LJ-1.67` is a third measurement of the SAME
mechanism, the campaign has ONE mechanism measured four times and **has never
tested the alternative**. Section E.1 shows it is the second.

## E.1. Extension Q1. What the failures have in common

**Your reading is right in substance and too weak in its prediction. It
predicts NEUTRAL. The data are all REGRESSIONS, and the sharper statement
predicts the sign.**

### E.1.1 The mechanism

**In Agda, `module M = N args` COPIES. It does not reference.** For every
definition in `N`, the application creates a NEW definition whose type is
`N`'s type with the arguments substituted. **INFERRED**, from Agda 2.8.0
semantics, at high confidence, and consistent with every measurement below.

The arithmetic then forces the sign. Put an intermediate module `M` between
`k` sites and a target `N`, where `M` re-exports `N`:

- before: `k x copies(N)`
- after: `1 x copies(N)` (inside `M`, at abstract arguments) `+ k x copies(M)`
- and `copies(M) >= copies(N)`, because `M` re-exports `N`.

**So the after side exceeds the before side by at least `copies(N)`. An
interposed module that re-exports its target CANNOT save; it must add one
full set of copies.** That is not an empirical finding. It is arithmetic over
the copy semantics.

### E.1.2 It separates the successes from the failures cleanly

| move | shape | measured |
|---|---|---:|
| chain frames, abstract args | **interpose, re-export** | +17.23 s |
| band frames, concrete slots | **interpose, re-export** | +10.88 s |
| alias of a duplicate tree | **interpose, degenerate (one definition)** | +3.29 s |
| abstract stack at the row | **interpose, re-export** | +2.82 s |
| birth-site sealing (`opaque`) | adds a seal; content elaborated once already | +1.61 s |
| band record bundle, one family | narrows a parameter telescope, one family only | -0.06 s |
| **`KFacts` record bundle** | **narrows what each site passes** | **-30 s** |
| **`Lift12Back` / `Lift12Out` kits** | **narrows the restated telescope** | **4.28x** |
| **`StageCardinal` `Successor` cluster** | **removes un-consumed content** | **-9.85 s** |

**Four interpositions, four regressions. Three narrowings, three large wins.
MEASURED on every row** (the campaign's own table, plus
`_build/lj-1.66-report.md:94` and `_build/lj-1.67-report.md:32`).

The seal is the one row the law does not explain, and `[LJ-1.47]` already
explains it: "sealing buys the repeats, never the once"
(cited at `_build/diag-dd24-residual.md:91`).

### E.1.3 The law it names, and the class it does NOT refute

**Proposed for `dev/LESSONS.md`, ID for the orchestrator to assign per
AGENTS.md.**

> **An interposed module cannot amortize a module application, because a
> module application copies rather than references. Interposing a module that
> re-exports its target strictly ADDS one set of copies. The only moves that
> reduce instantiation cost are: (a) fewer applications, (b) fewer
> definitions copied per application, (c) cheaper types on the definitions
> that are copied.**
>
> **Measured (2026-08-12), four regressions and no success in class
> (interpose): +17.23 s (`_build/lj-1.63-report.md` section 5), +10.88 s
> (`_build/lj-1.66-report.md:94`), +3.29 s (same), +2.82 s
> (`_build/lj-1.67-report.md:32`). Three successes, all in classes (a) to
> (c): `KFacts` -30 s, `Lift12` 4.28x, `StageCardinal` -9.85 s.**

**This law would have refused four of the six dispatches before they were
funded**, and it costs nothing to check: count the definitions the
interposed module exports.

**And it names the exception precisely.** Interposition wins when the
interposed module **NARROWS**, that is, when it exports FEWER definitions
than its target. `EnvSet` exports sixteen; the eighteen sites reach three (section
4.1, MEASURED). **Section 4.1's thin face is interposition that narrows 16 to
3.** It is the only member of class (b) anyone has proposed at this wall, and
**no measurement in this campaign bears on it.**

## E.2. Extension Q2. Did the `LJ-1.67` brief cause the outcome?

**YES, decisively, and the defect is visible in the brief's own text.**

The brief did not merely constrain the agent. **It prescribed the failing
shape**, in these words:

> "a module parameterized by `(γ' : S ^ (6 + m))` plus the site facts stated
> at `γ'` ... The `EnvSet` application then happens once against `γ'`, where
> `lookup` cannot reduce, **and the row's `out`/`back` instantiate it at their
> own stacks**" (`_build/briefs/LJ-1.67.md:78-84`).

**The last clause is the regression.** Instantiating the inner module at the
sites' own stacks is interposition, and it puts the concrete stack back
exactly where the brief's stated goal was to remove it. **The brief's
mechanism claim and its prescribed shape contradict each other, and the
contradiction is on the page.** The agent built what it was told and measured
it honestly.

**The `[LJ-1.25]` analogy fails on the same point.** The brief calls this
"`[LJ-1.25]`'s measured cure at a new site ... abstracting the SOURCE won
12.8x" (`:68-71`). There the transparent index NEVER appeared afterwards.
Here the concrete stack still appears, at every site. **The analogy is broken
at the one joint that made the original work**, which is what P-l
(`dev/LESSONS.md:2305`) exists to catch.

**The pattern, and this is the third instance.** Both briefs gated GO on a
cost term while leaving the structural precondition ungated:

| brief | premise it did not gate | measured |
|---|---|---|
| `LJ-1.66` | "the slot arguments look identical, so eighteen could become three" (`:74-76`) | false (`_build/lj-1.66-report.md:84-90`) |
| `LJ-1.67` | an abstract inner module keeps the stack from unfolding at the site | false: the site instantiates it concretely |

**The cure is the same two-part gate I gave in section 3.3**, and it is now
worth writing into `dev/ORCHESTRATION.md` rather than into one brief: **a
brief that funds a cure states the structural precondition the cure needs,
and requires the agent to verify it by READING before building anything.**

**Cost of the defect: six cold runs across the two dispatches, roughly 20
minutes of Agda, plus two build cycles.** The consolation is real and I do
not dismiss it: interposition is now MEASURED false at three sites and one
spelling, which is what makes section E.1's law admissible under this
project's "no law without its measurement" rule.

## E.3. On my own prediction, scored

In section 4.5 I predicted, before the return landed, that the shape as built
would regress by roughly 0.5 to 1.0 s. **The measurement is +2.82 s.**
Direction right, magnitude wrong by about 3x. My model counted added
definition-copies only, and ignored that `NegEnv`'s own parameter telescope
(an abstract stack plus three large site-fact types) is substituted at each
of its two instantiations. **I record the miss because it prices my own
inferences: my mechanism reasoning predicts SIGN reliably and MAGNITUDE
badly.** No verdict in this review rests on a magnitude I inferred.

## E.4. Extension Q3. Does 1.016 s survive?

**It survives, and your dilemma is a false one. Neither branch holds.**

The question assumes the six failures tested recoverability. **They did not.
All six ADD elaboration; none removes any.** A measurement of what it costs
to add a copy tells you nothing about what it saves to remove one, unless you
also know the cost is linear in the copy count. **Nobody has measured in the
removal direction. Not once, in this whole campaign.** MEASURED, by reading
all six moves.

So the 1.016 s measures a real cost. Whether that cost is recoverable is
**untested**, and the six failures are not evidence either way.

**Three independent readings of "one module-copy layer at a band site" now
exist, and they should be quoted as a range:**

| source | per copy-layer per site |
|---|---:|
| `LJ-1.66` hoist, 18 sites (+10.88 s) | 0.604 s |
| `LJ-1.66` probe, 3 host rows (+6.096 s over 6) | 1.016 s |
| `LJ-1.67` `NegAgree`, net one added application (+2.82 s) | 2.82 s |

**A 4.7x spread. MEASURED**, by arithmetic over the three reports. It says
rows differ greatly, which the "three hot rows" finding already implied. **So
the family price is 10.9 s to 50 s, not 18.29 s.** Every value is far above
the 2.33 s residual, so no decision changes; but **the campaign must stop
writing 18.29 s as a point figure**, exactly as it must stop writing 2.33 s
as one.

### E.5. How to tell the two apart, and it is one cheap measurement

**Run `LJ-1.66`'s own instrument on a NARROWED face.** No site is touched, no
statement changes, and the edit is purely additive and revertible:

1. Add `EnvSetFace`, a module with the same parameters as `EnvSet`, whose
   body is **three** definitions with written types (I-5), each a TERM
   application of `EnvSetImpl.out` / `.back` / `.memE-bnd`. It exports 3
   where `EnvSet` exports 16.
2. Add N = 6 unused applications of `EnvSetFace` at the same three depths
   `LJ-1.66` used.
3. Measure cold, three runs each side, gate caliber, one process. Divide by
   6.

**The discriminator, fixed in advance:**

- **Unit at or below 0.35 s** (about 3/16 of 1.016): cost scales with copied
  definitions. **The 18.29 s is largely recoverable**, and section 4.1 is the
  move to fund.
- **Unit still near 1.0 s**: the cost sits in the three consumed definitions'
  own types, not in the copy count. **The copy-count lever is dead**, and P-t
  (`dev/LESSONS.md:2601`) then names the remaining lever: `φB` and `φ`, the
  built formula trees inside those types (`src/L/Condensation.lagda.md:2770-2774`).
  That is a type-level move, and nobody has priced one.

**Either answer closes a question the campaign has been guessing at for six
dispatches. Cost: six cold runs, about 11 minutes of Agda.**

## E.6. Extension Q4. The standing verdict, plainly

**Not yet the owner's to rule. Two cheap measurements stand between this
campaign and that decision, and both were skipped in favour of cures.**

| # | measurement | cost | what it decides |
|---|---|---|---|
| A | `check-ratio.py --recalibrate` three times on one quiet tree, publish the spread | ~10 min | **whether a residual exists.** The bar rests on ONE un-repeated pass with no recorded spread (section 5.2). A 1 percent baseline error moves the ceiling 1.05 s; the residual is 2.33 to 3.75 s |
| B | the narrowed-face probe (E.5) | ~11 min | **whether the 18.29 s is recoverable at all.** The only untested class |

**Under 25 minutes of Agda, against six cure dispatches already spent.**

- **If A says the bar is firm and B says the unit falls**: the residual is
  real and closable. Fund section 4.1. No owner ruling needed.
- **If A says the bar moves by 2 percent or more**: the residual is inside
  the instrument, and the honest report is that the wing is AT the bar, not
  over it. The owner rules on a re-armed baseline, not on 2.33 s.
- **If A says firm and B says the unit holds near 1.0 s**: every named lever
  is measured false, and **then** it is the owner's to rule.

### E.6.1 The thing that outranks all of it, and I put it last on purpose

**Closing 2.33 s does not save the wing, and the campaign should say so to
the owner before asking for a ruling on 2.33 s.**

The pending wiring is MEASURED at **0.045 to 0.047 s per in-fence line**
(`_build/lj-1.62-report.md:87-88`, cited at
`_build/diag-dd24-residual.md:170-173`). The bar is 0.012716. **Each wiring
line adds about 0.0333 s of overage:**

| wiring lines still to write | projected residual |
|---:|---:|
| 0 | 2.33 s |
| 250 | 10.7 s |
| 500 | 19.0 s |
| 1,000 | 35.6 s |

`levelIn` and `cover` are not discharged, and `TwelveAgree`'s 24 hypotheses
are not wired. **The wing is not a finished object that is 2.33 s over. It is
an unfinished object whose remaining work is projected to arrive at 3.6x the
bar.**

**So the decision actually in front of the owner is not "accept 2.33 s".** It
is: **does DD24 bind the wing continuously while it is being built, or at
completion?** Every cure dispatch in this phase has answered the first
reading, and six of them have failed. **The second reading turns the residual
into a rate budget on work not yet written**, which is steerable, and which
DD4 and P-m push the same way: parameterized content checks at 0.010 to
0.013, instantiation at 0.22.

**My recommendation to put to the owner**: run A and B first, then present
the ruling as a choice between those two readings of DD24, with the wiring
projection above beside it. **A ruling on 2.33 s alone answers a question
that the next 500 lines will make obsolete.**

## E.7. DD4 for the extension

- **Section E.1's proposed law. DD4-positive, and this is its main value.**
  It is a generic statement about Agda's module system, not about `L`. Both
  towers instantiate parameterized machinery, so the J tower's authors face
  the same wall and would otherwise re-derive it at their own cost. **A law
  that stops four dispatches on the L side stops four on the J side.**
- **Section E.5's narrowed face. Sharing is UNCHANGED**, for the reason in
  section 6: `EnvSet` stays one generic artifact over abstract slot positions
  whose own comment claims "one copy serves every frame layout and both
  towers" (`src/L/Condensation.lagda.md:2757-2758`). The split is packaging.
  The J tower applies the same face and inherits both layers.
- **`LJ-1.67`'s reverted shape. Its DD4 answer was correct and I uphold it**
  (`_build/lj-1.67-report.md:107-119`): the abstract-stack module was more
  generic and traded nothing away. **It was a good shape at a bad price**,
  and the revert loses nothing the J tower needed.
- **Section E.6.1's rate budget. DD4-positive by construction**, as in
  section 6: a block that must land at or below 0.0127 s per line must stay
  parameterized, and parameterized content is what both towers share.

## E.8. What the extension does NOT answer

- **Whether the copy-count scaling law holds.** This is the single
  load-bearing inference in the whole review, and it is untested. Section E.5
  tests it for 11 minutes.
- **Whether `NegAgree` is representative.** Its 2.82 s per added application
  is 4.7x the 18-site figure. One row was measured; rows differ.
- **The exact per-definition cost of a copy.** I quote 1.016/16 as an order
  only. It assumes uniform cost across sixteen definitions of very different
  type complexity, which is certainly false in detail.

## 8. ARCHIVE USED

- `_build/lj-1.66-report.md`, WHOLE. TOOK the unit cost and its instrument
  (`:23-33`, `:50`), the three-run table and loads (`:44-48`), the hoist code
  and its mechanism (`:70-102`), the non-identical-argument finding
  (`:84-90`), the DD4 answer (`:111-122`), and negative 5, which names the
  statement-change cure (`:152-155`).
- `_build/briefs/LJ-1.66.md`, WHOLE. TOOK the false structural premise
  (`:72-76`), the one-term GO gate (`:90-97`), the DD4 stop clause (`:137`),
  the eighteen-site list (`:45-49`) and the prior-measurement table
  (`:24-37`).
- `_build/diag-dd24-residual.md`, WHOLE. TOOK the residual arithmetic and the
  Condensation attribution (`:28-32`), the band figure (`:34-38`), the
  application count that I found wrong (`:66-68`), the P-t reading of
  `PropAgree` (`:85-87`), the `V.Presentation` arithmetic (`:157-159`) and
  the pending-wiring marginal class (`:170-175`).
- `_build/briefs/LJ-1.64.md:26-38`. TOOK the six-row wing table, the
  aggregate, and the recorded residual BAND of 2.33 to 3.75 s.
- `_build/lj-1.63-report.md:192-194`. TOOK the two gate runs, 108.27 and
  108.90 s.
- `_build/lj-1.64-report.md:86`. TOOK the 108.47 s reading at the same tree.
- `_build/lj-1.65-report.md:13-26`. TOOK the largest recorded single-module
  three-run spread, 1.5 to 1.7 s.
- `_build/lj-1.62-report.md:87-88`. TOOK the chain's marginal class, 0.045 to
  0.047 s per line.
- `_build/briefs/LJ-1.44.md:22`, `:37-40`. TOOK the "module-load floor" label
  on `V/Presentation` and the recorded 5 to 10 percent noise band.
- `_build/lj-1.48-report.md:170-171`. TOOK the same noise band, second
  citation.
- `_build/lj-1.67-report.md`, WHOLE (extension). TOOK the verdict and the
  revert (`:8-14`), the three-run table with loads (`:27-30`), the disjoint
  ranges and the load-bias direction (`:32-38`), **the two code blocks that
  refute its own section 2** (`:52-65`, `:71-74`), the false no-layer claim
  (`:78-81`), the section 5 admission that contradicts it (`:113-115`), and
  the generalization status (`:97-105`).
- `_build/briefs/LJ-1.67.md`, WHOLE (extension). TOOK the P-h argument
  (`:55-65`), the `[LJ-1.25]` analogy (`:68-71`), **the prescribed shape whose
  last clause is the regression** (`:78-84`), the identical-content
  constraint (`:85-90`) and the 1.0 s GO gate (`:96-101`).
- `_build/lj-1.25-report.md` and `_build/lj-1.24-report.md`: **NOT READ.**
  Your brief told me not to re-test the abstract-source hypothesis, and P-l
  forbids transferring their 12.8x to this site, so reading them could not
  change a verdict here. The extension does not need them either: I attack
  the analogy at its joint, which is visible in the `LJ-1.67` brief itself. I
  state this rather than claim a read I did not make.
- `dev/LESSONS.md`: P-h (`:174`), P-l (`:2305`), P-m (`:2460`), P-n (`:2483`),
  P-o (`:2509`), P-t (`:2601`), P-q (`:2633`), D-30 (`:3255`), each read
  whole. TOOK P-t as the law that predicts against the abstract-stack
  hypothesis (`:2601-2632`), D-30 as the shape of section 4.1's cure and its
  5.45x measurement (`:3255-3280`), P-h as the constraint section 4.1 must
  not break (`:174-186`), P-l as the reason `[LJ-1.25]` does not transfer,
  and P-m for the rate budget in section 4.4.
- `scripts/check-ratio.py`: header docstring (`:1-45`), the per-invocation
  timing (`:118-123`), `recalibrate` (`:155`), and the aggregate verdict
  (`:296-330`).
- `scripts/ledger.py:223-290`, `validate_ratio_baseline`. TOOK the fact that
  the staleness guard validates `ac_baseline_lines`, the whole-cone
  denominator, and **not** `ac_baseline_module_lines`, the pair that renders
  the verdict.
- `dev/ledger.toml`: the `[ratio]` block, `ac_baseline_module_rate` (`:2590`)
  and its stale comment (`:2567-2589`), the slice-versus-cone measurement
  (`:2579-2585`), the tolerance admission (`:2802-2809`), the wing list.
- `src/L/Condensation.lagda.md`, READ ONLY: `EnvSet` and its sixteen exports
  (`:2761-2900`), the eighteen application sites, and the `NegAgree` region
  at 10:05 and again at 10:13. Counts by `grep` and `awk`, quoted in sections
  1.5 and 4.1.
- `git show HEAD:src/L/Condensation.lagda.md`. TOOK the committed site list
  (18 applications, lines 3484 to 5070) and `NegAgree`'s two concrete `EnvSet`
  applications at 3559 and 3586.
- `archive/rud-route/`: **NOT READ.** `[LJ-1.11]` ruled its condensation
  target classically false, so it carries no price for this question, and
  shape alone cannot decide a seconds verdict. I spent nothing.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. I spent nothing.
