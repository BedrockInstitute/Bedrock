# LJ-1.15-R: adversarial review of the one-clause probe (DD25)

## 1. VERDICT

**OVERTURN.** The report's line counts are correct. Its conclusions are not.

Three findings carry the overturn.

1. **The 155-against-40 is a re-price, and it lands INSIDE the band.** The row
   the probe gates is booked at 0.7 to 1.6 thousand lines for twelve clauses.
   The top of that band already allows 133 lines per clause. The probe measured
   the HARDEST clause at 155. That is 1.16 times the band top's own per-clause
   average, not four times anything. The gate of 40 lines sat below the band it
   was written to test.
2. **Statement 2's diagnosis is wrong in both of its reasons.** The environments
   do NOT have unbounded stages. The seal on `hierAt` is NOT the block.
3. **Route A does not move.** The re-price is 3.3 thousand lines, unchanged,
   with a NARROWER band of 2.4 to 4.3 thousand. Two corrections cancel. The
   table row comes down on the measurement. The carrier row goes up to the
   archive's own figure.

**What the report got right, and it is the day's best number.** The probe checks
at 0.0052 seconds per line. The DD24 bar is 0.013193. P-n's concrete-carrier
floor is 0.22 to 0.297. The whole crossing at the measured rate costs 15 to 17
seconds against a wing budget of 99.6 to 147.7 seconds. At P-n's floor the same
content would cost 726 to 980 seconds, which is five to ten times the WHOLE
wing. **The probe proved the crossing fits the seconds budget. Nobody knew
that.** That result survives this review untouched.

**The literal NO-GO word is defensible and materially misleading.** The brief
made NO-GO a disjunction. Its second half was "the bound cannot be placed in the
carrier with the delivered closure lemmas". The archive had already priced that
same content at 0.40 to 0.75 thousand lines. So the second half was pre-failed
before the probe started. A gate that cannot return GO returns no information.

## 2. ONE OBSTRUCTION OR TWO?

**TWO. Do not organise the re-pricing around one obstruction.** The two facts
have different causes, different cures and different permanence.

### 2.1 `[LJ-1.16]`'s obstruction is permanent

The order element `relL α` is a relation ON the carrier `Lset α`. A relation on
a set always sits above that set. Its rank is α+1 by construction. **No coding
change moves it.** The cure is to stop making the order an element. Devlin's own
answer is a definable well-order, which is a FORMULA and never a set
(`dev/literature/devlin-II5.md:257-268`).

### 2.2 `[LJ-1.15]`'s obstruction is removable

The bound is built FROM members of a set at stage δ, and δ is strictly below α.
Its true rank is δ plus a finite number. **Devlin states the number: δ+4**
(`_build/literature/dev2.txt:676-678`). The tree inflates the same object to
δ+ω. The inflation is a representation choice, and section 3 names it.

### 2.3 What they actually share, and it is worth having

The only shared fact is the shape of every rank argument: an object needed
inside a carrier can sit above it. That shape is too generic to organise a
re-pricing.

**One real shared gap exists.** Neither obstruction has a stage-arithmetic API
to reason with. `src/L/Rank.lagda.md` exports `rank-mono`, `rank-ord` and
`rank-fix` only. `src/L/Ordinal/Stages.lagda.md:190` exports `rank-Lset` in one
direction only. Both agents had to build stage facts by hand. **A small stage
kit would serve both sites, and DD4 makes it shared code.**

### 2.4 A detail that separates them cleanly

`[LJ-1.15]`'s cure needs the constants-to-variables direction of
`FOL.Manipulation.Parameters`. That direction is DELIVERED (`placeFo` at
`src/FOL/Manipulation/Parameters.lagda.md:226-228`, `⊨-place` at `:362`).

`[LJ-1.16]`'s blocked shape needed the INVERSE direction, variables to
constants. That direction is not delivered, and `[LJ-1.16]` prices it at 100 to
160 lines (`_build/lj-1.16-report.md:31-41`).

**One chapter, two opposite directions, two different verdicts.** They are not
one obstruction.

## 3. STATEMENT 2, JUDGED AGAINST DEVLIN'S K(u)

### 3.1 Devlin's bound IS smaller, and the difference is the formula shape

Devlin's `K(u)` is the set of finite SEQUENCES over the symbols, the variables
and the members of `u` (`_build/literature/dev2.txt:600-609`). Devlin codes a
formula as a finite sequence of symbols. **A finite sequence is a function, so
its rank does not grow with its length.** Devlin's own arithmetic confirms this:
he states that the level sequence up to δ lies in `L(δ+4)`
(`_build/literature/dev2.txt:676-678`). The bump is finite.

The tree codes a formula as a TREE. `⌜ φ ∧̇ ψ ⌝ = mkTag 2 (pr ⌜φ⌝ ⌜ψ⌝)`
(`src/FOL/Coding.lagda.md:124-136`). Each nesting level adds a fixed rank. The
depth of a formula is unbounded. The alphabet is the carrier's own members
(`src/L/Coding/CodeSet.lagda.md:306`, `smallDom (Σ[ n ∈ ℕ ] Formula ⟪ fst A ⟫ n)`).
**So the code set over `Lset δ` has rank δ+ω, and Devlin's has rank δ plus a
finite number. The gap is exactly the formula representation.**

### 3.2 The agent's stated reason is FALSE

The report says: "The bound must contain the environments at every arity. The
environments at all arities have unbounded stages"
(`_build/lj-1.15-report.md:72-74`).

**The tree's environment is a finite function, not a nested pair.**

```agda
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))
```

That is `src/L/Coding/Environment.lagda.md:83-85`. An environment is a SET OF
PAIRS. Each pair holds a numeral and a value. **The rank of that set does not
depend on the arity.** For values in `Lset δ` with δ above ω, every environment
at every arity lies in `Lset (δ+3)`.

The probe's own statement-2 code proves the same pattern for the level sequence.
`pair-stage` puts a recorded pair at the third successor
(`src/ProbeLJ115.agda:292-306`). `graph-mem-stage` puts every member at one
common stage (`:308-321`). **The agent applied the argument to the graph and did
not apply it to the environments.**

The tree also ships the finished chapter. `L.Coding.EnvSet` proves that the
environments over a set form a set, and gives a bounding stage
(`src/L/Coding/EnvSet.lagda.md:176-184`). `L.Coding.Model` writes the
environment set in the object language at a VARIABLE arity
(`src/L/Coding/Model.lagda.md:1150`).

**So the number δ+ω is right and the reason for it is wrong.** The agent found
the right order for the wrong object.

### 3.3 Is the failure real, or an artefact of a bad bound choice?

**It is an artefact, and the tree already ships the cure.**

`FOL.Manipulation.Parameters` states the trade in its own first paragraph:
"constants are as many as there are sets, so a syntax with constants can be
neither counted nor coded ... A formula with parameters becomes a parameter-free
formula of higher arity together with a vector of the constants it mentioned,
and satisfaction is preserved when those constants are supplied in the
environment instead of in the syntax"
(`src/FOL/Manipulation/Parameters.lagda.md:3-13`).

`placeFo` returns a formula over the EMPTY alphabet, `Formula (⊥* {ℓz}) (n + k)`
(`src/FOL/Manipulation/Parameters.lagda.md:226-228`). `⊨-place` is its delivered
adequacy (`:362`).

Apply it to the code set and the arithmetic changes:

| object | with carrier constants | parameter-free plus environment |
|---|---|---|
| code set | rank δ+ω | rank ω·2, and δ does not enter |
| environment set at every arity | rank δ+3 | rank δ+3 |
| the bound | **rank δ+ω** | **rank δ+4** |

**A parameter-free code carries no carrier member, so its rank is fixed and the
carrier stage never enters it.** The parameters move into the environment, whose
rank is already uniform. The bound then sits at δ+4, which is Devlin's own
number, and δ+4 is below every limit α above δ.

### 3.4 What the current shape actually costs, exactly

With the current shape the bound needs `Lset α` to contain a set of rank δ+ω. If
α is the next limit above δ, then α equals δ+ω, and the bound fails. **The
failure case is precisely the smallest limit above δ, and no other case.** For α
a limit of limits the current shape already works.

So three cures exist and they are not equal.

- **Cure A, restrict α.** Require α to be closed under adding ω. Cost is a
  hypothesis change. The consumers apply condensation at cardinals, which are
  closed. **The archive already used this cure on the J side:** the rud route
  records that "the bound is a member of the carrier only above the first limit"
  (`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:210-212`). ESTIMATED cost:
  under 50 lines. It is a case split, not new mathematics.
- **Cure B, re-shape the bound with `placeFo`.** The forward operator and its
  adequacy are delivered. The work is to re-state `DefAt`'s code existential over
  parameter-free codes plus an environment (`src/L/Coding/Powerset.lagda.md:442`).
  ESTIMATED cost: it is a refactor of delivered content, not a new chapter.
- **Cure C, change `⌜_⌝` to a sequence coding.** Do NOT do this. It rewrites the
  coding of every chapter that reads a code.

**Neither cure was considered by the report.** Its price of 0.40 to 0.75
thousand lines is the archive's survey for the unreshaped object.

### 3.5 The other headline claim, `hierL δ ∈ Lset α`

**This one does not close, and the report is right that it does not.** My
criticism is of the reason, not the fact. See section 4.

I add one archive fact the report missed. The retired route did not prove this
by stage arithmetic. It carried `hierL β ∈ˢ Sset γ` as an INDUCTION HYPOTHESIS
supplied by the ambient induction (`_build/l3.31-r2probe-report.md:153-158`).
**That is a fourth cure, and it may be the cheapest: re-shape the induction so
the containment arrives as a hypothesis.** The report cited the same file and
took only the negative half from it.

## 4. THE SEALING: real block or missing export?

**Neither. The seal is real, and it is not the cause.**

### 4.1 The seal does not hide what the report says it hides

`hierAt` is `opaque` (`src/L/Hierarchy.lagda.md:536-537`). But `hierL-spec`
exports the FULL extension of the graph as a membership equivalence
(`src/L/Hierarchy.lagda.md:624-626`, `IsHier B h` at `:501-502`). The extension
is exactly `Recorded δ` (`:497-498`).

**The probe proves this itself.** `graph-mem-stage` derives the member-level
bound from `hierL-spec` alone (`src/ProbeLJ115.agda:308-321`). It never touches
the seal. So the seal did not stop the agent, and no export would have helped.

### 4.2 What is actually missing

The missing step goes from "every member lies in `Lset γ`" to "the set lies in
`Lset (sucV γ)`". **That step is FALSE without definability.** A subset of
`Lset γ` that lies in `L` need not lie in `Lset (sucV γ)`. `Lset (sucV γ)` holds
the DEFINABLE subsets only (`Lset-suc`, used at `src/ProbeLJ115.agda:274-277`).

So the residue is mathematical content, not an export. The report calls it "a
new carrier fact" and is right about that word. It is wrong about the cause.

### 4.3 What unsealing would cost, since the brief asked

**Do not unseal.** R-38 anchors an unsealed invocation at 25.7 seconds
(`dev/LESSONS.md:2295`). The wing's WHOLE seconds budget is 99.6 to 147.7
seconds (`dev/ledger.toml:273`). **One unsealed invocation would spend 17 to 26
percent of the wing.** R-38's measured cure is the opposite move: seal at birth
and export the spec from inside (`dev/LESSONS.md:829-843`).

The tree's own cheap pattern is a re-derivation in the consumer. The archive
records it: `recL` cost 13 lines in a consumer because `L/Hierarchy` proves it
twice inside and exports neither (`_build/l3.31-r2probe-report.md:175-180`).
**MEASURED price of that pattern: 13 lines. That is the price of an unexported
fact in this tree, and it is not a block.**

## 5. THE RE-PRICE

### 5.1 The measured input

MEASURED by me, recounted from the delivered files.

| item | lines | evidence |
|---|---:|---|
| statement 1, whole block | **155** | `src/ProbeLJ115.agda:70-268` |
| statement 2, closing pieces | **37** | `src/ProbeLJ115.agda:274-321` |
| probe total, agent caliber | 246 | non-blank, comments excluded |
| probe total, LEDGER caliber | **282** | non-blank inside fences, `scripts/ledger.py:120-136` |

**The headline 155 reproduces exactly.** The report's internal split of
155 into 111 plus 4 plus 40 does not reproduce; my per-range counts give 68,
37, 4 and 36 plus 14 lines of glue. The split is loose. The total is right.

**One caliber slip.** `scripts/ledger.py` counts every non-blank line inside a
fence, including comments. The probe's ledger figure is 282, not 246. The rate
falls to 0.0045 seconds per line, further UNDER the bar. **The slip helps the
probe's own conclusion, so nothing turns on it.**

### 5.2 Twelve clauses at the measured rate

The booked row is 0.7 to 1.6 thousand lines for the table
(`_build/lj-1.12-report.md:32`). **That booking already implies 58 to 133 lines
per clause.** The report compared 155 against an average of 40 and reported a
factor of four. The correct comparison is 155 against 133.

Two numbers, and I mark which is which.

- **MEASURED worst case.** All twelve clauses at the measured hardest:
  12 × 155 = **1.86 thousand**. That is 0.26 above the booked top.
- **ESTIMATED composition.** The probe's matrix is 68 of its 155 lines, so the
  formula is 44 percent of a clause. `[LJ-1.2]` measured light clauses at 10 to
  23 formula lines (`_build/lj-1.2-gate.md:27-45`). Scaling by 155/68 gives 23
  to 52 total lines for a light clause. Four of the twelve clauses are quantifier
  clauses. So the row is 4 × 155 plus 8 × (23 to 52), which is **0.80 to 1.04
  thousand**.

**The composed row sits INSIDE the booked band and below its centre of 1.15.**
The measurement moves the table row DOWN, not up.

### 5.3 What Route A becomes

| row | booked | re-priced | basis of the change |
|---|---:|---:|---|
| bounded code set | 0.2-0.5 | 0.2-0.5 | unchanged |
| twelve-clause table | 0.7-1.6 | **0.80-1.04** | MEASURED, section 5.2 |
| step, graph, Σ₁ stack | 0.3-0.6 | 0.3-0.6 | unchanged |
| equivalence | 0.3-0.8 | 0.3-0.8 | unchanged |
| transport certificate | 0.15-0.30 | 0.15-0.30 | unchanged |
| carrier facts | 0.15-0.45 | **0.40-0.75** | the archive's own row (a), `_build/l3.32-t51-report.md:206` |
| iso-invariance | 0.08-0.14 | 0.08-0.14 | unchanged |
| limit case | 0.124 | 0.124 | unchanged |
| **total** | **2.0-4.5, centre 3.3** | **2.4-4.3, centre 3.3** | |

**Route A stays at 3.3 thousand lines. The band narrows by 0.35 at the bottom
and 0.26 at the top.** The two corrections cancel almost exactly. The report's
"3.6 to 3.9 thousand" does not follow from its own numbers.

### 5.4 The seconds, which are the real result

At the measured 0.0052 seconds per line, 3.3 thousand lines cost **17.2
seconds**. At the ledger caliber's 0.0045 they cost 14.9. The wing's whole
budget is 99.6 to 147.7 seconds. **The crossing takes 10 to 17 percent of the
wing.**

At P-n's concrete-carrier floor of 0.22 to 0.297, the same 3.3 thousand lines
would cost 726 to 980 seconds. **That is five to ten times the WHOLE wing
budget.** The probe's rate is therefore the finding that makes the crossing
fundable at all. `[LJ-1.6-R]` killed the square law on exactly this budget.

## 6. THE BRIEF'S SHARE

### 6.1 The ill-typed `hierL (Lset δ)`

`hierL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S`
(`src/L/Hierarchy.lagda.md:621-622`). `IsOrd (Lset δ)` is false, so the literal
reading does not type.

**The agent's reading is right, and it cost nothing.** `hierL δ`'s extension is
`Recorded δ`, the pairs of an ordinal below δ with the level there
(`src/L/Hierarchy.lagda.md:497-498`). That is Devlin's object, the sequence up
to δ (`_build/literature/dev2.txt:676-678`). The agent flagged the reading in
its own section 10 (`_build/lj-1.15-report.md:180-182`). **That is correct
practice and it deserves the credit.**

### 6.2 The two gates, and this is the brief's real defect

**The 40-line gate contradicts the brief's own commissioning table.** The table
tops at 1.6 thousand for twelve clauses, so 133 lines per clause. A gate of 40
for the HARDEST clause could not return GO under any outcome consistent with the
booking.

**The 100-line gate contradicts the archive.** `[LJ-1.12]` booked the carrier
facts at 0.15 to 0.45 thousand. The archive's own survey of the same object, the
"K(u)-binding set, bounded witness", is 0.40 to 0.75 thousand
(`_build/l3.32-t51-report.md:206`). The gate was four to seven times below the
project's standing figure.

**A NO-GO produced by a gate below its own band carries no information about the
route.** Both halves of the NO-GO trace to the gates.

### 6.3 A scope defect that produced the wrong diagnosis

The brief's SCOPE (read) names `src/L/Coding/` and `Sequence.lagda.md`. It does
NOT name `L.Coding.EnvSet`, `L.Coding.CodeSet` or `FOL.Manipulation.Parameters`.
**Those three chapters hold the whole answer to statement 2's second half.** The
agent's false claim about environments is partly a consequence.

### 6.4 What the brief got right

The brief ordered seconds as well as lines, against both the DD24 bar and P-n's
floor. **That instruction produced the only durable result in the return.** Keep
it in every wing brief.

## 7. DD4: DOES THE OBSTRUCTION HIT THE J TOWER?

**No, and the asymmetry is larger than `[LJ-1.12]`'s 2 to 3 times.**

The δ+ω comes from the code set over the carrier, and the code set exists to
serve the Def step. **The J tower has no Def step.** The archived J-side level
sigma collapses the Def clause by the Refine lemma, "that under transitivity
every member of a set is definable there by the atom naming it"
(`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:16-20`). Its bounded content
is the internal-powerset atom and the sixteen rud operations, which are a FIXED
finite set with no unbounded depth.

So the L tower pays a carrier-indexed code set and the J tower does not. **The
J tower's levels are generated, so its bound is structurally smaller, exactly as
DD2's ruling at `[LJ-2.5]` supposes.** This is evidence FOR the architecture
ruling.

**But the cure is shared, and that is the DD4 result.** `placeFo` and `⊨-place`
live in `FOL.Manipulation.Parameters`, which is shared FOL infrastructure below
both towers. `⌜_⌝` lives in `FOL.Coding`, also shared. **One fix at the shared
layer serves both ends.** A stage-arithmetic kit (section 2.3) is shared too.

The J side already met the same bound-in-carrier question and answered it by
restricting the carrier, not by new mathematics
(`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:210-212`). **That precedent
transfers as a HYPOTHESIS, not as a price. P-l applies: re-measure at the L
site.**

## 8. WHAT THE ORCHESTRATOR SHOULD DO NEXT

Ordered. Each item names its own gate.

1. **Do NOT stop `[LJ-1.5]` for a re-price.** The re-price is 3.3 thousand, the
   booked figure. Nothing changed the centre. Record the narrowed band 2.4 to
   4.3 and the changed composition.
2. **Record the seconds result as the probe's deliverable.** The crossing costs
   10 to 17 percent of the wing's seconds budget at the measured rate. That is a
   MEASURED figure and it belongs in the ledger.
3. **Dispatch one probe on the bound's re-shaping, and gate it on rank not
   lines.** The question is whether `placeFo` plus `⊨-place` re-state `DefAt`'s
   code existential over parameter-free codes and an environment. GO if the
   re-stated bound has a stage below δ+ω. Do NOT set a line gate. This probe is
   the one that decides between Cure A and Cure B, and it is cheap.
4. **Ask Cure A first, because it may cost 50 lines.** Check whether the wing's
   consumers ever apply condensation at a limit that is not closed under adding
   ω. If they never do, the whole δ+ω question closes by a hypothesis change.
   The archive already used this cure on the J side.
5. **Probe the fourth cure for `hierL δ ∈ Lset α`.** Ask whether the containment
   arrives as an induction hypothesis rather than as a stage lemma. The retired
   route did exactly that (`_build/l3.31-r2probe-report.md:153-158`).
6. **Commission the stage-arithmetic kit as SHARED code under DD4.** Both
   today's rank reports needed it. Neither had it. Price it before the crossing
   block opens, not inside it.
7. **Fix the gate-setting practice, and this is the process item.** A gate below
   the band it tests cannot return GO. **Derive every line gate from the booked
   row's own per-unit figure, and write that derivation in the brief.**
8. **Do not unseal anything.** R-38 prices an unsealed invocation at 25.7
   seconds against a 99.6 to 147.7 second wing. Re-derive in the consumer at the
   archive's measured 13 lines.

## 9. LITERATURE USED

- `_build/literature/dev2.txt:600-609`. **USED and decisive.** Devlin's `K(u)`
  is finite SEQUENCES over the symbols, the variables and the members of `u`.
  Sequences are functions, so the rank does not grow with length.
- `_build/literature/dev2.txt:676-678`. **USED and decisive.** Devlin states the
  level sequence up to δ lies in `L(δ+4)` for δ above ω. That is the finite bump
  the tree loses.
- `_build/literature/dev2.txt:679-686`. **USED.** The Σ₁ level formula `H(x, α)`
  that the brief named, and its uniform Δ₁ status at limit α above ω.
- `_build/literature/dev2.txt:585-601`. **USED.** Devlin's own account of why he
  seeks a single bound, and that the earlier `Sat` bound is not large enough.
- `dev/literature/devlin-II5.md:209-256` (section 2.3). **USED.** Item 1 is the
  Σ₀ matrix, item 2 the witness inside the carrier. Item 2's own text names
  2.6(ii) as the requirement, which is the `L(δ+4)` fact.
- `dev/literature/devlin-II5.md:257-268` (section 2.4, Step D). **USED** for
  section 2. The order must be a DEFINABLE well-order, never an element. That is
  the cure for `[LJ-1.16]`'s obstruction and it does not apply to this one.
- `dev/literature/devlin-II5.md:433-490`, the two UNRESOLVED OCR items.
  **CHECKED, and NEITHER touches the bound.** Item 6.5 is the carrier subscripts
  in 5.2's lines (c) and (j), which is the hull chapter. Item 6.6 is the
  displayed matrix of 2.2's `A(v, u)`, which is the formula BEFORE the binding
  step; the binding step and `K(u)` itself are clean in the OCR at `:614-620`.
  **WHY NOT further: an unresolved matrix layout cannot change a rank.**
- `dev/literature/devlin-errata.md`. **NOT USED. WHY NOT:** `[LJ-1.14]` checked
  that it does not cover Chapter II section 5
  (`_build/lj-1.16-report.md:144-145`). I did not re-check it.

## 10. ARCHIVE USED

- `_build/lj-1.12-report.md:30-40` (section 2.1, Route A's table). Took every
  booked row and both totals. This is the arithmetic of section 5.3.
- `_build/lj-1.12-report.md:41-52` (sections 2.2 and 2.3, Routes C and B).
  Confirmed that both rest on the same substrate, so the re-price transfers.
- `_build/lj-1.2-gate.md:27-45`. Took the measured 10 to 23 formula lines per
  light clause. It is the input to section 5.2's composition.
- `_build/lj-1.10-reprice.md:80-84`. The 40-lines-per-clause archive anchor.
  **I judge it an AVERAGE, and the report used it as a per-clause bound.**
- `_build/l3.32-t51-report.md:206`. Row (a), "the Σ₁ form of the level story
  (K(u)-binding set, bounded witness)", 0.40 to 0.75 thousand naive. **This is
  the archive's own price for statement 2, and it is what the 100-line gate
  contradicted.**
- `_build/l3.32-t51-report.md:208`. Row (c), the equivalence row, 0.30 to 0.80
  thousand. **The report cited `:208` and quoted `:206`'s number.** The number
  is the right one. The citation is two lines off.
- `_build/l3.31-r2probe-report.md:153-158`. **The retired route carried
  `hierL β ∈ˢ Sset γ` as an INDUCTION HYPOTHESIS.** This is the fourth cure and
  the report missed it while citing the same file.
- `_build/l3.31-r2probe-report.md:175-180`. `recL` cost 13 lines to re-derive
  because `L/Hierarchy` exports it nowhere. **MEASURED price of an unexported
  fact in this tree.**
- `archive/rud-route/src/L/Rud/LevelSigma.lagda.md:3-22` and `:210-212`. The J
  tower's level sigma collapses the Def clause by the Refine lemma, and it
  restricts the carrier to get its bound named. Both feed section 7.
- `_build/lj-1.16-report.md:43-51` and `:31-41`. The sibling rank claim, and the
  undelivered inverse of `placeFo`. Section 2 rests on both.
- `dev/LESSONS.md:829-843` (R-38) and `:2295`. The 25.7 seconds per unsealed
  invocation. Section 4.3 rests on it.
- `dev/LESSONS.md:782-796` (R-35), `:929-947` (R-40). R-40 names
  `limit-succ-mem` at `L.Rud.Hierarchy:455`. **I confirm the report: that module
  is archived, and the name survives only in
  `archive/rud-route/rud-route-src.patch`.** R-40's rule still binds; only its
  named cure is gone.
- `dev/ledger.toml:243-245` and `:273`. The DD24 bar and the wing's 99.6 to
  147.7 second budget.
- `scripts/ledger.py:120-136`. The pinned caliber. Comments inside a fence COUNT.

## 11. WHAT I AM NOT SURE OF

1. **I ran no Agda, under C-12.** I cannot confirm that the probe typechecks or
   that it takes 1.26 to 1.28 seconds. I confirm the files hold no `postulate`,
   no hole and no `TERMINATING` pragma. I confirm the line counts by recount.
   **The seconds are the report's word alone, and they are the load-bearing
   number.** Somebody with a slot should re-run the two files once.
2. **The 90-second wall does not check.** The report cites
   `src/ProbeLJ115b.agda:28-33` for a hang past 90 seconds with implicit
   arguments. Those lines hold the CURED form with explicit arguments. The
   walled form is not in the delivered file. **The wall may be real and it is
   not evidence.**
3. **My composition of the twelve clauses is ESTIMATED, not measured.** I assume
   four heavy quantifier clauses and eight light ones, and I scale `[LJ-1.2]`'s
   formula lines by the probe's own 155-over-68 ratio. A different split moves
   the row inside 0.7 to 1.9 thousand. **The conclusion that survives every
   split is that 155 for the WORST clause does not break a band whose top allows
   133 on average.**
4. **Cure A's acceptability is unchecked.** I did not read the wing's
   condensation consumers to see which α they use. If some consumer needs a
   limit that is not closed under adding ω, Cure A fails and Cure B is forced.
   **This is the cheapest thing left to check and I could not check it here.**
5. **I did not price Cure B in lines.** I state that `placeFo` and `⊨-place` are
   delivered and that the re-statement is a refactor. **A refactor of delivered
   content is not free, and I give no number. P-l forbids me to borrow one.**
6. **The rank arithmetic for the parameter-free code set is mine, not the
   tree's.** I argue that a parameter-free code holds no carrier member, so its
   rank is fixed at about ω·2. The tree proves no such lemma. **A probe should
   confirm it before anybody funds Cure B.**
7. **I did not verify `[LJ-1.16]`'s rank claim.** The sibling review holds it. I
   compared the two claims as stated, and my section 2 stands whether or not the
   α+1 figure is exact, because it rests on the relation-on-a-carrier shape.
