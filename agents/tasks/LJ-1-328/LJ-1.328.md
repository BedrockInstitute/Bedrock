# LJ-1.328: the definable well-order of L, AS A FORMULA

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THIS IS A REDIRECT, and the task that asked for it recommended against
## itself

**`[LJ-1.327]` was funded to describe the square law's pairing as a formula. It
priced that at about 820 lines and then said, in its own last line:**

> **Do not fund the square law's formula. Fund a probe on the definable
> well-order as a formula.**

**Three measurements drove that recommendation and you should re-derive each:**

1. **`pairω` is a WELL-FOUNDED RECURSION, not arithmetic.** It is the order
   collapse of the Gödel order: `col = W.induction ... colStep` at
   `src/L/Ordinal/SquareLaw.lagda.md:383-385`. **This refuted an earlier
   40-line estimate.**
2. **A coded square law is consumed by NOTHING that exists today. MEASURED.**
   `sq`'s only two consumers are AMBIENT, at `src/L/StageCardinal.lagda.md:63-68`
   and `src/L/BoundedSubset.lagda.md:1388-1391`, and they already have the
   ambient function.
3. **Devlin does NEITHER thing.** `dev/literature/devlin-II5.md:160-163` and
   `:411-419`: **he never needs the pairing definable in L**, because 5.6 gets
   it from generic cardinal arithmetic. **And `:360-362` calls the
   uniformly-Δ₁ level well-order「the single engine II.5 leans on most」.**

## THE OBJECT

**The definable well-order of L is DELIVERED, ambient, and SEALED:**

```agda
opaque
  orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))
  orderAt = ∈-induction famStep
```

`src/L/Choice/Step.lagda.md:739-741`. **Read the whole module, and read what the
seal costs and why it is there** (P-y prices a seal by how many definitions look
INSIDE it).

## THE QUESTION

**Can the definable well-order be described by a formula in the object
language, so that L's own order becomes an L-SET rather than an ambient
relation?**

**And what does that cost, against the delivered describe-and-carve machinery?**

## WHY IT IS THE RIGHT OBJECT, and check this reasoning rather than trusting it

**`[LJ-1.325]` already found half of it delivered:** `orderL : S` at
`src/L/Choice/Order.lagda.md:693`, **an order AS AN L-SET, with both adequacy
directions.** **Read it FIRST.** **If `orderL` already is what this task asks
for, say so and the task closes in an hour** — three times this month a report
called absent what the repository held (D-10).

**If `orderL` is the order at ONE stage and the object needed is the order
UNIFORMLY, name the gap and price it.**

**This object is upstream of several open things at once**, which is why it
beats the square law:

- **`[LJ-1.321]`'s live route.** A well-order on `sq α` gives its
  `2-Constant` map outright, and `pullOrder` at
  `src/L/Choice/Step.lagda.md:252-258` reduces that to an injection into any
  well-ordered carrier.
- **The restated trophy's reverse bound**, whose widest unmeasured term
  `[LJ-1.325]` named as **the order-type predicate in the object language**.
- **`[LJ-1.316]`'s diagnosis:** what blocks the classical move is that the
  object to select is an ambient FUNCTION, outside every well-ordered domain
  the tree has. **A coded order changes which side of that line objects sit
  on.**

**Say whether one description serves all three, or whether they want different
objects.** **That is the most valuable single thing you can return**, because
it decides whether this is one funded line or three.

## THE MACHINERY, and the brief that sent `[LJ-1.327]` got this WRONG

**MY EARLIER BRIEF SAID「`Carve` takes a formula」. That is FALSE, MEASURED by
`[LJ-1.327]`, and I record the correction here rather than repeating it:**

**There are TWO `Carve` modules and each HARD-WIRES its own formula**:
`src/L/InjChain.lagda.md:468` fixes `inclFo D` at `:480`;
`src/L/Absorption.lagda.md:385` fixes `shiftFo D γ ω z` at `:412`. **A fourth
site needs a fourth `Carve`, measured at about 127 lines.**

**The Absorption one is the caller contract for an AMBIENT function**, and it
demands: the function, its injectivity, **THREE READBACK LEMMAS** at
`src/L/Absorption.lagda.md:388-394` (**those are the description**), a decision,
the bound, and `sep`.

**No Δ₀ or Σ₁ certificate is demanded**: `hasSeparationL` is FULL separation for
an arbitrary `Formula S 1`, `src/L/Axioms/Full.lagda.md:144-145`. **MEASURED.**

**`src/L/Coding/Model.lagda.md` delivers 25 atomic constructors, so vocabulary
is not the distance.** **The distance is the OBJECTS.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`orderL` ALREADY IS IT.** **Say where, and this task closes in an hour.**
- **IT IS WRITABLE AND YOU BUILD THE DECISIVE PART.** Report the term, its
  lines, its seconds. **Do not build the whole thing; build the part that
  decides.**
- **IT IS EXPENSIVE.** Price it against the delivered comparables the way
  `[LJ-1.327]` did: **each term against ONE named delivered comparable, and say
  which is MEASURED and which is a comparable.**
- **IT IS BLOCKED.** Name what is missing at `file:line` and price THAT.
- **IT SERVES ONLY ONE OF THE THREE CONSUMERS.** **Say which, and the project
  funds it as one line rather than three.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-328/`. **`src/` is forbidden** (I-5).
- **Do not unseal `orderAt` in `src/`.** **If your work needs to see inside it,
  copy it into your probe and say what the seal costs you.**
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-327/ProbeLJ1327A.agda` and
  `agents/tasks/LJ-1-326/ProbeLJ1326A.agda`; you may not change them.
- **`src/L/GCH.lagda.md` was RESTATED and `src/L/BoundedSubset.lagda.md` had a
  slot-role cure landed, both hours ago.** **Read the CURRENT files.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling (`[LJ-1.322]`) is measuring CHECK TIMES.** Take ONE slot and
  report the load beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RUN A NEGATIVE CONTROL on anything you build.** **`[LJ-1.326]` and
  `[LJ-1.327]` both did, and both GOs are believable because of it: break the
  term deliberately and show Agda refuses at the exact point.** **A green
  typecheck with no control is a weaker result and this chain has stopped
  accepting them.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-328/lj-1.328-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**
**`orderL` may already be the answer. Check before you build.**

**C-44. A brief's claim is a measurement until you check it.** **This brief
carried a false claim about `Carve` in its predecessor and an agent caught it.
Assume this one carries another.**

**C-45. `exit 0` is not a supply.** **`orderAt` typechecks and is ambient, which
is exactly why it cannot serve.**

**C-42. A refutation measures the site it names.**

**P-y.** The seal on `orderAt` is priced by how many definitions look INSIDE it.

**P-l.** A judgement at one site is a hypothesis at another. **`[LJ-1.326]` ran
its miniature twice for this reason.**

**A STOP IS A DELIVERABLE, and「do not fund this, fund THAT」has now been the
most valuable return twice running.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**AND THIS OBJECT IS THE BEST DD4 CANDIDATE ON THE BOARD.** **The definable
well-order is what makes `L ⊨ AC` a theorem**, and `[LJ-1.321]` measured that
`pullOrder` in the AC trophy's own machinery already serves the GCH descent.
**A coded order would sit in the SHARED part by construction.** **Say whether
your object does, and whether it is tower-blind.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-327/lj-1.327-report.md`, read WHOLE.** It funds you, it
  names the four missing objects, and two of them are BUILT and green in its
  probe.
- **`agents/tasks/LJ-1-325/lj-1.325-report.md`**, which found `orderL` and
  named the order-type predicate as the reverse bound's widest term.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`**, the well-order route that is
  still live.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had a definable order too. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:360-362`**, which calls the uniformly-Δ₁ level
well-order the single engine II.5 leans on most. **Say what「uniformly Δ₁」
demands that a bare well-order does not**, because that phrase may be the whole
specification. Also **`dev/literature/truncation-and-selection.md`**, whose
diagnosis this object is aimed at. Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Choice/Order.lagda.md:693` and its module FIRST, because `orderL` may
already be the answer.

## SCOPE (write)

`agents/tasks/LJ-1-328/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, D-10, C-44, C-45, C-42, P-y, P-l.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-53, C-49, C-50, P-i, P-k, P-m, R-40, R-41.**
- **C-22, C-32, C-36, C-38, C-39, C-40.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: DELIVERED, WRITABLE, EXPENSIVE or BLOCKED.** Then what
`orderL` is and whether it already answers this. Then the gap, at `file:line`.
Then the price, each term against ONE named comparable, marked MEASURED or
COMPARABLE. Then whether ONE description serves all three consumers or whether
they want different objects. Then what「uniformly Δ₁」demands. Then your
negative control. **Mark every negative MEASURED or INFERRED.**
