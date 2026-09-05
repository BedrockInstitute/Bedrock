# LJ-1.574 review: `succ-assignment-definable` is a THREE-step obligation and
# this brief funds two of them

## HEAD
head_slot: coder
machine: shared
verdict: STOP

**THIS IS A STOP AND NOT A HEAP EVENT, NOT A BUDGET EVENT AND NOT A RED
PROBE.** `agents/tasks/LJ-1-574/Probe574.agda` is green, exit 0, and carries no
hole and no postulate. It does not inhabit `succ-assignment-definable`, and
this file says why with `file:line`.

## THE ONE SENTENCE THE BRIEF'S PREMISES DO NOT CARRY

Premise 1 cites `agents/tasks/LJ-1-552/review-of-succ-assignment.md:161`. That
line is `BRIEF NEEDS.** `[LJ-1.549]` recorded its residue as two independent missing`,
and the sentence the brief quotes from it is four lines later, at `:165-169`.
The premise is TRUE and the reading is right. **But the same file prices this
obligation 16 lines past where the brief stopped, and the price has THREE items
and not one:**

> 2. **The square law INSIDE L**: an L-set injection of κ × κ into κ. The tree
>    has only the ambient one, cited in finding 3(c).
> 3. **The formula that carves the coded subset out of κ**, given 1 and 2, by
>    `hasSeparationL`.
>
> Step 2 is a chapter and not a task. **A brief that funds this obligation
> without funding step 2 is funding half a task**, and that is the same shape
> of error `[LJ-1.549]` recorded about its own residue.

`agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-192`.

**THIS BRIEF DOES NOT FUND STEP 2, AND IT FORBIDS THE ROW THAT WOULD.** Its
`## THE REASONING` says "DO NOT ATTEMPT ROWS 1, 2, 3 OR 4", and row 2 of
`[LJ-1.564]`'s bill is `P550.SqAt` (`agents/tasks/LJ-1-550/Probe550.agda:309-310`),
which is `SqLaw` (`Probe550.agda:82-86`): an AMBIENT function
`⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫`. **So even paying row 2 in full would not supply step
2**, because step 2 asks for an L-SET and row 2 delivers an ambient function.
`[LJ-1.552]` finding 3(c) says exactly that at
`review-of-succ-assignment.md:126-133`: "Every one of them is an AMBIENT
function `⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫`. An ambient pairing carries an L-set to an
ambient subset of κ, which is (b) again."

## I RE-MEASURED IT AT THIS SITE RATHER THAN INHERIT IT

`AGENTS.md:45` forbids transferring a measured cure by analogy, and the same
discipline binds a measured obstruction. So the file does not quote
`[LJ-1.552]`; it re-derives the shape as types.

**`Obligation` (`Probe574.agda`, section 6) and `[LJ-1.549]`'s `Residue δ κ`
are the SAME REQUEST, and two typechecked terms say so, not a sentence:**
`residue-closes` and `obligation-gives-residue`. So the brief's target is
`Residue δ κ`, which `[LJ-1.549]` recorded and which nothing in `src/`
inhabits (`agents/tasks/LJ-1-549/Probe549.agda:658-660`: "NOTHING IN THIS FILE
INHABITS `Residue`. NOTHING IN `src/` DOES.").

**AND `Residue δ b` IS INHABITED IN THIS FILE AT `b := LsetS β oβ`**
(`Probe574.agda`, `residue-at-stage`). The two types differ in ONE symbol, the
bound. That symbol is step 2 and step 3.

## WHAT THE STOP IS NOT

It is not "the reflection step does not bound the search". **W3 came out GO**
(`agents/tasks/LJ-1-574/runs/W3.agda`, three cold runs exit 0). The brief
anticipated a NO-GO there and named it "THE LAST OPEN QUESTION ON THIS ROW";
that question is now CLOSED, and closed positively:

- `InjL a κ` IS the object language's own unbounded existential at a formula
  (`Probe574.agda`, `injL-is-search` and `search-is-injL`). `[LJ-1.557]`'s
  objection, "a quantifier over the whole L-carrier and not over a stage"
  (`agents/tasks/LJ-1-557/lj-1.557-report.md`, `## POINTWISE AGAINST UNIFORM`),
  is answered.
- One stage holds a code for EVERY member of δ (`codes-at-one-stage`).
- The least such code is selected at that stage, injectively (`Select`), and a
  formula describes the selection in both directions (`Link.link`).

**So steps 1 and 3 of `[LJ-1.552]`'s price are paid at the stage, and the
pointwise-to-uniform gap that `[LJ-1.557]` named is closed.** Only the bound
is left.

## WHAT I DID NOT DO

I did not inhabit `Obligation`. I did not postulate. I did not weaken the
obligation's type and call it the obligation: the weakened form is named
`stage-assignment-definable` and its type carries `LsetS β oβ` in plain sight.
I did not attempt rows 1, 2, 3 or 4. Nothing lands in `src/`. I did not commit
and did not push.

## WHAT WOULD REOPEN THIS

One of two, and the choice is the mathematician's and not mine.

1. **FUND STEP 2 AS ITS OWN TASK.** An L-set injection code from the pairs of
   κ into κ. `[LJ-1.552]` priced it as a chapter. If it lands, step 3 is a
   `hasSeparationL` over the description this file already carries, and the
   selection machinery of sections 3 and 4 is reused unchanged.
2. **ASK WHETHER `LsetS β oβ` IS ENOUGH FOR SOMETHING ELSE ON THE BILL.**
   `residue-at-stage` is a delivered term with a free bound. `[LJ-1.549]`
   section 2 measured that the freedom in `b` is worth nothing FOR B10; it did
   not measure what a definable injective assignment of δ into a STAGE is worth
   elsewhere, and B9 (`StageCountedCoded`) is stated at a stage.
