# LJ-1.327: the square law needs a FORMULA, not an adapter

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHERE THIS SITS, and why it is now the ONLY thing that matters on this leg

**Three tasks in a row shrank the restated trophy's first debt, and each one
shrank it by MEASURING rather than by arguing:**

- `[LJ-1.323]`'s ruling priced「the final injection, delivered coded」at about
  **800 naive lines**, by survey.
- `[LJ-1.325]` found the survey used the WRONG comparable and re-priced the
  adapter at about **25**.
- **`[LJ-1.326]` BUILT it: the adapter is 8 lines, MEASURED at `absorbs`'s own
  site**, `agents/tasks/LJ-1-326/ProbeLJ1326A.agda:81-91`, exit 0. **And it
  built the sibling `InjL κ (𝒫 κ)` in 14 lines.**

**So the adapter half is finished as a question. What remains is ONE thing and
it now dominates entirely.**

## THE THING, stated as `[LJ-1.326]` measured it

> **`pairω` at `src/L/InjChain.lagda.md:175-176` and `squareω` at `:184-185`
> are a bare AMBIENT function and an injectivity proof.** **`Comp` at
> `:314-323` demands EIGHT arguments, the four conjuncts of each side.**
>
> **The gap is a missing FORMULA, not a missing adapter.**

**And `[LJ-1.326]` added a finding nobody had stated:** **`Comp`'s parameter
list IS `InjCode`'s four fields written out twice, so the coded composition
needs no adapter at all.** **Verify that; it decides how your result plugs in.**

## THE QUESTION

**Can `pairω`'s graph be DESCRIBED by a formula in the object language, so that
the four conjuncts can be carved for it as they are for the shift and the
inclusion?**

**If yes, the square-law leg enters `Comp` and debt 1 closes.**
**If no, name what blocks it, because that blocker then prices the whole leg.**

## WHAT「DESCRIBE」MEANS HERE, and the tree has the pattern three times

**`Carve` and `InclGraph` take a formula and produce an L-set with its four
conjuncts.** **Three delivered sites already do this**, and `[LJ-1.326]`
measured that they work because `Carve` and `Comp` were written generic:

| site | what it describes |
|---|---|
| `src/L/Absorption.lagda.md:538-605`, `ShiftGraph` | the shift |
| `src/L/InjChain.lagda.md:478-547` | the inclusion |
| `src/L/InjChain.lagda.md:337-422` | the composite |

**Read all three before you write anything.** **Your job is the FOURTH: the
pairing.**

## THE MATHEMATICS, stated plainly so you can judge the difficulty yourself

**`pairω` is the ordinal pairing at ω: a bijection between `α × α` and `α`.**
**Classically it is Gödel's pairing function and its graph is definable.** **The
question is not whether a formula EXISTS in principle. It is what it costs to
write THIS one in THIS object language, against the delivered `Formula`
machinery.**

**So the deliverable is a PRICE with a basis, and a term if you can reach one.**

## THE FOUR THINGS TO MEASURE

**1. WHAT `pairω` ACTUALLY IS.** Read `src/L/InjChain.lagda.md:160-200` whole.
**Report its definition, not its type.** **If it is built from a delivered
ordinal construction, the formula may be a composition of formulas that already
exist.**

**2. WHAT `Carve` DEMANDS.** Find it, read its signature, and state exactly what
a caller must supply: the formula's arity, its free slots, and any Δ₀ or
Σ₁ certificate. **`[LJ-1.318]` landed a slot-role cure in
`src/L/BoundedSubset.lagda.md` hours ago, so read the CURRENT file and not any
report written before it.**

**3. THE DISTANCE.** **How far is `pairω`'s graph from something the delivered
`Formula` vocabulary can say?** **Name the missing pieces at `file:line`.**

**4. THE PRICE.** One number with its basis named (DD8): a build, a delivered
comparable, or a survey. **The three delivered describe-and-carve sites are your
comparables and you should use them rather than guessing.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE FORMULA IS WRITABLE AND YOU WRITE IT.** **Then debt 1 closes and this
  is the largest single result available tonight.** Report the term, its lines
  and its seconds. STOP.
- **IT IS WRITABLE AND EXPENSIVE.** Price it against the three comparables and
  name the widest remaining term.
- **IT NEEDS SOMETHING UNDELIVERED.** **Name it at `file:line` and price
  THAT.** **That is the honest answer and it is what the project needs to
  decide the leg.**
- **`pairω` IS NOT THE RIGHT OBJECT.** **If the leg can be closed another way,
  say so; a cheaper route beats a described `pairω`.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-327/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.** **You may READ and RE-RUN
  `agents/tasks/LJ-1-326/ProbeLJ1326A.agda`; you may not change it.**
- **`src/L/GCH.lagda.md` was RESTATED hours ago and typechecks.** Read the
  CURRENT file; `InjL` and `SuccCardL` live there now.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling (`[LJ-1.322]`) is measuring CHECK TIMES.** **Take ONE slot and
  report the load beside every figure.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-327/lj-1.327-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**C-45. `exit 0` is not a supply.** **`pairω` typechecks and is useless to
`Comp`, because an ambient function is not a coded one. That is this task in one
line.**

**C-44.** Every claim above is `[LJ-1.326]`'s, `[LJ-1.325]`'s or mine. **The
chain that got here shrank an 800-line survey to 8 measured lines by re-deriving
its predecessors, three times running. Do the same.**

**C-42. A refutation measures the site it names**, and `[LJ-1.326]` said so
about its own GO: **it measured the assembly at three sites and could not say
how many legs of the chain remain uncarved.** **Say how many, if you can.**

**P-l. A judgement at one site is a hypothesis at another.** **`[LJ-1.326]` ran
its miniature TWICE for exactly this reason. Follow that discipline.**

**C-36. A failed substitution is not a proof of impossibility.**

**A STOP IS A DELIVERABLE.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**AND `[LJ-1.326]` MEASURED A DD4 RESULT YOU SHOULD PROTECT.** Its 8-line
adapter costs 8 lines **because `Carve` and `Comp` were written generic**, and
its three modules add zero new mathematics. **Write your formula so the same
holds: generic where the delivered machinery already is.** **Say in one line
whether your term is tower-blind.**

**Also: `[LJ-1.326]` measured that the restatement's 2.0-point DD4 rise is an
artifact the proof hands straight back**, and that both terms together restore
39.1 percent exactly. **Your term is part of that restoration; say what it adds
to the GCH closure.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-326/lj-1.326-report.md`, read WHOLE.** It funds you and
  it is the authority on the assembly pattern.
- **`agents/tasks/LJ-1-325/lj-1.325-report.md`**, which named the square-law leg
  as the widest unmeasured term.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route described objects in an object language too. **Say what would
  not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin's square law is II.5 and his
pairing is definable in L by construction.** **Say in one line whether he
describes the pairing's graph explicitly or gets it from a general definability
lemma**, because if it is the latter, the tree may want that lemma rather than
this one formula. Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/InjChain.lagda.md:160-200` and `:314-323` FIRST. Then the three
describe-and-carve sites named above.

## SCOPE (write)

`agents/tasks/LJ-1-327/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, DD8, C-44, C-45, C-42, C-36, P-l.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-53, C-49, C-50, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-10, D-26.**
- **DD0, DD4, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: WRITABLE, EXPENSIVE or BLOCKED.** Then what `pairω`
actually is, from its definition. Then what `Carve` demands of a caller. Then
the distance, with the missing pieces at `file:line`. Then the price with its
basis. Then how many legs of the chain remain uncarved, if you can say. Then
what your term adds to the GCH closure. **Mark every negative MEASURED or
INFERRED.**
