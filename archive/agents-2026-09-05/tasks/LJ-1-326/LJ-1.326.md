# LJ-1.326: the miniature that gates BOTH new debts

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE FINDING THIS TESTS, and it is `[LJ-1.325]`'s

**`InjCode` is a FOUR-PART product at `src/L/Cardinal.lagda.md:223-228`.**
**Three delivered modules already build an L-set by separation and prove
exactly those four facts about it, under their own heading「THE FOUR
CONJUNCTS」:**

| module | what it proves the conjuncts for | lines |
|---|---|---|
| `src/L/Absorption.lagda.md:448` | the shift, A6's `absorbs` | `:410-498` |
| `src/L/InjChain.lagda.md:376` | the COMPOSITE of two coded injections | `:337-422` |
| `src/L/InjChain.lagda.md:513` | the INCLUSION | `:478-547` |

**All three are opened `public` at their L instantiation, so the coded
witnesses are reachable today.** **MEASURED by `[LJ-1.325]`, and the three
headings verified by me.**

**AND THE DELIVERED CODE THROWS THEM AWAY AT THE LAST STEP.**

## THE TASK, and it is small on purpose

**Build `InjL κ (𝒫 κ)` from `L.InjChain`'s `InclGraph`.**

**The mathematics is one line:** every member of an ordinal is a SUBSET of it,
so `κ ⊆ 𝒫 κ` gives the inclusion, and the inclusion's four conjuncts are
already proved.

**`[LJ-1.325]` prices it at about 10 lines and says it gates BOTH new debts.**
**Re-derive that claim before you accept it** (C-44).

## WHY IT GATES BOTH, and check this reasoning rather than trusting it

**Debt 2, the reverse bound `InjL δ (𝒫 κ)`**, is the new half of the restated
trophy and it has **no lemma behind it: MEASURED, the tree has no Cantor lemma,
zero grep hits.** **If a coded injection can be assembled at all from delivered
conjuncts, this miniature is the cheapest demonstration.**

**Debt 1, the coded final injection**, needs the same assembly move at a
different pair.

**So a GO here says the assembly pattern works and both debts are priced
against a MEASURED move rather than a survey.** **A NO-GO says the delivered
conjuncts do not compose into an `InjCode` and both survey prices are
unfounded, which is a much bigger finding than ten lines.**

## THE SECOND MINIATURE, if the first is cheap and green

**`[LJ-1.325]` replaced the ruling's named miniature for debt 1 and gave two of
its own. Take miniature A if you have budget:**

> **Miniature A: form the tuple `(sv , dm , ij , ran)` at type `InjCode`, about
> 10 lines, one run.**

**It measures whether the four delivered facts TYPE as an `InjCode`, which is
the question the whole 800-line survey rested on.**

**Do NOT attempt miniature B**, describing and carving `pairω`, about 40 lines.
**That is a separate dispatch and this task must stay small.**

## THE WIDEST UNMEASURED TERM `[LJ-1.325]` NAMED, and you must NOT try to close it

**Debt 1's real blocker is the SQUARE LAW leg**: `pairω` at
`src/L/InjChain.lagda.md:175-185` and `squareω` at `:184` **return bare ambient
functions, and `SquareLaw` names no formula, so that leg cannot enter `Comp`.**

**That is out of scope here.** **If your miniature runs into it, STOP and say
so; naming where it bites is worth more than a partial attempt.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`InjL κ (𝒫 κ)` BUILDS.** Report the term and its lines. **Then the assembly
  pattern is MEASURED and both debts re-price against it.** **Try miniature A,
  then STOP.**
- **IT DOES NOT BUILD.** **Name the conjunct that will not close, at
  `file:line`.** **That refutes both survey prices and it is the most valuable
  outcome available for ten lines.**
- **THE INCLUSION IS NOT AT THE PAIR YOU NEED.** **Say what pair it IS at and
  what a translation would cost.**
- **IT NEEDS THE SQUARE LAW LEG.** **STOP. Say where.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-326/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.**
- **`src/L/GCH.lagda.md` was RESTATED hours ago** by the `[LJ-1.323]` ruling and
  it typechecks. **Read the CURRENT file; do not trust any report written
  before it.** `InjL` and `SuccCardL` live there now.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling (`[LJ-1.322]`) is measuring CHECK TIMES and needs a quiet
  machine.** **Take ONE slot, keep your runs short, and report the load beside
  every figure so the sibling's noise is attributable.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-326/lj-1.326-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**C-45. `exit 0` is not a supply.** **The three modules PROVE the conjuncts and
then discard them. A proof that exists and is not exported supplies nothing.**

**C-44.** Every claim above is `[LJ-1.325]`'s or mine. **Re-derive the three
headings and the `public` opens yourself.**

**C-36. A failed substitution is not a proof of impossibility.** If the tuple
will not type, write the tuple you could not write.

**C-52. A sweep names the discriminating property.** **`[LJ-1.325]` found the
ruling priced debt 1 against the wrong comparable, because
`src/L/Coding/Injection.lagda.md` runs CODE to AMBIENT in every module and the
AMBIENT-to-CODE sites are elsewhere. Do not repeat that: check which direction a
module runs before you cite it.**

**D-1, DD8.** This task exists to turn two survey prices into gated ones.

**A STOP IS A DELIVERABLE.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**AND THERE IS A LIVE DD4 ANOMALY YOU SHOULD KNOW ABOUT.** `[LJ-1.325]`
measured that the restatement pushed `Absorption`, `InjChain` and
`Axioms/Infinity` OUT of the GCH closure: GCH went 51 masters and 9,967 lines
to **48 and 8,889**, SHARED went 44 and 7,632 to **43 and 7,596**, and the
share ROSE from 39.1 to 41.1 percent **because the denominator fell faster.**
**So DD4's figure got prettier while nothing about the mathematics improved**,
and the understatement `dev/ledger.toml:204` names grew by about 1,027 lines,
because the two chapters the proof needs MOST are now outside the closure.
**`InjChain` is one of them, and it is the module you are about to build
from.** **Say in one line whether your term would pull it back in.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-325/lj-1.325-report.md`, read WHOLE.** It funds you and
  it is the authority on the four conjuncts and on both debts.
- **`agents/tasks/LJ-1-323/lj-1.323-ruling.md` section 4**, the damage estimate
  this task is testing.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route assembled coded objects too. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`.** **A set theorist gets
`κ⁺ ≤ 2^κ` from Cantor and the definition of the successor cardinal, and the
tree has no Cantor lemma.** **Say in one line whether the classical route needs
anything your assembly does not give.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/InjChain.lagda.md:478-547`, the inclusion and its four conjuncts, FIRST.
Then `src/L/Cardinal.lagda.md:223-228`, `InjCode` itself.

## SCOPE (write)

`agents/tasks/LJ-1-326/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, DD8, C-44, C-45, C-36, C-52.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-53, C-49, C-50, P-i, P-k, P-l, P-m.**
- **C-22, C-32, C-38, C-39, C-40, C-42.** I-5. **D-10, D-26.**
- **DD0, DD4, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: BUILDS or BLOCKED.** Then the term or the conjunct that
will not close, at `file:line`. Then its lines and seconds, with the load.
Then miniature A's result if you reached it. Then what each debt's price becomes
now that the assembly move is MEASURED rather than surveyed. Then whether your
term pulls `InjChain` back into the GCH closure. **Mark every negative MEASURED
or INFERRED.**
