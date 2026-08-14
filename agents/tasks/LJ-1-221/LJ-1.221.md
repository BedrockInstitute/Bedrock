# LJ-1.221: DD25 review of two stops, and of the brief pattern that produced them

tier: opus (deepseek-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** Both targets were written by pi, so DD17's invariant
holds: the critic is never the same head as the author.

## GOAL

**Two returns today stopped by design, and both stops were branches I wrote into
their own briefs.**

| target | verdict | what it produced |
|---|---|---|
| `[LJ-1.216]` | **NO, AND IT NAMED THE BLOCKER** | brick one: the DELIVERED `L.Coding.Model`, at `GenPowersetAtAmbient.agda:68` |
| `[LJ-1.219]` | **MODEL LINK COMPOSES, BRICK TWO LEAKS** | brick two: `L.Coding.Recover`'s `keyOf`, at `JoinAtAmbient.agda:142` |

**Review both. One report. And then review the thing neither agent could see.**

## THE THIRD TARGET, and it is me

**Each brief told its agent: name the next brick and STOP, one link per task, so
a failure is always attributable.** **Both agents obeyed. Both returns are
clean. And the pattern has now consumed three dispatches to walk two links of a
seventeen-module chain.**

**`[LJ-1.211]` MEASURED that briefs caused 8 of 10 overturns on record, and that
the largest single cause, four of ten, is「the brief fixed a method that could
not answer the question」.**

**So the question this review exists for: is「one link per task」a sound method,
or is it a method that guarantees fifteen more dispatches and answers the
chain's price on none of them?**

**I have already dispatched `[LJ-1.220]` on the opposite bet:** parameterize
every leak instead of porting it, and census the chain in one pass. **Do not
read that as settled.** If parameterizing cannot work, say why, and the walk is
vindicated. **An independent answer either way is the point.**

## WHAT YOU ATTACK, per target

**Four questions, in this order:**

1. **Is the stop correct ON ITS OWN NUMBERS?** Re-derive them from the evidence
   each report cites, at `file:line`. **`[LJ-1.219]` claims five Model names
   typecheck at the ambient class and that `extAt-in` and the `domAt` trio were
   never reached. Check the file.**
2. **Is the measurement sound?** Both verdicts rest on an exit code and a line
   number rather than on seconds, which is the strong form. **So check the
   inverse: does the exit code mean what the report says it means?** A
   `UnequalTerms` at `:142` proves the term at `:142` does not typecheck. **It
   does not by itself prove the named module is the cause.**
3. **Did the BRIEF cause the outcome?** Both briefs named the abort branch that
   fired. **A branch that fires because the brief made it easy to fire is not a
   finding.** Say whether the agent had a real alternative.
4. **Is there a cure either return MISSED?**

**A review that AGREES is a real result.** Do not manufacture a disagreement.
**The record says the reviewer has been wrong 0 times in 25 decided reviews; do
not spend that.**

## THE LOAD-BEARING CLAIM OF THE WHOLE CHAIN

**`[LJ-1.213]` said: the fixed suppliers import the tower, so each must port
before its consumer can. It called that an ORDER and not a wall.**

**Everything since rests on that sentence.** `[LJ-1.216]` and `[LJ-1.219]` each
confirmed one step of it and neither tested the sentence itself.

**Attack it.** Is「port bottom-up」a fact about Agda's module system, or is it an
artifact of the way these probes are written? **A module parameter, a record of
operations, or an anonymous module argument can all supply a name without
porting its home.** **Say which of those the delivered tree already uses**, at
`file:line`, and whether any of them dissolves the order.

## C-42 BOTH DIRECTIONS, on each target

**A refutation measures the site it NAMES and never how far that site EXTENDS.**
**So ask of each: does it reach FURTHER than it claims, and does it reach LESS
far?**

**`[LJ-1.219]` is explicit that the other suppliers are INFERRED and refuses to
price them.** **Check that it kept that discipline everywhere, including in its
DD4 table.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

**Per target, one of:**

- **UPHELD.** Correct on its numbers. Say what you checked.
- **OVERTURNED.** Give the evidence at `file:line` and say what it unblocks.
- **UPHELD BUT MISATTRIBUTED.** The verdict is right and the CAUSE is wrong,
  most often the brief. **Three reviews today came back this way.**
- **UNDECIDABLE ON THE RECORD.** Say what evidence is missing. Do not guess.

**Then a THIRD verdict, on the method**, in one of these words: **SOUND**,
**WASTEFUL** or **UNDECIDABLE**. **A report that reviews the two tasks and
skips the method is incomplete**, because the method is why this review was
sent.

## WHAT YOU MUST NOT DO

- **Do not edit any master, brief or report.** Frozen records. **You write your
  own report and nothing else.**
- **DO NOT RUN AGDA.** Two siblings hold both Agda slots. **This review is a
  reading of the record and of four probe files that are on disk.**
- **Do not re-litigate the route.** DD2 rules the endpoint. **Do not reopen the
  chapter dissolution:** `[LJ-1.196]` said chapter, `[LJ-1.200]` refuted the
  word, `[LJ-1.210]` built the answer.
- **Do not touch `agents/tasks/LJ-1-217/`, `LJ-1-218/` or `LJ-1-220/`.** Three
  siblings are live there.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD4 is the entire reason the port exists, and it is still INFERRED.** No
ambient instantiation of `Powerset` has ever typechecked. **So ask the hard
version: if the chain's width turns out to be twelve modules rather than two,
at what count does the port stop being worth its plumbing?** `[LJ-1.213]` gives
389 shared, 12 plumbing, 8 residual at one module. **You are not asked to invent
a threshold. You are asked whether anything on record supports one.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-216/` and `agents/tasks/LJ-1-219/`** in full: the briefs,
  the reports, `GenPowersetAtAmbient.agda` and `JoinAtAmbient.agda`. **Read the
  probes, not the reports' accounts of them.**
- **`agents/tasks/LJ-1-213/lj-1.213-report.md`** and its four probes: the
  order claim you are attacking.
- `agents/tasks/LJ-1-210/lj-1.210-report.md` and `GenModel.agda`.
- **`agents/tasks/LJ-1-211/lj-1.211-report.md`**: the cause split, which tells
  you what to look for in a brief.
- `src/L/Coding/Powerset.lagda.md`, `src/L/Coding/Model.lagda.md`,
  `src/L/Coding/Recover.lagda.md`: **read where the tower enters, not the
  reports about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route may already hold a generic-over-a-class pattern. Take
  SHAPE from the archive, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:301-302` says Devlin's construction is
class-generic in his own words, and `:370-382` splits II.5 into nine
tower-neutral steps and three per-tower ones.** **`[LJ-1.219]` concluded the
table splits mathematics and not modules. Say whether that reading holds.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-219/lj-1.219-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-221/lj-1.221-report.md` ONLY.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **D-10.** Price the truth of a recorded target before pricing its proof.
- **C-22.** Write your deliverable incrementally, never at the end.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40. D-26, D-29, D-30. I-5.
  DD0, DD8, DD25.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` on BOTH sides. Write ASD-STE100.

## RETURN

**Lead with three verdicts in three words: `[LJ-1.216]`, `[LJ-1.219]`, and the
METHOD.** Then each target's four questions, answered. Then C-42 in both
directions on each. Then your attack on「port bottom-up」, with what the
delivered tree does at `file:line`. Then what each unblocks or confirms.
**Mark every negative MEASURED or INFERRED.**
