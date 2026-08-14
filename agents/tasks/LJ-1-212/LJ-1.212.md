# LJ-1.212: build the PREMISES gate, `[LJ-1.211]`'s change 1

tier: pi (in-harness-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** This gate is built against the orchestrator's own briefs
and the orchestrator writes them, so DD17's invariant applies: the critic is
never the same head as the author.

## GOAL

**`[LJ-1.211]` measured the cause of every DD25 overturn on record. The briefs
caused 8 of 10. The reviewer caused 0.**

| cause | count |
|---|---:|
| the brief fixed a method that could not answer the question | **4** |
| the brief carried a false premise | 2 |
| the brief shipped a conclusion as an instruction | 2 |
| the agent erred on its own, with the brief clean | 2 |
| the reviewer was wrong | **0** |

**Build the gate it proposed, which is the cure the reviews themselves wrote.**

## THE MECHANISM, in `[LJ-1.211]`'s words

**A checker, shaped like `scripts/check-dd25-review-named.py`, refuses a brief
that carries a TRIGGER TOKEN and has no `## PREMISES` section.**

**The trigger tokens it names:** `the gate is`, `GO needs`, `NO-GO is`, `the
only lever`, `shapes`, `section`, a LESSONS law ID, `do not weaken`, `measure
it, do not argue it`, **or a figure with a unit.**

**The section lists each load-bearing premise with a basis at `file:line`. The
return marks each premise VERIFIED or REFUTED at `file:line`. A DD25 review
attacks that list before anything else.**

## THE TWO REVIEWS THAT WROTE THIS CURE, and they are the evidence

- **`[LJ-1.66-R]`:** 「GO only if (a) the unit cost is 0.05 s or more AND (b) the
  applications genuinely collapse. **Verify (b) by reading the sites BEFORE you
  build anything**」
  (`agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258`).
- **`[LJ-1.15-R]`:** 「Derive every line gate from the booked row's own per-unit
  figure, **and write that derivation in the brief**」
  (`agents/tasks/archive/LJ-1-15/lj-1.15-review.md:407-409`).

**Read both. The gate exists to make those two sentences mechanical.**

## THE HARD PART, and it is where a bad gate would do damage

**The trigger list is BROAD on purpose and it will fire on briefs that are
fine.** A gate that fires wrongly trains the author to paste a heading, and a
pasted `## PREMISES` section is worse than none because it looks like diligence.

**So:**

1. **MEASURE THE FALSE-POSITIVE RATE FIRST.** Run the trigger list over every
   live brief and count how many fire. **If most fire, the list is wrong and you
   say so before building anything.**
2. **Tune the tokens against the record**, not against taste: a token earns its
   place if a brief carrying it produced an overturn, or if `[LJ-1.211]` names
   it.
3. **The refusal message must be actionable in one read**: name the token that
   fired and show the section's shape.

## THE PRE-EPOCH QUESTION, answered the way this project already answers it

**Every brief before today is a frozen record.** `check-dd4-stated.py` solved
this with a `PRE_EPOCH` set: the twelve frozen briefs are reported once and
never fail. **Do the same.** **But COUNT the backlog and report it**, because
that number is the honest scale of the lapse.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT AND GREEN.** The real tree passes after grandfathering, a synthetic
  brief with a trigger and no `## PREMISES` fails, and the false-positive rate
  is measured. **Show all three.** STOP.
- **THE TRIGGER LIST IS UNWORKABLE.** If it fires on most briefs, **say so with
  the count and propose a narrower list**, or say the gate should be a REPORT
  rather than a gate. `check-archive-cited.py` is that shape and its docstring
  argues the case.
- **THE PREMISE SECTION CANNOT BE CHECKED MECHANICALLY.** If 「a basis at
  `file:line`」 cannot be told from prose, **say so.** A gate that checks a
  heading and calls it a premise check is the false safety `AGENTS.md` names.

## WHAT THE GATE MUST ADMIT IT CANNOT DO, in its own docstring

- **It cannot tell whether a premise is TRUE.** It checks that the author
  listed one and gave it a basis.
- **It cannot tell whether the basis at `file:line` says what the author claims.**
- **It cannot fire at the moment the brief is WRITTEN**, which is when the
  failure happens. It fires at the commit or the gate.

**`AGENTS.md` says a row claiming more than its checker delivers turns a rule
into false safety. Write the limits down.**

## WHAT YOU MUST NOT DO

- **Do not edit `dev/PLAN.md` or any `DD` row.** DD0: a row is the owner's.
- **Do not edit any brief or report but your own.** Frozen records. **In
  particular do not add `## PREMISES` sections to existing briefs**: that is a
  backlog to grandfather, not to rewrite.
- **Do not run Agda.** Siblings hold Agda processes.
- **Do not dispatch an agent.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.
- **Create your report file in your FIRST five minutes (C-22).**

## THE CLASSIFICATION I WANT

**MEASURED or INFERRED, in those words**, and **the false-positive rate is
MEASURED or the gate does not land.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Write the trigger vocabulary as a TABLE, not as a regex inside a function.**
`[LJ-1.208]`'s gate needed a negative-verdict vocabulary and this one needs a
premise-trigger vocabulary; **a third rule will need a third, and a vocabulary
written inline is paid for every time.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-211/lj-1.211-report.md`**, read WHOLE. **The cause split,
  the proposal, and its two source reviews.**
- **`scripts/check-dd25-review-named.py`** and **`scripts/check-dd4-stated.py`**,
  read WHOLE. **The shape to follow: a narrow gate, an epoch set, and a
  docstring that states its own limits.**
- `agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258` and
  `agents/tasks/archive/LJ-1-15/lj-1.15-review.md:407-409`: **the two reviews
  that wrote this cure.**
- `scripts/check-archive-cited.py`: the REPORT shape, for the case where a gate
  would buy a pasted answer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-211/lj-1.211-report.md` FIRST, whole.

## SCOPE (write)

`scripts/check-<your-name>.py`, `Makefile`, `scripts/tests/` for its test, and
`agents/tasks/LJ-1-212/lj-1.212-report.md`. **Nothing else.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **C-37.** State a law with the ACTION it prescribes, never only the
  prohibition. **`[LJ-1.211]` names C-37 as the law behind its change 3, and it
  binds your docstring too.**
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-39, C-40.
  I-5. DD0.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **The checker must stay valid Python**: `python3 -m py_compile` after every
  edit, and report that you did.
- **No em dash in any language.**
- Evidence is a command and its output, or a `file:line`. Write ASD-STE100.

## RETURN

**Lead with the FALSE-POSITIVE RATE over the live briefs, then the three runs.**
Then the trigger table as you tuned it, with why each token earns its place.
Then the backlog count. Then what the gate cannot see, quoted from your
docstring. Then the `make check` wiring. **Mark every claim MEASURED or
INFERRED.**
