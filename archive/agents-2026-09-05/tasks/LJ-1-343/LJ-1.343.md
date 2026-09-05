# LJ-1.343: repair the two vacuous telescopes in `src/L/Condensation.lagda.md`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHAT IS WRONG IN THE DELIVERED TREE

**`[LJ-1.341]` proved, by machine, that two hypotheses of two delivered modules
are FALSE, and not merely unproved: their TYPES ARE EMPTY at every environment
and every bound slot.**

**The countermodel is one move:** instantiate `z` with **the bound itself**, the
set the conclusion names. **Nothing forbids it.** Then

- `defPairK` asserts a three-step membership cycle, and
- `envK` asserts a four-step one,

**and `regularityV` at `src/V/Hierarchy.lagda.md:139-144` refutes both.**
`agents/tasks/LJ-1-341/ControlA341.agda:54-91` restates the chapter's own two
types **VERBATIM**, at both index forms, and discharges all four into `⊥`.

**CONSEQUENCE:** `DefinesAgree` at `src/L/Condensation.lagda.md:6779-6834` and
`LeafAgree` at `:7107-7243` are **VACUOUS**. **Their telescopes cannot be
inhabited, so their `out` and `back` prove nothing anything can use.**

**And no conjunct of either formula bounds `z`. MEASURED**, by reading both
whole: `tagAtL-adequate` makes the premise EQUAL to a bare set equation, and
`envOneAt-out` likewise. **The bound is nowhere in the formula.**

## THE REPAIR, and both halves are already TERMS

**Bound `z` by the CARRIER slot `w`, not the bound slot `K`.**

**The hypothesis is FREE.** It is `hz`, **already bound** at
`DefinesAgree.fwd` (`:6798`) and `.bwd` (`:6813`), **and both `go` blocks sit
inside those `where` clauses.** **The sibling tie `satK` at `:7187-7189` already
carries exactly this bound inside its formula**, and `[LJ-1.338]` discharged it
in one line.

**Lines to change:** `src/L/Condensation.lagda.md:6781-6785` and `:7183-7186`.
**Call sites to feed:** `:6811`, `:6820`, `:6826`.

**Both repaired statements are TERMS** at
`agents/tasks/LJ-1-341/ProbeTies341.agda:248-266` and `:280-294`. **One gap
named:** `KFacts` carries no SINGLETON closure and `envOne v` is a singleton;
**it is TWO lines from `BoundOver.pr∈λ` at `src/L/Coding/Bound.lagda.md:69` and
`trans∈λ` at `:93`**, measured at `ProbeTies341.agda:285-286`.

## THE TASK

**Land the repair in `src/L/Condensation.lagda.md`, and verify every
consumer.**

**This is a DEFECT REPAIR, not a design change.** **The statements as delivered
are false; the repaired ones are the statements the chapter intended, and the
sibling tie two lines away already carries the same bound.**

## WHAT MAKES THIS DELICATE

- **`src/L/Condensation.lagda.md` is the wing's most expensive master**, about
  132 s and 71.4 percent of the GCH wing's seconds. **Budget for a slow
  re-check and report it beside the empty-file floor** (C-53 as extended).
- **DD23 freezes mathematical prose.** **If a comment describes the old
  telescope, the comment is now WRONG and must change with the code.** **Read
  the surrounding prose and say what you changed.**
- **Two waves of a generic port copy this chapter verbatim**,
  `agents/tasks/LJ-1-336/GenDirty.agda` and `agents/tasks/LJ-1-306/GenAgree.agda`.
  **Your change will make those copies stale.** **Do NOT update them; they are
  frozen probe records.** **Say which of them your change would break, so the
  next port wave knows.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE REPAIR LANDS AND THE CHAPTER IS GREEN.** Report the diff, the check
  time, and every consumer. STOP.
- **A CONSUMER BREAKS.** **`[LJ-1.338]` measured that `LeafAgree` has ZERO
  consumers in `src/`, so this should not happen.** **If one does, that
  measurement was wrong and saying so is more valuable than the repair.**
- **THE REPAIRED STATEMENT IS ALSO FALSE.** **Then the intended statement is not
  what anyone thinks and this goes to the owner.** **`[LJ-1.341]` gave both as
  terms, so this would mean its terms prove something weaker than the call sites
  need.**
- **THE CALL SITES DO NOT CARRY `hz` WHERE CLAIMED.** **Check `:6798` and
  `:6813` yourself before you rely on them** (C-44).
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.** **C-51, C-55 and
  C-56 are the three medicines this chapter's family has earned.**

## WHAT YOU MUST NOT DO

- **CHANGE ONLY WHAT THE REPAIR NEEDS.** **Five lines and their call sites.**
  **Do not tidy, do not rename, do not restructure.** **This chapter has already
  refused three restructurings this week, each with a measurement.**
- **Do not touch `src/L/GCH.lagda.md` or any other master** unless a consumer
  forces it, and then say so before you do.
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-341/`'s probes.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **Create `agents/tasks/LJ-1-343/lj-1.343-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `.venv/bin/python scripts/gate/lint-agda.py --check` and
  `.venv/bin/python scripts/site/weave-i18n.py --check` on the chapter.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE LAW THIS EPISODE IS THE PUREST INSTANCE OF

**C-45: `exit 0` is not a supply.** **`[LJ-1.338]`'s `module Leaf` takes both
false hypotheses as PARAMETERS, so its exit 0 established nothing about leaf
adequacy.** **A module that assumes a false thing typechecks forever.**

**And D-10: price the TRUTH of a recorded residue before pricing its proof.**
**Three tasks priced these ties before anyone asked whether they were true.**

**C-57: `[LJ-1.341]` answered non-vacuity TWICE**, inhabiting both premises at
the refutation's own witnesses, **so neither hypothesis is refuted merely
because nothing meets it.** **Hold that standard.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eight of my last fifteen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the hypothesis is FREE at the call sites」.** **That is
`[LJ-1.341]`'s reading of `:6798` and `:6813`, and it did not land the repair
itself.** **If `hz` is not in scope where you need it, the repair costs more
than five lines and that is your headline.**

## THE RULES

**C-45, D-10, C-57, C-44, C-40, C-42, C-36.**
**C-12, C-22, C-32, C-39, C-49, C-50, C-51, C-53, C-55, C-56, P-i, P-l, P-y.**
I-5. **D-1, D-26. DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for rewrite` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.341]` measured that the repair is CLASS-FREE, so it is written once and
serves both ends.** **Confirm that, and report the closure**, noting
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read WHOLE.** It funds you, it
  holds the countermodel, both repairs as terms, and the five negative controls.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`**, whose 234-line supply this
  repair partly invalidates: **its residue drops from 51 lines and six ties to
  43 and four.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route carried unbounded hypotheses too.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:245-250`.** **`[LJ-1.341]` measured that Devlin
writes the formula and「then binds every unbounded quantifier by the concrete
set」, so his corresponding step has NO unbounded variable at all.** **Our
telescope moved the bound out of the formula into a hypothesis, and `z` lost its
binder on the way.** **Say in one line whether the repair puts it back where
Devlin has it.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-341/ProbeTies341.agda:248-294`, the two repairs as terms,
FIRST.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `agents/tasks/LJ-1-343/` only.

## RETURN

**Lead with ONE line: does the repair land green, and what is the chapter's
check time.** Then the diff, five lines and their call sites. Then whether `hz`
was in scope where claimed. Then every consumer, checked. Then which frozen port
copies your change makes stale. Then any comment you changed and why. Then the
closure and the DD4 axis. **Mark every negative MEASURED or INFERRED.**
