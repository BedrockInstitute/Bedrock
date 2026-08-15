# LJ-1.340: write the `μ` apparatus generic

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THIS IS DD4's OWN WORK, and `[LJ-1.339]` found it with a number

**DD4 has no metric by the owner's ruling. This task has one anyway, because a
sweep measured it:**

> **Sixteen of `src/L/Choice/Stage.lagda.md`'s 21 exports have no consumer
> outside the chapter**, and the `using` lists are exhaustive, so that is by
> construction. **Fourteen are the `μ` and `defStage` apparatus.**
>
> **And `src/L/Choice/Step.lagda.md` REBUILT the half it needed**: it imports
> only `IsPredOf` and `isPropPredOf`, then **writes 32 lines against this
> chapter's 45, calling the same four lemmas.**
>
> **Step's own prose at `:90` says「The argument applies verbatim to a single
> set」.** **The operation was never written generic.**

**A delivered chapter says in English that its argument applies verbatim
elsewhere, and the elsewhere then wrote it again.** **That is DD4's failure mode
in one file pair.**

## THE QUESTION

**Can the `μ` apparatus be written ONCE, generic, so that both sites use it?**

**And what does that cost against the 45 plus 32 it replaces?**

## WHAT TO MEASURE, in order

**1. WHAT IS ACTUALLY SHARED.** Read both sites whole:
`src/L/Choice/Stage.lagda.md` and `src/L/Choice/Step.lagda.md:90-135`. **Name
the four lemmas both call.** **Say what differs between the two uses: is it the
carrier, the motive, or only the instantiation?**

**2. THE GENERIC FORM.** Write it. **If Step's prose is right and the argument
applies verbatim, the generic form is close to one of the two and the other
becomes an application.** **Measure how close.**

**3. THE PRICE.** Lines of the generic form, plus each site's application,
against 45 plus 32. **Say whether it SAVES lines or only moves them**, and state
the basis (DD8). **A restructuring that saves nothing is worth knowing about
before it is funded, not after.**

**4. THE SECONDS.** **Do not assume.** `[LJ-1.331]` measured that one
restructuring of this kind exhausted 8 GB where the original was free, and
`dev/LESSONS.md` C-55 records why. **Check the generic form's check time
against the two originals in the same session.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT WRITES GENERIC AND SAVES.** Report the form, both applications, the line
  delta and the seconds delta. STOP. **Landing is the orchestrator's.**
- **IT WRITES GENERIC AND SAVES NOTHING.** **A real answer.** Then DD4's own
  rule says write it generic anyway for re-instantiation, **and you say what
  that costs so the owner can weigh it.**
- **THE TWO USES DIFFER MORE THAN THE PROSE SAYS.** **Then Step's own sentence
  is wrong and that is the finding.** Name the difference at `file:line`.
- **A WALL.** **C-55 and C-56 are the two medicines this family earned.** Do not
  fold telescopes into records.

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-340/`. **`src/` is forbidden** (I-5).
- **Do not move any chapter.** `[LJ-1.339]` tested placement as a cause and
  REFUTED it: **3 of 21 exports and 24 of 140 code lines are pure ordinal
  arithmetic, and every failed search was a whole-tree grep, which is directory
  blind.** **A move is not warranted.**
- **Do not edit another task directory.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling may be live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure.
- **RUN A NEGATIVE CONTROL that MEASURES.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-340/lj-1.340-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## C-57, WRITTEN TODAY FROM THIS CHAIN, AND IT BINDS YOU

**A search that RETURNS the answer and a reading that DISCARDS it are two
different failures, and the second is invisible.** **When you clear a search
result, say HOW MANY hits you read and name the ones you rejected.** **「Every
hit is a different subject」over 59 lines, naming three, is what cost this leg
three briefs and one funded task.**

**And D-10: when you inherit an absence, re-run the search that established
it.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Seven of my last twelve briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the operation was never written generic」.** **That is
`[LJ-1.339]`'s reading of two files, not a build.** **A generic form may exist
elsewhere in the tree under a name neither of us searched for, which is exactly
C-57's subject.**

## THE RULES

**DD4** is the task. **C-57, C-52, D-10, C-44, C-55, C-56, P-l, C-42, C-45.**
**C-12, C-22, C-32, C-36, C-39, C-40, C-49, C-50.** I-5. **D-1, D-26.**
**DD0, DD8, DD9, DD13, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task IS that rule applied at a site
somebody measured.**

**NAME YOUR AXIS** (C-46), which is AC-against-GCH, fixed at
`scripts/measure/ledger.py:50`. **`[LJ-1.339]` measured that `L.Choice.Stage`
is the AC trophy's machinery and the GCH side already uses 3 of its exports,
with at least 3 more available.** **So a generic form here serves BOTH ends by
construction, which is rare.** **Report the closure effect and note
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-339/lj-1.339-report.md`, read WHOLE.** It funds you and
  its DD4 section is your brief's own evidence.
- **`agents/tasks/LJ-1-337/lj-1.337-report.md`**, which used two of this
  chapter's exports from the GCH side. **`[LJ-1.339]` CORRECTED its
  recommendation to keep a 13-line duplicate: MEASURED, the GCH trophy closure
  is 48 masters with or without that edge, so the duplicate buys nothing.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route also rebuilt what it had.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on whether an operation is written generic.**
Say so in one line and return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Choice/Step.lagda.md:85-140` FIRST, including the prose at `:90` that
claims the argument applies verbatim.

## SCOPE (write)

`agents/tasks/LJ-1-340/` only.

## RETURN

**Lead with ONE line: does the generic form save lines, and how many against 45
plus 32.** Then what the two uses share and what differs. Then the generic form
and both applications. Then the seconds, same session. Then whether Step's own
prose is right. Then the closure effect on both ends. **Mark every negative
MEASURED or INFERRED.**
