# LJ-1.223: read the ten remaining suppliers in ONE pass, and split them thin from thick

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it and
record why: the task READS Agda source and judges what each definition costs to
port, which is the subject matter the `--agda` flag cannot see.** The clock
selected the mode.

## GOAL

**After three dispatches the project still has NO figure for the class-generic
port's total price, and `[LJ-1.221]` measured that every brief in the sequence
forbade producing one.**

**Produce it. Read all ten remaining suppliers in one pass.**

`[LJ-1.221]` names the repair in its section 5.5: **the order `[LJ-1.213]`
observed is a TYPECHECK order, my briefs converted it into a DISPATCH order, and
that conversion was never measured.** Nothing forces one dispatch per link.

## THE TEN, and the list is already on disk

**`agents/tasks/LJ-1-219/JoinAtAmbient.agda:24-39` imports twelve `L.Coding`
modules with an explicit `using` list on each.** Two are settled:

- **`L.Coding.Model` is PORTED**, class-generic and green at
  `agents/tasks/LJ-1-210/GenModel.agda`.
- **`L.Coding.Environment` supplies only `env`**, whose type never mentions a
  structure. **Check that and then set it aside.**

**Ten remain: `Recover`, `CodeSet`, `Graph`, `Table`, `Slot`, `Sound`, `Unique`,
`Sat`, `Bridge`, `Uniform`.**

## THE ONE QUESTION, PER NAME

**The `using` lists tell you exactly which names the body takes.** For each name
on each list, answer one question:

**THIN or THICK?**

- **THIN:** the delivered definition is short and it is built from operations
  that `agents/tasks/LJ-1-210/GenModel.agda` already exports generically, or
  from a name that could be a module parameter. **Porting it is a using-list
  edit or a few lines.**
- **THICK:** the definition carries real content that must be re-derived at the
  class. **Porting it is a build.**

**`[LJ-1.221]` MEASURED the first case and it is your template.** Brick two was
`Recover`'s `keyOf` and `keyOf-fst`, both one-liners at
`src/L/Coding/Recover.lagda.md:112-116`, both built from `prʟ`, `prʟ-fst`,
`numeralL` and `numeralL-fst`, **all four already generic in `GenModel.agda` at
`:193`, `:196` and `:16-17`.** `GenModel.agda:215` even carries a body character
for character identical to `keyOf-fst`. **The repair was two names in a `using`
list.**

**Do not assume the other nine are the same. Read each one.**

## WHAT THIS TASK IS NOT, and the boundary matters

**`[LJ-1.220]` is LIVE and it measures a DIFFERENT thing:** which names Agda
actually DEMANDS, by running the typechecker until the body passes. **That is
the chain's WIDTH.**

**You measure the chain's PRICE: what each demanded name costs to supply.**

**Do not run Agda.** Two siblings hold both slots. **Do not re-derive
`[LJ-1.220]`'s width, and do not wait for it.** The two answers multiply.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL TEN ARE THIN.** Then the chain is a `using`-list problem and not a port,
  **and that is the best outcome available.** Give the total written lines and
  the modules that need no dispatch at all. STOP.
- **N ARE THICK.** Name them, price each in written lines, and give the total.
  **Then LJ-1.7's environment lift has a price for the first time.**
- **A MODULE CANNOT BE JUDGED BY READING.** If a supplier's cost turns on
  something only the typechecker can settle, **name the module and say what the
  typechecker would have to decide.** **That is the honest boundary between this
  task and `[LJ-1.220]`, and naming it is a complete answer for that module.**
- **THE READING REFUTES THE PORT.** If the ten together cost more than the
  delivered fixed chain is worth, **say so with both figures.** `[LJ-1.213]`
  gives 17 modules and 5,822 lines for the fixed chain.

## THE FIGURE THAT IS WRONG, and it is in five documents

**「nine tower-neutral steps and three per-tower ones」is FALSE.** The table at
`dev/literature/devlin-II5.md:370-383` has **twelve rows: eight EITHER and four
PER-TOWER**, and the word「nine」does not occur in that file. **Three briefs and
two reports carry the wrong figure. They are frozen records. Use 8 and 4.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Two siblings hold both Agda slots (C-12).
- **Do not edit any master, brief or report.** **You write your own report and
  nothing else.**
- **Do not port anything.** This task reads and prices. It builds nothing.
- **Do not touch `agents/tasks/LJ-1-217/`, `LJ-1-220/` or `LJ-1-222/`.** Three
  siblings are live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A line count from a file you read is
MEASURED. A port cost you judge from that count is INFERRED, and P-l says so.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**This task gives DD4 the number it has never had: the price of making the whole
coding chain serve both towers.** `[LJ-1.213]` gives 389 shared, 12 plumbing and
8 per-tower residual at ONE module. **Give the three numbers for the CHAIN**,
and say plainly whether the shared half still dominates when the plumbing is
paid ten more times.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-221/lj-1.221-report.md`**, read WHOLE. **It is your brief
  within this brief.** Sections 4, 5.4 and 6 hold the template, the corrected
  count and three delivered counterexamples to「port bottom-up」.
- **`agents/tasks/LJ-1-219/lj-1.219-report.md`** and `JoinAtAmbient.agda`: your
  import list and the second leak.
- **`agents/tasks/LJ-1-213/lj-1.213-report.md`**: the 17 modules, the 5,822
  lines, the 125-line census floor, and the 389 / 12 / 8 split.
- `agents/tasks/LJ-1-210/lj-1.210-report.md` and **`GenModel.agda`, read
  WHOLE**: everything the ported module already exports is your supply list.
- `src/L/Coding/*.lagda.md`: **the ten suppliers themselves. Read the
  definitions, never a report about them.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **`[LJ-1.221]` found `archive/src/2026-08-09-rud-route/L/Rud/ClassJ.lagda.md`
  declares a second class that no consumer ever took. Read that warning.** Take
  SHAPE from the archive, never a claim.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:370-383` is the twelve-row table, 8 EITHER and 4
PER-TOWER.** **`:387-389` says the per-tower content is exactly two objects, and
`[LJ-1.221]` measured that no brief has ever used that line.** **Use it: say
whether your thick list matches those two objects.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-221/lj-1.221-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-223/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **D-10.** Price the truth of a recorded target before pricing its proof.
- **C-22.** Write your deliverable incrementally, never at the end.
- **P-l.** A cost measured at one module is a hypothesis at another. **`Model`'s
  42 lines and `Recover`'s two one-liners are comparables, not prices.**
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-39, C-40. DD0, DD4, DD8, DD24. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. **Ledger caliber: non-blank
  lines inside ` ```agda ` fences.**
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with two numbers: how many of the ten are THIN, and the chain's total
port price in written lines.** Then one table row per name: the name, its home
at `file:line`, its delivered line count, THIN or THICK, and for a THIN name the
generic supplier that already covers it. Then the three DD4 numbers for the
chain. Then any module you could not judge by reading, and what the typechecker
would have to settle. **Mark every negative MEASURED or INFERRED.**
