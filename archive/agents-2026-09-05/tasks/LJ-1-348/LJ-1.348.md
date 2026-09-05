# LJ-1.348: supply `witK` and `graphWitK`, the last two construction ties

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHERE THIS SITS

**`[LJ-1.338]` found SIX construction ties with no supplier at either carrier.**
**`[LJ-1.341]` proved two of them FALSE, `[LJ-1.343]` repaired them,
`[LJ-1.345]` reviewed and UPHELD, and `[LJ-1.346]` landed their supply green.**

**Four remain. A sibling has the two arity-numeral conjuncts. You have the other
two.**

## WHAT `[LJ-1.344]` MEASURED ABOUT EACH

**`witK`:**

> It has the **same shape defect** as the two refuted ties: `closedAt` and
> `shapedAt` both quantify over MEMBERS of `w'` and **neither bounds it above**,
> MEASURED by reading `src/L/Coding/Model.lagda.md:2191` and
> `src/L/Coding/Shape.lagda.md:189`. **It is NOT refutable by `[LJ-1.341]`'s
> countermodel, MEASURED, because `shapedAt` blocks it.**
> **Cure: `[LJ-1.343]`'s repair plus one `carrierK` call.**

**`graphWitK`:**

> It needs a field `KFacts` does not have: its conclusion is about the CARRIER
> itself, so it needs **the carrier as a MEMBER of the bound**. **INFERRED at
> one field plus one line.**

## THE TASK

**Supply both, or refute either, and say which.**

**`witK` is the interesting one:** it has the fatal shape and is NOT refutable
by the countermodel that killed its two siblings. **So either the cure applies
and it is supplied cheaply, or the block that saves it from refutation also
blocks the cure.** **Settle which.**

**`graphWitK` needs a new `KFacts` field**, which is the first new field this
chain has proposed. **`[LJ-1.344]` and `[LJ-1.346]` both landed with NO new
field, deliberately.** **So price the field honestly: what else would carry it,
and is there a supplier at the L carrier already?** **`module KValue` at
`src/L/Condensation.lagda.md:7264-7318` is the place to look; it had zero
consumers until this week.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH SUPPLIED.** Report the terms, their lines and seconds, and the negative
  controls. **Then all six construction ties are settled and the third kind of
  debt is closed.** STOP.
- **`witK` IS ALSO FALSE.** **Then `shapedAt` does not save it and a third
  telescope needs repair.** **Give the countermodel; do not land the repair.**
- **THE NEW FIELD IS NOT ONE LINE.** **Price it and say what it drags in.** **A
  new field on a 29-field record is a change every consumer sees.**
- **A WALL.** 30 minutes on one invocation is a wall: interrupt, report ELAPSED
  SECONDS, bisect. **NEVER raise the cap.** **A plain re-check of the chapter is
  a CACHE HIT at about 2.4 s; copy it verbatim with the module renamed for an
  honest figure, as `[LJ-1.345]` and `[LJ-1.346]` both did.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING in `src/`. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-348/`. **`src/` is forbidden** (I-5). **If a supply belongs
  in the chapter, say where and I land it.**
- **Do not touch the two arity-numeral conjuncts.** A sibling has them, and one
  is marked INFERRED FALSE with a wall at one clause.
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-344/`, `LJ-1-346/` and `LJ-1-341/`.
- **The landed supply is IN the chapter now**, at the module after `KFactsCons`.
  **Read it before you write: your terms should extend it, not duplicate it.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES, and include NON-VACUITY.**
  **`[LJ-1.346]`'s control asked its landed supply for a pre-repair unbounded
  tie and got exit 42, which proves a repair is load-bearing in the PROOF.**
  **Keep that standard.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-348/lj-1.348-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Nine of my last twenty briefs carried a claim an agent measured FALSE.**
**The one at risk: 「`graphWitK` needs a field `KFacts` does not have」.**
**`[LJ-1.344]` marked that INFERRED at one field plus one line, and `[LJ-1.344]`
also predicted a two-line closure that turned out to be an eight-line one
stated a SORT up.** **The same move may apply here: the field may exist at
another sort.** **Check that before proposing a new field.**

## THE RULES

**C-45** is the law of this chain: `exit 0` is not a supply.
**D-10, C-42, C-44, C-36, C-53, C-57, P-l, P-k.**
**C-12, C-22, C-32, C-39, C-40, C-49, C-50, C-51, C-55, C-56.** I-5.
**D-1, D-26. DD0, DD4, DD8, DD9, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**Every term this chain has produced is class-free and serves both carriers
because the record is already generic.** **A NEW FIELD is where that could
break.** **If you propose one, say explicitly whether it keeps the record
generic**, and note `dev/ledger.toml:204`: the GCH closure is read from a
STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** It funds you and
  it priced both of your ties.
- **`agents/tasks/LJ-1-346/lj-1.346-report.md`**, the landing your terms extend,
  and its interface ruling.
- **`agents/tasks/LJ-1-341/lj-1.341-report.md`**, the countermodel that does NOT
  reach `witK` and why.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.344]` reported its supply is the
port of a closure Devlin PROVES, where the repaired hypothesis was the port of a
premise he ASSUMES.** **Say in one line which of the two yours are.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Coding/Shape.lagda.md:189` FIRST, the conjunct that blocks the
countermodel, because it decides `witK`.

## SCOPE (write)

`agents/tasks/LJ-1-348/` only.

## RETURN

**Lead with ONE line: are both supplied, and at what cost.** Then `witK`:
supplied, or false with its countermodel. Then `graphWitK`: whether the field
exists at another sort before you propose a new one. Then where each supply
belongs. Then your negative controls including non-vacuity. Then the DD4 axis.
**Mark every negative MEASURED or INFERRED.**
