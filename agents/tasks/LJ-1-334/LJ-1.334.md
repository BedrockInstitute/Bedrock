# LJ-1.334: item 1, the pointwise-least pairing. The last untried candidate

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS IS SHORT, and why it may be over quickly

**This is the LAST untried candidate on a leg that has now converged.**
`[LJ-1.321]` wrote four candidate maps. **Items 3 and 4 are RETIRED**, by
`[LJ-1.330]` and `[LJ-1.332]`. **Item 2 was settled STATEMENT-LEVEL by
`[LJ-1.333]`.** **Item 1 is untouched, and `[LJ-1.333]` said so explicitly.**

**AND THE LITERATURE MAY ALREADY REFUTE IT.** `dev/literature/truncation-and-selection.md:311-316`,
which this project landed yesterday, reads:

> **the greedy construction that sends each element to the least unused target
> fails at order type `ω · 2` into `ω`. A canonical injection needs a
> well-order on the INJECTIONS, which is what `<_L` supplies classically and
> what an ambient function type does not have.**

**`ω · 2` is a non-initial limit, which is exactly this band.** **So the digest
may kill item 1 in one paragraph.**

**READ THAT FIRST, decide whether it applies, and if it does, STOP AND SAY SO.**
**A short honest closure is the deliverable here. Do not spend a budget proving
what a landed digest already states.**

## WHAT `[LJ-1.333]` MEASURED, and it is the frame

**The band is the exact complement of the tree's only canonicalizer.** It
traced `via-col-square`'s hypothesis down to `InitialCore`'s `noinj²`, which is
**`Init`'s FOURTH ROW** at `src/L/Ordinal/SquareLaw.lagda.md:696-698`, **and the
limit band is DEFINED by that row failing.** Green term,
`agents/tasks/LJ-1-333/ProbeLJ1333A.agda:201-204`.

> **Item 2 searched for a canonicalizer exactly where the tree's only
> canonicalizer is refuted by the band's own definition. Five attempts were not
> unlucky.**

**Item 1 is the fifth. Ask whether it escapes that frame BEFORE you build.**

## THE QUESTION

**Does a pointwise-least pairing give a canonical `sq α` at a non-initial limit
α, and if not, exactly where does it fail?**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE DIGEST ALREADY KILLS IT.** **Say so with the reasoning re-derived, and
  STOP.** **Then the leg's four candidates are exhausted and the question is
  structural, which the project needs stated cleanly.**
- **IT ESCAPES THE DIGEST'S COUNTEREXAMPLE.** **Say how, then build.** That
  would be a genuine surprise and worth the budget.
- **IT BUILDS.** **Then `[LJ-1.8]`'s blocker is gone.** Report the term, its
  lines, its seconds and its negative control. STOP.
- **A WALL.** **C-56:** a truncated proof that walls is paying for its
  ASSEMBLY. Write the untruncated control FIRST and keep it.

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-334/`. **`src/` is forbidden** (I-5).
- **Do not re-derive what four siblings settled.** `[LJ-1.329]` refuted the
  naive map; `[LJ-1.330]` and `[LJ-1.332]` retired items 3 and 4; `[LJ-1.333]`
  settled item 2 and closed the propositional-motive question. **Cite them; do
  not repeat them.**
- **Do not edit another task directory.** You may READ and RE-RUN their probes;
  you may not change them.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS and
  `grep -c 'libexec.*bin/agda'` over-counts too. MEASURED 2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure.
- **RUN NEGATIVE CONTROLS that MEASURE.** **Four siblings running have produced
  fifteen of them, and several put a whole verdict into one error message.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-334/lj-1.334-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Six of my last seven briefs carried a claim an agent measured FALSE.**
**The one at risk here: 「`ω · 2` is a non-initial limit, which is exactly this
band」.** **`[LJ-1.332]` marked that same claim INFERRED and did not build it.**
**Check it; if `ω · 2` is not in the band, the digest's counterexample does not
reach item 1 and the task is live after all.**

## THE RULES THIS CHAIN EARNED

**C-36.** Four siblings each refuted ONE thing and each said so. **If you cannot
build item 1, you have refuted item 1 and nothing wider.**

**C-56, C-54, C-44, C-42, D-10, P-l, C-45.**

**A STOP IS A DELIVERABLE.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46). **Every term on this
leg has been tower-blind and has taken a POINT of a delivered injection type
rather than a map out of `sq α`. Keep that or say why you cannot.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-333/lj-1.333-report.md`, read WHOLE.** It funds you and
  its section 3 is the frame you must escape.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md` section 8**, item 1 as written.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md:311-316`, quoted above. It is the
task's own abort criterion, so read it before anything else.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`dev/literature/truncation-and-selection.md:305-320` FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-334/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, C-36, C-44, C-42, C-45, C-54, C-56, D-10, P-l.**
- **C-12.** Two Agda processes, counted with the command above.
- **C-22, C-32, C-39, C-40.** I-5. **D-26. DD0, DD4, DD8, DD18, DD24.**

## RETURN

**Lead with ONE word: KILLED-BY-DIGEST, ESCAPES, BUILDS or WALLED.** Then
whether `ω · 2` is in the band, MEASURED or INFERRED. Then the reasoning or the
term at `file:line`. Then what remains of `[LJ-1.8]`'s blocker once all four
candidates are settled. **Mark every negative MEASURED or INFERRED.**
