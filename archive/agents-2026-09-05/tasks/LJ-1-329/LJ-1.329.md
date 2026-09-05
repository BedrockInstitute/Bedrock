# LJ-1.329: code ONE ambient function as a member of an L-set

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THREE INVESTIGATIONS CONVERGED ON THIS OBJECT, and none of them set out
## to find it

**This is the only remaining line on the GCH descent, and it arrived by
elimination rather than by design.**

- **`[LJ-1.321]`** shrank the debt to a well-order on `sq α`, then measured that
  `pullOrder` reduces that to **an INJECTION of `sq α` into a well-ordered
  carrier**. `agents/tasks/LJ-1-321/lj-1.321-report.md:281-282`.
- **`[LJ-1.316]`** diagnosed the blocker from the literature: what stops the
  classical move is **that the object to select is an ambient FUNCTION, living
  outside every well-ordered domain the tree has.**
  `agents/tasks/LJ-1-316/lj-1.316-report.md:206-208`.
- **`[LJ-1.328]` measured that those two are ONE LINE**, and that the coded
  order is not what either needs: **the carrier the tree offers, `Mem (Lset β)`
  under `orderAt`, is AMBIENT and DELIVERED already.**

**`[LJ-1.328]`'s own last line:**

> **Fund nothing for the coded order. Fund the ambient-to-code crossing for a
> FUNCTION once, because `[LJ-1.321]` and `[LJ-1.316]` are the same line.**

## THE QUESTION

**Take ONE ambient function that the descent actually needs, and produce a
member of an L-set that codes it.**

**Not a family. Not a general theory. ONE function, at the smallest site where
the descent needs it, with a negative control.**

## WHAT IS ALREADY DELIVERED FOR THIS, and the chain measured all of it

**The assembly is solved.** `[LJ-1.326]` MEASURED that `InjCode`'s four
conjuncts assemble from delivered parts at **three** sites, and built the
adapter in 8 lines at `absorbs`'s own site.
`agents/tasks/LJ-1-326/ProbeLJ1326A.agda:81-91`.

**The carving contract is known.** `[LJ-1.327]` MEASURED what a `Carve` caller
must supply for an AMBIENT function, at `src/L/Absorption.lagda.md:385-401`:
**the function, its injectivity, THREE READBACK LEMMAS at `:388-394` (those are
the description), a decision, the bound, and `sep`.** **A fourth site needs a
fourth `Carve`, measured at about 127 lines.**

**Full separation is available**: `hasSeparationL` takes an arbitrary
`Formula S 1`, `src/L/Axioms/Full.lagda.md:144-145`, **with no Δ₀ or Σ₁
certificate demanded.** MEASURED.

**So the machinery exists and the question is the DESCRIPTION: what does the
function's graph say in the object language.**

## THE FIRST THING TO DO, and it may change the whole task

**CHOOSE THE FUNCTION, and justify the choice at `file:line` before you build
anything.**

**`[LJ-1.321]` names the shape it needs: an injection of `sq α` into
`Mem (Lset β)`.** **Read that report's section on `pullOrder` and say exactly
which function the descent hands over.**

**If the smallest site turns out to want a DIFFERENT function than the one you
first pick, say so and take the smaller.** **The point of this task is one
measured crossing, not the most impressive one.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **YOU CODE IT.** Report the term, its lines, its seconds, **and its negative
  control.** **Then the crossing is MEASURED once and the whole descent
  re-prices against it.** STOP.
- **THE DESCRIPTION IS THE WALL.** **Name what the graph cannot say, at
  `file:line`, and price what would let it.** **That is the honest answer and it
  is what decides the leg.**
- **THE FUNCTION IS NOT WHAT THE DESCENT NEEDS.** **Then the convergence is
  wrong and that is the most valuable thing you can return.** Say which object
  it actually wants.
- **IT NEEDS THE Π₁ HALF.** `[LJ-1.328]` measured **zero Π₁ certificates in
  `src/L/`** and refused to price that half. **If you meet it, STOP and say
  where; do not invent a basis.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-329/`. **`src/` is forbidden** (I-5).
- **BUILD ONE CROSSING, NOT A THEORY.** **If you find yourself generalising,
  stop and report the one.** Three tasks before you shrank this leg by staying
  small; the 800-line survey fell to 8 measured lines that way.
- **Do not edit another task directory.** You may READ and RE-RUN the sibling
  probes in `agents/tasks/LJ-1-326/`, `LJ-1-327/` and `LJ-1-328/`; you may not
  change them.
- **`src/L/GCH.lagda.md` was RESTATED and `src/L/BoundedSubset.lagda.md` had a
  cure landed, both yesterday.** **Read the CURRENT files.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling may be measuring CHECK TIMES.** Take ONE slot and report the load
  beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RUN A NEGATIVE CONTROL on anything you build.** **The three tasks before you
  all did, and one of them ran a control that MEASURED rather than checked: it
  wrote the certificate it expected to fail and let Agda name the blocker.**
  **That is the standard here now.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-329/lj-1.329-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE WARNING THIS CHAIN HAS EARNED, and it is about MY briefs

**Two consecutive briefs of mine carried a claim that an agent then measured
FALSE:**

- **To `[LJ-1.327]`: 「`Carve` takes a formula」.** There are TWO `Carve`
  modules and each hard-wires its own.
- **To `[LJ-1.328]`: 「a coded order changes which side of that line objects sit
  on」.** MEASURED FALSE for two of the three consumers.

**Assume this brief carries a third. C-44 binds it as hard as any agent's
claim.** **Every number and every reading above is some other agent's or mine;
re-derive what you rely on, and say plainly if a premise of mine is wrong.**

## THE RULES THIS CHAIN EARNED

**C-44.** See the warning above. **This is the third brief in a row to say it
and the first two were right to.**

**C-45. `exit 0` is not a supply.** **The function typechecks ambient and is
useless coded. That is this task in one line.**

**C-36. A failed substitution is not a proof of impossibility.** If you cannot
code it, write the description you could not write.

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**
**`[LJ-1.328]` found a whole uniform family the previous task called absent.
Search before you build.**

**P-l, C-42.** One crossing measures one site.

**A STOP IS A DELIVERABLE, and「do not fund this, fund THAT」has been the most
valuable return three times running. If it is right a fourth time, say it.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**This crossing is the best shared candidate left.** `pullOrder` lives in
`src/L/Choice/Step.lagda.md`, **the AC trophy's own machinery**, and
`[LJ-1.321]` measured that the GCH descent already re-uses it. **Say whether
your crossing is tower-blind and which closure it would land in.**

**And `[LJ-1.326]` measured that the restatement's DD4 rise is an artifact the
proof hands back exactly. Do not read the share; read the SHARED row.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-328/lj-1.328-report.md`, read WHOLE.** It funds you, it
  measured that two consumers are one line, and it corrected its predecessor.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`**, the route and the exact shape
  `pullOrder` reduces to.
- **`agents/tasks/LJ-1-327/lj-1.327-report.md`**, the `Carve` caller contract
  for an ambient function.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route crossed between ambient and coded too, and `[LJ-1.293]` refuted
  its identity by machine. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, whose diagnosis this task is
aimed at: **the classical move works because an injection in `L` is a SET and
the order reaches it.** **Say in one line whether your crossing puts the object
on that side.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-321/lj-1.321-report.md`, the `pullOrder` section, FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-329/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, C-44, C-45, C-36, D-10, P-l, C-42.** Named above with what each
  governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-53, C-49, C-50, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: CODED, WALLED or WRONG-OBJECT.** Then which function you
chose and why, at `file:line`. Then the term or the wall. Then its lines,
seconds and load. Then your negative control and what it named. Then what the
descent re-prices to now that the crossing is measured once. Then the DD4 axis
and the closure. **Mark every negative MEASURED or INFERRED.**
