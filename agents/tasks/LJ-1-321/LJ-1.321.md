# LJ-1.321: the door. Is there a `2-Constant` map `Wat α → sq α`?

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE QUESTION, stated exactly as `[LJ-1.319]`'s ruling states it

> **Inside the non-initial branch of the descent, is there a `2-Constant` map
> `Wat α → sq α`?**

**This is NECESSARY AND SUFFICIENT for J1**, so a positive answer settles the
eliminator question for good. **A negative answer prices the wall and does NOT
close the door**, because failing to build one map is not a proof that none
exists (C-36).

## WHY THIS TASK EXISTS, and it replaces a proposed axiom

`[LJ-1.305]` returned NEEDS-A-PRINCIPLE and asked the project to admit
`InjData` into a trophy. **`[LJ-1.316]` then measured that the claim rested on
the wrong eliminator**, and `[LJ-1.319]`'s ruling REFUSED the principle and
funded this file instead.

**`[LJ-1.305]`'s J1 says `PT.rec` demands a propositional motive. That is true
of `PT.rec` and FALSE of the library this project builds against.** MEASURED in
the installed cubical library:

```agda
rec→Set    : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B     -- under isSet B
trunc→Set≃ : (∥ A ∥₁ → B) ≃ Σ (A → B) 2-Constant              -- necessary too
elim→Set   :                                                   -- dependent motive
```

at `/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/PropositionalTruncation/Properties.agda:181-190`,
`:225` and `:270-274`, exported at `:268`. **VERIFY all three yourself** (C-44).

**The general criterion is Kraus, Escardó, Coquand and Altenkirch, LMCS 13(1)
2017, Theorem 16: a type has `∥X∥ → X` IF AND ONLY IF it has a weakly constant
endomap.**

## THE PREMISE, ALREADY MEASURED, and you re-run it first

**`sq-set : (α : V ℓ) → isSet (sq α)` is GREEN**:
`agents/tasks/LJ-1-319/SqIsSet.agda`, exit 0, 2.01 s, load 5.89.

**RE-RUN IT before anything else.** If it fails on your machine, everything
below is void and that is your report.

## THE FOUR THINGS TO BUILD, in this order

**1. THE DISCHARGE ATTEMPT, and this is the task.** Normalize the member half
by `leastOf`, following the delivered `LeastCardInjL` pattern at
`src/L/Cardinal.lagda.md:116-134`. **The residue is a canonical injection
`⟪ α ⟫ ↪ ⟪ κ ⟫` BUILT FROM ORDINAL STRUCTURE, never extracted from the
witness.**

**The classical content is the choice-free ZF fact that an infinite ordinal and
its cardinal are equinumerous.** **Measure whether this tree's ordinal machinery
builds it. If it walls, NAME THE WALL at `file:line`.**

**`[LJ-1.316]` warns that the well-orders alone do not give it**, section 2.4,
the `ω · 2` example. **So the expected hard case is the LIMIT non-initial
ordinal. Go there first rather than last.**

**2. THE REFUTATION ATTEMPT, and it is cheap so do it early.** Adapt `NotProp`'s
`swap` machinery (`agents/tasks/LJ-1-305/NotProp.agda`) to two witnesses of
`Wat α` and measure whether the naive step map, the `sq-transport` composite,
violates `2-Constant`.

**INFERRED by the ruling, and you MEASURE it: it does violate, because two
injections differing by a transposition give two different composites.** **A
refuted naive map NARROWS THE SEARCH. It does not close the door, and your
report must not say it does.**

**3. THE CODED COMPOSITE, about 20 lines.** Build `BoundedToCode → InjData` to
finish `[LJ-1.314]` section 1.4's INFERRED join, **so the coded route's record
is complete whatever the door does.** Start from
`agents/tasks/LJ-1-314/CodeUntrunc.agda`, which is green.

**4. THE VERDICT, in the ruling's own vocabulary.** `[LJ-1.305]`'s
NEEDS-A-PRINCIPLE is downgraded to
**NEEDS-A-2-CONSTANT-MAP-OR-THE-CROSSING**. **Say which of the two the tree
now owes.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE `2-Constant` MAP EXISTS AND YOU BUILD IT.** **The best outcome and it
  ends this line.** J1 discharges with no new principle. Report the term, its
  lines and its seconds. STOP.
- **THE CANONICAL INJECTION WALLS.** **Name the wall at `file:line` and price
  what would build it.** Then the tree owes the crossing rather than a map, and
  say so.
- **THE NAIVE MAP IS REFUTED AND NO OTHER IS FOUND.** **That is a NARROWED
  SEARCH, not a closed door** (C-36). Write the map you could not write.
- **`sq-set` FAILS ON RE-RUN.** Everything rests on it. Report and stop.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-321/`. **`src/` is forbidden** (I-5) and
  `check-probes.py` enforces it.
- **Do not edit `src/L/GCH.lagda.md` or `src/L/Cardinal.lagda.md`.** **A
  separate repair to `Cardinal.lagda.md:256-258` is ruled and pending; leave it
  to the orchestrator.**
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-319/SqIsSet.agda`, `agents/tasks/LJ-1-314/CodeUntrunc.agda`
  and `agents/tasks/LJ-1-305/NotProp.agda`. **You may not change them.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **No sibling holds a slot when this is dispatched, so both are yours in
  principle. Take ONE.** **`[LJ-1.322]` is written and HELD for a quiet
  machine, because its deliverable is a TIMING and yours is a TERM.** **The
  moment you finish, that task starts, so do not idle a slot you are not
  using.** Report the load beside every absolute figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **C-51, written last night:** a `with`-pattern on a record-returning function
  exhausted the cap six times and an `opaque` seal did NOT cure it; projections
  did. **If you hit that wall you already have the medicine.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-321/lj-1.321-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## PREMISES

- **`sq α` is a Σ of a function type into a set with a propositional
  component**, `src/L/Ordinal/SquareLaw.lagda.md:685-687`, so it is a set. **Now
  MEASURED by `SqIsSet.agda`; re-run it.**
- **`leastOf` demands `P : A → hProp`**,
  `src/L/WellOrder/Base.lagda.md:158-161`, and **no `SWO` in the tree carries a
  function type**, census of all 14 by `[LJ-1.314]`. **VERIFY the census.**
- **`InjCode` is a proposition and `leastOf` untruncates it**,
  `agents/tasks/LJ-1-314/CodeUntrunc.agda`, green. **That is the coded route
  and it is the fallback if the door walls.**
- **What blocks the classical move is NOT the truncation**, by `[LJ-1.316]`:
  it is that the object to select is an ambient FUNCTION, living outside every
  well-ordered domain the tree has. **That diagnosis is what makes item 1's
  "build it from ordinal structure" the right shape.**

## THE RULES THIS CHAIN EARNED

**C-45. `exit 0` is not a supply, and its mirror: a successful typecheck of an
ASSUMED object proves nothing about that object.** **`InjData` typechecked as a
module parameter and that is how a needless axiom nearly landed.**

**C-36. A failed substitution is not a proof of impossibility.** **The single
most important rule for this task's negative branch.**

**C-38 as extended. A hypothesis is discharged when something SUPPLIES it.**

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
residue「the truncation cannot be lifted」was recorded and it was measured
against the wrong eliminator.**

**C-44.** Every claim in this brief is `[LJ-1.316]`'s, `[LJ-1.314]`'s,
`[LJ-1.319]`'s or mine, and you re-derive each one.

**P-l. A judgement at one site is a hypothesis at another.**

**A STOP IS A DELIVERABLE.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**AND DD4 IS LOAD-BEARING HERE, which is unusual.** `[LJ-1.319]`'s ruling
weighed it and it CUT AGAINST the principle: today every import the descent adds
is GCH-only, and **when DD4's goal is met for this descent it moves into the
SHARED part, which would seat a choice-shaped module parameter in the AC
trophy's own telescope.** **A canonical, witness-free construction is
tower-blind and generic by construction, so it has no such cost.** **Report on
this axis: does your construction name any tower?**

**Also note `dev/ledger.toml:204`: the GCH closure is read from a STATEMENT
whose proof is not wired, so it UNDERSTATES.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-319/lj-1.319-ruling.md`, sections 1 and 2.3, read
  WHOLE.** The ruling that funds you.
- **`agents/tasks/LJ-1-316/lj-1.316-report.md` section 2.4**, the `ω · 2`
  example and why well-orders alone do not give the injection.
- **`agents/tasks/LJ-1-314/lj-1.314-report.md`**, the coded route and the
  `leastOf` side condition.
- **`agents/tasks/LJ-1-305/lj-1.305-report.md`**, the target that measured the
  wrong eliminator, and its `NotProp` countermodel.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route met choice-shaped obligations too. **Say what would not
  transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`agents/tasks/LJ-1-316/truncation-and-selection.md`, the proposed digest, is
your literature and it is not yet landed.** **Read it.** It carries HoTT Book
section 3.9 and Theorem 10.4.3, Escardó's exiting-truncations notes, and Kraus
et al Theorem 16. **Say in one line whether Theorem 16's criterion is usable
constructively here or only as a classification.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-319/lj-1.319-ruling.md` sections 1 and 2.3 FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-321/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **C-36, C-38, C-44, C-45, D-10, P-l.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-49, C-50, R-40, R-41, P-i, P-k, P-m, P-y.**
- **C-22, C-32, C-39, C-40, C-42.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: BUILT, WALLED or NARROWED**, where BUILT means the
`2-Constant` map exists and J1 discharges with no new principle. Then the term
or the wall at `file:line`. Then `sq-set` re-run, VERIFIED or REFUTED. Then the
naive map's `2-Constant` status, MEASURED. Then the coded composite,
`BoundedToCode → InjData`, built or not. Then whether the tree now owes a map or
the crossing. Then the DD4 axis with your construction's tower-blindness stated.
**Mark every negative MEASURED or INFERRED.**
