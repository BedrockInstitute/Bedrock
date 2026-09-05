# LJ-1.311: DD25 review of `[LJ-1.309]`'s no-hit sweep

tier: pi (in-harness-subagent-mode), **the switch's ADVERSARIAL row.** I ran
`scripts/dispatch/dispatch_policy.py` before writing this line. `[LJ-1.309]` was
authored **in-harness by opus**, which is this mode's DEFAULT row, so the
adversarial row is `herdr` / `pi` / `glm-5.3` and DD17's invariant holds: the
critic is not the author.

## WHY THIS REVIEW EXISTS, and the reason is not routine

**`[LJ-1.309]` returned a NO-GO: three sites, deepest depth TWO, no depth-3 or
depth-4 site anywhere in `src/`, and「DO NOT FUND」on the only respelling.**
DD25 fires on a NO-GO.

**AND THE OWNER FUNDED THIS LINE BY NAME, 2026-08-15**, with the instruction
not to abandon the small hope. **A single sweep that closes a line the owner
asked us to keep open is exactly the return that must be attacked before it is
believed.**

**The stake, from `[LJ-1.309]`'s own ladder:** depth 3 costs 9,286 ms and depth
4 costs 419,218 ms. **One undiscovered depth-4 site is worth about 400 seconds
against a DD24 gap of 60.0 s.** If the sweep missed a site, the project stops
looking for a 400-second prize on one agent's grep.

## ATTACK THE FILTER, NOT THE SITES

**The sweep found three sites because it searched for one shape. The three sites
are almost certainly right. THE QUESTION IS WHAT THE SHAPE EXCLUDED.**

**1. THE BIGGEST STAKE, and attack it first.** `[LJ-1.309]` reports:

> `Condensation.lagda.md`, which the brief said to sweep first, holds 12 `sucV`
> and ZERO `sucIter`. MEASURED. **It cannot hold the shape.**

**`src/L/Condensation.lagda.md` is about 132 s, about 62 percent of the GCH
wing's entire seconds, and its overage alone is about the size of the whole
DD24 gap.** **The sweep declared the tree's single most expensive file
structurally immune on ONE grep for ONE identifier.**

- **VERIFY the count**: 12 `sucV`, 0 `sucIter`, at `file:line`.
- **Then ask the question the sweep did not: is `sucIter` the ONLY numeral
  iterate in this tree?** Search for any other way a level is spelled as an
  iterate: a different function name, a numeral literal chain, a `Fin`-indexed
  ladder, an `Lset`-indexed one. **If a second spelling exists, the filter has
  a false negative and Condensation is where it would hurt most.**
- **If `sucIter` really is the only one, SAY SO WITH THE EVIDENCE** and
  Condensation is genuinely clear. **That is a fine outcome and it is worth the
  slot to know it.**
- **Condensation's 132 s has a cause whatever the answer is.** If R-41 is not
  it, **say in one line what the profile attributes it to**, so the project
  stops guessing.

**2. THE UNRESOLVED 522 MILLISECONDS.** `[LJ-1.309]` reports honestly:

> `splitKey∈` does not appear in `[LJ-1.292]`'s profile (MEASURED by absence in
> a table reporting down to 12 ms), yet its shape costs 261 ms isolated. I did
> not reconcile that. **The honest bound on ranks 2 and 3 is a RANGE: 0 ms
> delivered to 522 ms isolated.**

**A shape that costs 261 ms in isolation and 0 ms in the delivered master is
either not charged, or charged under a name the profile groups elsewhere.**
**Settle which.** The answer matters beyond this site: **if a profile can hide a
charged definition by grouping, then every「not charged」verdict in this
project's seconds work is weaker than it reads**, including `[LJ-1.292]`'s.

**3. THE LADDER ITSELF.** `[LJ-1.309]` re-measured depth 2 in the site's own
setting (`t2` 219 ms against `b2` 221 ms) and that transfer is good work.
**Depths 3 and 4 were NOT re-measured; they are `[LJ-1.292]`'s bisect figures
carried forward.** **P-l says a judgement at one site is a hypothesis at
another.** **Check whether the 43-times step survives in a realistic setting**,
because the whole「DO NOT FUND」rests on the prize being small, and the prize is
computed from that ladder.

**4. THE 90 OF 96.** `[LJ-1.309]` clears 90 masters because「only FOUR name
`sucIter` at all」. **That is attack 1 generalised: the clearance is exactly as
strong as the claim that `sucIter` is the only iterate spelling.** **Re-derive
the four, and the 96.**

**5. THE PROPOSED CURE'S SELF-REFUTATION, and check it because it is
load-bearing for the NO.** `[LJ-1.309]` argues the half-cure MOVES the cost:
respelling `:118` would push `T-fin` at `:115` to a depth-3 chain, from 219 ms
to 9,286 ms, **42 times worse**. **That is the sentence that makes「DO NOT
FUND」correct rather than merely cheap.** **If it is wrong, the cure is
available and the verdict flips.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE FILTER IS COMPLETE AND THE TREE IS CLEAN.** **UPHOLD.** Report the
  evidence that `sucIter` is the only iterate spelling, and the line closes with
  a record instead of a hope. STOP.
- **A SECOND SPELLING EXISTS.** **That is the hit and it is the reason this
  review is funded.** Name it, count its sites, rank by depth. **Do not cure
  it.**
- **CONDENSATION'S COST HAS A DIFFERENT MECHANISM.** **Name it.** That is worth
  more than this whole sweep, because it is 62 percent of the wing.
- **THE 522 ms RECONCILES TO ZERO.** Then ranks 2 and 3 are free and the census
  is tighter than its author claimed. Say so.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## COUNTING THE AGDA SLOTS, and the previous brief got this wrong

**C-12 caps this machine at TWO concurrent Agda processes.** **`ps aux | grep -c
'[a]gda '` OVER-COUNTS**: it matches the `/bin/bash -c` wrapper. **`grep -c
'libexec.*bin/agda'` over-counts too**: it matches the grep itself. **MEASURED
2026-08-15, both.** Use:

```sh
ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
```

**Run it before every `agda` invocation. If it returns 2, do not start a
third.** A third process is the crash the heap caps exist to prevent.

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-311/`. **`src/` is forbidden** (I-5) and
  `check-probes.py` enforces it. **Propose nothing; this review measures.**
- **Do not edit `agents/tasks/LJ-1-309/`**, the record under review, or any
  other task directory.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  machine load beside every absolute figure.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-311/lj-1.311-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, as the first word of your return.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
13 of 32 decided DD25 reviews in this project overturned their target, a 41
percent rate. **An UPHOLD is also a real answer here and it closes a line the
owner cares about, so do not manufacture a hit either.**

## PREMISES

- **`[LJ-1.309]`'s census is three sites, all in `src/L/Coding/Key.lagda.md`,
  at `:118-120`, `:129-131` and `:133`, all depth 2.** Re-derive.
- **The ladder is 219 ms, 9,286 ms, 419,218 ms at depths 2, 3 and 4**,
  `agents/tasks/LJ-1-292/lj-1.292-report.md:37-39`. Re-derive the reading.
- **DD24's gap is 60.0 s**, `dev/ledger.toml:303-304`. `[LJ-1.309]` corrected my
  earlier「about 63 s」and I take the correction. **Verify it.**
- **`[LJ-1.309]` REFUTED one sentence of `[LJ-1.292]`**: that `pair∈` has no
  `sucIter` mismatch. **Check that refutation; a refutation is a claim too.**

## THE RULES THIS CHAIN EARNED

**C-42. A refutation measures the site it names and never how far it extends.**
**`[LJ-1.309]` extended a per-file grep to a whole-tree clearance. That is the
exact move C-42 governs, and it may still be right.**

**C-50. Profile before you cure.** `[LJ-1.309]` obeyed it and recommended
against its own cure. **Check the profile, not the recommendation.**

**C-44. A brief's claim is a measurement until you check it**, and that binds
`[LJ-1.309]`'s numbers AND mine here.

**R-41, `dev/LESSONS.md:4247`, read the FULL entry.**

**P-l. A judgement at one site is a hypothesis at another.** Attack 3.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). `[LJ-1.309]` reports all three sites are in NEITHER
trophy closure, so their seconds are paid zero times on DD4's own
AC-against-GCH axis, which is fixed in code at `scripts/measure/ledger.py:50`.
**VERIFY that, because it is half the reason not to fund.** **And note the
qualification the ledger itself carries at `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not yet wired, so it
UNDERSTATES.** **A file outside the closure today can be inside it once `sq` is
supplied.** **Say whether that applies to `Key.lagda.md`.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-309/lj-1.309-report.md`, read WHOLE.** The target.
- **`agents/tasks/LJ-1-292/lj-1.292-report.md`**, the ladder's origin and the
  report `[LJ-1.309]` partly refutes.
- **`agents/tasks/LJ-1-287/lj-1.287-report.md`**, the weak reading and its
  triage, for what a false positive cost.
- **`agents/tasks/LJ-1-289/lj-1.289-report.md`**, the one landed cure: 495.23 s
  to 6.65 s for five lines. **The only measured prize of this shape.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on a typechecker's cost model for a
spelling.** Say so in one line and return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-309/lj-1.309-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-311/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **C-42, C-50, C-44, P-l, R-41.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-22, C-32, C-36, C-39, C-40, C-49.** I-5. **D-10, D-26.**
- **DD0, DD4, DD8, DD18, DD24, DD25.**

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1: whether
`sucIter` is the only iterate spelling in this tree, with the evidence, and what
that makes of Condensation. Then the 522 ms, reconciled or still open. Then
whether the 43-times ladder step survives a realistic re-measurement. Then the
half-cure's self-refutation, checked. Then the DD4 axis with the understatement
qualification applied. **Mark every negative MEASURED or INFERRED.**
