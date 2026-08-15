# LJ-1.309: sweep the WHOLE tree for R-41's full-chain shape

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

**THE OWNER FUNDED THIS SWEEP DIRECTLY, 2026-08-15**: do not abandon the small
hope. **A previous return called its own site clean and I nearly closed the
line on it.** The site is clean. **The TREE was never swept, and the report
that cleared the site says so in its own words.**

## THE PRIZE, and it is measured rather than hoped

**R-41's ladder, MEASURED by `[LJ-1.292]` at
`agents/tasks/LJ-1-292/lj-1.292-report.md:37-39`:**

| depth | cost of the mixed spelling |
|---|---:|
| 1 | not charged |
| 2 | 219 ms |
| 3 | 9,286 ms |
| 4 | **419,218 ms** |

**About 43 times per depth step. The cost is EXPONENTIAL in depth, not linear.**

**And the cure is cheap where the shape is found.** `[LJ-1.289]` landed the
respelling of ONE site, `src/L/Coding/EnvSupply.lagda.md:223-224`: **495.23 s to
6.65 s, minus 488.59 s, for FIVE lines.** That master went from 56.5 times the
DD24 bar to 0.76 times.

**So one undiscovered depth-4 site is worth about 400 seconds.** DD24's whole
standing gap is about 63 s.

## THE EXACT SHAPE TO HUNT, and it is NOT the one the first sweep used

**`[LJ-1.292]` states the strong reading at its `:243-247`:**

> The costly shape is now measured precisely: **a full explicit `sucV` chain
> against a numeral iterate, with or without `Lset`**, super-linear from depth
> 2. **Any future sweep should grep for THAT, not for `sucIter` alone.**

**`[LJ-1.287]`'s original sweep used the WEAK reading**, `sucIter` beside
`sucV`, and it flagged a file the strong reading clears. **Use the strong
reading. Report how many the weak reading would have flagged, so the project
learns which one to keep.**

## THE SENTENCE THAT MAKES THIS TASK EXIST

**`[LJ-1.292]` at `:248-251`, its own words:**

> MEASURED count of further full-chain sites in `src/`: **I did not sweep the
> whole tree, and I say so plainly.** This task's scope was this master.

**That is an honest stop, not a defect. It left the tree unswept and this task
sweeps it.**

## PREMISES

- **R-41 is at `dev/LESSONS.md:4247`.** Read the FULL entry, not the heading.
- **The two known sites are `src/L/Coding/EnvSupply.lagda.md:223-224` (cured by
  `[LJ-1.289]`) and `src/L/Coding/Key.lagda.md:424-429` (measured CLEAN by
  `[LJ-1.292]`).** **Read both, so you know the charged spelling and the free
  spelling by sight before you grep for either.**
- **The standing tree is 94 masters, 32,488 lines** (`ledger.py --brief`,
  measured from HEAD). **VERIFY that count; do not take mine** (C-44).
- **`src/L/Condensation.lagda.md` is the wing's largest single cost**, about
  132 s and about 62 percent of the GCH wing's seconds. **It is therefore the
  first file to sweep, not the last.**

## THE ORDER OF WORK, and phase 1 runs NO AGDA

**PHASE 1, THE CENSUS. NO AGDA. Do this first and completely.**

**Grep every master under `src/` for the strong shape and produce ONE table**,
one row per site: `file:line`, the chain's DEPTH, the spelling on each side,
and whether the site is inside a type or a term. **Rank by depth, descending.**
**Depth is the whole prize, because the cost is exponential in it.**

**A site at depth 1 is worth nothing and you must still list it**, because the
count of depth-1 sites tells the project whether the shape is rare or common.

**PHASE 2, THE PROFILE. AGDA, AND ONLY IF A SLOT IS FREE.**

**C-12 caps this machine at TWO concurrent Agda processes and a sibling
(`[LJ-1.305]`) holds one. A second sibling (`[LJ-1.308]`) may take the other at
any moment.** **So BEFORE any `agda` invocation, run `ps aux | grep '[a]gda '`
and count. If two are already live, DO NOT START A THIRD.** Report the census
and stop; I fund phase 2 separately. **A third process is the crash the heap
caps exist to prevent, and it costs the whole machine.**

If a slot is free: **profile the top-ranked master with
`agda --profile=definitions`, cold, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised**, and report the load beside every absolute figure.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE TREE HOLDS NO FURTHER FULL-CHAIN SITE.** **That is a real and valuable
  answer and it closes the line honestly.** Report the census, the count of
  files searched, and the grep you used, so a later reader can re-run it. STOP.
- **THE TREE HOLDS SITES AT DEPTH 1 ONLY.** Then R-41 is delivered-tree-clean
  and the ladder never fires. **Say so with the count.**
- **A SITE AT DEPTH 3 OR MORE EXISTS.** **That is the hit.** Name it, price it
  from the ladder, and say what the respelling would be. **Do not land it.**
- **THE STRONG READING IS NOT GREPPABLE.** If the shape needs a typechecker to
  recognise, **say so and say what a mechanical proxy would cost in false
  positives.** That answer would tell the project this law can never have a
  checker, which is worth knowing.

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-309/`. **`src/` is forbidden for probes** (I-5) and
  `check-probes.py` enforces it. **Propose a respelling; never apply one.**
- **Do not edit any master.** Do not touch another task directory.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-309/lj-1.309-report.md` in your FIRST five
  minutes** and fill the census table into it as you go (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**R-41, `dev/LESSONS.md:4247`. Depth is free and MIXED SPELLING is what costs.**
The law this task extends. **It is DEPTH-GATED, which `[LJ-1.292]` added.**

**C-42. A refutation measures the site it names and never how far it extends.**
**This task exists because `[LJ-1.292]` obeyed C-42 exactly**: it cleared its
site and refused to clear the tree. **Do the same: clear what you measure.**

**C-50. Profile before you cure.** `[LJ-1.283]` proposed a seal on a site where
it was worth minus 0.19 percent. **A shape that looks costly is a hypothesis.**

**C-44.** Every number in this brief is `[LJ-1.292]`'s, `[LJ-1.287]`'s,
`[LJ-1.289]`'s or mine, and you must re-derive each one.

**P-l. A judgement at one site is a hypothesis at another.** **The ladder was
measured in ONE master's bisect file. Whether it holds in `Condensation` is a
hypothesis until you measure there.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). **A respelling changes SECONDS and not lines, and it
changes them in whichever wing the site sits in.** DD4's own axis is
AC-against-GCH, fixed in code at `scripts/measure/ledger.py:50`. **For every
site you find, say which closure its master sits in: AC, GCH, both, or
neither.** A site in BOTH is worth more than a site in one, and that is the DD4
reading of this sweep.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-292/lj-1.292-report.md`, read WHOLE.** It holds the
  ladder, the strong reading and the honest stop this task starts from.
- **`agents/tasks/LJ-1-287/lj-1.287-report.md`**, especially its sweep note at
  `:402`, which used the WEAK reading. **Take the SHAPE of its error.**
- **`agents/tasks/LJ-1-289/lj-1.289-report.md`**, the landed cure, for what a
  respelling actually looks like in a master.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had its own seconds crisis. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on a typechecker's cost model for a
spelling.** Say so in one line and return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-292/lj-1.292-report.md` FIRST, whole. Then
`dev/LESSONS.md:4247`, the R-41 entry, whole.

## SCOPE (write)

`agents/tasks/LJ-1-309/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **R-41, C-42, C-50, C-44, P-l.** Named above with what each governs.
- **C-12.** Two Agda processes, and phase 2 checks before it starts.
- **C-22, C-32, C-36, C-39, C-40, C-49.** I-5.
- **DD0, DD4, DD8, DD18, DD24.**

## RETURN

**Lead with ONE number: how many full-chain sites the strong reading finds in
`src/`, and the DEEPEST depth among them.** Then the census table, ranked by
depth, with the DD4 closure named per site. Then how many the WEAK reading
would have flagged. Then, if you got a slot, the profile of the top-ranked
master. Then the respelling you propose for any site at depth 3 or more, as a
diff you did NOT apply. **Mark every negative MEASURED or INFERRED.**
