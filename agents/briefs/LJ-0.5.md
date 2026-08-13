# LJ-0.5: re-measure the DD24 baseline, cold, on a quiet machine

tier: codex (default)

## GOAL

Measure the AC tree's cold build time and write the two numbers DD24's bar
needs. **You measure and report. You change no code.** The orchestrator writes
the ledger.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS EXISTS

`scripts/ledger.py --check` is RED and has been all day:

> RATIO BASELINE IS STALE: DD24's 0.007693 s/line was measured over 17,271
> in-fence lines and the AC side now stands at 17,149, a drift of 122.

`[LJ-0.4]` compressed the tree and **both terms of the ratio moved.** Neither
moved predictably, because a line lever is not a seconds lever
(`dev/LESSONS.md` P-q measured 315 lines removed buying 11.8 seconds). Until
this task runs, DD24's bar is a number from a tree that no longer exists, and
the whole GCH wing is judged against it.

## THE ONE THING THAT RUINS THIS MEASUREMENT

**A CONTENDED MACHINE.** Measured today: a cold gate read **150.09 s** while
two agents held Agda slots, against **133.69 s** quiet. That is a 12 percent
artifact, larger than anything this campaign has moved.

- **I have confirmed from my side that no sibling is live.** Do not try to
  re-confirm it with the dispatch registry: inside your sandbox `os.kill`
  returns EPERM for any pid outside your view and `ps` is blocked, so the
  registry reads a long-dead agent as RUNNING and you cannot clear it.
  `[LJ-0.5]` hit exactly that on 2026-08-10 and had to fall back to `lsof`.
- **What you CAN do, and should:** if you see evidence of a competing Agda or
  GHC process, by any means, report it and stop. That is an observation you
  can make. A verdict on the whole machine is not.

## THE SECOND THING THAT RUINS IT

**THE WRONG `GHCRTS`.** Measured today: `-M16g` alone gave **163.49 s** where
the Makefile's exported setting gave **133.69 s**, a 22.3 percent artifact I
nearly recorded as a regression.

**Use `make typecheck`**, which exports `GHCRTS=-A64m -I0 -M16g` from the
Makefile. Do not invent flags. Do not use `-M8g`: that is the AGENT cap under
C-12, and this task is the orchestrator's own measurement, run alone.

## THE PROTOCOL

1. Confirm no sibling is live.
2. Move the interface cache aside so the check is genuinely COLD. Record how
   you did it.
3. Run `make typecheck`, timed to hundredths of a second. Record the exit
   code.
4. **Repeat twice more, cold each time.** Three runs, three numbers.
5. Report all three plus the spread. The wall's own three measurements once
   spread 0.82 s, so a single number hides its own noise.
6. Count the AC side with `python3 scripts/ledger.py --brief`, which reads
   HEAD. **Do not count by hand.**

## THE NUMBERS TO RETURN

- **Cold seconds**, three runs, with the spread and the exit codes.
- **AC in-fence lines** at HEAD, from `ledger.py --brief`.
- **The ratio**, seconds divided by lines, to six decimals.
- **The comparison to 0.007693**, as a percentage, and whether it sits inside
  DD24's 1.15 tolerance.
- **The wing's separate figure**: `src/V/Collapse.lagda.md`,
  `src/L/Hull.lagda.md` and `src/V/Presentation.lagda.md` are declared wing in
  `dev/ledger.toml` and are NOT in the AC count. Say what the AC-only figure
  is, so the two are never conflated.

## WHAT A HONEST FAILURE LOOKS LIKE

If the ratio rose more than DD24's tolerance, **say so plainly with the
number.** Do not soften it and do not look for a favourable framing. The
campaign removed about 124 lines at roughly flat seconds, so the ratio MUST
rise by arithmetic; the question is only by how much. A rise inside tolerance
is the expected result, not a problem.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For this task DD4 is not in play: you write no code.** Say so in one line.
But the measurement SERVES DD4: DD24's bar is what stops the GCH wing being
built at instantiation rates instead of parameterized ones, and shared generic
code is exactly what keeps the rate low (P-m: parameterized 0.010 to 0.013 s
per line, instantiation 0.22 to 0.297, a twentyfold spread no line count
reveals).

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. **This is a timing
measurement and no mathematics bears on it.** Say that in one line naming
`dev/literature/` and move on. That is an honest answer and it satisfies
DD18. Silence is not.

Return a **LITERATURE USED** section.

## ARCHIVE (DD18)

- `dev/ledger.toml`, the `[ratio]` block: `ac_baseline_provenance` records the
  protocol the last measurement used. **Follow it, so the two numbers are
  comparable.**
- `_build/lj-0.8-review.md` section 5, which judged the seconds bar and
  explains why seconds and not the ratio is the operative gate.
- `dev/LESSONS.md` is NOT archived and still binds. **P-q, P-m and P-s decide
  timing questions. C-28: a threshold from your own projection carries its
  error.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

The write scope names only `_build/`, so this is a recon by derivation. Run
`python3 scripts/rules.py --for recon` AND `--for probe`, and read each
statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The 0.007693 figure and its 17,271-line denominator are BOTH recorded
  residues. Check that `dev/ledger.toml` still says what this brief says it
  says before you compare anything to it.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Relevant to reading the result: a rate
  certifies a content class, so say which class the number describes.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Not in play for a timing run. Say so in one line.
- **P-q. A line lever is not a seconds lever.** This is why the baseline must
  be re-measured rather than recomputed.
- **P-m. The check-cost rate is a content-class certificate.**
- **P-s. Slice rates do not extrapolate to a tree.**
- **C-12.** One Agda process. Heap exhaustion is a wall to report, never a cap
  to raise.
- **C-22. Write the deliverable incrementally.** Fill each run's row as it
  lands, so a killed task still leaves its numbers.
- **D-1. A probe prices THIS setting.** Throw the measurement setup away; land
  nothing.

## SCOPE (read)

`dev/ledger.toml`'s `[ratio]` block, the `Makefile`'s `typecheck` and `GHCRTS`
lines, and `scripts/ledger.py --brief`.

## SCOPE (write)

`_build/lj-0.5-report.md` only. **No file under `src/`, no file under `dev/`.**
The orchestrator writes the ledger, because `ac_baseline_seconds_per_line` and
`ac_baseline_lines` must land in ONE commit or the guard goes stale again.

## CONSTRAINTS

- **Never commit and never push.**
- **Change no code.** If the tree does not typecheck, that is a finding: report
  the error and stop.
- **Evidence is `file:line` for anything read, and a raw number for anything
  measured.**
- **Never report a verdict word where a number fits.**
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.5-report.md` INCREMENTALLY.

1. **THE THREE COLD RUNS**, with spread and exit codes.
2. **AC LINES AT HEAD**, from the tool.
3. **THE RATIO**, six decimals, and the percentage against 0.007693.
4. **INSIDE OR OUTSIDE DD24's 1.15 TOLERANCE**, stated plainly.
5. **THE QUIET-MACHINE CONFIRMATION**, before and after.
6. **THE EXACT COMMANDS YOU RAN**, so the next re-measurement matches.
7. **DD4**, one line.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
