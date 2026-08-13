# LJ-0.8: adversarial review of the AC-side compression

tier: fable 5, high effort. **Owner-named for this task**, 2026-08-10.

## GOAL

Attack the AC-side compression campaign: what is done, what is running, what
is planned. **The deliverable is CORRECTIONS TO THE CODEX BRIEFS** that come
next, concrete enough to paste.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE SITUATION, in numbers

The owner set a prerequisite: bring the AC side to about **16,400** non-blank
in-fence lines, without badly worsening the seconds-per-line ratio. Both are
recorded in `dev/ledger.toml`.

- AC side today: **17,273**. Owed: **873**.
- Banked so far: **minus 240**, block A alone.
- Cold wall: 132.87 s over 17,271 AC lines, ratio 0.007693. Ceiling 133.4 s.

**The estimate track record is the reason you are here.** Three blocks have
been measured against the July survey and it missed two:

| Block | Surveyed | Measured | Outcome |
|---|---|---|---|
| A, dead names | −226 to −296 | **−240** | landed |
| E, traversal share | −60 to −120 | **+19** | refused, reverted |
| G, lex kit | −40 to −80 | **about −49** | refused, reverted |
| C, clause frames | −180 to −315 | **−59** | STOPPED by the orchestrator |

Blocks B (running), D, F and H rest on the same survey.

## WHAT EACH TASK DID, and where its evidence is

- `_build/lj-0.4-compression.md`. The recon. Re-verified the six July levers,
  found eight more (N1 to N8), and planned eight blocks. **Read its section 2
  carefully: it reports T208 as having MEASURED the levers at minus 620 to
  minus 860 against the survey's minus 755 to minus 1,486, and then still
  built a block plan whose raw total is minus 886 to minus 1,541.**
- `_build/l3.32-t208-report.md`. The measurement the recon leans on.
- `_build/lj-0.4a-report.md`. Block A, delivered.
- `_build/lj-0.4e-report.md`. Blocks E and G, both refused with numbers.
  **This is the model return, and the briefs should say so.**
- `_build/lj-0.4c-report.md`. Block C's report is an all-TODO skeleton,
  because the orchestrator stopped the agent at 38 minutes. What it had done
  is in the git history and in the audit commit.
- `_build/briefs/LJ-0.4a.md`, `LJ-0.4c.md`, `LJ-0.4e.md`, `LJ-0.4b.md`. **The
  briefs themselves are objects of review.**

## YOUR JOB

**1. IS THE TARGET SOUND?** 16,000 was refuted by `[L3.32-T205]` as an
unprobed survey optimum, and the owner then set about 16.4k. **Ask whether
16.4k rests on anything better.** If the honest reachable figure is elsewhere,
say where and on what evidence. The owner asked for honest numbers, not
reachable ones.

**2. ARE THE REMAINING ESTIMATES CREDIBLE?** Blocks D, F and H, plus the N1 to
N8 levers, are estimates from site counts. Two of three tested bands failed.
**Give each remaining block a credibility verdict** and say which should be
attempted at all. A block not worth attempting is a finding: it saves a
dispatch.

**3. WAS BLOCK C's FAILURE THE AGENT'S OR THE BRIEF'S?** This is the question
the orchestrator cannot answer about itself, and it is why you were sent.
Block C gutted `L/Coding/Sound` from 801 in-fence lines to seven and `Unique`
from 630 to eleven, moved 1,354 lines into a new module, and netted minus 59.
Read `_build/briefs/LJ-0.4c.md`. **Did that brief invite the outcome?** It
said "extract the SHELL, not the fold" and warned about P-r, but it did NOT
say "a chapter must remain a chapter" until afterwards. Judge the brief.

**4. IS THE SECONDS BAR THE RIGHT BAR?** The reasoning recorded in
`dev/ledger.toml` is that compression at flat seconds must raise the ratio by
arithmetic, so the operative bar is seconds and not the ratio. **Check that
reasoning.** Does it hold at the target? Is 133.4 s the right ceiling, given
that the wing will add its own seconds later and DD24 judges the wing against
the AC baseline?

**5. WHAT DID EVERY SURVEY MISS?** Three passes have now looked at this tree
for compression: July's `[L3.28]`, `[L3.32-T208]`, and `[LJ-0.4]`. All three
priced by inspecting statement surfaces. **Is there a class none of them
looked at?** `L/Coding` is 6,441 lines and `L/Choice` 6,046, together 71
percent of the tree. Look where a survey looks last.

**6. WRITE THE CORRECTIONS.** For each brief still to be written, D, F, H and
any re-run, give the concrete text to add or change. Address at least: what
the net must be measured across, what must not be gutted, when to revert, and
what evidence the return must carry. **This section is the deliverable.**

## WHAT THE BRIEFS ALREADY SAY, so you correct rather than repeat

The most recent brief, `LJ-0.4b`, already carries: the build-measure-revert
protocol from E and G as the model; a chapter must remain a chapter; the net
judged across every file including new modules; seconds before and after per
file and per consumer; C-22 with block C's 38-minute skeleton as its reason;
explicit territory to avoid a C-25 collision. **Do not re-derive these. Say
what is still missing or wrong.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For you it is a live tension to judge, not a box to tick.** `[LJ-0.4e]`
built two kits with real DD4 value whose arithmetic still failed, and refused
them. Blocks B, C and D are the highest DD4 value of the eight because the GCH
wing's twelve clauses would instantiate their frames. **So: does DD4 argue for
landing a block that misses its line band?** The current briefs say no, that
DD4 licenses recording the kit for revival rather than landing it. **Test that
position.** If a frame is worth building for the wing even at a line loss, the
briefs are wrong and should say so.

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. For a compression pass the
question is whether a shape being unified is one the literature treats as a
single object, and whether a chapter being reshaped has a literature-fixed
identity.

- `dev/literature/digest.md`, the orthodox route and section 3 on the order.
- `dev/literature/j-hierarchy.md` for the order and well-order material.
- `dev/literature/fine-structure.md` for the Sigma-1 machinery, if a frame
  touches it.

**If none of it bears on a mechanical unification, say so in one line and move
on.** That is an honest answer. Silence is not.

Return a **LITERATURE USED** section with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- `_build/l3.32-t208-report.md`, the measured levers, and `[T205]`'s verdict
  on where 16,000 came from, in `archive/dev/TASKS-archived.md:276,279`.
- `dev/memos/simplification-register.md:33-38`. **S13 to S18 with their
  verdicts: two SHIPPED, two REVERTED at their gates, one probe RED.** This is
  the record of what has already been tried and refused at this site.
- `archive/dev/JOURNAL-archived.md:4200-4240`, the July survey and its gating.
- `dev/LESSONS.md` is NOT archived and still binds. **P-q, P-r, P-m and P-s
  are the four that decide compression questions.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A REVIEW

From `python3 scripts/rules.py --for review`.

- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  recorded lever names a TARGET and a PRICE, and both can be false. **This is
  your spine: three surveys have priced this tree and two of three tested
  bands failed.**
- **C-22. Write the deliverable incrementally, never at the end.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Relevant to any frame proposal: a
  frame that drags a presentation into a type buys lines and loses seconds.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Relevant if a proposed unification would erase the distinction
  between the two towers' stage content.

## SCOPE (read)

The five reports and four briefs named above, then `src/L/Coding/` and
`src/L/Choice/` where a lever points, then the archive and literature.

## SCOPE (write)

`_build/lj-0.8-review.md` only. **Read-only on `src/`.** An agent holds an
Agda slot, so run no `agda` and no `make check`.

## CONSTRAINTS

- **No edits outside your report. No commit, no push.**
- **Evidence is `file:line`.**
- **Separate what was MEASURED from what was ESTIMATED.** That distinction is
  the subject of this review and conflating them anywhere is a defect.
- **Rank findings.** A wrong target outranks a clumsy brief.
- **An agreeing review is a real result.** If the current briefs are right,
  say so and spend your effort on questions 1, 2 and 5, where the money is.
- Write ASD-STE100: active voice, one instruction per sentence, 20 words or
  fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-0.8-review.md` incrementally, skeleton first.

1. **VERDICT.** Is the target reachable, and is the plan to reach it sound?
2. **THE TARGET**, judged. What figure the evidence supports.
3. **EACH REMAINING BLOCK**, with a credibility verdict and attempt-or-skip.
4. **BLOCK C: BRIEF OR AGENT?** With the brief text that would have prevented
   it.
5. **THE SECONDS BAR**, judged.
6. **WHAT EVERY SURVEY MISSED**, if anything.
7. **THE BRIEF CORRECTIONS.** Concrete text. **This is the deliverable.**
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
