# LJ-0.4: compress the internalization AC tree under 16,000 in-fence lines

tier: codex (default)

## GOAL

Find every line that can come out of the delivered tree, priced, ordered by
risk, and say whether **under 16,000 non-blank in-fence lines** is reachable.
If it is not, say so with the evidence and STOP.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS EXISTS, AND WHY IT IS URGENT

The owner ruled this a PREREQUISITE to phase 1 on 2026-08-09. Phase 1 builds a
GCH wing on this tree, and every line the wing is written on top of is a line
the whole campaign carries. Compressing after the wing lands is more expensive
and touches more code.

## THE FACTS, MEASURED, SO YOU START FROM THE TRUTH AND NOT FROM A MEMORY

**The tree today.** 75 masters, **17,492** non-blank lines inside ` ```agda `
fences, measured by `python3 scripts/ledger.py --brief` from HEAD. It proves
`L ⊨ ZF` and `L ⊨ ZFC`. It typechecks cold in 133.19 s.

**A survey already exists and it is the right survey.** On 2026-07-31
`[L3.28]` surveyed THIS tree at exactly this baseline, whole-tree, and found
first that **there is no module-level dead weight**: the import cone of
`Landmarks` reaches all 74 non-index masters. Its lever table, conservative to
optimistic:

| lever | what it is | conservative | optimistic |
|---|---|---:|---:|
| (a) | dead names | −150 | −400 |
| (b) | verbatim-repeat extraction in `Sound` / `Unique` | −90 | −90 |
| (c) | an `∃ⁿ`-with-`∧` frame combinator | −120 | −300 |
| (d) | frame retrofit of the pre-law chapters | −200 | −341 |
| (e) | one generic fold for `FOL/Manipulation` | −120 | −200 |
| (f) | the recursion-assembly triplication | −130 | −200 |
| (g) | sealed-constant dedupe | **DECLINED**, module-application hazard | |
|  | **sum (a) to (f)** | **−755** | **−1,486** |

Source: `archive/dev/JOURNAL-archived.md:4214-4224`. Landing 16.0k to 16.7k.

**THE GATE ON FOUR OF THEM HAS LIFTED, and this is the finding that makes the
task fundable.** Levers (b), (c), (d) and (f) were GATED in July because
ruling C, the rud fork, would have deleted the chapters they compress. The
record says they "retire with the chapters they would have compressed"
(`archive/dev/JOURNAL-archived.md:4232-4235`). **Ruling C is dead.** The rud
route was replaced on 2026-08-09 and `src/` is the internalization tree, every
one of those chapters intact. So all six levers apply again. Verify this
reasoning before you rely on it; if it is wrong, that is a stop.

**AND THE ARITHMETIC DOES NOT CLOSE ON THESE LEVERS ALONE.** 17,492 minus
1,486 is **16,006**, which is **six lines above the target** at the optimistic
end, and 16,737 at the conservative end. **So the target needs compression
this survey did not find**, or it needs a lever to beat its optimistic
estimate. Do not paper over this. It is the central question of your recon.

**One more input the owner named: the shared base.** `[L3.32-T8]` shipped a
foundation kit on the retired branch: C3 made eight `V.Coding` pair and
singleton helpers public, and C4 added an 18-line `V.Presentation` collecting
four facts about the small presentation, turning inline fiber-and-embedding
sites across the axiom chapters and `L.Definability` into one-line calls.
**The `src/` restore reverted it**: `src/V/Presentation.lagda.md` is gone.

**Measure its real worth before you recommend it.** A first measurement says
it may COST lines net: against `godel-route`, today's `L/Definability` is 4
lines larger and `V/Coding` 1 line larger, so the kit saves 5 at the call
sites while `V/Presentation` itself adds about 18. If that holds, the kit is a
READABILITY refactor, not a slimming one, and it should be judged on that and
not counted toward the target. **Say which it is, with numbers.**

## YOUR JOB

1. **Re-verify the six levers against today's tree.** Each was priced on
   2026-07-31. For each: does its target still exist, is any of it already
   banked, and what is it worth NOW? Lever (a) and lever (e) were partly
   executed on the ZF cone while the others were gated, so some of their value
   may already be inside the 17,492. **A lever whose saving is already banked
   is worth zero and must be said to be zero.**
2. **Hunt for what the July survey missed.** It ran once, in a day, under a
   fork question that has since been answered the other way. The target needs
   about 1,500 lines and the known levers reach 1,486 optimistically, so new
   compression is the difference between success and a stop. Look where a
   whole-tree survey looks last: repeated proof skeletons across the twelve
   satisfaction clauses, the `L/Choice/*` cluster at about 6.0k, `L/Coding/*`
   at about 6.2k, and any place a lemma is stated three times at three
   carriers.
3. **Price the shared-base foundation kit** as above, and say plainly whether
   it adds or removes lines.
4. **Order the work into dispatchable blocks**, each with: the files it
   touches, net lines, the risk that it changes a signature a consumer
   depends on, and whether it can run in parallel with another block. **Two
   agents may not write the same file** (`dev/LESSONS.md` C-25), so the
   partition must be disjoint by file.
5. **Answer the question.** Is under 16,000 reachable? If yes, give the
   ordered plan and the total with its basis. If no, say the best reachable
   figure and what it would cost to go further.

## WHAT THIS TASK MUST NOT DO

- **Do not change any theorem statement, and do not weaken any proof.** The
  tree proves `L ⊨ ZF` and `L ⊨ ZFC` and it must still prove them, with the
  same signatures in `src/Landmarks.lagda.md`. Compression that changes what
  is proved is not compression.
- **Do not count blank lines, comments or prose.** The caliber is non-blank
  lines inside ` ```agda ` fences, and `scripts/ledger.py` is the only
  admissible counter.
- **Do not propose deleting a chapter to hit the number.** There is no
  module-level dead weight, and the cone reaches every master.
- **A line lever is not a seconds lever** (`dev/LESSONS.md` P-q, measured: 315
  lines removed bought 11.8 s). Do not promise seconds. Do report where you
  expect a block to move them, because a separate task re-measures the
  seconds-per-line baseline after this lands.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For you it is unusually direct.** Levers (c), (d), (e) and (f) ARE the
generic rule applied: a frame combinator, a frame retrofit, one generic fold,
and a de-triplicated assembly. Each replaces repeated fixed content with one
generic thing. **So price every block for what it makes cheaper LATER, not
only for the lines it removes today.** A block that removes 100 lines and
makes the GCH wing's twelve clauses free is worth more than one that removes
200 and makes nothing easier. Say which is which. And write the replacements
generic at full strength: a stop-line is never a reason to write fixed.

## ARCHIVE

Per DD18. Required:

- `archive/dev/JOURNAL-archived.md:4200-4240`. The survey, the lever table,
  the gating, and the resolution. **This is the primary source.**
- `dev/memos/L3.28-ac-route.md`. The fork memo. Section 1 has the cone
  measurements, section 3 is Option A, section 7 is the gating.
- `dev/memos/simplification-register.md`. S13 to S18 with their verdicts: S13
  and S15 SHIPPED, S14 and S16 REVERTED at their gates, S17 probe RED. **A
  candidate already tried and reverted must not be re-proposed without new
  evidence.**
- `archive/dev/TASKS-archived.md`. Grep for the compression tasks, `[T8]`,
  `[T168]`, and the `[L3.32-F]` rows. Several compression classes were hunted
  source-wide; say what they found.
- `archive/dev/DECISIONS-archived.md` for D15 and D16.
- `dev/LESSONS.md`, NOT archived and still binding. **P-q, P-r, P-m and P-t
  bear directly on this task.** P-r is a warning: a fold over a clause list
  costs about 3x the hand-written conjunction when its result type must be
  unfolded by every consumer, so a fold lever can lose seconds badly.

Report an **ARCHIVE USED** section: what you read and took, at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`.

- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  recorded lever names a TARGET and the target can be false. **For you: a
  July estimate is a hypothesis about today's tree, not a measurement of it.**
  Re-verify each before you sum them.
- **C-22. Write the deliverable incrementally, never at the end.** Skeleton
  first, fill as answers land.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Naming a transparent construction in a
  TYPE is what costs. Relevant when you propose a frame or a combinator: keep
  the carrier abstract or the lever buys lines and loses seconds.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** The Def tower's stages carry nothing, which is why the coding cone
  exists and is 6.2k lines. Do not propose compressing it away.

## SCOPE (read)

`src/` whole, with `L/Coding/*` and `L/Choice/*` first because they are 12.2k
of the 17.5k. Then `scripts/ledger.py`, `dev/ledger.toml`. Then the archive
above.

## SCOPE (write)

`_build/lj-0.4-compression.md` and nothing else. **Write no master.** This
task is a recon; the blocks it plans are dispatched separately.

## CONSTRAINTS

- **Read-only on the tree.** No edits outside your report. No commit, no push.
- **A sibling agent holds the tree for reading right now** (`[LJ-1.1]`, a
  read-only recon). You may both read. Neither writes.
- **Do not run `agda` on the whole tree**, and do not run `make check`. You
  may time a SINGLE master under `GHCRTS=-M8g` if a block's seconds are in
  doubt; say so if you do.
- **Count with `scripts/ledger.py`, never by hand.** A hand count of in-fence
  lines is how a figure drifts.
- **Evidence is `file:line`.** A lever with no site is a wish.
- **A stop is a deliverable.** If under 16,000 is not reachable, say the best
  reachable figure with its basis and STOP. That is a real result and the
  owner asked for the honest number.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-0.4-compression.md` INCREMENTALLY, skeleton first.

1. **VERDICT.** Is under 16,000 reachable? The projected landing figure, with
   its basis. One paragraph.
2. **THE SIX LEVERS RE-VERIFIED**, one row each: still live, already banked,
   or dead, with today's value and the site at `file:line`.
3. **NEW COMPRESSION FOUND**, if any. Each with site, net lines, and risk.
   This section decides the verdict.
4. **THE SHARED-BASE FOUNDATION KIT**, priced: does it add or remove lines,
   and should it land on readability grounds regardless.
5. **THE BLOCK PLAN.** Disjoint by file, ordered by risk, each with net lines,
   consumer risk, and what it makes cheaper later (DD4).
6. **WHAT I WOULD NOT DO**, and why. A rejected lever with a reason is worth
   as much as an accepted one.
7. **ARCHIVE USED.**
8. **WHAT I AM NOT SURE OF**, and what would settle it.
