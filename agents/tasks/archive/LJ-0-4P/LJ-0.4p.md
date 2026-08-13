# LJ-0.4p: re-test every name kept by a citation, READ ONLY

tier: codex (default)

## GOAL

Find every dead name in `src/` that survives **only because a document
mentions it**, and judge each against the amended D-27. **Write no code and
delete nothing.** Return a ranked list with a line count per row. The
orchestrator deletes afterwards.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS IS READ ONLY, and it is not negotiable

`[LJ-0.4n]` is editing `src/L/Coding/Sequence.lagda.md`,
`src/L/Choice/Table.lagda.md`, `src/L/Choice/Before.lagda.md` and
`src/L/Hierarchy.lagda.md` RIGHT NOW, and it is measuring cold seconds. Those
four files sit in the dependency cone of most of the tree. **A second Agda
process writing interfaces would corrupt its measurements**, which already
happened once today: `[LJ-0.4f]` had to clone the tree to `/tmp` because a
sibling edit made its baseline unbuildable.

So: **run NO `agda`. Run NO `make check`.** You hold no Agda slot. You read,
you grep, you count, you rank.

## THE RULE YOU ARE APPLYING, amended hours ago

`dev/LESSONS.md` **D-27**: "no code consumer" identifies a dead HELPER, never a
dead RESULT. Read the whole entry. It has two surviving classes and one
withdrawn class, and the withdrawal is the point of this task.

- **CLASS 1, SURVIVES. A chapter's stated result.** If the chapter's opening or
  its recap advertises the property, deleting the proof leaves the chapter
  asserting what it no longer proves. **The cure is to delete the clause TOO,
  not to keep the code.** Class 1 is a reason to do more work, not a veto.
- **CLASS 2, SURVIVES AND IS THE STRONG ONE. The readings of a seal.** An
  `opaque` definition plus its unsealing lemmas are ONE unit. Delete the
  readings and the definition survives as a seal nobody can open.
- **CLASS 3, WITHDRAWN TODAY. "A recorded measurement cites it."** This is
  **not** a reason to keep code in `src/`. Repoint the citation at the commit
  where the name was last green. `dev/ARCHIVE.md` already accepts a commit as
  provenance, and `git show <sha>:<path>` re-runs the measurement.

**The worked case, so the standard is unmistakable.** `L.Choice.Name.denote-table`
was held back this morning on class 3, because `dev/LESSONS.md` Rule 20 cites
it by fully qualified name. The owner asked why a law more general than its
instance needs the instance alive. It does not. Rule 20 now carries commit
`35cb762` and the lemma is deleted, at minus 16 including its orphaned
imports. **Distrust any argument of the form "a document mentions it."**

## THE KNOWN CANDIDATES, and the first is the sharpest

Re-test all of these. Each was kept TODAY, by me or by a sibling agent.

1. **`Codes-out` and `Codes-in` in `src/L/Coding/CodeSet.lagda.md:476,484`,
   plus the `AllCodes-out` and `AllCodes-in` pair.** About 8 lines. I kept
   them because they "characterize the set". **Check the provenance of that
   protection: I WROTE the recap clause that names them, this morning, in
   commit `ab99b23`, when I deleted `Codes-spec`.** A name protected by a
   sentence its own deleter wrote hours earlier is circular. Judge it fresh.
2. **The `Codes` and `CodesT` families in `src/FOL/Coding.lagda.md:156-182`,
   with the fourteen `c-*` constructors.** About 28 lines. `[LJ-0.4m]` kept
   them as "the chapter's real interface", and that prose is OLD, so class 1
   looks genuine here. **Test it anyway**, and if it holds, say what the recap
   would have to lose.
3. **`LsetGraph` in `src/L/Coding/Sequence.lagda.md:364`.** 2 lines. Kept on
   "the chapter prose names it as the deliverable". **READ ONLY on this file,
   harder than the rest: `[LJ-0.4n]` is editing it. Do not open it for
   writing and do not trust its current line numbers.**
4. **Anything you find that these three missed.** Your own scan matters more
   than my list. Four deletion rounds have landed and each one orphaned more.

## WHAT IS ALREADY SETTLED. Do not re-open it.

- `endExtension` and its private block in `src/L/Choice/Step.lagda.md`, and
  `defStage-ord`, `defStage-suc` and `Lset-μ` in `src/L/Choice/Stage.lagda.md`.
  These were deleted this morning and **REVERTED on purpose**. Step's opening
  calls end extension "the property the rest of the part needs", and the Stage
  names are the only openings of a seal. Class 1 and class 2. **They stay.**
- `Sat-out`, `σ₁-up` and `π₁-down`: the funded plan rides them
  (`_build/lj-0.4a-report.md:103-105`).
- `src/L/Hull.lagda.md`, `src/V/Collapse.lagda.md` and
  `src/V/Presentation.lagda.md`. GCH wing, landed days ago, consumed by work
  not yet written. Their names read as dead and are not.

## HOW TO JUDGE A ROW, and give me the numbers to act on

For each candidate report, in one table row:

- the name and its `file:line`;
- **in-fence lines freed**, counted at ledger caliber, INCLUDING cascade: the
  helpers that die with it, and the imports that fall out. `denote-table`
  looked like 7 and measured 16;
- **every reference**, at `file:line`, split into code, own-chapter prose,
  `src/Everything.lagda.md` prose, `dev/` document;
- **which D-27 class applies, or NONE**;
- **who wrote the protecting prose and when.** Run `git log -S` or
  `git blame`. A clause written today by the same sweep is worth less than one
  that predates the campaign. This column is the finding I most want.
- **VERDICT: DELETE, DELETE WITH A CLAUSE CUT, or KEEP**, with the reason.

## WHAT WOULD MAKE THIS TASK A FAILURE

Recommending a deletion you have not traced to every reference. The point of a
read-only pass is that it can afford to be exhaustive. **Rank by lines freed,
and put anything you are unsure of at the bottom with its doubt written out.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Here DD4 is a KEEP argument and you must look for it.** A dead name the GCH
wing would otherwise rebuild is cheaper kept than re-derived. If a candidate
looks like something the wing needs, say so and mark it KEEP.
`_build/lj-1.1-recon.md` lists the six funded wing blocks. Nothing else in
this task builds shared code, so answer DD4 in one line otherwise.

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. The live question is narrow:
**does a candidate state something the orthodox development treats as a named
result?** A dead helper is safe to lose. A dead theorem that the literature
names is content under D-27 class 1.

- `dev/literature/digest.md`, the orthodox route.
- `dev/literature/j-hierarchy.md` for order and well-order material.

**If nothing bears on the sweep, say so in one line naming
`dev/literature/`.** That is an honest answer and it satisfies DD18. Silence
is not.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-0.4m-report.md` sections 2 and 3. Read first.** Its section 3
  is the keep list you are re-testing.
- `_build/lj-0.4a-report.md` section 3 and `:151-154`, the original keep list
  and its three false positives, all live through a RENDERED form a token scan
  misses.
- `dev/ARCHIVE.md`, the "Last green" column, which is why a commit is adequate
  provenance.
- `dev/LESSONS.md` is NOT archived and still binds. **D-27 is the task. D-10
  is why you verify every line number.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Every row of my candidate list is a residue and I have told you one of them
  is circular.
- **C-22. Write the deliverable incrementally**, never at the end. Block C ran
  38 minutes and left an all-TODO skeleton.
- **P-m. The check-cost rate is a content-class certificate.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Relevant when you judge whether a dead
  statement is content: a statement that drags a presentation into its type is
  usually a helper, not a result.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Relevant if a candidate sits in the order or well-order material,
  where a name may look dead and be the two towers' shared vocabulary.
- **R-35, R-38: sealing and opacity.** A name inside an `opaque` block may be
  reached through the seal. This is D-27 class 2 and it is the class that
  protects the most.

## SCOPE (read)

All of `src/`, `dev/LESSONS.md` D-27 and Rule 20, `dev/ARCHIVE.md`, and the
two reports above. Use `git log -S` and `git blame` freely.

## SCOPE (write)

`_build/lj-0.4p-report.md` and nothing else. **No file under `src/`, for any
reason.**

## CONSTRAINTS

- **READ ONLY on `src/`. No edits, no commit, no push.**
- **Run NO `agda` and NO `make check`.** A sibling is measuring.
- **Never run `git checkout`, `git stash`, `git reset` or `git clean`.**
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Evidence is `file:line`.**
- **A row that says KEEP with a reason is as valuable as one that says
  DELETE.** The last sweep over-reached and cost 51 reverted lines.
- Write ASD-STE100: active voice, one instruction per sentence, 20 words or
  fewer, no em dash.

## RETURN

Write `_build/lj-0.4p-report.md` INCREMENTALLY, skeleton first.

1. **THE TOTAL**, first line: lines freed if every DELETE row is taken.
2. **THE TABLE**, ranked by lines freed, with the columns above.
3. **THE PROSE PROVENANCE FINDING**: which protections were written by the
   sweep that created them, and when.
4. **WHAT I COULD NOT DECIDE**, with the doubt written out.
5. **FALSE POSITIVES**: what looks dead and is alive, and how it is reached.
6. **DD4.**
7. **LITERATURE USED.**
8. **ARCHIVE USED.**
9. **WHAT I AM NOT SURE OF.**
