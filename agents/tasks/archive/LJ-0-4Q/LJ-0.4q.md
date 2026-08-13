# LJ-0.4q: take the two DELETE rows [LJ-0.4p] traced

tier: codex (default)

## GOAL

Delete two dead blocks and cut the prose clauses that name them, in both
languages. **About 34 in-fence lines.** Refuse either row with a reason if the
tree disagrees with the report.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE TWO ROWS, TRACED BY `[LJ-0.4p]` READ ONLY

`_build/lj-0.4p-report.md` traced every reference for each, with `git blame`
for the prose provenance. **Re-verify every line number: the tree moved under
`[LJ-0.4n]` after that report was written.** D-10.

**ROW 1, about 27 lines. `src/L/Coding/CodeSet.lagda.md`, the arity-one
block.** `Codes`, `Codes-out`, `Codes-in`, `key∈Codes`, `IsKeyOver`, and the
cascade `isCode`, `small`, `sep`. Nothing in the tree consumes any of them.

**THE `AllCodes` PAIR STAYS.** `AllCodes`, `AllCodes-out`, `AllCodes-in` have
live consumers in `Internal`, `Uniform`, `Faithful`, `Adequate` and `Order`.
**Confirm that by grep before you touch the file.** The two sets differ by one
conjunct and they are easy to confuse, which is the whole reason this row is
delicate.

**ROW 2, about 7 lines. `src/L/Choice/Table.lagda.md`, `ix-fill` and
`ix-rep`.** These are the `relL` INSTANTIATION only. **The general pair
`ixRel-fill` and `ixRel-rep` is LIVE, and the `relL-fill` and `relL-rep`
siblings are LIVE.** Delete the instantiation and nothing else.
`[LJ-0.4n]` just edited this file, so its line numbers have moved.

## THIS IS A CONTENT CUT AND THE BRIEF SAYS SO

`dev/LESSONS.md` **D-27** is the rule. Read it. Class 1 says: if a chapter's
opening or recap advertises a result, deleting the proof leaves the chapter
asserting what it no longer proves. **The cure is to cut the clause TOO, and
that is what you are doing here.**

**Row 1's chapter genuinely advertises the characterization**, and its
advertisement is OLD: the opening and the "Both directions" and "Round trip"
sections date from 2026-07-28, well before this campaign. `[LJ-0.4p]` checked
the provenance and found the RECAP clause circular, written this morning by
`ab99b23`, but the older sections real. **So the cut is real work, not free.**
The chapter is about two sets that differ by one conjunct, and after this it
is about one.

**Report what the chapter loses, in your own words, in the return.** If while
reading you conclude the arity-one set is content that must stay, **say so and
refuse the row.** A refusal with a reason is a full deliverable and it will be
believed.

Row 2's recap calls its four statements "the chapter's deliverable"
(2026-07-31), so the same test applies at smaller scale.

## HOW TO CUT A CLAUSE

- Cut the clause in **BOTH language groups**, `<!--en-->` and `<!--zh-->`. The
  masters carry no `<!--ja-->`.
- **`src/Everything.lagda.md` is off limits to you.** If the catalog names a
  name you delete, LIST IT with its line number in the return and leave it. I
  rewire the catalog myself.
- **This exact failure happened today:** `ab99b23` rewired the English catalog
  and left ten dead names standing in the Chinese one. `[LJ-0.4p]` found them.
  **Grep for every name you delete, in every file, before you call the row
  done.**
- **DD23 freezes mathematical prose.** You may DELETE a clause that names a
  deleted name. Do NOT write new mathematical exposition to replace it.

## THE NUMBER THIS SERVES, and it must not bend your judgment

The AC side stands at **17,029** against an owner target of **17,000**. These
two rows are 34 lines, so they decide whether the target is met.

**That is a reason to be careful and NOT a reason to force either row.** If a
row does not hold up, refuse it and I will tell the owner the target is short.
This campaign has run eight blocks and its best returns were refusals.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Here DD4 is a KEEP argument and you must test it before deleting.** A dead
name the GCH wing would otherwise rebuild is cheaper kept than re-derived.
`[LJ-0.4p]` kept `LsetGraph` on exactly this ground: the wing's certificate
`LsetGraphAt {2} zero (suc zero)` is definitionally `LsetGraph`. **Ask the
same question of the arity-one code set**, whose subject is naming arity-one
formulas from inside the model, and say the answer in the return.
`_build/lj-1.1-recon.md` lists the six funded wing blocks.

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. The live question is narrow:
**does the orthodox development treat the arity-one code set as a named object
of the theory?** If it does, row 1 is content under D-27 class 1 and should be
refused, whatever the grep says.

- `dev/literature/digest.md`, the orthodox route, on definability and the
  definable powerset.
- `dev/literature/j-hierarchy.md` if the material touches the order.

**If nothing bears on it, say so in one line naming `dev/literature/`.** That
is an honest answer and it satisfies DD18. Silence is not.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-0.4p-report.md`. Read it first.** It is your input: both rows,
  traced to every reference, with prose provenance per row.
- `_build/lj-0.4a-report.md` `:151-154`, three false positives that are live
  through a RENDERED form a token scan misses. Check for that shape.
- `dev/memos/simplification-register.md:33-38`, S13 to S18 with verdicts.
- `dev/LESSONS.md` is NOT archived and still binds. **D-27 is the task. D-10
  is why you re-verify every line number.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Both rows are residues and the tree moved after they were written.
- **P-h. Definability walks are module-parameterized, never
  function-parameterized.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38: sealing and opacity.** A name inside an `opaque` block may be
  reached through the seal. D-27 class 2 protects the readings of a seal.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. You are alone;
  keep it that way.
- **C-22. Write the deliverable incrementally.**

## SCOPE (read)

`_build/lj-0.4p-report.md` first. Then `src/L/Coding/CodeSet.lagda.md` and
`src/L/Choice/Table.lagda.md` in full. Then a whole-tree grep per name.

## SCOPE (write)

`src/L/Coding/CodeSet.lagda.md` and `src/L/Choice/Table.lagda.md`. Your report
is `_build/lj-0.4q-report.md`. **Never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT** that survives, and do not weaken a
  proof.
- **Do not leave any file as a re-export stub.**
- **Typecheck every file you edit AND every consumer you touch**, one process
  at a time. Do NOT run `make check` or a whole-tree check.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.** Deleting names orphans imports and each
  removal is another line.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Evidence is `file:line`.**
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4q-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the net landed, per row.
2. **PER ROW**: in-fence before, after, net, seconds before and after, exit
   code, landed or refused.
3. **WHAT THE CHAPTER LOSES**, in your own words, for row 1.
4. **THE CATALOG NAMES I COULD NOT TOUCH**, with `src/Everything.lagda.md`
   line numbers, for me to rewire.
5. **EVERY NAME I GREPPED**, and where it still appears.
6. **DD4**: could the wing want either of these?
7. **LITERATURE USED.**
8. **ARCHIVE USED.**
9. **WHAT I AM NOT SURE OF.**
