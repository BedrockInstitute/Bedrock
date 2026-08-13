# LJ-0.4m: the dead-name re-scan, after four rounds of deletion

tier: codex (default)

## GOAL

Find every name that is dead in code TODAY and delete it. Block A's scan is
four rounds stale, and deletion CASCADES: a name dies when its last consumer
dies. Land what is really dead. Refuse anything that is content.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS BLOCK AND NOT ANOTHER

The AC side stands at **17,166** against an owner target of **17,000**, so 184
lines must go. Seven survey bands have now been tested and the record is one
sentence:

| Block | Band | Measured | Outcome |
|---|---|---|---|
| A, dead names | -226 to -296 | **-240** | landed |
| B, existential frame | -190 to -340 | **+24** | refused |
| C, clause frames | -180 to -315 | **-59** | stopped, it gutted two chapters |
| E, traversal share | -60 to -120 | **+19** | refused |
| G, lex kit | -40 to -80 | **+49** | refused |
| I, within-file dedup | -80 to -140 | **-30** | landed one file of seven |
| prose-freed names | -55 to -65 | **-59** | landed |

**EVERY KIT BLOCK MEASURED NET POSITIVE. Only DELETION measured negative.**
That is why you are being sent to delete rather than to extract. **Do not
build a kit. Do not extract a helper. Do not share a shape.** If you find
yourself writing a new definition, you have left the task.

## WHY THERE IS ANYTHING LEFT TO FIND

Deletion cascades and nobody has re-scanned. Four rounds have landed since
block A's scan: block A itself, `[LJ-0.4i]`'s `Separation` fold, and the
prose-freed names in commit `ab99b23`, which deleted 14 names across 12
masters.

**Worked example, so the shape is unmistakable.** `ab99b23` deleted
`endExtension` from `src/L/Choice/Step.lagda.md`. Its two private helpers
`unfoldγ` at `:837` and `unfoldβ` at `:840` existed only to serve it, and the
`agree` block above them may now be dead too. The same commit deleted
`Lset-μ` from `src/L/Choice/Stage.lagda.md`, which may have been the last
consumer of `defStage-suc` at `:270`.

**Verify each of those rather than trusting this paragraph.** D-10: a recorded
residue names a target and the target can be false.

## MY OWN SCAN, WHICH IS CRUDE AND WHICH YOU MUST NOT TRUST

I ran a token-count scan and it returned 53 candidates with known false
positives. **Treat it as a place to start looking, never as a list to
delete.** Block A's own report records three false positives of exactly this
kind, at `_build/lj-0.4a-report.md:151-154`: `_⊆ᵇ_`, `isSet⟪_⟫` and `⌜_⌝ᵗ` are
all live through a RENDERED form that a token scan misses.

Candidates worth checking first, with their trap where I know it:

- `src/FOL/Coding.lagda.md:157-181`, the `c-con`, `c-var`, `c-∈`, `c-≐`,
  `c-∧`, `c-∨`, `c-⇒`, `c-¬`, `c-⊤`, `c-⊥`, `c-∀`, `c-∃`, `c-∀∈`, `c-∃∈`
  family, 14 names. **HIGH FALSE-POSITIVE RISK**: this is the same chapter as
  `⌜_⌝ᵗ`, which block A found live through its rendered form. Check for a
  pattern-match use before you believe any of them is dead.
- `src/L/Choice/Step.lagda.md:837,840` and the block above them, the cascade
  worked above.
- `src/L/Choice/Stage.lagda.md:266,270`, `defStage-ord` and `defStage-suc`.
- `src/L/Constructible.lagda.md:176-179`, `∅-layer`, `union-layer`,
  `union₂-layer`.
- `src/L/Recursion.lagda.md:195,281`, `val-graph` and `defines`.
- `src/L/Choice/Internal.lagda.md:186`, `InLimitAt-out`.
- `src/L/Coding/Sequence.lagda.md:364`, `LsetGraph`.
- `src/L/Choice/Limit.lagda.md:406`, `limitS`.
- `src/FOL/ZFModel.lagda.md:397`, `uniqueSetOf`.
- `src/Base/Truth.lagda.md:50`, `isSetΩ`.

**Run your own scan too.** Mine looked at one thing. A name re-exported
through a module instance can hide a consumer, which block A recorded as its
own residual doubt at `_build/lj-0.4a-report.md:277-279`.

## THE TWO RULES THAT DECIDE A DELETION

**RULE 1, THE LIVENESS TEST.** A name is dead when a boundary-aware whole-tree
grep finds no use outside its own definition, in code. **Check the rendered
form, the pattern-match position, and any `open ... public` re-export.**
Prose alone does not keep a name alive; prose gets rewired.

**RULE 2, THE CONTENT LINE, and this one is the reason a human wrote this
brief.** A name that is dead in code may still be CONTENT, and content stays.
Two worked cases from today:

- **STOPPED at `Codes-out` and `Codes-in`** in `src/L/Coding/CodeSet.lagda.md`.
  They became dead when `Codes-spec` was deleted. They are the two directions
  that CHARACTERIZE the set `Codes`. Deleting a set's whole characterization
  leaves a chapter that defines two sets and proves nothing about them. **That
  is content removal, not compression. They stay, and so does the `AllCodes`
  pair.**
- **KEPT `denote-table`** in `src/L/Choice/Name.lagda.md`. It is dead in code,
  but `src/L/Choice/Adequate.lagda.md:942` records a MEASUREMENT against it:
  the composite equation does not discharge in 400 s while its two factors
  take 2.4 s each. Deleting the name orphans a measured law at its own site.

**The operational form: if deleting a name would make a chapter stop stating
what it is about, or would orphan a recorded measurement, KEEP IT and say so
in the report.** A kept name with a reason is a good return.

## WHAT YOU MAY NOT TOUCH

- **`src/Everything.lagda.md`.** Never, by standing rule. **If a name's only
  surviving reference is prose there, LIST IT with the catalog line number and
  leave the name in place.** I rewire the catalog and delete it afterwards.
  That is exactly how the last 59 lines were found.
- **`src/L/Hierarchy.lagda.md`, `src/L/Choice/Table.lagda.md`,
  `src/L/Choice/Before.lagda.md`.** `[LJ-0.4f]` is editing them RIGHT NOW
  (C-25).
- **`src/L/Hull.lagda.md`, `src/V/Collapse.lagda.md`,
  `src/V/Presentation.lagda.md`.** These are the GCH wing, landed days ago and
  consumed by work not yet written. Their names read as dead and are not.

## HOW TO REVERT, and a sibling makes this dangerous

- **Revert ONLY by exact path**, one at a time:
  `git checkout -- src/L/Choice/Stage.lagda.md`.
- **NEVER `git checkout .`, `git checkout -- .`, `git stash`, `git reset
  --hard`, or `git clean`.** Any of those destroys `[LJ-0.4f]`'s work.
- **Never commit and never push.**

## STAGING

Delete in batches by file. Typecheck after each batch. **A batch that fails to
typecheck reverts alone**, and its names go in the report as live with the
error. Do not let one wrong call sink the block.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For this block DD4 applies in the NEGATIVE, and that is deliberate.** You
are deleting, not building, so nothing here becomes shared. Block A's brief
carried the same clause and block A is the campaign's best result. **Say so in
one line and spend no effort forcing generality.**

**One live DD4 question you must answer, though:** if a name you are about to
delete looks like something the GCH wing will want, RECORD it with its
`file:line` instead of deleting it silently. A name the wing needs is cheaper
to keep than to rebuild.

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. For a deletion pass the live
question is narrow: **does a name you are about to delete state something the
literature treats as a named result of the theory?** A dead helper is safe. A
dead theorem that the orthodox development names is content under rule 2.

- `dev/literature/digest.md`, the orthodox route.
- `dev/literature/j-hierarchy.md` if a name sits in order or well-order
  material.

**If nothing there bears on the sweep, say so in one line naming
`dev/literature/`.** That is an honest answer and it satisfies DD18. Silence
is not.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-0.4a-report.md`. Read it first.** It is the model return for
  this exact task. Its section 3 lists what it kept and why; `:151-154` lists
  its false positives; `:277-279` records its own residual doubt.
- `_build/lj-0.8-review.md` 6.1 and 7.6, the scan and the orchestrator actions
  this block completes.
- `dev/memos/simplification-register.md:33-38`, S13 to S18 with their
  verdicts. Do not re-propose their shapes.
- `dev/LESSONS.md` is NOT archived and still binds. **P-q, P-m and D-10 decide
  this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Your whole input is a residue list and I have told you it is crude.
- **P-q. A line lever is not a seconds lever.** Expect zero seconds saved.
- **P-m. The check-cost rate is a content-class certificate.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk.
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity. **Directly on point: a name inside an
  `opaque` block may be reached through the seal, so check the seal before
  you call it dead.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **C-22. Write the deliverable incrementally.** Block C ran 38 minutes and
  left an all-TODO skeleton. Fill each row as its number lands.
- **C-25.** Parallel writers may not share a file. See the revert warning.

## SCOPE (read)

`_build/lj-0.4a-report.md` first. Then the candidate sites. Then a whole-tree
grep per candidate.

## SCOPE (write)

Any master under `src/` **except** `src/Everything.lagda.md`,
`src/L/Hierarchy.lagda.md`, `src/L/Choice/Table.lagda.md`,
`src/L/Choice/Before.lagda.md`, `src/L/Hull.lagda.md`,
`src/V/Collapse.lagda.md` and `src/V/Presentation.lagda.md`. Your report is
`_build/lj-0.4m-report.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT** and do not weaken a proof.
- **Rewire the prose** in every language group of any chapter you edit, when
  it names a name you delete. The masters carry `<!--en-->` and `<!--zh-->`
  only, so there are two.
- **Typecheck every file you edit**, one process at a time. Do NOT run
  `make check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.** Deleting a name orphans imports: the last
  round produced 12 unused-import violations and each removal is another line.
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4m-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the net landed.
2. **DELETED**: one table, name, `file:line`, lines freed.
3. **KEPT AND WHY**: the content line, per rule 2, with the reason.
4. **BLOCKED BY THE CATALOG**: names whose only reference is
   `src/Everything.lagda.md` prose, with its line number, for me to free.
5. **FALSE POSITIVES**: what my crude scan flagged that is alive, and how it
   is reached.
6. **THE NUMBER**: in-fence before and after per file, and the net.
7. **SECONDS**: any file whose check time moved, with the noise rule.
8. **DD4**: one line, plus anything recorded for the wing.
9. **LITERATURE USED.**
10. **ARCHIVE USED.**
11. **WHAT I AM NOT SURE OF.**
