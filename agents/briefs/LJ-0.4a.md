# LJ-0.4a: compression block A, the dead names and one shortened proof

tier: codex (default)

## GOAL

Remove the dead names from the delivered tree, and shorten one proof. Land
about 226 to 296 non-blank in-fence lines of reduction, with the tree still
green and every theorem still proved.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT

`src/` is the delivered internalization tree: 75 masters, **17,492** non-blank
lines inside ` ```agda ` fences, proving `L ⊨ ZF` and `L ⊨ ZFC`. It typechecks
cold in 133.19 s.

The owner set a compression target of about **16.4k** on 2026-08-10, before
the GCH wing is built on this tree. `[LJ-0.4]` planned eight blocks. **You are
block A**, and it runs alone because dead-name removal touches many files and
`dev/LESSONS.md` C-25 forbids two writers sharing a file.

## WHAT TO REMOVE

`[L3.32-T208]` ran a name-flow scan over all 75 masters. It extracted 3,097
declaration names and flagged those with zero occurrences in other files and
no in-file use beyond their definition lines. It verified each flag by reading
the occurrence lines. **It found 54 dead names, 210 non-blank lines**, and
called 210 a floor with the true surface likely 210 to 280.

The report is `_build/l3.32-t208-report.md` section 3.1. It names some
directly: `codes-complete` (13 lines, `src/FOL/Coding.lagda.md:202-214`),
`memPairAt-adequate` (16, `src/L/Coding/Environment.lagda.md:148-163`),
`NameAt-out` (12, `src/L/Choice/Internal.lagda.md:714-722`), `isPropBundle`
(9, `src/L/Choice/Table.lagda.md:676-684`), `Lset-μ` / `bound-limit` /
`bound-self` / `bound-below` (13 together, `src/L/Choice/Stage.lagda.md:286`
onward), `endExtension` (3, `src/L/Choice/Step.lagda.md:843-845`),
`Codes-spec` (2, `src/L/Coding/CodeSet.lagda.md:489-490`).

**Re-run the scan yourself.** T208 measured on `main`; `src/` today is the same
content, but verify rather than assume, and the 54 is a floor. Every name you
remove must be verified dead by grep over the whole tree, including mixfix
forms, which the report says it checked by direct grep because the scan misses
them.

## THE ONE RULE THAT MATTERS MOST HERE

**A NAME WITH NO CONSUMER TODAY MAY HAVE A NAMED CONSUMER IN THE FUNDED PLAN.
Check every candidate against `_build/lj-1.1-recon.md` before you delete it.**

This is not hypothetical. I checked two of T208's own examples:

- **`σ₁-up` and `π₁-down`** (`src/FOL/Absoluteness.lagda.md:182-190`) are on
  T208's dead list, described as having "zero code consumers; only prose and
  `src/README.md` name them". **`[LJ-1.1]`'s block plan rides them twice.**
  Its block 1, the Skolem hull, lists "Rides: `abs₀`/`σ₁-up`/`π₁-down`
  (FOL/Absoluteness.lagda.md:122-190)", and section 2.2 calls them "the
  transfer theorems the hull argument uses". **DO NOT DELETE THEM.**

Grep each candidate name in `_build/lj-1.1-recon.md`. If it appears, KEEP it
and list it in your report under "kept for the funded plan", with where the
plan uses it. Deleting and re-adding is churn at best, and at worst the
re-adding never happens because nobody remembers it was there.

`Codes-spec` is a judgement call: it is `[L3.32-T24]`'s closing theorem, the
round trip as an equality, and `[LJ-1.2]`'s NO-GO analysis is about the code
set. It does not appear in `[LJ-1.1]`'s plan. Decide, and say why either way.

## THE SECOND ITEM: `𝒟ₒ→isL`

`src/L/Axioms/Basic.lagda.md:98` holds `𝒟ₒ→isL` as an 18-line proof with a
`where` block. `[LJ-0.4]` reports it can be about 2 lines, because `isL-𝒟ₒ`
sits at `:96` in the same file and `isL-trans` is also there. Net about −16.

**Verify that before you write it.** If the short proof does not typecheck, or
needs a lemma that is not there, say so and leave the long one. A failed
shortening is a fine result; a broken proof is not.

## WHAT YOU MAY NOT DO

- **Do not change any theorem STATEMENT.** The tree proves `L ⊨ ZF` and
  `L ⊨ ZFC` and must still prove them, with the signatures in
  `src/Landmarks.lagda.md` unchanged.
- **Do not weaken a proof** to make it shorter.
- **Do not touch `src/Everything.lagda.md`.** The orchestrator wires it.
- **Do not delete a chapter.** There is no module-level dead weight; the cone
  reaches every master.
- **Do not remove a name that only PROSE uses** without also fixing the prose
  that names it. A `.lagda.md` master's prose is part of the file. If prose
  explains a name you delete, the prose goes too, and the surrounding text
  must still read correctly in all three languages. **Prose you edit is
  exempt from DD23's freeze only in the sense that you are removing it; do
  not write new mathematical prose.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For block A it applies in the negative, and that is the point.** This block
is pure removal and creates nothing generic, so its DD4 value is low and
`[LJ-0.4]` says so. **Your job is therefore not to invent generality here.**
If you see a generalization while you work, RECORD it in your report for
blocks B to G and do not build it: those blocks are separately planned and
have disjoint file territories, and building into their files would break
C-25.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. These bind this task.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, and the parameters stay ABSTRACT through the walk.
  Relevant if a shortened proof tempts you to inline a concrete body.
- **P-k. A read lemma is stated where its consumers use it**, not where its
  proof ends.
- **P-m. The check-cost rate is a content-class certificate**, and
  instantiation is the expensive class. Parameterized work runs about 0.010 to
  0.013 s per line; instantiation about 0.22 to 0.297.
- **P-n. Satisfaction content at a concrete carrier is a payable floor**, not
  a defect.
- **R-35** and **R-38**: the sealing and opacity discipline.
- **I-5**: the inference trap this tree has paid for.
- **C-12. Agda runs under a hard heap cap.** `GHCRTS=-M8g agda <file>`, ONE
  process. Report a heap exhaustion as a wall and never raise the cap.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Naming a transparent construction in a
  TYPE is what costs, not being about a concrete position. **For you: if a
  shortened proof forces a concrete presentation into a statement, the lines
  you saved will be paid back in seconds many times over.**
- **R-40. A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.** State a membership witness at a
  SHALLOW index and climb. Relevant to the `𝒟ₒ→isL` shortening, which is about
  a successor stage.
- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  recorded residue names a TARGET and the target can be false. **For you: the
  54-name list and the 210 lines are T208's measurement of `main`, not a
  promise about today. Re-verify each name before you delete it.**
- **C-22. A dispatched agent writes its deliverable incrementally, never at
  the end.** Create the report early as a skeleton and fill it as each name is
  verified and each typecheck lands. A deletion pass that dies with its budget
  and no record leaves the tree half-edited and nobody knowing which half.

Run `python3 scripts/rules.py --for build` yourself and read each statement.

## ARCHIVE

Per DD18.

- `_build/l3.32-t208-report.md` section 3.1: the scan, the method, its limits,
  and the named examples. **This is your primary source.**
- `_build/lj-0.4-compression.md` sections 2, 3 and 5: the re-verification and
  the block plan you are executing.
- `_build/lj-1.1-recon.md`: **the funded plan, and the list you must not
  delete against.**
- `dev/memos/simplification-register.md:33-38`: S13 to S18 verdicts, so you do
  not re-propose something already reverted at its gate.
- `dev/LESSONS.md` is NOT archived and still binds.

Report an **ARCHIVE USED** section at `file:line`.

## SCOPE (read)

`_build/l3.32-t208-report.md` first, then `_build/lj-1.1-recon.md`, then the
masters your scan flags.

## SCOPE (write)

Any master under `src/` that holds a verified dead name, plus
`src/L/Axioms/Basic.lagda.md`. **Not `src/Everything.lagda.md`.** Also write
your report to `_build/lj-0.4a-report.md`.

## CONSTRAINTS

- **Never commit and never push.** Leave the tree as your report describes it.
- **Typecheck every master you edit**, `GHCRTS=-M8g agda <file>`, one process.
  Say which you ran and the exit code. Do NOT run `make check`: the full gate
  is the orchestrator's to schedule.
- **Count with `python3 scripts/ledger.py`, never by hand.** Report standing
  before and after.
- **Run `python3 scripts/lint-prose.py --check` on every file you edit**, and
  `python3 scripts/lint-agda.py` on the tree. Both are cheap.
- **Evidence is `file:line`.**
- **A stop is a deliverable.** If the dead set is far smaller than 210 lines
  once the funded-plan exclusions are applied, report the real number and
  stop. The measurement is the deliverable, not the target.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-0.4a-report.md` INCREMENTALLY, skeleton first.

1. **THE NUMBER.** Standing before, standing after, net lines, from
   `scripts/ledger.py`.
2. **WHAT I DELETED**, one row per name: name, file:line, lines, and how you
   verified it dead.
3. **WHAT I KEPT FOR THE FUNDED PLAN**, one row per name, with where
   `[LJ-1.1]` uses it. **This section is as important as the deletions.**
4. **`𝒟ₒ→isL`**: shortened or not, with the typecheck result.
5. **TYPECHECKS**: every file, exit code, seconds.
6. **GENERALIZATIONS I SAW AND DID NOT BUILD**, for blocks B to G.
7. **ARCHIVE USED.**
8. **ANYTHING I AM UNSURE OF.**
