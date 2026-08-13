# LJ-0.7: digest Devlin II.5 and its engine into the literature

tier: codex (default)

## GOAL

Digest Devlin's chapter II.5 and the machinery it runs on into
`dev/literature/`, so `[LJ-1.12]` can price the crossing against a source
instead of against memory. **Write no Agda. You hold no Agda slot.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS BLOCKS THE PHASE

`[LJ-1.12]` re-targets the condensation crossing and it **cannot start without
this**. `[LJ-1.2]` returned NO-GO on the first crossing: the step clause of
`LsetGraphAt` has no Δ₀ witness at any carrier. `[LJ-1.11]` then refuted the
fallback: route C's archived structural story has a Def-step that collapses to
`⊤̇`, so it recognizes no level at all. **Two routes are dead and the third has
never been read out of the source.**

So the phase is blocked behind one literature task, and that is why it goes
first.

## WHAT TO DIGEST, and the widening is `[LJ-1.11]`'s

The primary text is `_build/literature/dev2.txt`, the OCR of Devlin chapter
II. **Cite it by line number**, as `dev2.txt:NNNN`, which is how the existing
corpus cites it.

- **II.5 entire**, the condensation chapter. 5.1 to 5.4 are the spine.
- **5.2(i) and 5.2(ii)**, the collapse. `[LJ-1.4]` delivered `fixes` as
  5.2(ii); the review found 5.2's object is an EXTENSIONAL substructure and
  not a transitive one (F2).
- **5.3**, the hull, and **its implicit substitution step**, which `[LJ-1.11]`
  F3 names as a possible route around a missing theorem.
- **5.4**, the counting.
- **II.2.4 to II.2.7**, **II.1.1(vii)**, and **5.9 to 5.11**: `[LJ-1.11]`
  widened the task to these. Say for each whether it bears on the crossing.
- **The ENGINE**: whatever machinery II.5 assumes and does not prove. Name it
  explicitly. The point of this task is that a later brief can cite it.

## THE QUESTION `[LJ-1.12]` WILL ASK YOU, so answer it in the digest

**What does the condensation argument actually require of the level story?**
`[LJ-1.2]` measured that a Δ₀ witness does not exist at the satisfaction
leaves. So: does Devlin's argument need one? If it does, the internalization
route needs a different crossing; if it does not, say what it needs instead
and at what strength.

**Do not price the Agda.** That is `[LJ-1.12]`'s job. Give it a source it can
price against.

## OCR IS THE HAZARD, and the corpus already records it

`dev/literature/primary-sources.md` records that the Dev chapters are ABBYY
scans with degraded math glyphs, and that two load-bearing pages needed a
second pass with tesseract. `dev/literature/devlin-errata.md` records the
known ERRORS in the book itself, separately from OCR damage.

- **Cross-check every load-bearing statement against Jech chapter 13**, which
  is a typed PDF, per this task's row in `dev/PLAN.md`.
- **Mark a reading you cannot resolve as UNRESOLVED with both candidates.** Do
  not silently pick one. A guessed glyph in a digest becomes a false premise
  in a build brief.
- **Separate an OCR doubt from a Devlin ERRATUM.** The errata file exists
  because the book has real errors, and confusing the two classes wastes a
  later dispatch.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For a digest DD4 is a READING INSTRUCTION, and it is the most useful thing
you can do for the campaign.** The route builds an L tower and a J tower and a
bridge between them (DD2). So when II.5's argument uses a property of the
level story, ask: **is that property specific to the Def tower, or would the
J tower supply it too?** Say so per step. A step that needs only a general
property is a step both proofs can share, and nobody has read the source with
that question in hand.

## LITERATURE (DD18)

This task IS the literature work, so the section names what already exists so
you extend rather than duplicate.

- `dev/literature/digest.md`, the orthodox route. **Read it first** and say
  what it already covers of II.5.
- `dev/literature/fine-structure.md` and `dev/literature/rudimentary-functions.md`
  already reference 5.2, 5.3 and 5.4. **Extend, do not restate.**
- `dev/literature/j-hierarchy.md` for the order and the S-hierarchy.
- `dev/literature/primary-sources.md` for what was fetched and how.
- `dev/literature/devlin-errata.md` for the known book errors.
- `dev/literature/BIBLIOGRAPHY.md` for what was fetched and what consumed it.
  **Add your rows there.**

Return a **LITERATURE USED** section naming what you read and what you took.

## ARCHIVE (DD18)

- `_build/lj-1.11-review.md`, sections F1 to F3 and section 2. **This is your
  commissioning document.** F1 killed route C, F2 and F3 are the two build
  tasks running beside you.
- `_build/lj-1.1-recon.md`, the wing plan the review corrected.
- `_build/lj-1.2-gate.md`, the NO-GO and WHY, which is the question above.
- `archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`: the
  retired rud route read this same chapter. **Say what it concluded and
  whether that conclusion survives the route change.**
- `dev/LESSONS.md` is NOT archived and still binds. **D-26 decides level-story
  questions and it is the law your reading tests.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Every claim in the existing digests is a residue. Two have already been
  refuted this phase.
- **C-22. Write the deliverable incrementally**, never at the end.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Directly on point: it is the shape of
  the question you are asking of Devlin's argument.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** The J tower carries generation data; the Def tower carries syntax.
  **Report which one II.5 leans on at each step.**

## SCOPE (read)

`_build/literature/dev2.txt` first. Then the existing `dev/literature/` files.
Then the three `_build/lj-1.*` reports. Then the archive.

## SCOPE (write)

`dev/literature/devlin-II5.md`, new, and rows appended to
`dev/literature/BIBLIOGRAPHY.md`. **No file under `src/`. No other file under
`dev/`.** Your report is `_build/lj-0.7-report.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Run NO `agda` and NO `make check`.** Two siblings hold the Agda slots.
- **Evidence is a line citation into the source**, as `dev2.txt:NNNN`, or a
  page number for a PDF. A digest that cannot be checked can only be believed.
- **Quote, never paraphrase, a load-bearing statement.** Then say what it
  means in your own words, separately and marked as yours.
- **Mark every unresolved glyph** rather than choosing.
- **DD23 freezes mathematical prose in `src/`.** It does NOT freeze
  `dev/literature/`, which is a digest of somebody else's mathematics. Write
  plainly.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `dev/literature/devlin-II5.md` INCREMENTALLY, skeleton first, and
`_build/lj-0.7-report.md` beside it.

1. **THE SPINE**: 5.1 to 5.4, each with its statement quoted and cited.
2. **WHAT THE ARGUMENT REQUIRES OF THE LEVEL STORY**, step by step, with the
   strength each step needs.
3. **THE ENGINE**: what II.5 assumes and does not prove, named.
4. **DEF TOWER OR EITHER TOWER**, per step (DD4, D-26).
5. **THE WIDENED SECTIONS**: II.2.4-2.7, II.1.1(vii), 5.9-5.11, each with a
   bears-or-does-not-bear verdict.
6. **UNRESOLVED OCR**, with both candidates, and the Jech 13 cross-check.
7. **ERRATA**, kept separate from OCR doubt.
8. **WHAT THE RETIRED ROUTE CONCLUDED**, and whether it survives.
9. **LITERATURE USED.**
10. **ARCHIVE USED.**
11. **WHAT I AM NOT SURE OF.**
