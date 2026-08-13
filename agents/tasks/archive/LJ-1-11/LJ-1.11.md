# LJ-1.11: adversarial review of LJ-1 against the literature route

tier: fable 5, high effort. **Owner-named for this task**, 2026-08-10.

An owner ruling names the tier directly, so DD17's codex default does not
apply here. The task also satisfies the standing case for a heavier tier: it
is whole-phase synthesis, and it must judge mathematics against a primary
literature rather than check facts against a file.

## GOAL

Judge every completed and planned task of phase 1 against the mathematical
route the collected literature pins. Where the project deviates, demand a
sufficient reason from BOTH perspectives: **the thresholds** and **the DD
rulings**. Report deviations that lack one.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS REVIEW EXISTS

`dev/literature/` holds thirteen digested notes, built by dispatched agents at
real cost, including a sourced GCH-in-L derivation. **Every phase-1 brief was
written without citing any of it.** DD18's literature half was only added on
2026-08-10, after the recon, the gate, the re-price and two delivered chapters
were already done.

So phase 1 was designed and partly built with the archive consulted and the
literature not. **This review is the compensating pass.** Nothing is presumed
wrong; the question is whether the route the project chose is the route the
mathematics supports, and whether each divergence was paid for.

## WHAT PHASE 1 HAS DONE, with its artefacts

Read each report. They are the object of review.

| Task | State | Artefact |
|---|---|---|
| `[LJ-1.1]` | recon RETURNED | `_build/lj-1.1-recon.md`, the block plan, wing 8.0-10.8k |
| `[LJ-1.2]` | gate **NO-GO** | `_build/lj-1.2-gate.md`, the step clause has no Delta-0 witness |
| `[LJ-1.10]` | re-price RETURNED | `_build/lj-1.10-reprice.md`, chose a THIRD route |
| `[LJ-1.3]` | DELIVERED 343 lines | `_build/lj-1.3-report.md`, `src/L/Hull.lagda.md` |
| `[LJ-1.4]` | DELIVERED 239 lines | `_build/lj-1.4-report.md`, `src/V/Collapse.lagda.md` |
| `[LJ-1.5]` to `[LJ-1.9]` | planned | `dev/PLAN.md` section 11 rows |

**The chosen route in one line:** hull by least-witness search over the
delivered well-order, Mostowski collapse carrier-generic, then condensation by
porting the ARCHIVED STRUCTURAL STORY rather than certifying the tree's own
level description, which `[LJ-1.2]` proved impossible.

## YOUR JOB

**1. PIN THE ORTHODOX ROUTE FROM THE LITERATURE FIRST.** Before judging
anything, state what the literature says the proof of `L ⊨ GCH` IS: its steps,
its order, its dependencies, and where each is sourced. `digest.md` pins the
orthodox form; `j-hierarchy.md` section 2 has condensation at the Sigma-1
level with its three dependencies; `digest.md:508-520` records Devlin ch. II
section II.5, "The Condensation Lemma. The GCH in L", with Theorem 5.6
(V = L implies GCH) and Corollary 5.7. **If you cannot state the orthodox
route from the corpus, say so: that is itself a finding about the corpus.**

**2. COMPARE, STEP BY STEP.** For each delivered chapter and each planned
block, does it match the literature's step, and at the literature's
generality? Look hardest at:

- **The hull.** The literature route builds a Skolem hull via Skolem
  functions. `[LJ-1.3]` built a least-witness search over the delivered
  well-order instead, on `[LJ-1.1]`'s reasoning that reflection cannot be
  iterated into a hull. **Is that the same object?** Does it have the
  elementarity the condensation step needs?
- **Condensation.** The literature puts it at Sigma-1. `[LJ-1.2]` found the
  tree's level sentence cannot be certified Delta-0 at the step clause, and
  `[LJ-1.10]` routed around it by porting the archived structural story whose
  Def-step collapses to top. **Does the literature support that move, or is it
  an artefact of this tree?**
- **The cardinality step and GCH itself.** `[LJ-1.6]` to `[LJ-1.8]` are
  planned but unbuilt. Does the plan match Devlin's II.5 chain, or has a step
  been skipped or merged?

**3. FOR EVERY DEVIATION, DEMAND BOTH REASONS.** A deviation is legitimate
here. This is a formalization in cubical Agda, not a transcription, and the
tree has machinery a textbook does not. But a deviation must be paid for
TWICE:

- **THE THRESHOLD PERSPECTIVE.** DD5's two relative constraints, both
  suspended until measured; DD24's seconds-per-line bar, currently 0.007693;
  the a-priori ceiling from `[LJ-1.1]`'s projection, which DD5 measure 1 fixes
  and which a re-price may NOT move. Does the deviation keep the wing inside
  those, and is that claim measured or asserted?
- **THE DD RULING PERSPECTIVE.** DD2 (the endpoint ruled, the architecture a
  candidate ruled at `[LJ-2.5]`), DD4 (maximize shared code, write it
  generic), DD8 (gate a block before funding it), DD13 (price a port against a
  fresh write), DD18 (survey the archive and the literature), DD23 (no prose),
  DD24. Which ruling licenses the deviation, and does it actually say what is
  claimed?

**A deviation with only one of the two reasons is a finding.** Say which is
missing.

**4. LOOK FOR WHAT THE LITERATURE WOULD HAVE CHANGED.** The counterfactual is
the point of the review: had the literature been cited in the briefs, what
would have been done differently? Name concrete instances or say there are
none. **Finding none is a real result and you should say it plainly** rather
than manufacturing a difference.

**5. CHECK THE CORPUS ITSELF.** Is it sufficient for `[LJ-1.5]` to `[LJ-1.9]`?
`[LJ-0.7]` is registered to digest Devlin II.5 because the corpus RECORDS that
section as verified but does not CARRY the derivation. Is that the only gap?
Note the recorded caution: the II.5 scan is OCR-degraded, and
Wilkie-Stanley's errata inventory covers chapters I and VI, NOT II.5
(`devlin-errata.md`).

## THE FAILURE MODE THIS CAMPAIGN HAS ALREADY PAID FOR

`dev/LESSONS.md` **D-10**: a recorded residue names a TARGET, and the target
can be FALSE. This project lost a bridge kernel to a per-level identification
that is classically false, Devlin VI.2.4. **So check the mathematics, not just
the citations.** If a delivered chapter proves something subtly weaker than
the condensation step needs, that is the most valuable thing you could find,
and it outranks every process observation in this brief.

## MANDATORY RULES FOR A REVIEW

From `python3 scripts/rules.py --for review`. Added after dispatch: the brief
went out in-harness, so `dispatch.py`'s rule-bundle refusal never ran on it,
and two of the four were missing.

- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  residue names a TARGET and the target can be false. Cited above.
- **C-22. Write the deliverable incrementally, never at the end.** Cited above.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Naming a transparent construction in a
  TYPE is what costs, not being about a concrete position. **For you: both
  delivered chapters claim the stage stays an ATOM to the elaborator. That is
  a P-l claim and it is checkable against the code.**
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** A stage built from finitely many total operations carries its own
  generation data, so a well-founded key exists with NO syntax. A stage built
  as a definable power carries NOTHING. **This is the law the whole review
  turns on.** `[LJ-1.10]` used it to argue that `[LJ-1.2]`'s NO-GO is the Def
  tower paying D-26's bill, and that the same story costs 470 to 610 lines on
  the J tower against thousands here. **Test that argument.** It is the most
  consequential claim phase 1 has produced, and it is headed for `[LJ-2.5]`.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For you it is also an object of review.** Both delivered chapters claim to
be fully generic. Check that claim against the code, and ask the harder
question: is the wing's shared core the one the literature's route would
suggest, or has genericity been applied where it does not pay and skipped
where it would?

## LITERATURE (DD18)

Your primary corpus, and the subject of the review:

- `dev/literature/digest.md`, the orthodox form pinned, and its open items at
  :487 onward. **:508-520 is the GCH derivation record.**
- `dev/literature/j-hierarchy.md`, condensation at Sigma-1, section 2.
- `dev/literature/fine-structure.md`.
- `dev/literature/devlin-errata.md`, the known errors in the primary text.
  **Read this before trusting any Devlin citation.**
- `dev/literature/primary-sources.md` and `BIBLIOGRAPHY.md`, what was fetched
  and what consumed it.
- `dev/literature/formalizations-landscape.md`, prior art, and section 9's
  GCH-in-L verdict.
- `dev/literature/rudimentary-functions.md` and `owner-notes-rud.md` for the
  J-side comparison.

Return a **LITERATURE USED** section: what you read, what you took, and WHY
NOT for anything you skipped.

## ARCHIVE (DD18)

- `archive/rud-route/src/L/Condensation.lagda.md`, 751 lines, the structural
  story `[LJ-1.10]` proposes porting. **Read it: the review turns on whether
  it is the literature's object.**
- `archive/rud-route/src/L/Hull.lagda.md` and `V/Collapse.lagda.md`, the
  comparables the two delivered chapters ported from.
- `archive/dev/TASKS-archived.md` for `[T51]`, `[T91]`, `[T130]`, `[T257]`,
  `[T263]`.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## SCOPE (read)

The five `_build/lj-1.*` reports first, then the two delivered chapters
`src/L/Hull.lagda.md` and `src/V/Collapse.lagda.md`, then the literature, then
the archive, then `dev/PLAN.md` sections 0, 3 and 11 for the rulings and rows.

## SCOPE (write)

`_build/lj-1.11-review.md` only. **Read-only on `src/`.** Two compression
agents hold the Agda slots, so run no `agda` and no `make check`.

## CONSTRAINTS

- **No edits outside your report. No commit, no push.**
- **Evidence is `file:line`.** A mathematical claim needs a source; a claim
  about this tree needs a location.
- **Separate what the LITERATURE says from what the REPORTS say from what YOU
  infer.** Three different kinds of authority, and conflating them is the
  failure mode of a review like this.
- **Rank findings.** A wrong theorem outranks a missing citation.
- **An agreeing review is a real result.** Do not manufacture deviations. If
  the route matches the literature, say so and spend your effort on the
  planned blocks instead, where the cost of an error is still ahead of us.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-1.11-review.md` incrementally, skeleton first (C-22).

1. **VERDICT.** Does phase 1 follow the literature's route? One paragraph.
2. **THE ORTHODOX ROUTE**, pinned from the corpus, with sources.
3. **STEP BY STEP**, one row per delivered chapter and planned block: matches,
   deviates, or unknown.
4. **DEVIATIONS**, each with its threshold reason and its DD reason, and a
   verdict of JUSTIFIED or NOT. Say which reason is missing when one is.
5. **WHAT THE LITERATURE WOULD HAVE CHANGED**, concretely, or none.
6. **IS THE CORPUS SUFFICIENT** for `[LJ-1.5]` to `[LJ-1.9]`, and what to
   collect if not.
7. **MATHEMATICAL DEFECTS**, if any. This section outranks the others.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
