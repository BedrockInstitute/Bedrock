# LJ-1.32: does the placement wall scale with the constant count?

tier: codex (default)

## GOAL

`[LJ-1.27-R]` measured a placement WALL at 8 GB with **17 constants**.
`[LJ-1.31]` delivered a coding-layer cure and the real clauses now carry only
**1 to 5**. **Nobody knows whether the wall scales.** Measure it. **This is a
PROBE. Throw the code away.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS IS THE CHEAPEST DECISIVE QUESTION LEFT

The condensation crossing needs `Δ₀ (embed (absFo φ))`, the certificate of a
PLACED formula. `[LJ-1.27-R]` built it at the 17-constant clause and it
**exhausted 8 GB in 55 s**, in two formulations, including one with every
placement written out by hand.

`[LJ-1.31]` then made `consAtL` constant-free, removing 16 constants. The
delivered clause counts, machine-verified in `src/ProbeLJ131.agda` which I ran
myself:

| form | constants |
|---|---:|
| `consAtL` | **0** |
| `existClauseAt`, `forallClauseAt` | **1** |
| `allInClauseAt`, `exInClauseAt` | **5** |

**Two futures follow and they are worth very different amounts:**

1. **The wall scales with the count.** Then 1 to 5 constants may place
   cheaply, the crossing needs NO further coding-layer work, and route A funds
   today.
2. **The wall is there at any positive count.** Then the arity tag and the
   term-value tags must ALSO move to slots. That changes `binClause-out`'s
   statement and every proof using it, and nobody has priced it.

**One probe separates them. Do not assume either.**

## THE MEASUREMENT

Build `Δ₀ (embed (absFo φ))` for φ at a **rising constant count** and record
where it walls, if it walls. Suggested ladder: **0, 1, 2, 5, then upward.**
Stop when you wall or when you pass the real clause's worst case with room.

**Use the DELIVERED clause forms** from `src/L/Coding/Model.lagda.md`, so the
answer is about the real site and not about a synthetic formula.
`src/ProbeLJ131.agda` names the exact forms and their counts. `existClauseAt`
at 1 and `exInClauseAt` at 5 are the two that matter most.

**Report the shape of the curve, not only the endpoints.** If it walls between
2 and 5, the project needs to know that boundary, because the difference is
whether `exInClauseAt` must be re-shaped.

## RULES OF EVIDENCE FOR A WALL

- **`GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. NEVER raise the cap.**
  Report a heap exhaustion as a WALL, with the seconds it took to reach it.
  `[LJ-1.27-R]` did exactly this and its report is the model.
- **A wall is not a price.** Do not extrapolate a finishing time from it.
- **Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the source.**
  Deleting a `.agdai` next to a `.agda` removes NOTHING and turns a cold
  measurement into a warm read. **I made exactly that mistake today** and
  caught it only because a 1-second reading sat beside a 32-second record.
- **Measure the control in the same session**, so a machine effect cannot be
  mistaken for a content effect.

## WHAT YOU MAY NOT ASSUME

- **`[LJ-1.31]`'s delivery is uncommitted and in the working tree.** Its two
  masters are `src/L/Coding/Environment.lagda.md` and
  `src/L/Coding/Model.lagda.md`. **Build against the tree as it stands.**
- **Do not re-litigate `[LJ-1.29]`.** The crossing cannot drop the shared
  formula. That was settled with evidence.
- **Do not re-litigate the `# 0` finding.** `# zero = ∅` definitionally, and I
  verified it in the ACTIVE cubical library myself.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.27-R]` found the J tower's certificate is structural and avoids the
syntax entirely (D-26). **So this wall is a Def-tower cost.** If it scales with
the count, the law you measure is template knowledge that the J tower inherits
for free. **Say what the law is, in one sentence, if you find one.**

## LITERATURE (DD18)

**None bears.** This is an elaborator cost measurement on this tree's own
formulas. **Say so in one line naming `dev/literature/` and spend nothing.**

## ARCHIVE (DD18)

- **`_build/lj-1.27-review.md` section 4**, the wall and its two formulations.
  **`src/ProbeDD25D.agda` is the walling probe. Start from it.**
- **`src/ProbeLJ131.agda`**, the machine-verified counts. I ran it: exit 0.
- `_build/lj-1.31-report.md` section 6, which forms count what and why.
- `_build/lj-1.30-report.md`, the `# 0` mechanism.
- `dev/LESSONS.md` is NOT archived and still binds. **P-u, admitted today, is
  the law under test:** a Levy witness travels along a relabelling for free and
  does not travel along a placement at all. **If the wall scales, P-u needs a
  quantitative clause and you should propose one with its measurement.**
  Also **P-m, P-t, D-1 and D-10.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.**

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price, thrown
  away.
- **D-10.** Every figure here is a residue hours old. Re-verify the counts
  before you build the ladder.
- **P-l.** A measured cure does not transfer by analogy.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-t.** The class follows the FORMULA, not the carrier.
- **C-12.** One process, `-M8g`, never raised.
- **C-22.** Write the deliverable incrementally.

## SCOPE (read)

`src/ProbeDD25D.agda` and `src/ProbeLJ131.agda` FIRST, then
`_build/lj-1.27-review.md` section 4, then `src/L/Coding/Model.lagda.md` for
the delivered clause forms.

## SCOPE (write)

`src/ProbeLJ132*.agda` only, and your report `_build/lj-1.32-report.md`.
**No master. No file under `dev/`. Never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.** `scripts/check-probes.py` refuses a
  committed probe.
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** `dev/` and two `src/L/Coding/` masters have uncommitted work.
- **Do NOT run `make check`.**
- **The machine is quiet and both Agda slots are yours.** Say if that changes.
- **Evidence is `file:line`.**
- **Either answer is a full success.** A wall at every positive count tells the
  project to fund the re-shaping; a scaling wall tells it route A funds today.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.32-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: does the wall scale, and does route A fund
   without further coding-layer work?
2. **THE LADDER**: constants against seconds or wall, as a table.
3. **WHERE THE BOUNDARY IS**, if there is one.
4. **THE REAL CLAUSES**: what `existClauseAt` at 1 and `exInClauseAt` at 5
   actually measure.
5. **THE LAW**, if you found one, with its measurement (P-u's quantitative
   clause).
6. **ARCHIVE USED.** 7. **WHAT I AM NOT SURE OF.**
