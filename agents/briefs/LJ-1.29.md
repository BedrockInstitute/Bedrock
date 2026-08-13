# LJ-1.29: does the crossing need ONE formula readable at TWO carriers?

tier: codex (default)

## GOAL

`[LJ-1.27]`'s gate went RED, and 31.0 of its 33.3 seconds buy exactly one
thing: **one formula readable at two carriers.** Decide whether the crossing
needs that at all. **Write no Agda and hold no Agda slot.** A sibling holds it.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHERE THIS CAME FROM, and it is an honest hand-off

`[LJ-1.27-R]`, the DD25 adversarial review, upheld the NO-GO and then wrote
this in its own uncertainties (`_build/lj-1.27-review.md:264-269`):

> I did not test whether the crossing needs `σL` at all. The whole 31 seconds
> buys ONE formula readable at two carriers. `[LJ-1.26]`'s design asks for it,
> and I take that as given. **If the crossing can be restated so that each
> carrier keeps its own formula and only the MEANINGS are compared, the
> apparatus goes away and the base rate governs.** That is an architecture
> question and it belongs to the orchestrator, not to a probe.

**It is now yours to answer, and it is a genuine question with two possible
answers.** Do not assume the restatement works because it would be convenient.

## THE ARITHMETIC THAT MAKES IT WORTH A DISPATCH

| shape | rate | route A at 3.3k lines |
|---|---:|---:|
| the measured block, one formula placed at two carriers | 0.110 to 0.113 | **about 370 s** |
| the same content stated directly, measured in the same probe | 0.0053 to 0.0114 | **about 18 to 38 s** |

The GCH side's WHOLE seconds budget is 99.6 to 147.7 s (`dev/ledger.toml`).
**So the present shape does not fund and the direct shape does.** That is the
whole stake.

## THE THREE WAYS OUT THAT ARE ALREADY CLOSED

**Do not re-open these. They were closed by measurement, not by argument**
(`_build/lj-1.27-review.md:210-216`).

1. The Δ₀ placement lemma was BUILT and it **walls at 8 GB**, in two
   formulations.
2. A parameter-free clause is impossible while `consAtL` is used: the clause
   carries 17 constants and 16 come from `consAtL`.
3. The delivered one-line `σ₁-up` is already in the block and already cheap. It
   does not carry the two-carrier comparison the crossing needs.

**`[LJ-1.30]` is pricing the fourth way out, the upstream `consAtL` rewrite.
That is not yours.** Yours is whether the two-carrier comparison is needed at
all.

## THE QUESTION, stated precisely

Condensation says a collapsed hull image is a LEVEL of the real tower. The
present design proves that by building ONE object-language formula and reading
it at the model carrier and at the class carrier, then comparing the readings.

**The alternative to test: each carrier keeps its OWN formula, and only the
MEANINGS are compared.** The tower-landing facts are already delivered and
`[LJ-1.28]` showed the equivalence legs RIDE them
(`_build/lj-1.28-report.md`): `Lset-only` at `src/L/Hierarchy.lagda.md:334`
gives the value from the graph, and `Lset-defines` at `:646` gives the graph
from the value. **Both are equalities of VALUES in `S`, not of formulas.**

**So ask: can the crossing be assembled from value equalities plus each
carrier's own local certificate, with no shared formula?**

## THE FOUR QUESTIONS

1. **What does the crossing actually need to conclude?** State it as a type, or
   as close to one as prose allows. Not as a description of the current proof.
2. **Which steps genuinely need ONE formula at two carriers**, and which only
   need the two readings to AGREE ON A VALUE? Go step by step. **Name each at
   `file:line`.**
3. **If the restatement works, what replaces `σL`?** Name the delivered lemmas
   it would ride, and say what is still missing.
4. **If it does NOT work, say why, and say it plainly.** Name the step that
   forces a shared formula. **That answer is worth as much as the other one**,
   because it tells the owner the upstream rewrite is the only route.

## THE TRAP TO AVOID, and it has caught this project before

**A value equality and a formula equality are not the same thing, and the gap
is where absoluteness lives.** Two carriers may satisfy their own formulas and
still disagree, unless something transports the meaning. **If your restatement
quietly assumes absoluteness that nobody proved, it is not a route, it is a
hole.** Say explicitly what carries the meaning across, and cite it.

`dev/LESSONS.md` D-10: `[LJ-1.11]` refuted an archived structural story whose
target was classically FALSE. **A cheaper shape that proves the wrong thing
costs more than an expensive shape that proves the right one.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.26]` split condensation into one TEMPLATE frame plus TWO per-tower
certificates. `[LJ-1.27-R]` found the Def certificate is expensive because it
keys on the defining SYNTAX, while the J tower's stage carries generation data
so its certificate is structural (D-26, `dev/LESSONS.md:1676`).

**So say whether your restatement is template or per-tower.** If dropping the
shared formula makes the crossing MORE per-tower, the J tower pays again and
that cost belongs in your answer.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 2.1 to 2.8, Step C.** Devlin writes
  the level formula ONCE and asserts absoluteness. **So the book uses the
  shared-formula shape.** Say whether his argument NEEDS it or merely uses it,
  because that is the closest thing to an answer the literature holds.
- `_build/literature/dev2.txt:1369-1388` for 5.5 and 5.6 themselves.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.27-review.md` sections 4, 5 and 6.** The closed routes and the
  hand-off. **Section 5 explains what the delivered `σ₁-up` does and does not
  carry.**
- `_build/lj-1.27-report.md` sections 4 and 9, the profile and the shapes.
- **`_build/lj-1.28-report.md` sections 2 and 3**, the delivered graph theorems
  and the per-leg analysis. **This is your strongest input.**
- `_build/lj-1.26-report.md` sections 5 and 6, route A and the DD4 split.
- **`archive/rud-route/src/L/Condensation.lagda.md:823-853`**, where the
  archived route did `σL = embed levelStory` and its two transfers. **Read it
  for the shape. Its target is classically FALSE (`[LJ-1.11]`), so never take a
  price from it.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-l, P-t, P-u (new
  today), D-10 and D-26 decide this block.** P-u is the law `[LJ-1.27-R]`
  measured: a Levy witness travels along a relabelling for free and does not
  travel along a placement at all.

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10.** Every figure here is a residue. The crossing's REQUIREMENT is the
  target, and a target can be false. **Check what the crossing must conclude
  before pricing how to conclude it.**
- **C-22.** Write the deliverable incrementally.
- **P-l.** Naming a transparent construction in a statement's TYPE is what
  costs.
- **D-26.** A well-founded key on a tower needs generation data, or it needs
  syntax. **It bears: the Def certificate keys on syntax and that is why the
  shared formula appeared.**

## SCOPE (read)

`_build/lj-1.27-review.md` sections 4 to 7 FIRST. Then
`_build/lj-1.28-report.md` in full. Then `src/L/Hierarchy.lagda.md`. Then
`src/FOL/Absoluteness.lagda.md`. Then the archived crossing for shape.

## SCOPE (write)

`_build/lj-1.29-report.md` only. **No file under `src/` and no file under
`dev/`.**

## CONSTRAINTS

- **Run NO `agda` and NO `make check`.** `[LJ-1.30]` may hold an Agda slot.
- **Never commit and never push.**
- **Separate MEASURED from ESTIMATED everywhere**, and ONE best-effort number
  per obligation naming its basis (DD8).
- **Evidence is `file:line`.**
- **A finding that the shared formula is REQUIRED is a full success.** Say it
  plainly if you find it.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.29-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: can the crossing drop the shared formula, yes
   or no, and what it costs either way.
2. **WHAT THE CROSSING MUST CONCLUDE**, stated as close to a type as prose
   allows.
3. **STEP BY STEP**: which steps need one formula at two carriers, and which
   need only a value agreement.
4. **WHAT CARRIES THE MEANING ACROSS** in your restatement, cited. If nothing
   does, say so.
5. **WHAT REPLACES `σL`**, or why nothing can.
6. **TEMPLATE OR PER-TOWER?** (DD4.)
7. **LITERATURE USED.** 8. **ARCHIVE USED.** 9. **WHAT I AM NOT SURE OF.**
