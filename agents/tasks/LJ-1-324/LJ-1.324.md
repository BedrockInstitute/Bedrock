# LJ-1.324: transplant `stage-card-upper` to `CanonInj`'s pair

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE LEAD, and it comes from the agent that refused to price it

**`[LJ-1.321]` named this and then refused to price it, correctly, under P-l:**

> **The lead I would fund first was not in the brief:** `stage-card-upper`
> (`src/L/StageCardinal.lagda.md:564-566`) is a delivered canonical witness-free
> injection `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, built by `∈-induction` with a limit step, **the
> exact shape `CanonInj` wants at a different pair.** P-l forbids me pricing it
> by analogy; I did not attempt the transplant.

**That refusal is why this task exists. A judgement at one site is a hypothesis
at another, and the only way to settle it is to try it at the other site.**

## WHERE THE PROJECT STANDS, so you know what you are unblocking

`[LJ-1.8]`'s blocker is `sq : SqShape`. Last night the chain ran:

1. `[LJ-1.305]` proposed admitting a NEW PRINCIPLE into a trophy.
2. `[LJ-1.316]` measured that the claim used the wrong eliminator: the library's
   `rec→Set` needs only a `2-Constant` map into a SET, and the target IS a set.
3. `[LJ-1.319]` REFUSED the principle and funded the door.
4. **`[LJ-1.321]` found the door narrower AND the debt smaller than anyone
   thought.** A map that factors through ANY proposition is `2-Constant`
   (`agents/tasks/LJ-1-321/Door.agda:126-129`), so the question is split support
   for `sq α`. **And a WELL-ORDER on `sq α` gives the map outright**, with no
   `Wat`, no least member and no per-member injection (`Door.agda:394-412`).
   `pullOrder` at `src/L/Choice/Step.lagda.md:252-258` reduces that well-order
   to **an injection into any well-ordered carrier** (`Door.agda:415-418`).

**So the whole remaining debt is ONE canonical injection, and this task tests
the most promising delivered source for it.**

## THE WALL THIS AIMS AT, MEASURED

`[LJ-1.321]` ran a COMPLETE census, `grep -rn "↪ ⟪" src/ | grep -v "⟫↪"`, 38
lines, all classified. **Exactly ONE delivered untruncated term has the shape
`⟪ β ⟫ ↪ ⟪ member of β ⟫`, and it is `absorbs` at
`src/L/Absorption.lagda.md:613-615`, whose type names `sucV`.** **So the LIMIT
non-initial case has no supplier.** MEASURED.

**`stage-card-upper` is the candidate because it is built by `∈-induction` with
a LIMIT STEP**, which is exactly the case that has no supplier:

```agda
  stage-card-upper : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
                   → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
  stage-card-upper = ∈-induction step
```

`src/L/StageCardinal.lagda.md:564-566`. **Read the whole induction, `step`,
`limit-step` and `branch`, not just the signature.**

## THE QUESTION

**Does `stage-card-upper`'s construction transplant to the pair `CanonInj`
wants, and what does it cost?**

**Read `CanonInj` in `agents/tasks/LJ-1-321/Door.agda` FIRST and state the
target pair exactly**, in your own words, at `file:line`. **My brief does not
restate it, deliberately: `[LJ-1.321]` is the authority and I will not put a
paraphrase between you and it** (C-47: a brief that welds a true claim to a
false one loses the true half).

## THE THREE THINGS TO MEASURE

**1. DOES THE SHAPE TRANSFER?** `stage-card-upper` injects `⟪ Lset α ⟫` into
`⟪ α ⟫`. **Name precisely what differs at `CanonInj`'s pair**: the carriers, the
hypotheses, and the induction's motive. **A difference in the motive is the one
that usually kills a transplant.**

**2. DOES THE LIMIT STEP TRANSFER?** **That is the case with no supplier, so it
is the case that decides.** **If the limit step needs something
`stage-card-upper` gets for free at its own pair, name it at `file:line` and
price it.**

**3. WHAT DOES IT COST?** Lines, and seconds if you can measure them on a quiet
enough machine. **State the basis** (DD8): a build, a delivered comparable, or a
survey.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT TRANSPLANTS AND YOU BUILD IT.** **The best outcome, and it may finish
  `[LJ-1.8]`'s last debt.** Report the term, its lines and its seconds. STOP.
- **IT TRANSPLANTS WITH A GAP.** Name the gap at `file:line` and price it.
- **IT DOES NOT TRANSPLANT.** **Say which of the three differences kills it**
  and write the term you could not write (C-36). **A refuted transplant is a
  real answer and it removes the project's most promising lead honestly,
  instead of leaving it as a hope.**
- **THE PAIR IS WRONG.** If reading `Door.agda` shows `CanonInj` is not what the
  crossing needs, **say so; that would be a refutation of `[LJ-1.321]`'s own
  framing and it is worth more than this transplant.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-324/`. **`src/` is forbidden** (I-5) and
  `check-probes.py` enforces it.
- **Do not edit another task directory.** **You may READ and RE-RUN
  `agents/tasks/LJ-1-321/Door.agda`; you may not change it.**
- **`src/L/GCH.lagda.md` and `src/L/Model.lagda.md` are UNDER A LIVE RULING**
  (`[LJ-1.323]`, on how both trophies should be STATED). **Do not touch either,
  and do not assume today's statement is final.** **If your result depends on
  the statement, say which part.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling (`[LJ-1.323]`) may take a slot to typecheck candidate trophy
  statements. Take ONE.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  machine load beside every absolute figure.
- **C-51:** a `with`-pattern on a record-returning function exhausted the cap six
  times and an `opaque` seal did NOT cure it; projections did.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-324/lj-1.324-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**P-l. A judgement at one site is a hypothesis at another, and an expected
figure anchored on a comparable elsewhere is a hypothesis rather than a price.**
**`[LJ-1.321]` obeyed it by refusing to price this. You settle it by building
it.**

**C-36. A failed substitution is not a proof of impossibility.** **If it will
not transplant, write the term you could not write.**

**C-42. A refutation measures the site it names.** **`[LJ-1.321]`'s census is
COMPLETE over `src/` for one shape. It says nothing about what a NEW term could
supply.**

**C-44.** Every claim in this brief is `[LJ-1.321]`'s or mine. Re-derive each.

**C-45. `exit 0` is not a supply.**

**A STOP IS A DELIVERABLE.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**`[LJ-1.321]` reported an UNEXPECTED DD4 GAIN and you should protect it:**
`pullOrder` lives in `src/L/Choice/Step.lagda.md`, **the AC trophy's own
machinery**, so this cure re-uses SHARED code instead of adding a GCH-only
import. **Say whether your transplant keeps that property or breaks it.**
**Write it generic in the carrier if you can**, because `[LJ-1.321]` measured
its whole positive machinery to be tower-blind and that is worth keeping.

**Note `dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose
proof is not wired, so it UNDERSTATES.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, read WHOLE**, and
  `Door.agda` with it. **It is the authority on the target and on what is
  already refuted.** **Its section 8 writes four maps it could not write, none
  refuted: read them so you do not re-refute one.**
- **`agents/tasks/LJ-1-314/lj-1.314-report.md`**, the coded route and
  `leastOf`'s side condition.
- **`agents/tasks/LJ-1-305/lj-1.305-report.md`**, the descent and its
  `NotProp` countermodel.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`, landed 2026-08-15.** **Its
section on why the classical move works says the ordering reaches the
injections because an injection in `L` is a SET, while ours is an ambient
function.** **Say in one line whether your transplant changes which side of that
line the object sits on**, because that is the whole diagnosis. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-321/Door.agda` FIRST, then
`src/L/StageCardinal.lagda.md:500-566`, the induction WHOLE.

## SCOPE (write)

`agents/tasks/LJ-1-324/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **P-l, C-36, C-42, C-44, C-45.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-54, C-49, C-50, R-40, R-41, P-i, P-k, P-m, P-y.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-10, D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: TRANSPLANTS, GAPPED or REFUTED.** Then `CanonInj`'s target
pair as you read it, at `file:line`. Then the three differences, each measured.
Then the limit step specifically, because it is the case with no supplier. Then
the term or the term you could not write. Then the cost with its basis. Then
whether the `pullOrder` DD4 gain survives. **Mark every negative MEASURED or
INFERRED.**
