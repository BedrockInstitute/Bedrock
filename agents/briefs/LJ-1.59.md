# LJ-1.59: the direction question, then place the rest of the leaf chain

tier: codex (default)

## GOAL

**Answer one question before you build anything.** Then place the rest of
the leaf chain and take `levelIn` and `cover`.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`29b8ea4`**. There are no working-tree edits.

## THE QUESTION, and it is a question

`[LJ-1.58]` narrowed the placed walk to **story to machine only**, and it
proved that every PINNED consumer needs that direction only. **I checked
each one at `file:line` and it is right.**

**But one consumer does not exist yet.**

```agda
-- src/ProbeLJ152A.agda:78
Adeq : S → Type (ℓ-suc ℓ)
Adeq m =
  ∥ Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ]
    (⟨ w' ∈ˢ K' ⟩ × ⟨ (w' ∷ v' ∷ m ∷ K' ∷ []) ⊨ LH0.matrix ⟩) ∥₁
```

**`LH0.matrix` is the BOUNDED matrix.** So `Adeq m` asserts that a story-side
witness EXISTS at a real ordinal `m`. In the whole tree `Adeq` appears only
as a HYPOTHESIS, in `adeq-decode` (`src/ProbeLJ152A.agda:85-104`). **Nothing
produces it.**

Its production is `[LJ-1.57]`'s own section 8 item 3, and that report calls
it **"the graph CONSTRUCTION direction through `Lset-defines`"**. That reads
like the direction `[LJ-1.58]` dropped.

**So: does producing `Adeq m` need the machine to story direction?**

- **If YES**, place `out` as well and re-measure. `[LJ-1.58]` says the port
  is the same shape at the same rate class; **measure it, do not assume it**
  (P-l: a measured cure does not transfer by analogy).
- **If NO**, say exactly what produces `Adeq m` instead, at `file:line`, and
  build it.

**Answer this FIRST and put the answer at the top of your report.** Do not
place the rest of the chain before you know, because the answer changes what
the shape transfers must carry.

**I am asking, not instructing.** `dev/LESSONS.md` C-33 and C-37 exist
because my briefs foreclosed answers, and `[LJ-1.55]` and `[LJ-1.56]` both
returned better answers than the question I asked.

## SOMETHING YOU MUST NOT DELETE

**`src/ProbeLJ157A.agda` holds the ONLY proof of the machine to story
direction.** It is untracked and a probe is never committed. **Do not delete
it, do not overwrite it, and do not let a cleanup take it** until the
question above is settled. If you need its content, copy it forward.

## THEN THE REST OF THE CHAIN

`[LJ-1.58]` placed the walk (387 lines, `Condensation:5083-5509`). **Still in
probes, story to machine only, same spelling:**

- `ClosedAgree.back`, `DomainAgree.back` (`ProbeLJ156A` sections 3 to 5)
- the `TwelveAgree` composition (`ProbeLJ155B`)
- `KeyAgree.back`, `DefinesAgree.back` (`ProbeLJ154A`)
- `SatGraphAgree.back` (`ProbeLJ156A` section 7)
- `ShapedAgree.back`, `WitnessAgree.back`, `LeafAgree.back` (`ProbeLJ157A`
  sections 4 to 5)

**`[LJ-1.58]` flagged that these need the shape transfers' `in'` directions
too**, because the closedness frame agreement consumes them, so the master's
`UnShapeClosed` and `BinShapeClosed` grow when they land. **That is a second
reason the direction question comes first.**

## THEN THE ACTUAL GOAL

`levelIn` and `cover` (`src/L/BoundedSubset.lagda.md:598-599`) have now
survived seven dispatches. The post-leaf chain is `[LJ-1.57]` section 8's
five named terms. **Take as much of it as your budget reaches, and say in
the ledger exactly where you stopped.**

## THE THRESHOLD, and it is tight now

DD24's live bar is **0.012716**. **Do not use 0.013193.**

`[LJ-1.58]` measured `L.Condensation` at **60.41 s over 5,027 lines, rate
0.01202**, under the bar with the walk placed. **The margin is 0.0007 s per
line.** At the measured marginal rate of 0.01765, roughly **1,300 more lines
would reach the bar.**

**So measure as you go, and if a placement takes the file over, STOP and
report it rather than placing more.** A measured stop with a price is a full
deliverable.

Report the marginal rate, the whole-file rate and the cone separately, each
from three cold runs in ONE caliber with the spread. **Re-measure the
baseline yourself; `[LJ-1.58]` did and got 53.58 s where `[LJ-1.56]` got
54.77 s.**

## THE SPELLING THAT WON, and it is yours to reuse

`[LJ-1.58]` measured 4.28x from two levers:

1. **P-t. State the assembly as a generic lift kit at abstract
   propositions**, not as eleven hand-written partial trees. The elaborator
   then normalizes each full formula tree once per statement instead of once
   per helper.
2. **D-30. Carry only the direction the consumer needs**, subject to the
   question above.

**Sealing (P-c, R-36, R-38) was NOT applied and the reason is recorded as
INFERRED, not measured**: the walk's own proofs must reduce `shapesBS`'s body
to match the disjunction, so a seal was argued to move the cost rather than
remove it. **If you hit a wall, that inference is the first thing to test.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-v.** Give a proof a NAME and pass the name. 150,133 ms against 220 ms.
- **P-l.** A measured cure does not transfer by analogy. **Re-measure at the
  new site.**
- **P-m.** Instantiation is the expensive class. Say which class each block
  you place is in.
- **P-u. CERTIFY BEFORE YOU PLACE.**
- **C-34. Build the cure or report the wall.**
- **C-35. A block with no consumer is UNTESTED.** Five definitions have been
  convicted this way already.
- **C-36.** A failed substitution is not a proof of impossibility. **Write
  the term you could not write.** You may strengthen; you may not weaken.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap.** If you narrow, name
  what was dropped AND what still consumes the narrowed form, at `file:line`.
- **Do not touch anything under `src/L/Coding/`.** If the machine looks
  wrong, STOP and report it.
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`. **If you
  need one, STOP and report it.**

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- The twelve row agreements, the shapedness walk, `WitnessAgree` and
  `LeafAgree` are PROVED. **This is a placement question, not a re-proof.**
  If you find yourself re-proving one, stop and say which.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

`src/L/Condensation.lagda.md` carries a superseded **Row layer**
(`RowTransfer`, `RowDecode`, eleven `*Row` modules, five `*Decode` kits),
about 613 lines. **The prepared compression patch is NOT your task, and I
measured that it would RAISE the ratio, not lower it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** This has produced something on each of the last three dispatches.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.58]` kept the template shape: no placed type mentions a concrete
carrier. **Keep that and say so.** If the direction answer forces a
tower-specific spelling, name the trade.

## ARCHIVE (DD18)

- **`_build/lj-1.58-report.md`**, read WHOLE, and `src/ProbeLJ158A.agda`.
  Its sections 2 and 5 are the spelling and the direction argument.
- **`_build/lj-1.57-report.md`** section 8, the five post-leaf terms, and
  **`src/ProbeLJ157A.agda`**, which is your source and must not be deleted.
- `src/ProbeLJ152A.agda` and `src/ProbeLJ152B.agda`, read WHOLE. **These hold
  `Adeq` and every pinned consumer, so they decide the direction question.**
- `_build/lj-1.56-report.md`, `src/ProbeLJ156A.agda`, `ProbeLJ155B.agda`,
  `ProbeLJ154A.agda`, the remaining probe content to port.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md` for what
  `levelIn` and `cover` each still need, written as terms.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md:216-231` is what `[LJ-1.58]` read for the
direction argument, so **read it yourself and say whether it supports the
conclusion drawn from it.** `_build/literature/dev2.txt:1372-1385` for 5.5.
The errata do NOT cover Chapter II section 5; `[LJ-1.14]` verified it.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`src/ProbeLJ152A.agda` FIRST, then `_build/lj-1.58-report.md` sections 2 and
5, then `_build/lj-1.57-report.md` section 8, then `src/ProbeLJ157A.agda`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ159*.agda`. Your report is `_build/lj-1.59-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.59-report.md` incrementally, skeleton first.

**Lead with the direction answer**, and whether you placed `out`. Then what
else you placed, with the whole-file rate after each. Then whether `levelIn`
and `cover` are discharged, and for anything unbuilt **the term you could not
write**. **Mark every negative MEASURED or INFERRED.** Then the rates with
spreads in one caliber, the DD4 answer, and **the convergence answer.**
