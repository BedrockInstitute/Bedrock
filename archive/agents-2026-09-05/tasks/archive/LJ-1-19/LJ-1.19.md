# LJ-1.19: Cure A, restrict the limit to closure under plus omega

tier: codex (default). **THROWAWAY PROBE under D-1.**

## GOAL

Close `[LJ-1.15]`'s statement 2 by restricting the limit ordinal to those
closed under `+ω`. **Estimated under 50 lines.** GO or NO-GO with numbers,
then throw it away.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE SITUATION, corrected twice

`[LJ-1.15]` probed the crossing and returned NO-GO. `[LJ-1.15-R]`, an
adversarial review, **OVERTURNED it** and found the diagnosis wrong in both
reasons. Read `_build/lj-1.15-review.md` first.

**What actually stands:** the bound `b ∈ Lset α` fails when α is the next
limit, because the tree codes formulas as TREES over an alphabet that is the
carrier's own members, giving rank about δ+ω. **Devlin puts the same object at
δ+4** (`_build/literature/dev2.txt:676-678`) because he codes formulas as
finite sequences. So the gap is the tree's coding, not the mathematics, and it
is **removable**.

**What was wrong in the refusal, so you do not inherit it:**

- **Environments are NOT the problem.** `env g = sett (Fin n) (λ i → pr (# i) (g i))`
  at `src/L/Coding/Environment.lagda.md:83-85` is a finite function, so its
  rank is uniform in arity. The probe proved this pattern itself, as
  `graph-mem-stage`, and did not apply it.
- **The seal is NOT the block.** `graph-mem-stage` derives the member bound
  from the EXPORTED `hierL-spec` without touching `opaque`. **Do not unseal
  anything:** R-38 measures unsealing at 25.7 s per invocation
  (`dev/LESSONS.md:2295`), which is 17 to 26 percent of the wing's whole
  99.6-to-147.7-second budget.

## CURE A, WHICH IS YOUR TASK

**Restrict α to limit ordinals closed under `+ω`.** Then δ+ω sits below α for
every δ below α, and the bound lands inside `Lset α`.

**The archive already used this on the J side.** Find it, and say where.
`[LJ-1.15-R]` estimates the whole cure at **under 50 lines**.

**Two questions the report must answer, and the second is the real one:**

1. **Does the restriction close the bound?** Show it, at arity one, for the
   existential clause the earlier probe measured.
2. **Does the CONSUMER survive the restriction?** The condensation chain
   applies at limit α. **Are the α it needs closed under `+ω`?** If the
   restriction excludes an α the chain requires, Cure A is dead however cheap
   it is. **Answer this before you write the proof**, and stop if it fails.

## THE GATE

- **GO**: the bound closes under the restriction, in **50 probe lines or
  fewer**, AND the consumer's α are all closed under `+ω`.
- **NO-GO**: either fails. Report which, with the number.

**Do not stretch.** Two probes this phase were sent with gates I set below the
band they were meant to test, and both produced NO-GOs that adversarial review
overturned. **If 50 is the wrong number, say so with your measured one**; that
is a correction, not a failure.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-1.15-R]` found the ONE shared gap behind both of this phase's rank
problems: neither site has a STAGE-ARITHMETIC API**, and that kit is
DD4-shared code both towers want. **If your cure wants such a kit, say what it
would contain**, in one paragraph. Do not build it; that is a separate
commission.

Keep the cure generic in the carrier (P-l) and parameterize the MODULE (P-h).

## LITERATURE (DD18)

- `_build/literature/dev2.txt:676-678`, where Devlin's bound sits at δ+4.
- `dev/literature/devlin-II5.md` section 2.3, item 2, the witness inside the
  carrier.
- **Say whether Devlin's argument itself needs α closed under `+ω`**, or
  whether his coding makes the restriction unnecessary. That is the honest
  comparison.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.15-review.md`. Your commissioning document.**
- `_build/lj-1.15-report.md`, the overturned NO-GO, for the 155-line clause
  and the 37 lines that did close.
- **`archive/rud-route/`: the review says the J side already used this
  restriction. FIND IT and cite it at `file:line`.**
- `_build/l3.31-r2probe-report.md:153-158`, the retired route's fourth cure,
  where the bound arrived as an INDUCTION HYPOTHESIS. **That is a rival cure;
  say which is cheaper.**
- `dev/LESSONS.md` is NOT archived and still binds. **D-1, P-l, R-38 and D-10
  decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A PROBE

From `python3 scripts/rules.py --for probe`.

- **D-1.** Smallest decisive miniature, then throw it away.
- **P-l.** Keep the stage's presentation out of the types.
- **P-i.** normalisation and heap.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling may
  hold the other slot.
- **D-10.** The under-50 figure is a residue from a review that did not build
  it.
- **C-22. Write the deliverable incrementally.** Two probes this phase missed
  this.
- **R-40**: state a membership witness SHALLOW and climb.

## SCOPE (read)

`_build/lj-1.15-review.md` first. Then `src/L/Coding/Sequence.lagda.md` for
`hierL-spec` and `graph-mem-stage`. Then `src/L/Ordinal/` for what the tree
has on ordinal closure. Then the archive.

## SCOPE (write)

**Probe files only, named `src/Probe*.agda`.** Your report is
`_build/lj-1.19-report.md`. **No `.lagda.md` master may be edited.**

## CONSTRAINTS

- **Never commit and never push. Do NOT unseal anything.**
- **Do NOT edit any master.** A missing export is a FINDING, not a task.
- **Do NOT run `make check`.**
- **Report SECONDS and the RATE** against the 0.013193 bar.
- **Evidence is `file:line`.**
- **A NO-GO with numbers is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.19-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: GO or NO-GO, with the line count.
2. **DOES THE CONSUMER SURVIVE THE RESTRICTION?** answered FIRST, before the
   proof.
3. **THE LINE COUNT**, against 50.
4. **SECONDS AND RATE**, against 0.013193.
5. **WHERE THE ARCHIVE USED THIS ON THE J SIDE**, at `file:line`.
6. **THE RIVAL CURE**, the induction-hypothesis route, and which is cheaper.
7. **THE STAGE-ARITHMETIC KIT** (DD4): what it would contain.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
