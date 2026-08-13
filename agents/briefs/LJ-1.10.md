# LJ-1.10: re-price the crossing, and say which route the wing takes

tier: codex (default)

## GOAL

`[LJ-1.2]` returned NO-GO and DD8 stopped the plan for a re-price. Deliver
that re-price: what the crossing really costs on each of the two candidate
routes, what the whole wing costs after it, and which route to take.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHERE THE PLAN STOPPED, AND WHY

`[LJ-1.1]` planned the internalization GCH wing at 8.0 to 10.8 thousand
in-fence lines, with the crossing priced at 700 to 1,720 on a survey.

`[LJ-1.2]` then probed the crossing and returned **NO-GO**
(`_build/lj-1.2-gate.md`). Three of four clauses certify. **The step clause
has no Delta-0 witness.** Two facts are missing and both are named at
`file:line` in that report, and I verified both: `CodesAt` exists
(`src/L/Choice/Faithful.lagda.md:334-335`) but is not Delta-0 because
`isCodeAnyAt` carries `hasWitnessAt`'s unbounded existential; and `satTable`
is a meta-level element (`src/L/Coding/Table.lagda.md:103-104`), not an
object-level formula.

**It is not a carrier problem.** The rewrite is parameter-free already. The
delivered satisfaction leaves carry unbounded quantifiers at EVERY carrier, so
P-l does not rescue it.

## THE TWO CANDIDATES, AND A CORRECTION YOU MUST START FROM

`[LJ-1.2]` named two next techniques. **Its pricing of the second is
incomplete, and I checked the source.** Do not repeat the error.

**Candidate A: build the bounded satisfaction substrate.** A bounded
object-level description of the code set and of the twelve-clause table at a
carrier. This is the archived crossing-rebuild content. **Measured at 5,047
lines** (`[L3.32-T257]` section 4.2).

**Candidate B: the cone abstraction fork.** `[LJ-1.2]` reports it as "1.0 to
1.7 thousand lines", three times cheaper. **The source says more than that.**
`_build/l3.31-ivprobe-report.md:488-491` reads: "Route B alternative (abstract
the cone over the carrier once, per D-16): R2p priced the re-run half at
1.0-1.7k **plus C-6-class re-typing across 21 masters**. Comparable at the low
end, with a **larger blast radius**. **Carried as a fork, not a saving**."

So the 1.0-1.7k is **the re-run half only**, and the re-typing across 21
masters is not in it. **Price the whole thing.** The source's own verdict is
that B is comparable to A at the low end, not three times cheaper. If your
measurement disagrees with that, say so with evidence: the source may be
wrong, and it was written for a route that has since been retired.

**This is D-10 exactly.** A recorded residue names a target AND a price, and
the price can be as false as the target. Re-verify both candidates against
today's tree before you sum anything.

## YOUR JOB

**1. Price both candidates on TODAY's tree.** Both figures come from the
retired route's era. Which of the 21 masters still exist? Does the substrate's
5,047 still describe work this tree needs, or has some of it been delivered
since? Give each a band with its basis named as probe, delivered comparable,
or survey (DD8).

**2. Say whether a THIRD route exists.** Both candidates assume the wing must
certify the level story through the delivered coded satisfaction. Ask whether
it must. `[LJ-1.1]` section 2 lists what the tree already gives. The
condensation argument needs the level story to transfer between a hull and its
collapse; the Levy certification is one way to get that, and the plan should
know whether it is the only way. **A cheaper third route is the highest-value
thing you could return.**

**3. Re-price the WHOLE wing** under each candidate, updating `[LJ-1.1]`'s
block table (`_build/lj-1.1-recon.md` section 6). The wing was 8.0 to 10.8k
with the crossing at 700 to 1,720. State the new total per route.

**4. ANSWER THE ARCHITECTURE QUESTION, and this is why the task matters
beyond phase 1.** `dev/LESSONS.md` D-26: a stage built as the values of
finitely many total operations carries its own generation data, so a
well-founded key exists with no syntax at all; **a stage built as a definable
power carries NOTHING.** The Def tower is the second kind. The crossing exists
BECAUSE the Def tower's stages carry nothing, so level-hood must be certified
through coded satisfaction.

**So ask directly: is `[LJ-1.2]`'s NO-GO evidence about the ARCHITECTURE
rather than about this wing?** On a J tower whose stages carry generation
data, is the level story Delta-0 cheaply or even free? If it is, the crossing
is a cost the Def tower imposes and the J tower does not, and that is evidence
`[LJ-2.5]` needs when it rules. **Do not overstate this.** You are not being
asked to re-open the architecture; you are being asked whether this
measurement bears on it, and to say plainly if it does not.

**5. Recommend.** Which candidate, or a stop. A stop is legitimate: if the
honest answer is that the internalization GCH wing costs 13k and is no longer
worth building as a measuring instrument, say so with the arithmetic. That is
a real result and the owner asked for honest numbers, not reachable ones.

## WHAT THE WING IS FOR, so your recommendation is grounded

Phase 1 exists to MEASURE what a GCH wing costs on the internalization tower,
because that measurement sets DD5's benchmark for the two-tower route. It is
an instrument, not a trophy. **A more expensive instrument is not a failure;
it is a bigger number.** But an instrument that costs more than the thing it
measures should be questioned, and that is your call to make.

Note for honesty, and it cuts against the wing being large: DD5's benchmark is
SELF-SET, so a bigger wing sets a looser bar for the two-tower route. The
project guards that with an a-priori ceiling from `[LJ-1.1]`'s projection.
**Your re-price does not raise that ceiling.** If the wing now costs more than
projected, the ceiling stays where `[LJ-1.1]` put it, and the gap is the
finding.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For you it is a scoring criterion between the candidates.** The bounded
satisfaction substrate is content BOTH trophies would use, and both towers, if
it is written generic. The cone abstraction is a re-typing of existing content.
Score each candidate on what it makes cheaper later, not only on what it costs
now, and say which one the two-tower route would still want.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  **This is the task's spine.** Both candidate prices are recorded residues
  from the retired route. The brief already caught one incomplete price; find
  the rest.
- **C-22. Write the deliverable incrementally, never at the end.** Skeleton
  first.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** `[LJ-1.2]` established the blocker is
  NOT presentation, so do not propose a P-l cure for it; the leaves' quantifier
  structure is the obstruction.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** A stage of finitely many total operations carries its generation
  data; a definable power carries nothing. **This is the law your job 4 turns
  on.**

## ARCHIVE

Per DD18.

- `_build/lj-1.2-gate.md` in full. The NO-GO, the per-clause table, the two
  missing facts. It is input, not output.
- `_build/lj-1.1-recon.md` sections 2, 4 and 6. The block plan you re-price.
- `_build/l3.32-t51-report.md` sections 3 to 5. The widest-term analysis and
  the re-priced W1' block, and it is where candidate B is named.
- `_build/l3.31-ivprobe-report.md:488-499`. Candidate B's ORIGINAL pricing,
  with the 21-master re-typing and the "not a saving" verdict.
- `_build/l3.32-t257-report.md` section 4.2 for candidate A's 5,047.
- `archive/rud-route/src/L/Condensation.lagda.md`, 751 lines: what the retired
  route certified and where it stopped.
- `archive/dev/TASKS-archived.md`: `[T51]`, `[T130]`, `[T257]`, `[T259]`,
  `[T261]`, `[T263]`. `[T263]` pre-gated sixteen Fof specs for Delta-0 and
  returned FAIL at the delivered formulas with a set-level conditional PASS.
- `dev/LESSONS.md` is NOT archived and still binds.

Report an **ARCHIVE USED** section at `file:line`.

## SCOPE (read)

The reports above first. Then `src/L/Coding/{CodeSet,Table,Graph,Model}.lagda.md`
and `src/L/Choice/Faithful.lagda.md` for the two missing facts. Then
`src/FOL/{LevyHierarchy,Absoluteness}.lagda.md`. Then the archive.

## SCOPE (write)

`_build/lj-1.10-reprice.md` only. Write no master, and no probe.

## CONSTRAINTS

- **Read-only on the tree.** No commit, no push.
- **Do not run `agda`** and do not run `make check`. This is a pricing task;
  `[LJ-1.2]` already spent the Agda slot on the measurement.
- **Evidence is `file:line`.** A price with no site is a wish.
- **Separate what you READ from what you INFER.**
- **A stop is a deliverable.**
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-1.10-reprice.md` INCREMENTALLY, skeleton first.

1. **RECOMMENDATION**, in the first line: candidate A, candidate B, a third
   route, or a stop.
2. **CANDIDATE A RE-PRICED** on today's tree, with basis.
3. **CANDIDATE B RE-PRICED IN FULL**, including the 21-master re-typing, with
   how many of those masters still exist.
4. **A THIRD ROUTE**, if one exists, priced. Say plainly if none does.
5. **THE WHOLE WING RE-PRICED** per route, against `[LJ-1.1]`'s 8.0 to 10.8k.
6. **DOES THIS BEAR ON THE ARCHITECTURE** (D-26, job 4). Evidence, and its
   limits.
7. **DD4 SCORING** of the candidates: what each makes cheaper later.
8. **ARCHIVE USED.**
9. **WHAT I AM NOT SURE OF.**
