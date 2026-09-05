# LJ-1.2: gate the crossing, the GCH wing's widest unmeasured term

tier: codex (default)

## GOAL

Answer one question with a thrown-away probe: **can the level story be
certified Delta-0 clause by clause at the class carrier?** Return GO or NO-GO
with a price.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS ONE, AND WHY NOW

`[LJ-1.1]` planned the internalization GCH wing and named ONE term as the
widest unmeasured cost: **the crossing**, the Levy certification of the level
story and its four transfer obligations (`TransferM`, `TransferL`, `ValueIsL`,
`AmbientOnly`). DD8 says a block is gated before it is funded, and this term
is the load-bearing step of the whole wing.

**Nobody has ever probed this site.** `[L3.32-T130]`'s status line reads "no
probe, no Agda run", and `[L3.32-T261]` was queued for the same site and never
launched. The archived condensation chapter left the crossing standing.

**The obstacle is the certification, not the count.** The delivered
`LsetGraphAt` is neither Delta-0, Sigma-1 nor Pi-1 in the delivered
certification, so NONE of the three transfer theorems applies to it. The raw
graph carries unbounded quantifiers of both kinds.

**What turns on your answer.** GO moves the crossing from the x3 survey class
to about x1.3 and funds `[LJ-1.5]` at the survey band. NO-GO re-prices it at
about 5.0 to 5.1 thousand lines and stops the plan for a re-price. The wing is
projected at 8.0 to 10.8 thousand lines in total, so this one term can move
the whole phase by half its size.

## THE PROBE, SPECIFIED BY `[LJ-1.1]`

Written to `_build/lj-1.1-recon.md` section 5. Build exactly this.

**The file.** `src/ProbeLJ12.lagda.md`, and it is NEVER committed (D-1).
`scripts/check-probes.py` refuses a staged probe, and it recognizes the
`Probe*` prefix in `.agda` and `.lagda.md` alike. Delete it when you are done,
or leave it untracked and say so.

**Imports.** `L.Coding.Sequence`, `L.Hierarchy`, `FOL.LevyHierarchy`,
`FOL.Manipulation.Relabelling`, `L.Constructible`.

**Statement 1, the certification.** Certify the level story at the CLASS
carrier. Write the bounded rewrite of each clause at the exact shape
`LsetGraphAt {2} zero (suc zero)` (`src/L/Coding/Sequence.lagda.md:361-364`).
Give each rewrite a Delta-0 witness. Then assemble the Sigma-1 witness
`levelSigma1 : Sigma1 (embed levelStory)` at the class carrier, using
`embed` and `mapDelta0` from
`src/FOL/Manipulation/Relabelling.lagda.md:117-118,209-221`.

**Statement 2, the class-carrier equivalence.** Prove that
`(v :: b :: []) AbsL.models sigmaL` is equivalent to `fst v = Lset (fst b)`
for `IsOrd b`. Ride `Lset-only` (`src/L/Hierarchy.lagda.md:333`) and
`Lset-defines` (`:678`). **No re-proved graph theorem may enter the probe**: if
you find yourself re-proving something `L.Hierarchy` already delivers, you
have left the probe's scope.

## THE VERDICT, AND ITS CRITERIA ARE FIXED IN ADVANCE (D-1)

Do not move these numbers to make an answer come out. A probe whose criterion
moves is not a probe.

**GO** requires all three:
1. every clause certifies at **25 non-blank in-fence lines or fewer**;
2. the Sigma-1 witness assembles;
3. the equivalence closes at **350 non-blank in-fence lines or fewer** in
   total.

**NO-GO** if any clause resists bounding without a NEW carrier fact. `[LJ-1.1]`
names the two shapes most likely to force this, so check them early: the
step's code and value existentials may need the code set as a level member,
and the `DefAt` leaves may need the twelve-clause table.

**A NO-GO IS A GOOD RETURN AND IS WHAT THIS TASK IS FOR.** It costs one
dispatch and saves a five-thousand-line surprise. Report it plainly, with
WHICH clause resisted and WHAT fact it wanted. Do not soften it, and do not
report a partial GO: if one clause fails, the verdict is NO-GO with that
clause named.

**Expected cost, from `[LJ-1.1]`:** the probe is 250 to 400 non-blank lines,
one Agda process, wall 2 to 15 s plus elaboration risk. If you are far outside
that, say so: the miss is itself a measurement.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For a probe this is not decoration.** Write the clause rewrites at an
ABSTRACT carrier with the stage opaque, exactly as P-l requires, and report
whether the certification is carrier-generic or needs the class carrier
specifically. **That answer is worth more than the GO itself**, because a
carrier-generic certification is reused by `[LJ-1.5]`'s substrate, by the
two-tower route later, and by both trophies. If the certification only works
at one carrier, say so plainly: that is a real finding and it re-prices the
block.

## MANDATORY RULES FOR A PROBE

From `python3 scripts/rules.py --for probe`. These bind this task.

- **D-1. The probe doctrine.** Run the cheapest decisive probe with its abort
  criterion FIXED IN ADVANCE; a red verdict costs the attempt and nothing
  else. **Probes are never committed.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Being about a concrete position is not
  what costs; naming a transparent construction in a statement's TYPE is. If
  the stage values are `opaque` upstream, quantify over them freely, because
  the stage is an ATOM to the elaborator and nothing unfolds. **This is the
  single most likely cause of a false NO-GO here**: a clause that will not
  bound may be fighting a presentation you dragged into the type, not the
  mathematics.
- **P-i. The conversion-explosion playbook.** When cubical Agda hangs or
  exhausts memory in this codebase family, the cause is one of three
  heavy-thing classes forced into normalization, and the cure is selected by
  the decision tree, NOT by trial. Read it before you start bisecting.
- **R-40. A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.** State a membership witness at a
  SHALLOW index and climb, never at a deep iterated successor. Directly
  relevant: the level story quantifies over stages.
- **C-12. Agda runs under a hard heap cap.** `GHCRTS=-M8g agda <file>`, ONE
  process. Report a heap exhaustion as a wall, never raise the cap.
- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  target can be false. **This campaign lost a bridge kernel to a hypothesis
  that was classically FALSE** (Devlin VI.2.4). If the clause you cannot bound
  is one that is not TRUE in the shape the plan assumes, that is the finding,
  and it outranks the line count.
- **C-22. Write the deliverable incrementally, never at the end.** Skeleton
  first, fill as answers land.

## ARCHIVE

Per DD18. The retired route reached this site and stopped at it.

- `archive/rud-route/src/L/Condensation.lagda.md`, 751 lines. It left the
  crossing standing. Read what it DID certify and where it stopped.
- `archive/dev/TASKS-archived.md`. Grep `[T130]`, `[T261]`, `[T257]`, `[T51]`,
  `[T263]`. `[T263]` pre-gated sixteen Fof specs for Delta-0 and returned FAIL
  at the delivered formulas with a set-level conditional PASS: **read that row
  before you start, because it is the closest thing to a prior result.**
- `archive/dev/JOURNAL-archived.md` only where a task row sends you.
- `dev/LESSONS.md` is NOT archived and still binds.

Report an **ARCHIVE USED** section, at `file:line`.

## SCOPE (read)

`src/L/Coding/Sequence.lagda.md` first, then `src/L/Hierarchy.lagda.md`,
`src/FOL/LevyHierarchy.lagda.md`, `src/FOL/Manipulation/Relabelling.lagda.md`,
`src/L/Constructible.lagda.md`. Then `_build/lj-1.1-recon.md` sections 2 and
5. Then the archive above.

## SCOPE (write)

`src/ProbeLJ12.lagda.md`, which is a PROBE and is never committed, and the
report `_build/lj-1.2-gate.md`. No master, and `src/Everything.lagda.md` is
the orchestrator's alone.

## CONSTRAINTS

- **Never commit and never push.** Leave the probe untracked.
- **One Agda process, `GHCRTS=-M8g`.** No other agent holds an Agda slot.
- **Do not edit any master.** If the probe needs a change to a delivered
  module to work, that is a FINDING and probably a NO-GO: report it, do not
  make the edit.
- **Evidence is `file:line`.**
- **A stop is a deliverable**, and here a NO-GO IS the deliverable half the
  time. Say which clause and which missing fact.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-1.2-gate.md` INCREMENTALLY, skeleton first.

1. **VERDICT: GO or NO-GO**, in the first line, against the three criteria
   above stated as pass or fail each.
2. **THE MEASUREMENT.** Lines per clause, total lines, wall seconds, exit
   code. The per-clause table is the evidence.
3. **CARRIER-GENERIC OR NOT** (DD4), with what it would cost to make it
   generic if it is not.
4. **WHAT THE CROSSING NOW PRICES AT**, and whether `[LJ-1.5]` is funded at
   the survey band or re-prices at about 5.0k.
5. **IF NO-GO**: which clause, which fact it wanted, and the next candidate
   technique with its price. A red must name what to try next.
6. **ARCHIVE USED.**
7. **THE PROBE'S FATE.** Confirm it is untracked or deleted.
