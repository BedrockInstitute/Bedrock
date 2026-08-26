# [LJ-1-671] Adversarial review of return 1: the NO-GO is UPHELD

## HEAD
verdict: upheld
head_slot: mathematician_adversarial
machine: shared
attacked return: `agents/tasks/LJ-1-671/lj-1.671-report.md`, with the full argument `agents/tasks/LJ-1-671/review-of-sat-at-packed.md`
routing: branch `stop-stated` of the work brief (exit 0, obligations delta 0, a `review-of-*.md` written, no `review-of-LJ-*` file). The acceptance arm agrees: `agents/tasks/LJ-1-671/runs/accept-1.out` carries `# exit 0`, `# obligations delta 0`, `"obligations_open": 1`, `# changed files own 21 of 21`, `# error class None`, `# in-fence lines 0`.

## 0. WHAT I DID

I attacked the return, not the task. I did not re-run the obligation and I wrote no `.agda` file. I verified, in this checkout, every load-bearing `file:line` the return rests on, I checked its arithmetic against its own sources, I searched `src/` for the lemmas the return says do not exist, and I looked for cures the return missed. The four lens questions are DD25's own, at `archive/dev/DD-archived.md:35`: "The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed." The three answers below are the ones my brief orders written.

## 1. THE FOUR, AS THE LENS

**1.1 Correct on its own numbers. Yes.** The obligation `sat-at-packed : SatAtPacked delivered` is not discharged, and the return says so in the same words in both files: the report verdict line is `agents/tasks/LJ-1-671/lj-1.671-report.md:5` ("**NO-GO.** The obligation `sat-at-packed : SatAtPacked delivered` cannot be built in this probe"), and the probe holds the type only: `agents/tasks/LJ-1-671/Probe671.agda:58` reads `sat-at-packed : Type (ℓ-suc ℓ)` with `:59` `sat-at-packed = SatAtPacked delivered`. The program scored it open (`"obligations_open": 1`, accept arm), so the stop is stated, not disguised as a go. The slot arithmetic is right: the `KFacts` record has fourteen `Fin` parameters (`A K N0` through `N11`, `src/L/Condensation.lagda.md:6079`), `LeafAgree` consumes it (`src/L/Condensation.lagda.md:7224` with the `KFacts` parameter at `:7226`), the obligation's formula has arity 2, and the review's "gap is twelve" is 14 minus 2. The fourth-conjunct claim is right at the source: `src/L/Condensation.lagda.md:2408` and `src/L/Coding/Sequence.lagda.md:117` both carry the same clause, `var (suc (suc (suc zero))) ∈̇ var zero`, so the bounded zero instance repeats the unbounded step clause the sequence chapter already builds and reads (`src/L/Coding/Sequence.lagda.md:202-231`, `src/L/Hierarchy.lagda.md:334-338`). The correction of record in review section 2.3 is consistent with both files and with the sources: the verbatim conjunct is `var 3` (slot 3 in slot 0), not `var 6`.

**1.2 Is the measurement sound. Yes, with two dents that do not move it.**
- The cap run is real: `agents/tasks/LJ-1-671/runs/atk-3.out` carries `1200.04 real`, `946241536  maximum resident set size`, `EXIT=142`, the GHCRTS line and both stamps. The numbers the report quotes (1200 s cap, 946,241,536 bytes) match the file exactly.
- The green claims reproduce: `runs/probe-5.out` (3.56 s, EXIT=0), `runs/atk-6.out` (3.21 s, EXIT=0), and the acceptance arm re-ran all three `.agda` files green (2.57, 2.23, 2.24 s, rc 0 each).
- Dent one, interpretation sold as measurement: "Agda spent the whole budget reducing one clause of the wrapped matrix to report an inequality" (report, THE MEASUREMENT THAT DECIDES; review section 3, Wall 3, "one frame step"). `atk-3.out` records termination by alarm, time and memory only. What Agda was reducing when the alarm fired is not in the record. The measured fact is: the deep witness attempt did not finish inside 1200 s.
- Dent two, the measured source is gone: `runs/ATK-1.agda` was overwritten after the cap run (its final content is the green stub, `runs/atk-6.out`), and `runs/ATK-1-red.agda.txt` preserves only the shallow skeleton, not the deep witness that hit the cap. The `.out` carries the run's facts but not the measured text, so the wall cannot be re-inspected, only re-read. The brief's own naming rule offered the fix: a second `.agda.txt` for the deep version.

**1.3 Did the brief cause the outcome. Partly, and the return says so.** The brief priced W3 at 120 to 260 lines on the basis that `[LJ-1.663]` "built the membership half and reached this one". That comparable is not comparable: the membership half runs on delivered lemmas (`agents/tasks/LJ-1-663/Probe663.agda:103-125`, from `rank-fix`, `rank-Lset`, `Lset-suc`, `Lset-mono`, EnvSupply), while this half has supply 0, which the brief itself states under WHAT IS DELIVERED ALREADY. The scope line "Land nothing in `src/`" forecloses the only construction that discharges the obligation, because the missing satisfaction lemma is a new module of chapter scale. The report flags exactly this price error, which is the correct output of a stop, and the branch table anticipated the stop (branch `stop-stated`).

**1.4 Is there a cure the return missed. None inside the scope.** See section 4.

## 2. THE THREE, AS WRITTEN

**2.1 Does the verdict LINE match its own BODY? Yes.** The line (report `:5`) states NO-GO, target true, delivery gap, run cap. The body backs each element: truth at review section 2 (clause identity at `src/L/Condensation.lagda.md:2405-2416` and `src/L/Coding/Sequence.lagda.md:114-118`, both verified above), the delivery gap at section 3 (Walls 1 and 2, verified below), the cap at Wall 3 (verified above). The correction of record appears in the report and in review section 2.3 with the same content. Two precision notes, neither a mismatch: (a) the interpretive phrasing of `atk-3` named in 1.2; (b) the review's section 2.2 calls its quotes "verbatim", but the sources carry the long forms, for example `var (suc (suc zero))` where the quote writes `var 2`; the shorthand is numerically faithful, yet the word "verbatim" is wrong, and review 2.3's own retraction was caused by exactly this kind of shorthand drift (`var 3` read as `var 6`). A future reader should re-derive any slot index from the file, not from the quote.

**2.2 Is every load-bearing claim backed by a `file:line` that resolves today? Yes.** I opened each one. Resolved and confirmed:

- `agents/tasks/LJ-1-663/Probe663.agda:135-138`, the `SatAtPacked` type, byte-identical inside the probe at `agents/tasks/LJ-1-671/Probe671.agda:47-48`.
- `agents/tasks/LJ-1-663/Probe663.agda:144`, `complete-from-sat`, which is why the truncation is over the satisfaction and not over the witness (brief premise 2 holds).
- `agents/tasks/LJ-1-651/Probe651.agda:63` (sixteen zero `Fin` positions), `:80-101` (the three closure steps), `:110-111` (`twoSlot`, ordinal 0 value 1), `:141-142` (`lset-formula`), and `agents/tasks/LJ-1-663/Probe663.agda:71-72` (`delivered = P.lset-formula`).
- `src/L/BoundedSubset.lagda.md:108-114`, `levelHoodB` and its `Δ₀` certificate.
- Wall 1, the absent lemma: my own search agrees. `approxBndAt` and `stepBndAt` occur in `src/` only at `src/L/Condensation.lagda.md:2417-2497`, their definitions and `Δ₀` certificates. No `⊨` consumer exists for either. The same wall is documented at `agents/tasks/LJ-1-666/review-of-sat-at-level.md` (sections 2 and 3, read).
- Wall 2, the bridge: `src/L/Condensation.lagda.md:6079` (fourteen-slot `KFacts`) and `:7224` (`LeafAgree`, consuming it at `:7226`).
- Wall 3, the residue type: printed by the wrong-term run, `runs/atk-2.out`, whose goal shows the renamed matrix at the four-slot environment.
- The unbounded machinery the return says has no bounded adapter: `src/L/Coding/Sequence.lagda.md:202-231` (`fill`, `StepAt-out`, `StepAt-back`, `StepAt-in`, all on the unbounded `StepAt` with `PowOK`).

Record gaps found, all inside the task home, none load-bearing for the verdict: `runs/runs.md` omits three runs that exist on disk with stamps (`floor-2`, 2.71 s EXIT=0; `probe-1`, 2.64 s EXIT=42; `probe-2`, 2.39 s EXIT=42); review section 4 says `SatAtPacked` "appears in one file ... and this task's probe", which undercounts the text (it also occurs at `agents/tasks/LJ-1-671/runs/ATK-1.agda:71` and `runs/ATK-1-red.agda.txt:64`), though as an obligation-site count of one it stands; and the lost `atk-3` source named in 1.2.

**2.3 Is the enumeration complete? Complete for every route that could change the verdict.** The two routes the review names (a bounded-frame satisfaction module; a re-derivation at the arity `KFacts` wants) are the right shapes, and both are chapter scale, hence outside a probe whose scope bars `src/`. One candidate route is not named, and I chased it: the formula is Sigma-1 by grade, `agents/tasks/LJ-1-651/Probe651.agda:87-88`, and the tree delivers the upward transfer, `src/FOL/Absoluteness.lagda.md:182-184` (`σ₁-up`). It is not a cure: `σ₁-up` carries satisfaction FROM a substructure model TO the ambient one, so it needs the substructure satisfaction first, and that is the same undelivered decode, named `HierInK` by `[LJ-1.532]` and recorded at `agents/tasks/LJ-1-663/Probe663.agda:151-155`. The transfer relocates the missing lemma, it does not remove it. The enumeration should have named it and dismissed it in one line; its absence does not change the answer.

## 3. TRANSITIONS

The brief orders the run's `model`, `effort` and `heads_sha256` read from `dev/pod/transitions/2026-08.jsonl`. That tracked file ends, at this worktree's base commit, at `"seq": 4378, "task": "LJ-1.666"` (RUNNING, 2026-08-26T13:43:53Z). No line carries `"task": "LJ-1.671"`. Per the brief I say so and use the accept arm: exit 0, tier wide, obligations delta 0, obligations open 1, error class None, heap wall false, twenty-one changed files all inside the task home. The arm carries no model or effort fact for the predecessor, and I infer none.

## 4. VERDICT AND WHAT THE NEXT BRIEF CARRIES

**UPHELD.** The target is true and the term is not buildable in a probe: the needed satisfaction lemma does not exist in `src/`, the only delivered bridge is arity-blocked by fourteen against two, and the direct route does not finish inside the measured cap. An upheld NO-GO closes the task. For the next brief, three things this review adds:

1. Preserve the capped source. A run that hits the wall must leave the file it measured as `.agda.txt` in the same edit that clears the `.agda`, or the measurement loses its object.
2. W2 applies to route 1: the satisfaction module for the bounded frames is to be stated once at a generic carrier and instantiated for both proofs, not written per proof.
3. Quote discipline: cite the long form (`var (suc (suc (suc zero))) ∈̇ var zero`) or say "paraphrase". This task's own retraction is the measured price of the shorthand.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: read. `archive/dev/DD-archived.md:35` carries the four review questions my slot file cites: "The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed." Used to confirm the lens is DD25's and not section 6.6's list.
- `archive/dev/ORCHESTRATION.md`: not read; the review turns on mathematics and record evidence, not on dispatch mechanics.
- `archive/dev/PLAN-archived.md`: not used; the plan of record is the live queue and this review moves nothing in it.
- `archive/dev/measurements/README.md`: not read; no new measurement protocol was designed here, and the runs under attack carry their own caliber lines.
- `archive/dev/README.md`: not surveyed; nothing here touches archive structure or a W4 move.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read, as a cross-check on the return's slot reading. `dev/literature/level-formula-slot-roles.md:35` reads "### 2.1 The free pair is the VALUE and the ORDINAL, in every source", which corroborates the two-slot free pair (ordinal 0, value 1) the return reads off `agents/tasks/LJ-1-651/Probe651.agda:110-111`.
- `dev/literature/BIBLIOGRAPHY.md`: not read; no primary source was consulted for this review, the arbiters being the tree's own clauses and run records.
- `dev/literature/devlin-errata.md`: not read; the truth claim under attack rests on in-tree proofs (`src/L/Coding/Sequence.lagda.md:202-231`, `src/L/Hierarchy.lagda.md:334-338`), not on Devlin's text.
- `dev/literature/primary-sources.md`: not used; no new fetch and no locator was needed.
- `dev/literature/glossary-review-2026-08.md`: not read; this review coins no term.
