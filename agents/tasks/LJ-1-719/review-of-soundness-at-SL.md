# Review of soundness-at-SL (LJ-1.719): NO-GO, with the bite located

**Reviewer note.** This file is the stated NO-GO of
`agents/tasks/LJ-1-719/Probe719.agda::soundness-at-SL`. It does not
close the task. The obligation type is written and green-framed in the
probe; it is deliberately not inhabited.

**Amendment, second dispatch (lint-back-to-author), 2026-08-28.** The
obligation name now stands STATED AND OPEN at
`Probe719.agda:225-231` with a hole body, and the file's line numbers
moved by 15. The cites below were verified against the first
dispatch's probe (197 lines); the same terms today: `from-V0` at
`:153`, `from-V1` at `:162`, `from-V2` at `:172`, `Gap` at `:195-199`,
the reduction at `:208-211`. Nothing in this verdict changes.

## 1. What the probe delivers

The obligation, verbatim from the brief
(`Probe719.agda:75-84`, stated as `SoundnessAtSL`):

    (a p z : AtStage.SL lam ordλ)
    → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
    → IsOrd (fst p)
    → fst a ≡ Lset (fst p)

Three results are green in the same file:

1. **Bridge 1 (carrier) retires at SL, demonstrated.** `from-V0`
   (`:139`), `from-V1` (`:148`) and `from-V2` (`:158`) take the
   hypothesis reading of `matrix₃` at raw slots to the 𝒮ʟ reading of
   `W3.three` at the packed triple. The carrier move is
   `read-at-SL` (`:119`), `[LJ-1.652]`'s `AtTrans.read`
   (`agents/tasks/LJ-1-652/Probe652.agda:162-166`) re-instantiated at
   Hierarchy's own `AbsL`, composed with `Cnt.erase-inv`. Premise 4 of
   the brief is confirmed by a term, not by analogy.
2. **The obligation reduces to one implication, demonstrated.**
   `soundness-with-graph` (`:194`) is `Gap → SoundnessAtSL` in one
   `Lset-only` line (`src/L/Hierarchy.lagda.md:334-336`). So bridge 3
   (IsOrd) retires, and every remaining difficulty sits in `Gap`
   (`:181`).
3. **`Gap` is named and open.** `Gap`
   (`:181-187`) is the implication from `matrix₃`'s reading at the
   packed triple to `⟨ packed … AL.⊨ᵐ (LsetGraphAt zero (suc zero)) ⟩`
   at the same triple.

## 2. The obstruction: `Gap` is bridge 2's leaf leg, and the placed
leaf cannot be instantiated at this generality

The chain from `Gap` to the graph at the packed triple decomposes
exactly as 667's report recorded
(`agents/tasks/LJ-1-667/lj-1.667-report.md:76-97`):

- the prenex half is mechanical (`agents/tasks/LJ-1-690/Probe690.agda:33-35`);
- the prenex-to-graph half is 690's forward, which spends the UP
  bridge (`agents/tasks/LJ-1-690/Probe690.agda:67-72`);
- `SameAsGraph` was delivered by 709 **from** the two bridges, not
  without them (`agents/tasks/LJ-1-709/Probe709.agda:47-67`);
- the UP bridge decomposes, by 162's `Graph` frame
  (`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:210-222`), into
  `approx-up` and `step-up`, whose forward halves run through the
  leaf: the bounded leaf `StepB.leafB`
  (`src/L/Condensation.lagda.md:2407-2413`) must yield the story leaf.

**The leaf leg is now PLACED.** `LeafAgree`
(`src/L/Condensation.lagda.md:7220-7354`) gives `DefBodyB` rows to the
machine clauses in both directions. This is new since 667: its report
recorded the leaf chain as unplaced
(`agents/tasks/LJ-1-667/lj-1.667-report.md:94-96`).

**But `LeafAgree` is parameterized by a `KFacts` site block, and the
block is the bite.** Its `pairK` field is pairing closure of the bound
(`src/L/Condensation.lagda.md:7425-7427`), and `DefinesAgree` consumes
it (`:7320-7324`). The tree supplies the block at ONE bound: `KValue`
(`:7363-7435`) builds it with the bound set to `Lset lam`, a stage,
via `Bound.prʟ∈λ`. The obligation quantifies `z` over all members of
`Lset lam`.

**`pairK` is FALSE at that generality.** Take `z = { ∅ , {∅} }`:
transitive (the matrix's own `transK` conjunct holds), constructible,
a member of every stage above rank 2 - and
`pr ∅ ∅ = {{∅}} ∉ z`. Transitivity of the bound does not give pairing
closure. So the placed leaf cannot be instantiated at the obligation's
generality, no delivered module discharges the leaf from the matrix
reading alone, and the frames that would carry the wiring
(`[LJ-1.52]`'s StepAgree / ApproxAgree / GraphAgree) are still absent
from `src/` (`src/L/Condensation.lagda.md:5477-5480`).

## 3. What was checked before this verdict (D-10)

The target's truth was priced before its proof. `domB` is a
both-directions clause (`src/L/Condensation.lagda.md:1749-1756`) and
`extAtB`'s reading carries the K-payload direction
(`:103-109`), so a vacuous countermodel with the approximation `h = ∅`
does NOT satisfy the bounded matrix: the covering direction of `domB`
fails it. A refutation was priced and rejected. The residue is a proof
obstruction at a named instance (`pairK` at a non-stage bound), not a
false target.

## 4. What GO would take

Any of the three, priced:

1. **The stage-bound reduction.** Restrict the witness slot to stage
   bounds (`z = Lset κ` with `κ ∈ˢ lam`, so `z ∈ˢ Lset lam` by
   cumulativity), or hand `[LJ-1.718]` the hypothesis with that
   restriction. There `KValue.facts` applies and the route closes
   through `LeafAgree.back`, the 162 frames, 690's forward and
   `Lset-only`. Estimated 250 to 400 lines of site-fact wiring, one
   dispatch.
2. **The leaf at the weak telescope.** A variant of
   `DefinesAgree.back` that threads the rows' own `∈ K` proofs instead
   of demanding `pairK` closure. That is `src/` work, one module, and
   it would also serve the absent `[LJ-1.52]` frames.
3. **The UP bridge as an explicit hypothesis** for `[LJ-1.718]`, at
   the 709 telescope. Cheapest, weakest: the consumer inherits the
   obstruction.

## 5. Measured basis for this review

All numbers are from `agents/tasks/LJ-1-719/runs/`:
`p-30.out` (the delivered shape, green, 105.82 s at
1,960,001,536 bytes), `p-final-1..3.out` (warm rechecks, 2.8 s),
`meter-obligation.out` (`1 UNRESOLVED of 1, 2.93 s, probe_red=False`),
and the heap-wall series `p-9.out` through `p-28.out` (seven runs,
200 to 300 s each, heap exhausted at the 2 GiB wide cap; each
restructuring was tested before the delivered shape went green, per
the 2026-08-23 ruling).
