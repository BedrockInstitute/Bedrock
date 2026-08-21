# LJ-1.492 adversarial review of return #1: the NO-GO at CoverWitnessesInHull

## HEAD
head_slot: mathematician_adversarial
verdict: upheld
machine: shared
attacked: agents/tasks/LJ-1-492/lj-1.492-report.md, with
agents/tasks/LJ-1-492/review-of-CoverWitnessesInHull.md,
agents/tasks/LJ-1-492/Probe492.agda and agents/tasks/LJ-1-492/runs/

The critic is not the author of the return. I re-measured at the
site: I re-ran the probe under the pane caliber `GHCRTS=-A64m -I0
-M8g` (one Agda process), I recomputed the medians from
`runs/*.time`, and I resolved every load-bearing `file:line` against
the tree as it stands today.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY

Yes. The verdict line is at `agents/tasks/LJ-1-492/lj-1.492-report.md:133`
to `:139`. I checked each clause against the body and against the
artifacts, and the body against the sources.

1. **"W3 is GO: the formula at arity one typechecks."** `coverFo` is
   inhabited at `agents/tasks/LJ-1-492/Probe492.agda:124-125`. My own
   re-run of the full file: exit 0, 1.97 s wall with the interface
   warm. The return's own numbers recompute exactly from
   `agents/tasks/LJ-1-492/runs/`: W3 forced rechecks 2.35 / 2.13 /
   2.14 s, median **2.14 s**, peak RSS median **472317952 bytes**
   (`w3-{1,2,3}.time`); full forced rechecks 2.81 / 2.71 / 2.98 s,
   median **2.81 s**, peak RSS median **483704832 bytes**, maximum
   across the kept full rechecks **508936192 bytes**, which is the
   figure the report's section 4 names
   (`full-recheck-{1,2,3}.time`). Every kept `.out` prints
   `Checking LJ-1-492.Probe492`.
2. **"`closed` is applied at that formula."** `closed-at-cover` at
   `Probe492.agda:191-195` is `closed (coverFo yc)`, and `closed`'s
   type at `src/L/Hull.lagda.md:119-122` is what the report says: an
   ambient stage witness goes in, a hull witness comes out.
3. **"The conversion ... is unbuilt."** `StageSatOfCover` at
   `Probe492.agda:205-209` is a declared `Type` with no term. No
   postulate exists in the file.
4. **"The obligation term is not written."** `CoverWitnessesInHull`
   at `Probe492.agda:216-219` is a `Type`. The witness meter reads
   `1 UNRESOLVED of 1, 2.74 s, probe_red=False`
   (`agents/tasks/LJ-1-492/runs/witness.out:1-2`). The meter's
   `NotInScope` is the same reading as `[LJ-1.487]`'s meter took: the
   obligation name sits inside the parameterized `HullStage`, so the
   meter cannot even see the type. The return says this in plain
   words and does not overstate the meter.
5. **"An obstruction of the conversion, not a refutation."** No term
   of any negation exists in the probe. The body's restatement of
   `[LJ-1-484]`'s steps is accurate: steps 5 and 6 were inhabited and
   step 7 was left as a type
   (`agents/tasks/LJ-1-484/lj-1.484-report.md:238-240`).

**The verdict's mathematical core holds at source, and it is stronger
than the return states.** The return says the graph is not Δ₀ and Δ₀
transfer does not move it. Check the shape: `GraphAt w b = ∃̇
(ApproxAt zero (suc b) ∧̇ Step ...)` at
`src/L/Coding/Sequence.lagda.md:291-292`, and `ApproxAt` carries two
UNBOUNDED `∀̇` (`src/L/Coding/Sequence.lagda.md:279-283`). So the
graph is not Σ₁ either. The delivered transfers run the wrong way or
cover the wrong class: `σ₁-up` goes inner to outer for Σ₁ only and
`π₁-down` goes outer to inner for Π₁ only
(`src/FOL/Absoluteness.lagda.md:182-184` and `:187-189`). No
delivered transfer moves the graph from the outer world into the
stage world. The adequacy of the graph lives at `𝒮ʟ`: `Lset-only` at
`src/L/Hierarchy.lagda.md:334-336` and `Lset-defines` at
`:646-648`, with `⊨` opened as the L-class inner world at
`src/L/Hierarchy.lagda.md:79`. The `⊨c` of `closed` lives at
`AbsL.𝒮M` (`src/L/Hull.lagda.md:323`, `:153`). Those semantics do
not meet, exactly as the verdict line says.

**One item is unverifiable in part, and nothing rests on it.** The
W3-only file was not kept; its transcripts carry one line each, and
the `.time` files differ from the full runs in the expected
direction. The full file, which contains all of W3's content, is
green under my own run, so W3's status does not depend on the unkept
file.

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY

I resolved every load-bearing citation in the return. All resolve.

- `src/` sites: `closed` `src/L/Hull.lagda.md:119-122`; `Code` at
  `:72-74`; `AbsL`/`SL` at `:153` and `:155-156`; `TermAlgebra` at
  `:323`; `hull-member` at `:336-339`; the hull telescope at
  `src/L/BoundedSubset.lagda.md:903-914`; `cover` at `:918`;
  `isOrdAt` at `:795-798`; `LsetGraphAt` and its type at
  `src/L/Coding/Sequence.lagda.md:349` and `:291`; `Lset-only` and
  `Lset-defines` at `src/L/Hierarchy.lagda.md:334-336` and
  `:646-648`; Δ₀ transfer at `src/FOL/Absoluteness.lagda.md:122-124`;
  `mapFo` at `src/FOL/Manipulation/Relabelling.lagda.md:54-56`;
  `Lset-mono` at `src/L/Constructible.lagda.md:355`;
  `ord∈Lset-suc` at `src/L/Ordinal/Stages.lagda.md:434`.
- Probe sites in `Probe492.agda`: `:48-51`, `:57-61`, `:67-78`,
  `:81-91`, `:97-100`, `:118-122`, `:124-125`, `:132-133`,
  `:137-151`, `:157-158`, `:162-179`, `:181-186`, `:191-195`,
  `:205-209`, `:216-219`. Each named object starts at the named
  line. Non-blank non-comment lines measure **128**, as the report
  states.
- Predecessors: `ambient-level`
  `agents/tasks/LJ-1-484/Probe484.agda:88-90`; `code-of` at
  `:68-69`; the obligation type at `:123-126`; `[LJ-1.487]` opened
  `wit` and not `closed` at
  `agents/tasks/LJ-1-487/Probe487.agda:73`; `φord` at `:79-80` with
  the generic spelling at `:52-55`; `wit 0 φord []` at `:97`; its
  verdict at `agents/tasks/LJ-1-487/lj-1.487-report.md:170` with the
  quoted text at `:172-175`; `[LJ-1.462]` at
  `agents/tasks/LJ-1-462/lj-1.462-report.md:77`; `OrdFromHull` and
  `ClosedLset` at `agents/tasks/LJ-1-481/Probe481.agda:105-106` and
  `:111-113`; `PiCommuteD` at
  `agents/tasks/LJ-1-489/Probe489.agda:139-141`; `[LJ-1.474]` GO at
  `agents/tasks/LJ-1-474/lj-1.474-report.md:70`; `[LJ-1.458]` GO at
  `agents/tasks/LJ-1-458/lj-1.458-report.md:71`; the non-transitive
  hull at `agents/tasks/LJ-1-160/lj-1.160-report.md:248`; the
  numeral census behind the decoder at
  `agents/tasks/LJ-1-466/lj-1.466-report.md:63`.
- Literature and direction: `dev/literature/devlin-II5.md:95`,
  `:107`, `:108`, each quote exact at its line;
  `dev/pod/direction.md:37`.

Two notes, neither material to the verdict:

1. `agents/tasks/LJ-1-484/lj-1.484-report.md:114` is the
   `## VERDICT` heading. The NO-GO sentence itself sits at `:115`.
   The citation resolves; the sentence is one line below the named
   line.
2. The dispatch's own reading list does not fully resolve.
   `dev/pod/transitions/2026-08.jsonl` has no row for `LJ-1.492`.
   Its last row is seq 158, task `LJ-1.399`, at
   `2026-08-19T13:31:57Z`, and the highest task named in the file is
   `LJ-1.400` at seq 145. So the six facts, `model`, `effort` and
   `heads_sha256` of this instance are not in the transitions log of
   this tree. The instance's facts are visible instead in
   `agents/tasks/LJ-1-492/runs/accept-1.out`: exit 0,
   `obligations_delta 0`, `obligations_open 1`, `heap_wall false`,
   2.73 s, 20 changed files. This is a defect of the brief's reading
   list, not of the return, and it removed no evidence from my
   attack: every fact the meter recorded is in that accept
   transcript.

## QUESTION 3: IS THE ENUMERATION COMPLETE

No. Two omissions, and neither overturns the verdict. Both enlarge
the next brief. The brief itself did not cause the outcome: it
ordered W3 first, `closed` and not `wit`, no postulate, no
elementarity hypothesis, and the return stopped at the cheapest
point, exactly as D-10 demands.

**Omission 1: the read-back side is not enumerated.** Section 4 of
the report (`lj-1.492-report.md:334-360`) funds only the
hypothesis-side conversion, `StageSatOfCover`. But `closed` returns
stage satisfaction of `coverFo` at a hull witness `a`
(`src/L/Hull.lagda.md:119-122`), and the obligation's third
conjunct, `⟨ y ∈ˢ Lset (fst a) ⟩`, must then be read OUT of the
`∃̇`-conjunct of `coverFo` at `⊨c` or at `𝒮M`. That is a
`Lset-only`-analogue at the stage world. The delivered `Lset-only`
is at `𝒮ʟ` (`src/L/Hierarchy.lagda.md:334-336`), not at the stage.
The `IsOrd` conjunct does read back, because the probe built
`isOrdFo-out` at `⊨c` (`Probe492.agda:162-179`). The level conjunct
does not. A next brief funded with `StageSatOfCover` alone still
cannot close the obligation. What must be funded is adequacy of
`LsetGraphAt` at the stage world `AbsL.𝒮M` in BOTH directions: the
defines direction, which is `StageSatOfCover`, and the only
direction, which the return leaves unnamed.

**Omission 2: the delivered spelling `hull-closed` is not
enumerated.** `src/L/Hull.lagda.md:421-431` restates `closed`'s
hypothesis at `AbsL.⊨ᵐ` under `mapFo val`, and its proof runs the
`⊨c`-to-`𝒮M` conversion with `⊨-map` (`src/L/Hull.lagda.md:424`,
`:427-428`). With `hull-closed`, the missing object is stated
without the Code-decoder detour: stage-world adequacy of the graph
at `𝒮M`. This is not a cure. The Π₁-shaped matrix of `ApproxAt`
blocks it as hard as it blocks `StageSatOfCover`. But it is the
cheapest spelling of the next task, and the next brief should name
it.

**Prior art the return did not name.** `src/L/Choice/Order.lagda.md`
consumes `LsetGraphAt` inside its own satisfaction world and proves
its own adequacy there: `⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩`
at `src/L/Choice/Order.lagda.md:267`, with uses at `:372` and
`:462`. That is evidence that restating graph adequacy at a
consumer's world is fundable at a price, and not blocked in
principle. It does not transfer by analogy to this telescope, and I
do not found anything on it. The next brief should read it before it
prices the stage-world adequacy.

**W8 cross-check.** The return leans on
`dev/literature/devlin-II5.md:107-108` for the orthodox reverse
inclusion. I checked the errata dossier for any correction that
touches it: its Chapter II items are amenability and the uniformity
of `Sat` (`dev/literature/devlin-errata.md:125-139`), not the II.5
transfer. The W8 reading stands.

## VERDICT

**UPHELD.** The NO-GO of LJ-1.492#1 is correct on its own numbers,
its measurement is sound, and I reproduced the green myself. The
obligation `agents/tasks/LJ-1-492/Probe492.agda::CoverWitnessesInHull`
stays open. The return's own account of what the hull's closure
lacks, "the hull's own closure does not reach its own consumer"
(`lj-1.492-report.md:147-149`), survives the attack, and my attack
sharpens it: what the consumer owes is adequacy of the level graph
at the stage world, in both directions, for which `hull-closed` is
the delivered spelling and `L.Choice.Order` is the delivered
precedent. An upheld NO-GO closes the task; the completed
enumeration above is what the successor brief should carry.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED
  2026-08-20`. Declined, not used. The per-episode journal is
  retired, and the history of this task is its own directory.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote: `#
  ORCHESTRATION: the orchestrator's operating rules`. Declined, not
  used. No orchestrator rule bears on a mathematical verdict.
- `archive/dev/DD-archived.md`: read at `:1`. Quote: `# THE `DD`
  RULING SERIES, archived in full 2026-08-18`. Declined, not used.
  The clauses that bind this review, W2, W3, W7 and W8, reached me
  through the live slot file, and I did not need the archived
  series.
- `archive/dev/PLAN-archived.md`: read at `:1`. Quote: `# ARCHIVED
  2026-08-20`. Declined, not used. The plan under review is a probe
  and its report, not a retired plan.
- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote: `# THE
  `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used. I
  read the live reports of `[LJ-1.458]` through `[LJ-1.489]`
  directly, at `file:line`, and the retired index adds nothing.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote: `> By 2.7
  there is a Σ₀ formula Φ(z, v, γ) of LST such that`. Also read at
  `:107`. Quote: `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the
  same transfer on the`. Used: the return's W8 section reads the
  reverse inclusion from these lines, and the quotes are exact. My
  review confirms the reading and adds that the transfer Devlin
  runs is Σ₁-elementarity, which the hull's `closed` does not
  deliver, so the literature does not close the gap the return
  names.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:23`. Quote: `2.
  Mathias, A. R. D. "Weak systems of Gandy, Jensen and Devlin." In
  Set`. Used as the pointer to the corrected foundations behind the
  errata dossier I checked in W8. Not load-bearing for the verdict.
- `dev/literature/digest.md`: read at `:1`. Quote: `# Digest: the
  orthodox form of the rud route, pinned from the collected
  literature`. Declined, not used. No rud-route step is at issue in
  this return.
- `dev/literature/geology.md`: read at `:1`. Quote: `# Geology
  dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. No geology question bears on the hull's
  closure.
- `dev/literature/devlin-errata.md`: read at `:125`. Quote: `### 2.3
  Errors in Chapter II (WS pp. 62-63)`. Used: I verified that the
  documented Chapter II corrections concern amenability and the
  uniformity of `Sat`, not the II.5 reverse-inclusion transfer the
  return cites. The return's W8 reading is undisturbed.
