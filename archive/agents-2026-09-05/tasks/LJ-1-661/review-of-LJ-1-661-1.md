# LJ-1.661: adversarial review of LJ-1.661#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## VERDICT: UPHELD

The predecessor's NO-GO stands. I re-opened every load-bearing site myself.
The obligation `hoodsound-at-levelhood0` demands one pin `φ₀` with `Δ₀ φ₀`
and `LsetOnlyAt φ₀` both inhabited, and no such pin exists in the tree. The
supplier side forces `φ₀ = erase LsetGraph p`, where the leading constructor
is the unbounded `∃̇` and `data Δ₀` has no case for it, and the pin term is
itself unstateable while `satGraphAt` is opaque. The chapter side has no
arity-2 formula at all, and its arity-2 readings are Σ₁. The literature
grades the arity-2 level-hood Σ₁ in every source. I attacked with DD25's
four questions (archive/dev/DD-archived.md:35) and found no crack; below I
answer section 6.6's three.

## QUESTION 1: does the verdict LINE match its own BODY?

**Yes.** The report's line is `VERDICT: NO-GO`
(agents/tasks/LJ-1-661/lj-1.661-report.md:3), and the body delivers exactly
that: site A fails the Δ₀ input and the pin's stateability, site B fails
arity, grade and slots, and no third site exists. The companion
`review-of-hoodsound-at-levelhood0.md` says the same thing at the same
sites. No sentence in either file concedes a route the verdict line denies.
The accept arm agrees with the body's mechanics: exit 0, `error_class`
None, `obligations_open` 1, `obligations_delta` 0, 20 changed files all
inside SCOPE (agents/tasks/LJ-1-661/runs/accept-1.out:16-25). An open
obligation with a green probe is precisely a stated NO-GO, not a landing.

## QUESTION 2: does every load-bearing claim resolve at its file:line today?

**Yes.** I opened each one in this checkout:

- `soundP-leg2-from-pix` takes `(φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀ →
  Site.Target … → Site.LsetOnlyAt … φ₀ → Site.HoodSoundP … φ₀`:
  agents/tasks/LJ-1-658/Probe658.agda:317-325, confirmed.
- `LsetOnlyAt φ₀` quantifies over `γL : AbsL.SM ^ 2` and reads value at
  slot zero, ordinal at slot one, no bound slot:
  agents/tasks/LJ-1-658/Probe658.agda:219-224, confirmed.
- The supplier `Lset-only` consumes `⟨ γ ⊨ LsetGraphAt w b ⟩`:
  src/L/Hierarchy.lagda.md:334-335, confirmed.
- `LsetGraph = LsetGraphAt zero (suc zero)`:
  src/L/Coding/Sequence.lagda.md:353-354, confirmed. The body cited at
  :291-292 is spelled `GraphAt` there; the name `LsetGraphAt` is the
  re-export renaming at src/L/Coding/Sequence.lagda.md:349
  (`renaming ( GraphAt to LsetGraphAt`). The probe states this precisely
  (Probe661.agda:69-72); the report's shorthand is cosmetic, not
  load-bearing. The leading `∃̇` at :291-292 is confirmed.
- `data Δ₀` has ten constructors and none for `∃̇` or `∀̇`:
  src/FOL/LevyHierarchy.lagda.md:47-57, confirmed by reading the block.
- `erase (∃̇ φ) p = ∃̇ erase φ p`: src/FOL/Count.lagda.md:607, confirmed.
- `satGraphAt` is `opaque` with readers as its only official unfoldings:
  src/L/Coding/Graph.lagda.md:203-205 and :207-216, confirmed.
- `LevelHood0` exports `matrix : Formula CS.S 4`, `Δ₀-matrix`,
  `Σ₂ : Formula CS.S 1`, `Σ₁-Σ₂ = σ-∃ (σ-∃ (σ-Δ₀ (δ-∃∈ Δ₀-matrix)))`:
  src/L/BoundedSubset.lagda.md:840-859, confirmed. The string
  `Formula CS.S 2` occurs nowhere in the chapter (grep, zero hits), so
  "no arity-2 export" is a checked fact.
- The section title "THE SIGMA-1 LEVEL-HOOD AT THE CLASS CARRIER":
  src/L/BoundedSubset.lagda.md:66, confirmed.
- The priced residue "the level-hood instantiation at the hull":
  src/L/BoundedSubset.lagda.md:899-904, confirmed with the 0.0097 s per
  line figure at :901-903.
- dev/ARCHIVE.md:285 carries both quoted fragments, including
  `ambientOnly-from` at 138.2 s of 150.2 s, confirmed.
- The grade measurement, 2,287 unbounded `∃̇` and 2,159 unbounded `∀̇`:
  agents/tasks/LJ-1-646/lj-1.646-report.md:82, confirmed.
- The zero-count precedents: agents/tasks/LJ-1-651/Probe651.agda:73-74 and
  :115-116, both `refl`, confirmed.
- `HoodExistsP` takes no Δ₀ input:
  agents/tasks/LJ-1-653/Probe653.agda:283-288, confirmed.
- The runs are what the report says they are. `runs/wall.out` shows exactly
  two `[UnsolvedInteractionMetas]`, at Wall661.agda:48.14-18 and :64.13-17,
  rc 42; the temp copy `Wall661.agda` is absent from the task home
  (verified by ls). `runs/floor-1.out` ends in `[UnequalTerms]` with a
  stuck count against `zero` at `countFo LsetGraph ≡ 0`, rc 42.
  `runs/floor-2.out` is green, rc 0, and the acceptance arm re-ran the
  probe green at 2.8 s (accept-1.out:16). The 3.12 s in the report is
  floor-2's own run, a different run from the accept arm's; the two
  numbers are not in conflict.
- The literature rows: dev/literature/level-formula-slot-roles.md:26 (the
  Devlin 5.2 (a) Δ₀ form, 3 slots in `Φ` with one closed) and :28 (the
  Jech 13.14 Σ₁ step at arity 2), both confirmed at their lines.

## QUESTION 3: is the enumeration complete?

**Yes, and I re-derived it rather than trusting it.** The obligation needs
a pin where BOTH inputs are inhabited, so a complete enumeration must cover
every source of each input.

- **Every supplier of the `LsetOnlyAt` hole.** I swept `src/L/` for every
  lemma concluding `≡ Lset (…)`. The lemmas whose premise is bare
  satisfaction of a formula plus ordinality are `Lset-only`
  (src/L/Hierarchy.lagda.md:334-335) and its class-carrier re-export
  `ride-only` (src/L/Condensation.lagda.md:422-425), and both consume
  `⟨ γ ⊨ LsetGraphAt w b ⟩` and nothing else. Every other `≡ Lset`
  conclusion (`step-Lset` at src/L/Hierarchy.lagda.md:190-193,
  `graph-table` at :381-386, `Lset-defines` at :644-647) either consumes
  table data `LsetOnlyAt` cannot provide or points the wrong direction.
  At arity 2 with value at slot zero and ordinal at slot one, the one
  covered formula is `LsetGraphAt zero (suc zero) = LsetGraph`. Site A is
  therefore THE supplier-side pin, not a sample of it.
- **Every source of the `Δ₀` input.** The tree's only Δ₀ certificate near
  the level-hood is the chapter's `Δ₀-matrix` at arity 4 with the bound
  `K` free (src/L/BoundedSubset.lagda.md:851-852), and the literature
  says the arity-2 form is Σ₁ in every source
  (dev/literature/level-formula-slot-roles.md:26-28), so no third pin can
  be manufactured by finding a different arity-2 Δ₀ level-hood. Site B is
  therefore THE certificate-side pin.
- **The C-42 sweep's count of 1 is right.** I grepped the tree and the
  task homes for consumers of `soundP-from-pix` / `soundP-leg2-from-pix`:
  the definitions in Probe658 and this task's files are the only hits.
  The sibling `HoodExistsP` takes no Δ₀ input
  (agents/tasks/LJ-1-653/Probe653.agda:283-288). One site carries the
  false shape.
- **The cure list misses nothing I can find.** The four-question lens asks
  whether a cure was missed. Candidates I attacked: swapping `Δ₀ φ₀` for
  `Σ₁ φ₀` in leg 2 fails because the delivered chain crosses carriers in
  both directions and Σ₁ absoluteness is one-directional; proving
  `countFo LsetGraph ≡ 0` by lemma fails because the count is stuck on an
  opaque FORMULA and any proof must open the seal, which is the report's
  cure 3; a direct proof of `LsetOnlyAt` at a fresh Δ₀ arity-2 pin IS the
  reshaped soundness lemma, which is the report's cure 1. Section 7 of
  the report already prices all three directions.

## THE BRIEF'S OWN PART, stated for the pair-reading

DD25's third question asks whether the BRIEF caused the outcome. Partly:
the brief's premises 2 and 3 were separately true and jointly
unsatisfiable, because premise 3's supplier exists only at `LsetGraph`
while the pin instruction names `LevelHood0`'s shape. But the brief
priced exactly this: "NO-GO earns the mismatch between `LevelHood0` and
`Lset-only`'s slots" (agents/tasks/LJ-1-661/LJ-1.661.md:69-71). The
return delivered the purchased fact and correctly voided the 70-150 line
W3 estimate as a shape fact, not a price. This is D-10 working as
written: the target was false, and the stop is the deliverable.

## THE TRANSITIONS JOURNAL

This worktree's `dev/pod/transitions/2026-08.jsonl` is at the base
commit and ends at seq 4317. The only line carrying `"task": "LJ-1.661"`
is the READY admission (seq 4313, `heads_sha256` cd49070c, `model` and
`effort` both null). The journal ends before the attacked run's dispatch
lines, so per the brief I say so here and take the run's six facts from
the accept arm (agents/tasks/LJ-1-661/runs/accept-1.out:10-23): six
conjuncts held, probe rc 0 at 2.8 s, 20 changed files all own, in-fence
lines 0, obligations delta 0, error class None, exit 0.

## A21 COMPLIANCE

This review needed no new measurement, so I name no probe and I wrote and
touched no `.agda` file. The predecessor's runs, re-read above, carry the
whole evidential load.

## ARCHIVE USED

- **archive/dev/DD-archived.md READ.** archive/dev/DD-archived.md:35
  reads `| DD25 | **A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT
  MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ TOGETHER. THE
  HEADS COME FROM THE SWITCH.**` and the same line carries the four
  questions ("is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a cure
  the return missed"). This is the lens this review attacked with.
- **archive/dev/ORCHESTRATION.md DECLINED.** Surveyed by grep for
  `hoodsound`, `Lset-only`, `level-hood`, `levelhood`, `soundP`; zero
  hits. The archived process document carries nothing on this task's
  mathematics.
- **archive/dev/PLAN-archived.md DECLINED.** Same survey, zero hits on
  this task's terms. The predecessor already took its one relevant line
  (:139, the no-Δ₀-witness precedent) and I verified nothing further
  bears.
- **archive/dev/measurements/README.md DECLINED.** Same survey, zero
  hits. A measurements index; the measurements this review needed live in
  the task homes and were read there.
- **archive/dev/README.md DECLINED.** Same survey, zero hits. The
  archive's map; the files it maps were reached directly.

## LITERATURE USED

- **dev/literature/level-formula-slot-roles.md READ.**
  dev/literature/level-formula-slot-roles.md:26 reads
  `| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`
  | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 |
  **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |`. I read
  rows 4 and 6 to check the predecessor's literature claim independently:
  every source grades the arity-2 level-hood Σ₁ and puts the Δ₀ form at a
  higher arity with a bound, so no third pin exists (question 3 above).
  The predecessor's quotes occur at the lines it cites.
- **dev/literature/BIBLIOGRAPHY.md DECLINED.** Surveyed by grep for the
  task's terms; zero hits. The shelf list; the shelf itself is
  level-formula-slot-roles.md, read above.
- **dev/literature/devlin-errata.md DECLINED.** Surveyed; zero hits. The
  errata do not touch the two rows used.
- **dev/literature/primary-sources.md DECLINED.** Surveyed; zero hits.
  The rows used carry their own extraction locators.
- **dev/literature/glossary-review-2026-08.md DECLINED.** Surveyed; one
  hit at :704, a terminology sentence about rendering the Δ₀/Σₙ/Πₙ
  hierarchy in Chinese. It settles a word, not a shape; not used.
