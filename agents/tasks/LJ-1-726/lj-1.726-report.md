# LJ-1.726 report: matrix₃ at a numeral-carrying witness slot

## HEAD
coder, wide caliber (-A64m -I0 -M2g), shared pane.

## The verdict

NO-GO, and the target is FALSE, not merely unproved (D-10). The obligation

    ambient-at-Lω :
      (δ : CS.S) (oδ : IsOrd (fst δ))
      → ⟨ (Lset (fst δ) ∷ fst δ ∷ Lset ω ∷ []) P652.⊨ₚ P667.matrix₃ ⟩

dies at `δ := ω`. This is the D-10 catch against premise 3: the corrected
target from 716 asked for a witness slot that carries the numerals, but the
graph half of `matrix₃` also carries the approximation table in the witness,
and no fixed stage carries the table for general δ.

## The site, and the falsity

The graph half of `matrix₃` is `graphBndAt` (src/L/Condensation.lagda.md:
2486-2506): one bounded existential over the witness slot producing the
approximation table, and its `approxBndAt` half opens with `domB` (src/L/
Condensation.lagda.md:1749-1761): the table answers exactly the members of
the parameter that lie in the witness (both directions, both bounded by the
witness). At `(Lset ω, ω, Lset ω)` every numeral lies in both `ω` and
`Lset ω`, so the table would hold a pair with first component `# k` for
every `k`. The table sits in `Lset ω`, so `rank-Lset`
(src/L/Ordinal/Stages.lagda.md:190) puts `rank c` in `ω`; the ω-members
decode makes `rank c` a numeral `# j`; the entry at `# j` then drags `# j`
inside `rank c = # j` through `rank-mono` (src/L/Rank.lagda.md:117), the
pair components, and `rank-fix` (src/L/Rank.lagda.md:191). `∈-irrefl`
closes. Everything in the kill is a delivered lemma; nothing is new
mathematics.

## What is green

- `#∈Lω` (runs/TablePerp.agda:67-70): numerals in `Lset ω`, by
  `ord∈Lset-suc` (src/L/Ordinal/Stages.lagda.md:434), `#∈ω`
  (src/L/Ordinal.lagda.md:248) and `Lset-mono`.
- `table-⊥` (runs/TablePerp.agda:72-97): the kill above, machine-checked
  end to end, on `rank-Lset` (src/L/Ordinal/Stages.lagda.md:190),
  `rank-mono` (src/L/Rank.lagda.md:117), `rank-fix`
  (src/L/Rank.lagda.md:191) and `ω-mem-ord` (src/L/Ordinal.lagda.md:258).
- `ω∈Lˡ` (Probe726.agda:148-149), `ambient-at-Lω-refutes`
  (Probe726.agda:151-155): the refutation composed against the
  obligation at `δ := (ω , Lset→isL (sucV ω) (suc-ord ω-ord) ω
  (ord∈Lset-suc ω ω-ord))`.
- The whole file checks at the wide caliber; the only holes are the
  designed one at `ambient-at-Lω` (Probe726.agda:157-163) and the parked
  extraction `matrix₃-table` (Probe726.agda:129-140, see below).

## What resisted, and what is parked

The extraction of the entry table from the matrix satisfaction was written
and driven to within one application. The route: transfer the erased
reading to the landing reading `SemV.At CS.S fst` (by `Count.erase-inv`,
src/FOL/Count.lagda.md:617, and `embed-⊨`,
src/FOL/Manipulation/Relabelling.lagda.md:188, both delivered), peel the
twelve bounded existentials one step at a time (each level a one-line
`PT.rec`; the standalone shapes are green), then take the graph half and
the domB conjunct. The final application of the projected domB
satisfaction left the satisfaction coercion unreduced at the application
check (runs/p-45.out), and every restructuring of the deep peel crashed
Agda 2.8.0 itself (the crash runs are p-50 to p-53, p-58, p-60 to p-61,
p-63 to p-67, p-70, p-74 to p-76, p-80, p-83: all `time: command
terminated abnormally`, no Agda message, 0.5-75 s in). This satisfies
the heap-wall clause's bar for reporting: the restructurings were made
and each was tested under the same cap, every test died as an abnormal
termination, and the surviving file parks exactly that step with the
route documented in the hole note.

The next brief's cheapest route to close it: reach the domB reading through
the delivered reading-lemmas (Sequence's `ApproxAt-value`,
src/L/Coding/Sequence.lagda.md:298, and `StepAt-back`,
src/L/Coding/Sequence.lagda.md:221, at variable slots) instead of raw
satisfaction peeling, or price a satisfactions-level `domAt-out` analogue.
Both unpriced; the raw-peel price is now measured as "one application short,
compiler-fragile".

Literature corroboration for the corrected target: in Devlin's own shape the
witness slot is a BOUND existential variable (the table itself), not a fixed
container. `dev/literature/level-formula-slot-roles.md:26` records Devlin
5.2 (a) as `Φ(z,v,γ)` with the witness `z` at position 0 BOUND and `v`, `γ`
free; the digest's law 2.1 (`dev/literature/level-formula-slot-roles.md:35`)
states the free pair is the VALUE and the ORDINAL in every source. A witness
slot that carries the numerals is nobody's shape in the corpus.

## W3, answered

Whether `matrix₃` holds at `(Lset δ, δ, Lset ω)` for general δ: NO-GO. The
pin that still needs a member of the table is `graphBndAt`'s domB conjunct,
whose right half demands an entry for EVERY member of the parameter that
lies in the witness. GO is not available at any fixed witness stage: the
same kill goes through whenever the parameter's numeral content outranks
the witness stage. The readings that survive keep the witness growing with
the parameter (z := Lset (suc^k δ) for small fixed k, the table's rank being
δ + finite) or drop the table bound. Which of these feeds `LsetGrounded` is
the mathematician's call; neither is priced here.

## C-42, the sweep

The shape "graph table bounded by a fixed-stage witness slot" occurs at
exactly ONE site: this obligation. Probe520's `levelFo` binds its thirteen
existentials unbounded (agents/tasks/LJ-1-520/Probe520.agda:171-185), and
the delivered `GraphB` consumers bind by a hull-relative K where the table
exists by construction (src/L/Condensation.lagda.md:2486-2506). Count: 1.

## Prices

Full-file checks at the wide caliber ran 128-1018 s wall, peak resident
1.55-1.63 GB, under the 2 g cap, in the quiet-pane windows; under memory
pressure the same file was killed by the pane at 0.8-1.5 GB (nondeterministic,
external SIGKILL, not an Agda message). The compiler crashes on the deep-peel
restructures reproduce deterministically on this pane (runs/p-50 series).
Final state, re-measured on the finished file:
runs/p-final3-tableperp.out (green, rc 0, 0.95 s, peak 282 MB) and
runs/p-final3-probe.out (rc 42, 2.94 s, peak 622 MB, the two designed
metas and nothing else).

## Files

- agents/tasks/LJ-1-726/Probe726.agda (the probe; nothing in src/)
- agents/tasks/LJ-1-726/runs/TablePerp.agda (the kill lemma, green, split
  out so its check runs on its own heap budget; imported by the probe)
- agents/tasks/LJ-1-726/review-of-ambient-at-Lω.md (the NO-GO review)
- agents/tasks/LJ-1-726/runs/ (p-1 to p-83, exp-1 to exp-12,
  p-final-check.txt, p-final2 and p-final3 tableperp/probe runs, the
  accept-1.out harness record, and ProbeExp.agda.txt, the bisect scratch)

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - read for DD4's wording, the clause this
  probe answered at W2: "MAXIMUM REUSE is the architecture's objective,
  and it is the same rule as WRITE IT GENERIC". The kill in
  runs/TablePerp.agda is built only from delivered lemmas for that
  reason.
- archive/dev/DD-archived.md:35 - read for DD25: "A NEGATIVE RETURN IS
  ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY". This return's
  verdict is a NO-GO, and review-of-ambient-at-Lω.md is the review
  companion the branch hands to the adversarial mathematician.
- archive/dev/ORCHESTRATION.md:88 - read for the negative-return
  trigger: "a refutation of the brief's premise, or a landed result that"
  misses its band. The verdict here is a refutation of premise 3, so the
  escalation path above is the one in force.
- archive/dev/PLAN-archived.md - not read: the archived construction
  registry of the retired route; nothing in it bears on this probe.
- archive/dev/STATUS-archived.md - not read: the retired route's frozen
  goal table, archived 2026-08-09; nothing in it bears on this probe.
- archive/dev/TASKS-archived.md - not read: the archived L3.32-T task
  index; nothing in it bears on this probe.

## LITERATURE USED

- dev/literature/level-formula-slot-roles.md:26 - read, and load-bearing
  for the corrected target: Devlin 5.2 (a) binds "z at position 0" and
  leaves only the value and the ordinal free, so a numeral-carrying
  witness slot is nobody's shape in the corpus.
- dev/literature/level-formula-slot-roles.md:35 - read: "The free pair is
  the VALUE and the ORDINAL", the law every surveyed source agrees on.
- dev/literature/glossary-review-2026-08.md - not read: a terminology
  review of pre-protocol glossary entries; this task raises no term
  dispute, so nothing in it bears.
- dev/literature/devlin-errata.md - not read: the errata target Devlin's
  rud-route chapters, and the file holds no "5.2" erratum (grep empty);
  the 5.2 slot-shape this verdict leans on is unaffected.
- dev/literature/primary-sources.md - not read: fetch notes for the
  Jensen/Devlin/Jech second round; no claim of this probe rests on a
  fetched page.
- dev/literature/BIBLIOGRAPHY.md - not read: the source registry with
  access status; no new source was needed.
