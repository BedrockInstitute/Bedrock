# LJ-1.726: adversarial review of LJ-1.726#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-726/lj-1.726-report.md` (NO-GO,
exit 42, error_class `unsolved_meta`, obligations_open 1; runs/accept-2.out).
`dev/pod/transitions/2026-08.jsonl` carries zero lines for task `LJ-1.726` and
ends at seq 4839, ts 2026-08-27T09:45:14Z, before this task started. Per the
brief I use the acceptance arm for the run facts and infer nothing else from
the transitions record; `model`, `effort` and `heads_sha256` for this task are
not recoverable today.

## The three questions

### 1. Does the predecessor's verdict LINE match its own BODY?

Yes. The verdict line is "NO-GO, and the target is FALSE, not merely unproved"
(lj-1.726-report.md, section "The verdict"). The body supports it at the D-10
bar, with one disclosed condition:

- The kill is machine-checked green. `table-⊥`
  (agents/tasks/LJ-1-726/runs/TablePerp.agda:72-97) runs rc 0, 0.95 s, peak
  282 MB (runs/p-final3-tableperp.out). It consumes only delivered lemmas, and
  each one says today what the report claims: `rank-Lset`
  (src/L/Ordinal/Stages.lagda.md:190), `rank-mono` (src/L/Rank.lagda.md:117),
  `rank-fix` (src/L/Rank.lagda.md:191), `#∈ω` (src/L/Ordinal.lagda.md:248),
  `ω-mem-ord` (src/L/Ordinal.lagda.md:258), `ord∈Lset-suc`
  (src/L/Ordinal/Stages.lagda.md:434).
- The refutation is composed against the briefed obligation at
  `δ := ω` (Probe726.agda:151-155) and the obligation stands as the designed
  hole (Probe726.agda:157-163). The final state has exactly two metas and no
  other error (runs/p-final3-probe.out: metas at 135.25-140.42 and
  158.22-163.56, rc 42).
- The condition: the falsity chain runs obligation to table through
  `matrix₃-table` (Probe726.agda:129-140), which is the parked hole. The body
  discloses this in three places (the report's "What resisted", "W3
  answered", and the probe's hole note), so line and body do not contradict.
  The parked step is not in mathematical doubt: bounded satisfaction is a
  `⋁` over members by definition (src/FOL/Semantics.lagda.md:103), so a
  satisfier yields a member witness; the residue is mechanical, and it is
  measured (runs/p-45.out, `CannotApply` on the Σ-typed `dmb`; 14 crash runs,
  each `terminated abnormally`, verified in p-50 to p-53, p-58, p-60, p-61,
  p-63, p-67, p-70, p-74, p-76, p-80, p-83).

This is not the 375/376 failure mode: no verdict line contradicts its body,
and no load-bearing citation points at an unread record.

### 2. Is every load-bearing claim backed by a `file:line` that resolves today?

Yes, with three findings against the narrative, none load-bearing for the
verdict. Verified today:

- The site. `graphBndAt` is `∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)`
  (src/L/Condensation.lagda.md:2493-2494), and `domB`
  (src/L/Condensation.lagda.md:1749-1753) answers exactly the members of the
  parameter bounded by `K`, both directions, as the report says.
- The witness binding. The matrix's table bound `K` is the witness slot:
  `Mx = Matrix {15} ww bb kk ...` passes `K := kk`, the last slot
  (agents/tasks/LJ-1-667/runs/W3.agda:56-61), and `Matrix` forwards it to
  `GraphB` (agents/tasks/LJ-1-520/Probe520.agda:53,77). The twelve tag
  existentials bind by `lastFin`, the witness
  (agents/tasks/LJ-1-667/runs/W3.agda:53-57,72-76).
- The obligation type. The probe's local `_⊨ₚ_` is Probe652's own spelling:
  same `SemV.At (∅*)` at agents/tasks/LJ-1-652/Probe652.agda:50-51, so the
  attacked type is the briefed type.
- The numbers that pick the branch: exit 42, error_class `unsolved_meta`,
  heap_wall false, obligations_open 1 (runs/accept-2.out).

Findings (I state them as findings, not as grounds to overturn):

- F-a, wrong run pointer. The probe comment says the peel-level shapes were
  "measured green in runs/exp-12.out" (Probe726.agda:113-114). exp-12.out is
  an abnormal termination (`time: command terminated abnormally`, EXIT=1).
  The green evidence exists in the same series at runs/exp-3.out and
  runs/exp-4.out (both rc 0, checking LJ-1-726.runs.exp). True claim, wrong
  pointer.
- F-b, a band the run files do not fully carry. The report's wall band
  "128-1018 s" is exceeded by runs/p-29 (1033.06 s) and one later run
  (1035.52 s). Whether those were full-file checks cannot be settled from
  the file names. The branch-bearing numbers are the arm's own and are
  correct, so this loads nothing.
- F-c, an undisclosed refusal. The program refused the return's review
  companion: `verdict_files_refused` names
  `review-of-ambient-at-Lω.md` in runs/accept-1.out and runs/accept-2.out
  (the non-ASCII ω). The brief itself mandated that path
  (LJ-1.726.md:32), so the defect is a brief/program mismatch, not a coder
  deviation. It changed only which escalation row fired
  (`no-go-attacked`, priority 15, instead of `no-go-stated`, priority 20);
  both target this head. The next brief must name an ASCII verdict path.

### 3. Is the predecessor's enumeration complete?

Complete for the decision, with small gaps:

- The C-42 sweep count of 1 holds against both named comparables: Probe520's
  `levelFo` is a Σ₁ shape with unbounded existentials
  (levelFo-Σ₁, agents/tasks/LJ-1-520/Probe520.agda:171-172), and the delivered
  `GraphB` consumers bind by a hull-relative `K`
  (src/L/Condensation.lagda.md:2486-2490). No third site appears in this
  attack's scope.
- Files: the report omits runs/exp.agda (the scratch the exp series checks).
  Minor.
- The brief's instruction to paste the survey-quotes output into the report
  was not carried out. The survey itself passes: accept-2 held conjunct 6
  with an empty lint_detail.
- W2 is answered (the kill reuses delivered lemmas only), W3 is answered
  (term named, surviving readings named, the choice routed to the
  mathematician), and the literature duty is met (see below).
- Loop artifact, untouched by me: agents/tasks/LJ-1-726/review-LJ-1-726-1.md
  is a copy of a dispatch preamble under a review-shaped name, carrying no
  review content.

## Ruling

UPHELD. The return's NO-GO stands on its own numbers: the obligation is open,
the fixed witness slot `Lset ω` is killed at `δ := ω` by a green lemma built
from delivered lemmas, and the one missing link is disclosed, measured, and
semantically immediate from the satisfaction definition. The task closes as
`done` / `no-go` under row `sys-critic-upheld-no-go`.

For the next brief (A21: I name the probe, I write no `.agda` myself): the
obligation is `matrix₃-table` exactly as typed at Probe726.agda:129-134. The
cheapest route is the delivered reading-lemmas at variable slots,
`StepAt-back` (src/L/Coding/Sequence.lagda.md:221) and `ApproxAt-value`
(src/L/Coding/Sequence.lagda.md:298), instead of the raw peel that crashed
the compiler; the alternative is a satisfactions-level `domAt-out` analogue.
The probe lives under agents/tasks/LJ-1-726/, tracked, never under `src/`.

## ARCHIVE USED

- archive/dev/DD-archived.md:35 - read; DD25's four questions are this
  review's lens: "is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a cure
  the return missed."
- archive/dev/ORCHESTRATION.md - not used; it governs escalation routing,
  which the acceptance arm already settled for this return.
- archive/dev/PLAN-archived.md - not read; the retired construction
  registry; nothing in this review turns on it.
- archive/dev/measurements/README.md - not read; the measurements I used
  come from the acceptance arm and the run files, not from measurement
  convention.
- archive/dev/README.md - not read; directory guide, no bearing.

## LITERATURE USED

- dev/literature/level-formula-slot-roles.md:26 - read; the Devlin 5.2 (a)
  row puts the witness at "`z` at position 0" as a bound slot, which is the
  corpus fact the report's literature claim rests on.
- dev/literature/level-formula-slot-roles.md:35 - read; "The free pair is
  the VALUE and the ORDINAL, in every source", the law that leaves a
  numeral-carrying fixed witness slot without corpus precedent.
- dev/literature/devlin-errata.md - declined after a verification grep: no
  "5.2" entry exists (grep empty), so the errata do not touch the 5.2
  slot-shape this verdict leans on.
- dev/literature/primary-sources.md - not used; fetch notes for a second
  source round, and no claim here rests on a fetched page.
- dev/literature/BIBLIOGRAPHY.md - not used; the source registry with access
  status; no new source was needed.
- dev/literature/glossary-review-2026-08.md - not used; a terminology
  review, and this task raises no term dispute.
