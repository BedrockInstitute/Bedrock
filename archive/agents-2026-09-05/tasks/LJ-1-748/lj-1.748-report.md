# LJ-1.748 return: pr-in-Lset-lim, BoundOver pairing under closedω

**Disposition: GO.** The obligation `pr-in-Lset-lim` is inhabited at
`agents/tasks/LJ-1-748/Probe748.agda:132-137`. The file typechecks at the pane
caliber with rc 0 (runs/green-1.out, runs/green-2.out; 1.50 s cold, 1.12 s
warm, runs/green-1.time, runs/green-2.time). `pair-in-Lγω` and `table-sat`
are not inhabited; neither name occurs in the file outside two header
comments that record their absence.

## What the obligation is

The brief asks for pairing of TWO STAGE MEMBERS at a closedω limit:

    pr-in-Lset-lim :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        (x y : V ℓ)
        → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
        → ⟨ pr x y ∈ˢ Lset γ ⟩

This is the `BoundOver.pr∈λ` law (src/L/Coding/Bound.lagda.md:69, "The
sequences: the Kuratowski pair") read at `T := Lset`, `lam := γ`. It is not
`pair-in-Lγω`, which places `pr x (Lset x)` for `x ∈ γ`
(agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:151).

## What was built

`agents/tasks/LJ-1-748/Probe748.agda`, 137 lines, three sections.

- SECTION 1, `Closer` at the telescope `(γ oγ clγ)`:
  `no-succ` (Probe748.agda:43-61) and `suc∈γ` (Probe748.agda:65-67), a
  verbatim copy of the 737-SPLIT legs (Probe737Split.agda:109-127) with the
  `hγ` argument dropped.
- SECTION 2, `PairLim` at `(lam ordλ succλ)`: the `pr∈λ` proof body
  transcribed from `BoundOver.pr∈λ` (src/L/Coding/Bound.lagda.md:69-91) at
  the concrete facts `Lset-out′` (imported from src/L/Coding/Bound.lagda.md:120),
  `Lset-mono` (src/L/Constructible.lagda.md:365) and `pr∈Lset-suc`
  (src/L/Axioms/Basic.lagda.md:596). The `climb` leg lifts the pair two
  successors and applies `succλ` twice; the `both` leg merges the two
  decomposition stages by `ord-tri`
  (src/L/Ordinal/Linear.lagda.md:136).
- THE OBLIGATION at Probe748.agda:132-137 is one line:
  `pr-in-Lset-lim γ oγ clγ = PairLim.pr∈λ γ oγ (Closer.suc∈γ γ oγ clγ)`.
  The statement text equals the brief's obligation text.

## Deviations

1. **The src wrapper `Bound` cannot host this instance, so the body is a
   transcription and not a module application.** The brief says
   "instantiate `BoundOver.pr∈λ`". The instantiation that src already
   performs, `module Bound` (src/L/Coding/Bound.lagda.md:130), demands
   `∅∈λ : ⟨ ∅ ∈ˢ lam ⟩` (src/L/Coding/Bound.lagda.md:132). The brief's
   telescope `(γ oγ clγ)` cannot supply it: `closedω` is vacuous at
   `γ := ∅` (src/L/Ordinal/StageArith.lagda.md:81) and `∅` has no member.
   The `pr∈λ` body never reads `∅∈λ`, and it never reads `T-ord` or
   `T-trans` either, so the transcription keeps only the five parameters
   the body uses: `T-out`, `T-mono`, `T-pr`, `ordλ`, `succλ`.
   Measured proof of that reading: the file typechecks with the three legs
   absent.
2. **`hγ` dropped from the `Closer` copy.** The brief names
   `Closer.suc∈γ` (Probe737Split.agda:125-127) as the `succλ`. That leg
   sits in `module Closer (γ oγ hγ clγ)` (Probe737Split.agda:105) but reads
   only `oγ` and `clγ`. The copy therefore takes `(γ oγ clγ)`, and the
   brief's omission of `⟨ isL γ ⟩` from the obligation is sound for this
   leg. No `isL` import remains in the probe.
3. **Dangling premise basis.** Premise 1 cites
   `agents/tasks/LJ-1-737/lj-1.737-report.md:42`. That path does not exist
   in this worktree; `agents/tasks/LJ-1-737/` is absent and no archived
   copy sits under `agents/tasks/archive/`. The surviving record is the
   SPLIT pair, Probe737Split.agda and lj-1.737-SPLIT-report.md, and the
   obligation did not need the missing file. Brief builders should cite the
   SPLIT paths.
4. **Interpreter path.** This worktree carries no `.venv/`. The survey
   check ran with the main checkout's pinned interpreter,
   `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, against this worktree's
   `scripts/pod/check-survey-quotes.py`. No dependency was added or
   installed.

## Measurements

All runs at the wide caliber `-A64m -I0 -M2g`, set on the pane by the
program, never set by this agent. One Agda process at a time.

| run | rc | real | file |
|---|---|---|---|
| floor-1 | 42, expected, the four floor holes are the only diagnostics | 1.48 s | runs/floor-1.time |
| green-1 | 0 | 1.50 s | runs/green-1.time |
| green-2 | 0 | 1.12 s | runs/green-2.time |

The floor prices the frame: header imports, both module telescopes, the
obligation statement. The proof body itself costs at most a few hundredths
of a second over the frame. The term is frame-dominated. No heap wall, no
timeout, no restructuring needed.

## What the next brief needs

- **Supply is now 1.** Cite `agents/tasks/LJ-1-748/Probe748.agda:132` as
  the pairing-of-stage-members leaf under closedω. The tower graph leaf
  that 737's report recorded now has its member-pair neighbour beside it.
- **The `∅∈λ` wall is a shape, not a one-off.** Any further closure law
  whose src home is `BoundOver` at a telescope without `∅∈λ` will hit the
  same wall and pay the same transcription. The measured cure is a src
  split: a numeral-free core over `(T-out, T-mono, T-pr, lam, ordλ,
  succλ)`, with numerals added by a thin module above it. That is src
  surgery; this brief barred src writes, so nothing landed there.
- **Prices to plan with:** cold 1.5 s, warm 1.1 s, floor 1.48 s at wide
  caliber. The import frame dominates; adding one more `src/` chapter to
  the header costs its own interface load.
- **Premise citations:** use the SPLIT paths for anything 737-shaped until
  the 737 directory returns to the tree.

## Stops

None. The obligation was supported, the premises held, and the term
typechecked under the delivered telescope.

## Check survey quotes

Output of the mandated check, run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-748`
against the finished return:

    check-survey-quotes: LJ-1-748 clean (0 note(s), 0 defect(s))

    rc=0

## ARCHIVE USED

Corpus search named five CANDIDATEs. None was read; none bears on a closed
Agda instantiation.

- archive/dev/ORCHESTRATION.md: declined, not read; the probe rules that
  govern this task live in agents/README.md, which the brief already
  reflects.
- archive/dev/DD-archived.md: declined, not read; the campaign decisions
  that formed the pod are closed history and name no pairing law.
- archive/dev/PLAN-archived.md: declined, not read; this task took its
  plan from its own brief, not from a retired plan.
- archive/dev/TASKS-archived.md: declined, not read; the retired-route
  task list cannot cite files this obligation stands on.
- archive/dev/STATUS-archived.md: declined, not read; standing status is
  dev/pod/screen.toml, the only admissible home for it.

## LITERATURE USED

Corpus search named five CANDIDATEs. None was read; the obligation is a
closed instantiation of a proved src law, so no primary-source or
formalization question arises.

- dev/literature/glossary-review-2026-08.md: declined, not surveyed; the
  return adds no term and translates nothing.
- dev/literature/primary-sources.md: declined, not read; the mathematical
  content came from the tree, src/L/Coding/Bound.lagda.md:69-91, not from
  a source digest.
- dev/literature/devlin-errata.md: declined, not read; no prose or
  attribution question is open in a code-only probe.
- dev/literature/level-formula-slot-roles.md: declined, not read; this
  obligation names no level formula and no slot arithmetic.
- dev/literature/formalizations-landscape.md: declined, not read; the
  formalization was fixed by the brief and by the src law it instantiates.
