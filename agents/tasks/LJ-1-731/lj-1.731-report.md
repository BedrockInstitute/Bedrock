# LJ-1.731 report: Sat sits in the carrier's stage

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.731
obligation: agents/tasks/LJ-1-731/Probe731.agda::Sat-in-carrier-stage
verdict: **NO-GO, STATED.** The obligation's type as the brief gave it is
FALSE at the intended generality, and the refutation is recorded. The
name `Sat-in-carrier-stage` is exported at the file's top level as a
TYPE (`Probe731.agda:174-181`), transcribed from the brief; it has no
inhabitant, no postulate stands under it, and the file carries
`--safe`. The refutation and the corrected target are in
`review-of-Sat-in-carrier-stage.md`, which is the file the critic
reads. This dispatch exits 42 by the stated-NO-GO convention, so row
`task-lj-1-731-no-go-stated` (priority 20) routes the task to
`mathematician_adversarial`. The `go` row must not fire: the name
resolves as a type, so `obligations_delta` reads -1, but no value was
delivered and none exists at that generality.

## 1. WHY THE TYPE IS FALSE (one paragraph)

The type quantifies over ALL `φ : Formula S n` and places none of
`φ`'s constants. For `φ := (var zero ∈̇ con c)` with an unplaced
constant `c`, `Sat A φ` is the c-trace of the carrier's values
(slot-0 decoded), and the trace varies with `c`'s part over the
carrier. At the site γ := `sucV ω`, A := `LsetS ω ω-ord` (both of the
obligation's own hypotheses hold there, `Probe731.agda:146-162`), a
`c` whose part over the carrier is new above γ makes the trace new
above γ, so `Sat A φ ∉ Lset (sucV ω) = γ`. The machine-checked core is
`cond-trace-equiv` (`Probe731.agda:108-125`): membership in
`Sat B (var zero ∈̇ con c)` at an environment IS the c-trace fact,
generic in `B` and `c`, both directions, from the landed readers
alone. The full argument and the projection step are section 3 and 4
of the review.

**D-10 was applied before any build.** The residue's truth was priced
first (the brief's own D-10 clause, and `dev/LESSONS.md:1375`); the
pricing found the target false, and this dispatch is the stop it
calls for. No Agda time was spent trying to inhabit a false type.

## 2. WHAT THE PROBE CARRIES

`agents/tasks/LJ-1-731/Probe731.agda`, 180 lines, raw `.agda`, lands
nothing in `src/`:

- `cond-trace-equiv` (`:108-125`), the c-trace reduction, generic in
  the carrier `B` and the unplaced constant `c` (W2: written once at
  the generic carrier, instantiated nowhere), both directions, from
  `cond∈-out`/`cond∈-in` (`src/L/Coding/Sat.lagda.md:217,212`) and
  `tmIs-var-out`/`tmIs-var-in` (`src/L/Coding/Sat.lagda.md:92,85`).
- The refutation site's facts (`:146-162`): `site-γ = sucV ω` with
  `IsOrd` and `ω ∈ γ`, `site-A = LsetS ω ω-ord` with
  `fst site-A ∈ Lset (sucV ω)` (the `EnvSupply` `B₀∈σ` pattern:
  `Lset-suc` + `𝒟ₒ-intro` + `defSet⊤≡A`).
- `Sat-in-carrier-stage` stated as a TYPE (`:174-181`), the brief's
  type with the two missing arrows inserted (the brief's transcription
  omits them; Agda's telescope grammar requires them). Nothing weaker
  is inhabited under the name.

## 3. THE RUNS

The worktree's Agda cone was already cached (`_build/2.8.0/agda`
interfaces), so every run below is warm: the file and its import cone
check in about 1.5 s. One Agda process at a time; `GHCRTS` was the
pane's own wide caliber, never set here, recorded as the first line of
every `.out`. p-1 to p-9 are the honest iteration record (one parse
error from the brief's missing arrows, one missing import, arity
pinning); p-10 is the verdict run.

| run | state checked | time | exit | record |
|---|---|---|---|---|
| p-1 | skeleton, parse error (telescope arrows) | 0.34 s | 42 (agda error) | `runs/p-1.out` |
| p-2 | `isL-trans` import missing | 1.42 s | 42 | `runs/p-2.out` |
| p-3 | `cond` missing from the import list | 1.18 s | 42 | `runs/p-3.out` |
| p-4 | `Lset-suc` scoped to the wrong module | 1.26 s | 42 | `runs/p-4.out` |
| p-5 | subst motive wrong (hu as path) | 1.27 s | 42 | `runs/p-5.out` |
| p-6 | ⇔toPath at the wrong level | 1.44 s | 42 | `runs/p-6.out` |
| p-7 | unpinned Fin arities | 1.55 s | 42 | `runs/p-7.out` |
| p-8 | more unpinned indices | 1.67 s | 42 | `runs/p-8.out` |
| p-9 | Fin 1 vs Fin 3 index clash | 1.31 s | 42 | `runs/p-9.out` |
| p-10 | the delivered file, complete, VERDICT RUN | **1.36 s** | **0** | `runs/p-10.out` |
| p-11 | final confirmation, same file, no edit between | 1.22 s | 0 | `runs/p-11.out` |

No heap wall (peak 352 MB against the 2 g cap, `p-10.out`). The
floor-ruling question ("is the frame the problem?") does not arise:
the frame prices at 1.4 s because the cone was cached. A fresh
worktree pays the cone build once (the sibling 727-SPLIT measured
2538.40 s cold for a comparable cone in its own worktree,
`agents/tasks/LJ-1-727-SPLIT/lj-1.727-SPLIT-report.md:10`); this
dispatch paid none of it and claims none of it.

## 4. THE BRIEF'S PREMISES, CHECKED

1. `lj-1.725-SPLIT-report.md:111`: verified, "Fund the stage bound
   first, as its own obligation". The stage bound this probe examined
   is the one that premise names, and the probe's NO-GO says the bound
   as typed cannot be the one 725-SPLIT's spine consumes: the spine's
   formulas are `toS`-shaped (premise 3), whose constants are carrier
   members, and the corrected target in the review is stated at that
   shape.
2. `Sat` is separation from `envSet`: verified,
   `src/L/Coding/Sat.lagda.md:142-147`.
3. Unbounded `fill` at `src/L/Coding/Powerset.lagda.md:502`: verified,
   `Sat A (toS ψ)` in the `DefBody` environment. This is the consumer
   shape the corrected target preserves.
4. `agents/tasks/LJ-1-724/lj-1.724-report.md:27`: **the file does not
   exist in this worktree** (nor does the `LJ-1-724` task directory;
   the 725-SPLIT report:26 already recorded that 724's probe is not in
   this worktree). The premise's content - the type carries `ω ≤ γ` -
   is in the brief's own type, and the refutation holds AT the guard,
   which is stronger than the premise claims. Recorded as unverifiable
   basis, not as a false premise.
5. `LsetS` at `src/L/Axioms/Basic.lagda.md:160-161`: verified.

## 5. W2

Answered. The probe's one new lemma, `cond-trace-equiv`, is stated
once at the generic carrier `B` with the unplaced constant `c` as a
parameter, and instantiated nowhere (the review cites it at the site).
No deadline forced a fixed form; the stop came before any price
conflict.

## 6. WHAT THE NEXT BRIEF NEEDS

1. Re-target at the corrected shape the review states (section 5
   there): either add the constant-placement hypothesis
   (`consts : every constant of φ has fst in Lset γ`), or state the
   obligation at the consumer's own `toS ψ` shape, where no placement
   hypothesis is needed because carrier members are already placed by
   `fst A ∈ Lset γ` plus transitivity.
2. The corrected target's honest price is 250 to 450 lines, not 20 to
   80. The bridge is twelve clauses of reader plumbing with witness
   placement forced by the hypothesis (the review's section 5, step
   3), and the recursion must carry defining formulas as data through
   a `PT.rec` (the truncated-formula obstacle:
   `𝒟ₒ-inv` returns the defining formula only truncated,
   `src/L/Constructible.lagda.md:306-308`).
3. Fund the pieces in order if splitting: (a) the stage merge and the
   definability-stability lemma (definable over `Lset δ₁` with
   `δ₁ ≤ δ` gives definable over `Lset δ`; about 40 to 60 lines, via
   `abs-defSet`, `src/L/Definability.lagda.md:280-284`, composed at
   two stages), (b) the twelve-clause adequacy at the merged stage,
   (c) the assembly. The trace lemma this probe delivered is not
   needed for the corrected target and is not a building block of it;
   it is the refutation's evidence.
4. Do not fund the original unbounded type again. It is false, and the
   counterexample site carries both of the obligation's own
   hypotheses.

## 7. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.36 s (`runs/p-10.out`) |
| peak, verdict run | 353533952 B, about 17 percent of the 2 g cap |
| runs this dispatch | p-1 to p-10 |
| in-file / in-fence lines | 180 / 0 (raw `.agda`) |
| brief estimate (W3) | 20 to 80 lines |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |
| exit | 42 (stated NO-GO) |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not read. This dispatch measures its own probe against the live brief; no archived dispatching rule bears on the stop.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not read. The coder clauses this dispatch answers to live in the slot file, the brief and the live rulings, not in the archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not read. The live screen is `dev/pod/screen.toml` and the live direction is `dev/pod/direction.md`; this task follows those.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not read. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not read. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.731.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. A raw `.agda` probe carries no translation surface, and this dispatch adds no glossary term.
- `dev/literature/devlin-errata.md`: declined, not read. This dispatch cites no Devlin page; the corrected target it records is stated against the tree's own landed lemmas, every one cited at `file:line`.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. The graph census it serves belongs to the `[LJ-1.725]` line; this dispatch re-funds no census.
- `dev/literature/primary-sources.md`: declined, not read. The fetch map is the literature team's record; this dispatch fetches nothing.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No new source is cited by this dispatch.
