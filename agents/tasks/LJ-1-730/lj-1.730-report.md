# LJ-1.730 report: `envSet-in-carrier-stage`, the environment set against the carrier's stage

(This skeleton was written before the first Agda run and filled as the
runs landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.730
obligation: agents/tasks/LJ-1-730/Probe730.agda::envSet-in-carrier-stage
verdict: **NO-GO, STATED.** The obligation's type is FALSE as stated. At
`γ = sucV (sucV ω)`, which satisfies the brief's hypothesis
`⟨ ω ∈ˢ γ ⟩`, the conclusion closes `Empty.⊥`. The refutation is
machine-checked: `envSet-in-carrier-stage-false`
(`agents/tasks/LJ-1-730/Probe730.agda:208`), green at EXIT=0
(`runs/p-11.out`). The obligation's name is exported as its TYPE at
`Probe730.agda:116`, with no inhabitant and no postulate under it, the
725-SPLIT form. `review-of-envSet-in-carrier-stage.md` carries the
counterexample, the headroom reading, and the corrected target for
ruling. Nothing lands in `src/`. The names `keyS-in-carrier-stage` and
`stage-read` are absent from the probe.

## 0. THE PREDECESSOR QUESTION

| piece | taken from | verdict there | use here |
|---|---|---|---|
| the membrane finding | the brief's premise 4, `agents/tasks/LJ-1-724/lj-1.724-report.md:27`; the file sits in the 724 worktree, read at `.pod-state/worktrees/LJ-1-724/agents/tasks/LJ-1-724/lj-1.724-report.md` (verdict sentence 4) | 724 NO-GO: the DefAt membranes fail below a fixed finite stage; corrected scope "limit `γ ≥ ω`" | the reason the brief's type carries `ω ∈ˢ γ`; D-10 priced against that scope before any proof |
| the missing-bound note | the brief's premise 1, `agents/tasks/LJ-1-725-SPLIT/lj-1.725-SPLIT-report.md:111` (section 6, item 1) | 725-SPLIT STOP: no landed lemma bounds `keyS`, `Sat` or the environment sets by the carrier's stage | this task funds one of the three named bounds, and returns NO-GO at the offered scope |
| `envSet`, `envS`, `envSet-in` | `src/L/Coding/EnvSet.lagda.md:189,153,381` | landed, green | the site of the bound; `envSet-in` is what forces the set to sit above its members |
| `stageFor` | `src/L/Coding/EnvSet.lagda.md:91` | landed, green | NOT used; see section 3 |

No predecessor NO-GO is contradicted here: 724's corrected scope already
said "limit", and this brief's `ω ∈ˢ γ` is weaker than "limit".

## 1. WHAT WAS BUILT

1. The counterexample objects (`Probe730.agda:86-110`): `γ₂ = sucV (sucV ω)`
   with its `IsOrd` and `ω ∈ˢ γ₂`; the carrier `A := Lset (sucV ω)` as an
   `S`, constructible by `isL-Lset`, sitting in `Lset γ₂` by the sealed
   zeroth instance (`𝒟ₒ-intro` at `⊤̇`, renamed by `Lset-suc`), and
   holding ω by `ord∈Lset-suc`.
2. The obligation's TYPE, stated with no inhabitant
   (`Probe730.agda:116`), glyphs verbatim except the V-level membership
   renamed `∈ˢᵥ` against the CS-level bare `∈ˢ`, the 725-SPLIT
   disambiguation.
3. The membrane (`Probe730.agda:134-206`, exported at :208): from the
   conclusion at `(γ₂, A, 1)` it derives `⊥`. Four `rank-mono` links
   (`src/L/Rank.lagda.md:117`) climb from `rank ω` to the rank of
   `envSet A 1` (ω into the unordered pair by `pair-spec`
   `src/V/Model.lagda.md:91`, the pair into the Kuratowski pair, that
   into the environment by the concrete `env` entry, the environment
   into `envSet A 1` by the landed `envSet-in`
   `src/L/Coding/EnvSet.lagda.md:381`); `rank-Lset`
   (`src/L/Ordinal/Stages.lagda.md:190`) pins the last rank inside γ₂;
   the two successors peel by `∈sucV-elim` (`src/V/Model.lagda.md:218`);
   four descents run on the transitivity of ω (`ω-ord`,
   `src/L/Ordinal.lagda.md:263`); `rank-fix` (`src/L/Rank.lagda.md:191`)
   and `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`) close. Every lemma is
   landed. Nothing is postulated, the file carries `--safe`, and there
   is no hole.

## 2. THE FLOOR AND THE RUNS

Per the heavy-object rule the floor was priced first: p-3 is the whole
frame, the import cone of `L.Coding.EnvSet`, `L.Ordinal.Stages` and
`L.Rank`, plus the counterexample objects and the stated type, with the
membrane absent. It is green at 1.66 s, so the frame is not the cost.
p-10 is the verdict run on the delivered bytes. One Agda process per
run, GHCRTS `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and never touched here. Peak RSS is instrumented
(`/usr/bin/time -l`). No heap wall was met: the largest peak,
334,659,584 B (p-6), is 15.6 percent of the 2,147,483,648-byte wide
cap. No run timed out. No failing run was repeated unchanged; p-9 was
an ineffective fix (a `zero` ambiguity that was not the meta's cause)
and was replaced in p-10, which changed the term: the numerals are
written as literals, `# 0`, and the fiber index is a renamed `fzero`,
so `toℕ`'s implicit index has no meta to block.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 | 1.62 s | 330,416,128 | scope error: `_∈_` not imported |
| p-2 | 1.64 s | 332,005,376 | `hA`: `subst` along `Lset-suc` ran the wrong way |
| p-3 | 1.66 s | 332,152,832 | **EXIT=0, the FLOOR** (frame + objects + stated type, membrane absent) |
| p-4 | 1.30 s | 334,462,976 | `f'` scaffolding removed; its `Fin` was not the `Fin` of `Ix` |
| p-5 | 1.59 s | 334,610,432 | the Ω-⊔ is the truncated sum; witnesses wrapped in `∣_∣₁` |
| p-6 | 1.34 s | 334,659,584 | `subst` direction in the `y ≡ ω` branches |
| p-7 | 1.28 s | 334,643,200 | chain nesting off by one: `toω` consumes `r3`, not `r4` |
| p-8 | 1.66 s | 334,446,592 | unsolved metas: `toℕ`'s implicit index |
| p-9 | 1.33 s | 334,413,824 | ineffective fix: hid Prelude's `zero`; the metas stayed |
| p-10 | 1.61 s | 334,626,816 | green; one stale comment name (`f'`) removed after re-read |
| p-11 (verdict) | **1.66 s** | **334,692,352** | **EXIT=0, green, delivered bytes** |

The probe is a raw `.agda` file, so it carries no fence, counts 0
in-fence lines, and the ratio bar cannot fire on it. This report and
the review carry no `agda` fence either.

## 3. WHERE THE SHAPE RESISTED

The shape did not resist; the STATEMENT was the problem, and D-10
caught it before any proof was priced. Two things were checked and are
NOT the wall:

1. `stageFor`'s opaque bound is not the obstruction. The brief's premise
   3 names the ambient `amb A n = LsetS βₙ oβₙ` with `βₙ` from
   `stageFor`. The refutation never unfolds `envSet` or `amb`; it reads
   only `envSet-in` (`src/L/Coding/EnvSet.lagda.md:381`), which is true
   for every member. Any GO proof would still have to clear the
   opacity, but the falsity stands without touching it.
2. The headroom arithmetic is not missing; it is FALSE at this scope.
   `ω ∈ˢ γ` gives `γ` a member, not a successor-closed tail. At
   `γ = ω+2` the pair that records a member of stage ω costs
   `sucV (sucV _)` above the merge stage (`pr∈Lset-suc`,
   `src/L/Axioms/Basic.lagda.md:596`), and `envSet-in` forces the set to
   sit above that pair. No route can close what `∈-irrefl` refutes.

## 4. W3 ANSWER

The brief's W3: whether `envSet A n` sits in `LsetS γ oγ` at `ω ≤ γ`,
estimated 40 to 100 lines. Answer: **NO at `ω ∈ˢ γ` alone, machine
checked.** The refutation cost 50 lines of probe against a 21-line
frame, and every line is a landed reading. The successor height the
GO needs is stated in the review's corrected target: a limit `γ ≥ ω`,
or the landed `closedω` shape (`src/L/Ordinal/StageArith.lagda.md:81`,
with `boundCloses` :86 and `envCloses` :92 already lifting members of
`Lset (+ω δ)` and `Lset (sucIter 3 δ)` into `Lset α`), or a
per-instance rank hypothesis. Price the GO after the ruling, not
before.

## 5. W2 ANSWER

The delivered mathematics is stated once and instantiated once: the
helpers `transω`, `toω` and `descend` are generic in their two sets,
and the chain is the single instance `(γ₂, A, 1)`. No sibling proof is
duplicated. The GO side is not built here, so W2's instantiate rule
binds nothing else in this dispatch.

## 6. WHAT THE NEXT BRIEF NEEDS

1. Rule the corrected scope first: limit `γ ≥ ω`, `closedω γ`, or a
   rank hypothesis with finite headroom. The review names the three
   shapes; the landed `StageArith` kit (`src/L/Ordinal/StageArith.lagda.md`)
   already carries the closure reading for the second.
2. C-42 sweep before any GO price on the siblings: this refutation
   measures ONE site. `keyS-in-carrier-stage` ([LJ-1.729]) and the
   `Sat` bound, the other two sites of the 725-SPLIT missing-bound note
   (`agents/tasks/LJ-1-725-SPLIT/lj-1.725-SPLIT-report.md:111`), must be
   priced against the same witness shape, a carrier holding ω at
   `γ = ω+2`, before any brief funds them at `ω ∈ˢ γ`. The sweep
   reports the COUNT first; the cure is not funded against one site.
3. Do not re-fund `envSet-in`, `rank-mono`, `rank-Lset`, `∈sucV-elim`,
   `ω-ord`, `rank-fix` or `∈-irrefl`: all seven are landed and green,
   and this probe is their assembly.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not read. This
return is a refutation assembled entirely from in-tree lemmas; its
lineage came through the brief's own premises and the 724 and 725-SPLIT
reports named there, so the archive corpora had no question to answer.

- archive/dev/DD-archived.md: declined, not read; no design decision
  bears on a machine-checked counterexample built from landed lemmas.
- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history does not touch the membrane.
- archive/dev/PLAN-archived.md: declined, not read; retired plans name
  no environment-set obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  lives in `dev/pod/screen.toml`, and this task's history is in its own
  runs directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  reports this task needed (LJ-1.724, LJ-1.725-SPLIT) are live files
  named by the brief and were read at the paths cited in section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
refutation quotes no book: every step is an in-tree lemma cited at
`file:line` in sections 1 and 3.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  terminology review names no stage arithmetic.
- dev/literature/devlin-errata.md: declined, not used; it collects the
  rud-route error classes (its own header), and this refutation is
  in-tree verification, not a do-not-repeat checklist item.
- dev/literature/primary-sources.md: declined, not used; no primary
  source is quoted in this return.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  level formula plays no part in the environment-set membrane.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source beyond
  the tree was consulted for this dispatch.
