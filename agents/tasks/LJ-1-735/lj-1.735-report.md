# LJ-1.735 report: `envSet-in-carrier-lim`, the environment set under the carrier's closure

(This skeleton was written before the first Agda run and filled as the
runs landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.735
obligation: agents/tasks/LJ-1-735/Probe735.agda::envSet-in-carrier-lim
verdict: **GO.** The obligation is INHABITED:
`envSet-in-carrier-lim` (`agents/tasks/LJ-1-735/Probe735.agda:65`,
term at :71-124) typechecks at EXIT=0 (`runs/p-6.out`), 1.74 s wall,
401,096,704 B peak, under `--cubical --safe --guardedness`, no
postulate and no hole. The route is one landed supply-side lemma plus
a 30-line consumer: `envSetNumeral∈`
(`src/L/Coding/Key.lagda.md:486-489`) already places
`envSet B n` at `Lset (sucIter 4 σ)` from `ω ∈ σ` and
`fst B ∈ Lset σ`; the probe merges the carrier's stage with `ω`
(`ord-tri`), runs the bound at `+ω m`, and absorbs the iterate by
`+ω-iter 4` and `closedω γ`. `envSet-in-carrier-stage` (the 730 name)
appears in a comment only: not stated, not inhabited, no postulate
under it. Nothing lands in `src/`.

## 0. THE PREDECESSOR QUESTION

| piece | taken from | verdict there | use here |
|---|---|---|---|
| the corrected target | the brief's premise 2, `agents/tasks/LJ-1-730/review-of-envSet-in-carrier-stage.md` (section "The corrected target, for ruling", option 2) | 730 NO-GO on `ω ∈ˢ γ` alone; `closedω γ` named as the landed closure shape | this brief Ruled option 2; the obligation carries `clγ : closedω γ` and the probe inhabits exactly that scope |
| the falsity of the old scope | the brief's premise 1, `agents/tasks/LJ-1-730/lj-1.730-report.md:13` | 730 NO-GO, machine-checked at `γ = sucV (sucV ω)` | the counterexample site is EXCLUDED under `closedω` (see the review, section 2); no conflict with the GO |
| the landed bound | the brief's neighbour task 731, `agents/tasks/LJ-1-731/review-of-Sat-in-carrier-stage.md` (section 4, last sentence) | 731 NO-GO on its own type; the review NAMES `envSetNumeral∈` (`src/L/Coding/Key.lagda.md:486-489`) as the landed supply-side bound for `envSet B n` | the whole placement route; the probe consumes it and funds nothing twice |
| the merge pattern | `agents/tasks/LJ-1-729/Probe729.agda` (the `step`/`close` helper over `ord-tri`) | 729 GO on `keyS-in-carrier-lim` | reused as shape: `Lset-out` for the carrier's stage, trichotomy against `ω`, one generic close |

No predecessor NO-GO is contradicted: 730's refutation measures the
site `ω ∈ˢ γ` alone, and this GO lives strictly above it.

## 1. WHAT WAS BUILT

1. The stage of the carrier (`Probe735.agda:78-83`): from `hA` the
   landed `Lset-out` untruncates `δ ∈ˢᵥ γ` with
   `fst A ∈ˢᵥ 𝒟ₒ (Lset δ)`; `Lset-suc δ` renames that to
   `fst A ∈ Lset (sucV δ)`. `oδ` is `mem-ord {A = γ} oγ δ δ∈γ`, the
   implicit given EXPLICITLY (measured, section 3 item 2).
2. The close, WRITTEN ONCE (`Probe735.agda:89-99`, W2): for any
   `m ∈ˢᵥ γ` with `ω ∈ˢᵥ +ω m` and `sucV δ ∈ˢᵥ +ω m`,
   `envSetNumeral∈ (+ω m) (+ω-ord m om) ω∈+ωm A n hB` lands
   `envSet A n` at `Lset (sucIter 4 (+ω m))`; `+ω-iter 4 (+ω m)`
   lifts into `+ω (+ω m)`; `clγ (+ω m) (clγ m m∈γ)` absorbs into
   `γ`. Two `Lset-mono` links. The conclusion's L-structure glyph
   matches definitionally (`𝒮ʟ`'s membership is `fst a ∈ˢᵥ fst b`).
3. The trichotomy cases (`Probe735.agda:101-124`): `ω ∈ˢᵥ δ` runs
   `m := δ`, with `ω ∈ˢᵥ +ω δ` by the transitivity field of
   `+ω-ord δ oδ` and `+ω-mem δ`, and `sucV δ ∈ˢᵥ +ω δ` by
   `+ω-iter 1 δ`. The two upper cases run `m := ω`: equality by
   `subst` along `ω≡δ` applied to `+ω-iter 1 ω`, and `δ ∈ˢᵥ ω` by
   `suc∈or≡` plus `+ω-sup ω`.

## 2. THE FLOOR, AND THE RUNS

Per the heavy-object rule the floor was priced: the floor harness is
the delivered file's import block, structure opens and a trivial
`refl` definition, with the obligation absent. It is green at 1.75 s,
408,387,584 B (floor recipe and logs in `runs/p-8-floor.*`; the
harness file itself is not kept, this section is its record). The
frame IS the whole cost: the delivered file's own rows add nothing
measurable, so there was nothing to trim. No heap wall was met: the
largest peak, 410,370,048 B (p-4), is 19.1 percent of the
2,147,483,648-byte wide cap. No run timed out. No failing run was
repeated unchanged.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 | 1.74 s | 408,354,816 | name typo: the landed lemma is `envSetNumeral∈` with the glyph, not `envSetNumeralin` |
| p-2 | 1.82 s | 409,911,296 | a `where` block under a `Tri` split pattern leaves metas; sub-case proofs hoisted to named helpers |
| p-3 | 1.78 s | 409,976,832 | `subst` direction in the equality case: `ω≡δ : ω ≡ δ` is already the right way, the `sym` was wrong |
| p-4 | 1.85 s | 410,370,048 | `mem-ord`'s implicit does not solve through `IsOrd`; given as `{A = γ}`, the 729 usage |
| p-5 | 0.27 s | 182,648,832 | runner artifact: `time: signal: Invalid argument`, no Agda output; direct run of the same bytes passed (729's protocol) |
| p-5b (direct) | - | - | EXIT=0, green, same bytes as p-4 |
| p-6 (verdict) | **1.74 s** | **401,096,704** | **EXIT=0, green, delivered bytes** |
| p-9 (confirm) | 1.73 s | 401,080,320 | EXIT=0, re-run of the delivered bytes after the report was filled |
| floor p-7, p-8 | 0.66 / 1.75 s | 252,477,440 / 408,387,584 | two harness parse slips, then the green floor |

The probe is a raw `.agda` file, so it carries no fence and counts 0
in-fence lines, and the ratio bar cannot fire on it.

## 3. WHERE THE SHAPE RESISTED

1. The shape did not resist; the work was ALREADY LANDED. The direct
   route this probe first priced (carving a bounded description at a
   stage of my own with `AtStage.separateAt`) is IMPOSSIBLE for
   `envFo`: the description's clauses carry unbounded quantifiers
   (`svAt` is built on `∀̇`, `domAt` on `∃̇` via `inDomAt`,
   `src/L/Coding/Model.lagda.md:210,269`), so no `Δ₀` certificate
   exists, and `hasSeparationL`'s reflection places its carve at an
   opaque stage. The route that closed needed NO new carve:
   `envSetNumeral∈`'s own internals (a bounded carrier description,
   the carve, the join by `extensionalV`) are the placement proof,
   paid once in `src/`. The consumer owes only the merge and the
   absorption.
2. `mem-ord`'s implicit `A` does not solve through the defined
   `IsOrd`; the constraints stay blocked on the meta. Measured at
   p-4; the cure is the explicit `{A = γ}`, which is how `Stages`
   and the 729 probe both call it.
3. The p-5 runner artifact is the same `time: signal: Invalid
   argument` 729 recorded; the mechanism was handled by 729's
   protocol, a direct run of identical bytes between the
   instrumented attempts.

## 4. W3 ANSWER

The brief's W3: whether `envSet A n` sits in `LsetS γ oγ` at
`closedω γ`, estimated 40 to 120 lines. Answer: **GO, and the
estimate held on the consumer side.** The delivered probe is 124
lines, 110 non-blank, raw `.agda`. The placement burden the estimate
would have covered at 730's NO-GO is not in this file at all: it is
about 230 lines of landed machinery (the `Land` module and
`envSetNumeral∈`, `src/L/Coding/Key.lagda.md:420-489`). A brief that
prices a sibling bound should read Key's `Land` module first, not
re-estimate the placement.

## 5. W2 ANSWER

The close is stated ONCE at a generic stage `m` (`Probe735.agda:104`)
and instantiated three times (`m := δ`, `m := ω` twice). The probe
duplicates no sibling: 729's CodeSet climb is orthogonal (keys are
recursion products; environment sets are separation instances whose
placement is landed), and no landed reading is re-derived inside the
probe. No deadline forced a fixed form.

## 6. WHAT THE NEXT BRIEF NEEDS

1. The `Sat` sibling (731's corrected target) may now be re-briefed
   against a supply-side fact that has moved: step 1 of that review's
   route (`untruncate a stage δ ∈ γ with envSet A n definable over
   Lset δ`) is no longer needed, because `envSetNumeral∈` hands the
   concrete stage `sucIter 4 (+ω m)` directly. Price the Sat bound
   from the 731 review's own estimate (250 to 450 lines), with this
   GO as its step-0.
2. Fund no move into `src/`: everything this GO consumes is already
   landed. The only new mathematics this dispatch produced is the
   30-line consumer, and it lives in the probe until a second
   consumer needs it.
3. Do not re-fund `envSetNumeral∈`, `Lset-suc`, `Lset-out`,
   `+ω-iter`, `+ω-mem`, `+ω-sup`, `+ω-ord`, `suc∈or≡`, `mem-ord` or
   `ord-tri`: all are landed and green, and this probe is their
   assembly.
4. C-42 note: this GO measures ONE site under `closedω`. The three
   725-SPLIT missing-bound sites now stand at: keys GO (729),
   environment sets GO (here), `Sat` unpriced. The sweep count is
   two of three before any cure brief.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not read. This
return assembles landed in-tree lemmas; its lineage came through the
brief's own premises and the live 729, 730 and 731 task files named
in section 0, so the archive corpora had no question to answer.

- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  retired operating rules do not touch an inhabited bound.
- archive/dev/DD-archived.md: declined, not read; the closed DD
  series is history, and this dispatch answers to the live slot file
  and brief alone.
- archive/dev/PLAN-archived.md: declined, not read; retired plans
  name no environment-set obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  lives in `dev/pod/screen.toml`, and this task's history is in its
  own runs directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  files this task needed (LJ-1.729, LJ-1.730, LJ-1.731) are live
  files named by the brief and cited at `file:line` in section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
GO is an assembly of landed lemmas; every step is cited at
`file:line` in sections 1 and 3, and no source beyond the tree was
consulted.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  raw `.agda` probe and its records carry no translation surface.
- dev/literature/primary-sources.md: declined, not used; no primary
  source is quoted in this return.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  slot census belongs to the graph tasks and plays no part in this
  bound.
- dev/literature/devlin-errata.md: declined, not used; the errata
  collects rud-route error classes, and this route touches no rud.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source
  beyond the tree was consulted for this dispatch.
