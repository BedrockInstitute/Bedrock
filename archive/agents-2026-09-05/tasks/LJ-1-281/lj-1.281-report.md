# LJ-1.281 report: probe R-35 against A1's 98 seconds

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe task. No
master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**The control, measured by me: A1 alone is 100.50 s cold (mean of four kept
runs, load 5.0 to 7.9). A reversed bracket of three more runs gives 97.40 s
(load 3.7 to 6.0).** This reproduces `[LJ-1.278]`'s 98.24 s and
`[LJ-1.232]`'s 100.3 s. MEASURED.

**The localized term: `κ-min-at` at `src/L/Cardinal.lagda.md:125-138`.** It
carries 85 of the 100 s. The root is the transparent well-order
`w = ordSWO (sucV (fst α))` at `src/L/Cardinal.lagda.md:86`, which unfolds in
the selection `least = leastOf w` (line 102) and then RE-unfolds inside
`κ-min-at`'s conversion checks (lines 129 to 138). The selection itself is
cheap; the re-unfolding is the 85 s.

**Both cures work. The opacity cure is cheaper than the R-35 cure.**

| arm | what changed | cold s (mean kept) | load |
|---|---:|---:|---:|
| control | A1 as landed | **100.50** | 5.0-7.9 |
| TreatedSmall | R-35: delete `κ-min-at`, keep small-index `κ-min` | **15.53** | 6.1-7.6 |
| TreatedParam | `κ-min-at` with `b`,`bδ` as parameters, no fiber | **34.29** | 6.2-6.9 |
| TreatedOpaque | seal `w` opaque, one read lemma `w-lt` | **9.16** | 4.9-5.3 |

**The R-35 cure works: 100.50 to 15.53 s, a delta of 85 s.** MEASURED.

**The opacity cure works better: 100.50 to 9.16 s, a delta of 91 s.**
MEASURED. This is the cheaper cure the brief asked to hear first.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No heap
exhaustion. No run past 30 minutes. No kill. Load is the one-minute average
at the start of each run. The probe's own interface under
`_build/2.8.0/agda/agents/tasks/LJ-1-281/` is deleted before every kept run.
Delivered master interfaces stay cached. No sibling agda ran during the kept
runs (`ps` shows none).

The four probe files:

- `ControlA1.agda` = A1 verbatim from `src/L/Cardinal.lagda.md`, module
  renamed. 108 non-blank lines.
- `TreatedSmall.agda` = control minus `κ-min-at`. 94 non-blank lines.
- `TreatedParam.agda` = control with `κ-min-at` restated so `b` and `bδ` are
  parameters, no fiber extraction. 103 non-blank lines.
- `TreatedOpaque.agda` = control with `w` sealed `opaque` and one read lemma
  `w-lt`. 115 non-blank lines.

All four typecheck green, `--safe`, exit 0. `lint-agda.py --check` exits 0 on
all four.

## 2. THE CONTROL, MEASURED BY ME

`ControlA1.agda`, A1 alone, cold.

| run | exit | cold/warm | elapsed s | load |
|---|---|---:|---:|---:|
| warm-up (discarded) | 0 | cold | 98.86 | 5.83 |
| kept 1 | 0 | cold | 101.28 | 6.99 |
| kept 2 | 0 | cold | 100.32 | 5.05 |
| kept 3 | 0 | cold | 99.87 | 5.80 |
| kept 4 | 0 | cold | 100.53 | 7.89 |

Mean of the four kept runs: **100.50 s**, range 99.87 to 101.28 s.

Reversed bracket, run after the treated arms to check drift:

| run | elapsed s | load |
|---|---:|---:|
| control again 1 | 97.28 | 3.66 |
| control again 2 | 97.14 | 4.39 |
| control again 3 | 97.78 | 5.96 |

Mean 97.40 s at the lower load. The control is load-sensitive around 97 to
101 s. The treated arms do not move with load. The deltas below are robust.

## 3. THE LOCALIZATION

**`κ-min-at` carries the 98 seconds.** `src/L/Cardinal.lagda.md:125-138`.
Removing it drops the file from 100.50 s to 15.53 s. MEASURED by bisection.

`--profile=internal` on the control agrees. It shows
`Typing.CheckRHS = 90.7 s` of the 100.8 s total. The cost is in the bodies,
not in the signatures. MEASURED.

**The root is `w`'s transparency, not the fiber extraction.** My first
bisection attributed 66 s to the fiber extraction. That attribution was
WRONG. The opacity arm refutes it. Here is the corrected story.

The selection `least = leastOf w lem InjP' nonempty` at line 102 unfolds the
transparent `w = ordSWO (sucV (fst α))` at line 86. The file without
`κ-min-at`, selection included, costs about 15 s. That is the once payment.
Then `κ-min-at`'s body needs two conversions. Both force `fst κ`
to re-unfold the selection. `fst κ` is `⟪ sucV (fst α) ⟫↪ γ-card` where
`γ-card = fst (leastOf w ...)`. The comparison `b<γ` at lines 137 to 138 must
convert `⟨ ⟪ sucV (fst α) ⟫↪ b ∈ˢ fst κ ⟩` to the transparent comparison
`SWO._<∙_ w b γ-card`. That conversion re-runs the `leastOf` selection over
the union representation `⟪ sucV (fst α) ⟫`. The fiber equality `bδ` at line
134 feeds the same re-unfolding through `sym bδ`.

Proof of the root: seal `w` opaque. Then `leastOf w` is a stuck atom. Then
`fst κ` and `γ-card` never re-unfold. Then `κ-min-at`'s conversions become
syntactic matching. The whole file drops to 9.16 s. MEASURED.

**This is the P-l body-bound disease, class (1) of P-i: a heavy set forced
into normalization by a conversion check.** It matches
`[L3.32-T154]`'s verdict for R-40, where R-35's index-extraction mechanism
was ruled out but the small-index cure shape was the cure. The fiber
extraction is cheap by itself. The transparent comparison is the cost.

## 4. THE TREATED ARMS

**Arm 1, the R-35 cure.** State the membership at the small index. The
small-index form of `κ-min-at` is `κ-min` itself, at
`src/L/Cardinal.lagda.md:121-123`. `TreatedSmall.agda` deletes `κ-min-at` and
keeps `κ-min` as the export.

| run | elapsed s | load |
|---|---:|---:|
| warm-up (discarded) | 16.15 | 8.40 |
| kept 1 | 15.74 | 7.61 |
| kept 2 | 15.40 | 6.86 |
| kept 3 | 15.45 | 6.88 |
| reversed kept | 15.12 | 6.05 |

Mean **15.53 s** (three kept). The reversed run is 15.12 s. Delta from control: **84.97 s**.

**Arm 2, the opacity cure.** Seal `w` opaque. Add one read lemma `w-lt` that
unfolds the comparison once, inside the seal. Keep `κ-min-at` full, with the
fiber extraction. `TreatedOpaque.agda`.

| run | elapsed s | load |
|---|---:|---:|
| warm-up (discarded) | 9.35 | 5.26 |
| kept 1 | 9.55 | 5.26 |
| kept 2 | 8.89 | 5.15 |
| kept 3 | 9.05 | 4.90 |
| reversed kept 1 | 8.86 | 4.06 |
| reversed kept 2 | 8.94 | 6.21 |

Mean **9.16 s** (three kept). The two reversed runs are 8.86 s and 8.94 s. Delta from control: **91.34 s**.

**Arm 3, a control for the split.** `TreatedParam.agda` keeps `κ-min-at` but
takes `b` and `bδ` as parameters. It removes only the fiber extraction. Mean
**34.29 s** (three kept). This isolates the fiber-plus-transparency
interaction at 66 s in the transparent setting, and it is the arm the opacity
arm refutes as the wrong attribution.

**The within-series paired design.** The control ran first, then the three
treated arms, then a reversed bracket: control, TreatedOpaque, control,
TreatedSmall, TreatedOpaque, control. The reversed bracket reproduces every
figure. No arm depends on run order.

## 5. PREMISES, MARKED

- **VERIFIED. A1 alone costs about 98 s cold.** My control: 100.50 s at load
  5.0 to 7.9, 97.40 s at load 3.7 to 6.0. MEASURED.
- **VERIFIED, with one correction. The cost runs through `κ-min-at`
  unfolding `⟪ sucV α ⟫`.** The load-bearing premise holds. The correction:
  the cost is not the `leastOf` selection (that is 15 s). It is the
  re-unfolding of the transparent comparison inside `κ-min-at`'s conversion
  checks. MEASURED by the opacity arm.
- **PARTLY VERIFIED. `orderAt` is opaque and A3 and A4 escape because of
  it.** Opacity IS a cure here, and it is the cheaper one. But the brief's
  mechanism is off. A1's selection is already cheap with a transparent order.
  A1's cost is in the refutation, not in the selection. MEASURED.
- **VERIFIED. R-35's cure is a hypothesis at this site, per P-l.** I
  measured it. It works. MEASURED.

## 6. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-278/lj-1.278-report.md:45-52`.** TAKEN: the bisect
  table and the 98.24 s control, which I re-derived.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md` section 5.** TAKEN: the named
  cause and the opaque `orderAt` escape.
- **`agents/tasks/LJ-1-232/lj-1.232-report.md:51`.** TAKEN: the 100.3 s
  figure and the sub-finding that A1 without `κ-min-at` is 16.9 s.
- **`dev/LESSONS.md:782-800`, R-35 whole.** TAKEN: the small-index cure and
  the appended GLp note.
- **`dev/LESSONS.md:929-944`, R-40 whole.** TAKEN: the shallow-index climb
  and the super-linear normalization law.
- **`src/L/Choice/Step.lagda.md:740-743`.** TAKEN: `orderAt` is opaque, the
  shape the opacity arm copies.
- **`agents/tasks/archive/R1B/r1b-report.md` section 4 and 5.** TAKEN: R-35's
  original site. Wall 1 was `∈-asFiber` on a membership over `⟪ y ⟫`; the fix
  was the small-index spec. The shape transfers.
- **`agents/tasks/archive/L3-32-T154/l3.32-t154-report.md:1-28`.** TAKEN:
  R-40's verdict. It rules out index extraction and names the transparent
  ordinal presentation as the disease. My finding agrees.
- **`archive/dev/TASKS-archived.md:1-10`.** TAKEN, SHAPE ONLY: the retired
  route's index. R-35's original site lives in the R1B report, not in this
  file. WHAT WOULD NOT TRANSFER: the R1B wall was an OOM on the backward
  direction of a spec; here there is no OOM, only a slow check.

## 7. LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## 8. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. A wall.** Longest run 101.28 s. No heap exhaustion. Cap
  never raised.
- **MEASURED FALSE. The control differs from the brief's 98.24 s.** My
  100.50 s and 97.40 s bracket it.
- **MEASURED FALSE. The fiber extraction is the dominant cost.** The opacity
  arm keeps the fiber and checks in 9.16 s. The fiber is cheap alone. The
  transparent comparison is the cost.
- **MEASURED FALSE. Opacity is not a cure here.** Sealing `w` drops the file
  to 9.16 s.
- **INFERRED. The R-35 cure's 85 s is a floor in the transparent setting.**
  The selection must unfold once. The restatement removes only the repeat.
- **INFERRED. The opacity cure may move cost to the consumer.** Sealing `w`
  makes `κ` and `κ-min` stuck. The consumer gets `κ-min-at` with a clean
  type, but a consumer that must compute `fst κ` would need a read lemma. I
  did not write that consumer.

## 9. WORKING TREE, AS MY REPORT DESCRIBES IT

Four probe files and this report, all in `agents/tasks/LJ-1-281/`:

- `ControlA1.agda` — green, 100.50 s cold mean.
- `TreatedSmall.agda` — green, 15.53 s cold mean.
- `TreatedParam.agda` — green, 34.29 s cold mean.
- `TreatedOpaque.agda` — green, 9.16 s cold mean.
- `lj-1.281-report.md` — this file.

No master edited. No `src/` edited. No `dev/ledger.toml`, no `dev/PLAN.md`.
No commit, no push, no `git checkout .`, stash, reset or clean. The sibling
directory `agents/tasks/LJ-1-280/` and `src/L/Choice/Name.lagda.md` were not
touched. `scripts/check-probes.py --check` exits 0.

## 10. THE DD4 ANSWER, WITH ITS AXIS

**Axis named (C-46): DD4's own axis is AC-against-GCH**, fixed at
`scripts/ledger.py:50`.

**The cure is generic, and the J tower inherits it.** `w = ordSWO (sucV
(fst α))`, `sucV`, `leastOf`, `⟪_⟫`, `fiber` and `member` are the
either-tower machinery that `[LJ-1.278]` section 7 lists as transferring
verbatim. The seal wraps `ordSWO (sucV α)`, the either-tower well-order. The
J tower's A1 would build the same `w` and apply the same seal. The 98 s is
not paid a second time.

**The R-35 restatement is also generic.** The small-index `κ-min` names only
the either-tower atoms. The deep-index `κ-min-at` is the wrapper that adds
the L-specific fiber extraction. Deleting it costs the J tower nothing.

**A1 itself stays per-tower** (`[LJ-1.227]`). The level-hood certificate
`isL`, `Lset→isL`, `ord∈Lset-suc` and `isL-trans` differ between towers. The
cure does not touch them. It touches only the either-tower `w`.

## 11. WHAT A BUILD BRIEF WOULD HAVE TO SAY

The build brief would propose sealing the well-order. The smallest change is
to make `w` opaque inside `module LeastCardInjL` and add the read lemma
`w-lt` beside it. This is the R-36 shape, applied to a definition that is
already local to the module. The consumer-facing theorem `κ-min-at` keeps a
clean type that does not name `w`. Two internal definitions, `least` and
`κ-min`, name `w` in their types; neither is what the GCH proof imports. The
file costs 9.16 s instead of 100.50 s.

The alternative is the R-35 restatement. It deletes `κ-min-at` and exports
`κ-min` only. It costs 15.53 s. It is more surgical in the module but changes
what the consumer can call. The consumer must use the small index.

The brief should price both against the consumer. If the GCH proof needs
`κ-min-at`'s deep-index form, the opacity seal keeps it and stays cheap. If
the consumer can be restated to the small index, the R-35 cure is the smaller
change. I did not write the consumer, so I mark that choice INFERRED.

## 12. THE RULES THIS CHAIN EARNED, CHECKED

- **P-l. A cure does not transfer by analogy.** I re-measured. Both cures
  held at this site, so no transplant failed here. But the premise needed a
  correction: the selection was not the cost.
- **P-t. An average hides the term.** The bisection found the term:
  `κ-min-at`, lines 125 to 138.
- **P-m. The check-cost rate is a content-class certificate.** A1's 0.93
  s/line is instantiation content, not parameterized content.
- **R-40. A deep successor-chain membership witness normalizes
  super-linearly.** The membership `fst δ ∈ˢ fst κ` forces the `sucV` union
  to normalize. The shallow-index climb is `κ-min`.
- **P-q. A line lever and a seconds lever differ.** The opacity cure adds
  seven lines and removes 91 s. The restatement removes 14 lines and removes
  85 s. Lines and seconds do not move together.
