# LJ-1.437 report: the truncated square law with no hypothesis

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-437/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-437/Probe437.agda`, at a GENERIC
band, with NO module hypothesis:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-437/Probe437.agda:345-348`,
exit 0, median 1.91 s on three forced rechecks) and it PASSes the program's
witness meter (`scripts/pod/witness.py --code LJ-1-437 --brief
agents/tasks/LJ-1-437/LJ-1.437.md`, exit 0, 1.64 s, 0 UNRESOLVED of 1,
`probe_red=False`). The file has no inner hypothesis module.

The term's telescope is `(δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁`
(`Probe437.agda:345-348`), under the module parameters `{ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀)`
(`Probe437.agda:35-36`) and nothing else.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict.

## 0. D-10, before any Agda

`[LJ-1.407]` is GO (`agents/tasks/LJ-1-407/lj-1.407-report.md:18`).
`[LJ-1.406]` is GO (`agents/tasks/LJ-1-406/lj-1.406-report.md:13`). Neither
report names the statement FALSE. Neither is NO-GO. The predecessor types
are taken from the probes that typechecked.

**The type of `[LJ-1.407]`'s bare hypothesis**
(`agents/tasks/LJ-1-407/Probe407.agda:204-209`):

```agda
  (init-at-kappa :
      (a : S) (oa : IsOrd (fst a))
    → ⟨ ω ∈ˢ fst (κL a oa) ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
         → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
    → Init (fst (κL a oa)))
```

**The type of `[LJ-1.406]`'s obligation**
(`agents/tasks/LJ-1-406/Probe406.agda:180-185`):

```agda
init-at-kappa :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst (κL a oa) ⟩
  → (ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
        → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
  → Init (fst (κL a oa))
```

Projection for projection:

| # | 407 hypothesis | 406 obligation | same? |
|---|---|---|---|
| 1 | `(a : S)` | `(a : S)` | yes |
| 2 | `(oa : IsOrd (fst a))` | `(oa : IsOrd (fst a))` | yes |
| 3 | `⟨ ω ∈ˢ fst (κL a oa) ⟩` | `⟨ ω ∈ˢ fst (κL a oa) ⟩` | yes |
| 4 | `(β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩ → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁` | the same, binder named `ih` | yes |
| 5 | `Init (fst (κL a oa))` | `Init (fst (κL a oa))` | yes |

The binder name `ih` is not a type. The 407 wrapping is a module parameter
(`Probe407.agda:203-210`) and the 406 wrapping is a definition
(`Probe406.agda:180-190`). That is packaging. The types are the same. I did
not stop. I did not weaken either type.

## 1. What was built

All in `agents/tasks/LJ-1-437/Probe437.agda`, module
`LJ-1-437.Probe437 {ℓ} (lem) (α₀) (oα₀)` (`:35-36`). No inner hypothesis
module. I did not import `LJ-1-406.Probe406` or `LJ-1-407.Probe407`. A probe
is not a library. I copied the text.

**Copied from `[LJ-1.406]` (`Probe406.agda`):**

- `isL-ord` (`Probe406.agda:59-61` → `Probe437.agda:68-69`)
- `comp-inj` (`Probe406.agda:64-66` → `:72-74`)
- `inf-member` (`Probe406.agda:69-70` → `:77-78`)
- `κL`, `κoL`, `κ-injL`, `κ-min-atL` (`Probe406.agda:81-95` → `:91-107`)
- `clause4-at-kappa` (`Probe406.agda:103-122` → `:114`)
- `Shiftω`, `shift-at`, `kappa-limit` (`Probe406.agda:131-172` → the same
  three names in `Probe437.agda` after `clause4-at-kappa`)
- `init-at-kappa` as a DEFINITION (`Probe406.agda:180-190` → `:184-194`)

**Copied from `[LJ-1.407]` (`Probe407.agda`):**

- module parameters `α₀` `oα₀` (`Probe407.agda:32-33` → `:35-36`)
- `κ∈sucL` (`Probe407.agda:105-106` → `:97-98`)
- `mem-incl` (`Probe407.agda:70-83` → `:203`)
- `kappa-not-fin` (`Probe407.agda:117-133`)
- `kappa-decides` (`Probe407.agda:140-162`)
- `descent-core` (`Probe407.agda:169-189`)
- `band-ord` (`Probe407.agda:193-196`)
- `Goal`, `step`, and `sq-trunc` renamed `sq-trunc-closed`
  (`Probe407.agda:214-265` → `:297-348`)

The hypothesis module header at `Probe407.agda:203-210` is deleted.
`init-at-kappa` now resolves to the definition at `:184-194`.

ONE opaque block (`:90-107`) carries the FIVE projections: `κL`, `κoL`,
`κ∈sucL`, `κ-injL`, `κ-min-atL`. `[LJ-1.406]` sealed four without `κ∈sucL`
(`Probe406.agda:81-95`). `[LJ-1.407]` sealed four without `κ-min-atL`
(`Probe407.agda:98-109`).

237 non-blank non-comment lines. The estimate was about 240, a comparable of
SHAPE. Nothing is funded against the estimate.

## 2. W3: the shared seal, first

**GO.** The widest unmeasured term was the shared five-projection seal, because
`[LJ-1.406]` proved `init-at-kappa` against a seal that did not include
`κ∈sucL` and `[LJ-1.407]` proved its cases against a seal that did not
include `κ-min-atL`. The probe is the file written down to `init-at-kappa`
(`Probe437.agda:184-194`), with `Goal`, `step` and `sq-trunc-closed` omitted.

Three forced rechecks, probe interface deleted, dependencies warm, caliber
`-A64m -I0 -M8g`, one Agda process. Each printed `Checking`. Exit 0 every
time. No heap event.

| run | wall s | peak RSS bytes | log |
|---|---|---|---|
| 1 | 2.02 | 425885696 | `runs/w3-1.out` / `w3-1.time` |
| 2 | 1.72 | 425902080 | `runs/w3-2.out` / `w3-2.time` |
| 3 | 1.72 | 425902080 | `runs/w3-3.out` / `w3-3.time` |

Median wall **1.72 s**. Median peak RSS **425902080 bytes**. The elaborator
did not refuse the five-projection block.

## 3. The joined obligation

`sq-trunc-closed` (`:345-348`) is `∈-induction` at motive `Goal` (`:297-298`).
The four cases of `step` (`:300-343`) are the four cases `[LJ-1.407]` already
closed (`lj-1.407-report.md:76-81`). The descent case is still `PT.map2`
(`:336-339`). The positive case still spends `init-at-kappa` as data, now
the definition at `:184-194`, and then `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`). Nothing untruncates.

The shape did not resist. I did not weaken a type. I did not add a
hypothesis.

## 4. W2 and DD4

The module is generic in `ℓ` and in `α₀`. Every term quantifies over a
generic carrier. No numeral and no site is named except `ω`, which both
predecessors already put in the same places. The mathematics is written
once at that carrier. There is no fixed form to report.

W4 does not fire: no module was retired.

## 5. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before each timed run
(`_build/2.8.0/agda/agents/tasks/LJ-1-437/Probe437.agdai`).

- W3 alone, three forced rechecks: 2.02 s, 1.72 s, 1.72 s. Median
  **1.72 s**. Median peak RSS **425902080 bytes**. Exit 0 every time.
  Each printed `Checking`.
- Full file, first check after the recursion landed: 1.92 s, peak RSS
  439599104 bytes, exit 0, printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks: 1.90 s, 1.91 s, 1.94 s. Median
  **1.91 s**. Peak RSS 439599104, 439648256, 439566336 bytes. Median
  peak RSS **439599104 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, the one obligation: PASS, exit 0, 1.64 s, 0 UNRESOLVED
  of 1, `probe_red=False`. `.venv/bin/python` is absent in this worktree.
  The meter ran under `python3` (3.14.7). I added no dependency.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event.

`[LJ-1.406]` measured a median of 1.80 s at 117 code lines
(`lj-1.406-report.md:153-154`). `[LJ-1.407]` measured a median of 1.77 s
at 176 (`lj-1.407-report.md:145-146`). The joined file measured a median
of 1.91 s at 237 code lines. The next brief prices a `src/` landing
against 1.91 s, not against an estimate.

## 6. What GO earns

**A GO closes the supply side.** The truncated square law holds at every
infinite band ordinal with an empty hypothesis telescope. The next brief
that wants this law in `src/` can cite one term,
`agents/tasks/LJ-1-437/Probe437.agda:345-348`, whose module parameters are
`{ℓ} (lem) (α₀) (oα₀)` and whose own telescope is
`(δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁`.

## WHAT THIS DOES NOT MEASURE

This task closes the SUPPLY of the truncated square law. It measures
nothing about the CONSUMER. The consumer's module parameter is the
untruncated Sigma today (`src/L/StageCardinal.lagda.md:17-19`):

```agda
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where
```

`[LJ-1.434]`, `[LJ-1.435]` and `[LJ-1.436]` are the tasks that measure the
consumer. I did not open those three tasks. I did not import their probes.
I did not copy a type out of their briefs.

This task also does not untruncate `κ-inj`. The injection stays truncated
(`src/L/Cardinal.lagda.md:132-133`). It does not prove `⟨ ω ∈ˢ fst (κL a oa) ⟩`.
That remains a hypothesis of `init-at-kappa`, because `[LJ-1.404]` refuted
it as a theorem.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not import `Probe406`. I did not import `Probe407`.
- I did not write `review-of-sq-trunc-closed.md`. The join is GO.
- I did not add a consumer-match term. C-42 keeps the consumer out of this
  measurement.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: named, not used. Opened at the head
  (`archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18").
  A search in that file for `truncated square`, `sq-trunc` and `init-at-kappa`
  returned nothing. This task is a live join of two LJ-1 probes, not a
  row from the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The bound that entry named is the law this probe now supplies in truncated
  form, with an empty hypothesis telescope.
- `archive/dev/JOURNAL.md`: named, not used. Opened at the head
  (`archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20"). The per-episode
  journal is retired. This task's record is the probe and this report.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**,". Read to resolve the injected archive paths.
  W4 does not fire: no module was retired.
- `archive/dev/ORCHESTRATION.md`: named, not used. Opened at the head
  (`archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules").
  This task is a probe join. It does not consult the archived orchestrator
  rules.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  The join spends a truncated injection and a truncated square. It does not
  untruncate either.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that
  only needs cardinal arithmetic never needs an injection as". The four
  cases of `step` never take an injection as data.
- `dev/literature/terms-2026-08.md`: named, not used. Opened at the head
  (`dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling").
  No glossary work in this task.
- `dev/literature/devlin-II5.md`: named, not used. Opened at the head
  (`dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L").
  The join copies two delivered probes. No step consults a condensation
  argument.
- `dev/literature/digest.md`: named, not used. Opened at the head
  (`dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature").
  This task is the L-band truncated law, not the rud-route architecture.
- `dev/literature/geology.md`: named, not used. Opened at the head
  (`dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions").
  Geology is not this join.
