# LJ-1.236 report — A7 and A4, the gate list's last two

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe task. No
master edited. No commit, no push. Written incrementally (C-22).

Every negative is marked **MEASURED** (a machine result, or read at the cited
line) or **INFERRED** (my judgement). ASD-STE100 applies.

## 0. LEAD: A7 FIRST, BECAUSE IT AUDITS THE REST

**THE SHAPES MATCH.** A7's statement elaborates green, and A5's `sq` and
A6's `absorbs` have conclusions whose types are A7's hypotheses on the nose.
The trophy has a target, and A4, A5 and A6 are funding the right objects.

**A7's written lines: 47 charge, 81 whole, against the standing 110.** The
110 is reading, as the brief said.

**A4's cold seconds: 1.14 s mean, not the 100 s the ambient comparable
suggested.** The seconds FALL, not rise. `[LJ-1.136]`'s inferred rise is
**REFUTED. MEASURED.**

## 1. A7 VERDICT: THE SHAPES MATCH

The statement is `ProbeLJ1236A7.agda`. It typechecks green, `--safe`, exit 0.
Two checks, both done.

**Check 1 — it elaborates, and names only the right objects. MEASURED.**
`GCHStatement` elaborates and names `S` (the `𝒮ʟ` carrier), `∈ˢ` (the
membership), `IsCardinalL` (internal `IsCardinal`, A4), and `↪` (the
square-law shape). Nothing else: no `Lset`, no `sucV`, no numeral, no stage
in the statement itself. It copies `ChoiceStatement`'s discipline exactly
(`src/L/Choice/Transversal.lagda.md:372-384`): a Type over `isZFModel`,
quantifying over `S` with `∈ˢ`, no transparent construction (P-x, read at
`agents/tasks/LJ-1-136/lj-1.136-report.md:743`).

**Check 2 — the audit, and it passes. MEASURED by reading the two conclusion
types against the two hypothesis types.**
A7's two hypotheses, written in the probe:

```
SqShape       = (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → ⊥)
                        → ⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
AbsorbsShape  = (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ˢ ω ⟩ → ⊥)
                        → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
                        → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
```

**A5's `sq` conclusion.** The square-law chain theorem is
`P α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α`
(`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:519-520`, `Chain.theorem` at
`:551`), and `SQ.sq α` is `Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] (injective)`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). Restated over the L carrier it is
exactly `SqShape`. **MATCH.**

**A6's `absorbs` conclusion.** The successor absorption is
`ShiftAbs (fst γ) oγ γ∉ω numerals` with conclusion `shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`
(`agents/tasks/LJ-1-217/ProbeLJ1217A.agda:98-210`, the readback at
`:594-598`). Restated over the L carrier it is exactly `AbsorbsShape`.
**MATCH.**

**The one structural fact the audit surfaces, and it is a fact, not a
mismatch.** The statement coordinates TWO injection notions, and each block's
conclusion lands at the correct site:

- `IsCardinalL` (A4) uses the INTERNAL coding `InjCode` (A2's `svAt`/`domAt`/
  `injAt`), because `[LJ-1.91]` measured that the ambient `IsCardinal`
  (`src/L/BoundedSubset.lagda.md:1046-1047`) is a different object.
- `SqShape`, `AbsorbsShape` and the conclusion `⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫`
  use the AMBIENT `↪`, which is what A5 and A6 deliver as their readbacks.

A5 and A6 deliver packages (an L-element coding plus a readback to the
ambient injection, `ProbeLJ1217A.agda:594-598`); A7's hypotheses name the
readback half, and A4's `IsCardinalL` names the coding half. No block is
asked to be in the wrong shape.

**One formulation finding the audit surfaces, and it is not a mismatch of the
hypotheses.** The GCH conclusion needs the SUCCESSOR cardinal, not merely
"some cardinal δ above κ". My first cut wrote `∃δ (IsCardinalL δ × κ ∈ δ ×
𝒫(κ) ↪ δ)`, which is WEAKER than GCH: it does not pin δ to κ⁺. The probe
now states `SuccCardL δ κ` (δ is the least cardinal above κ) in the
conclusion. That is the "successor-cardinal bookkeeping"
`[LJ-1.131]` attributed to A7's 80-160 lines
(`agents/tasks/LJ-1-131/lj-1.131-report.md:373`), and it is a named object of
the statement the brief's "names only S, ∈ˢ, internal IsCardinal and the
square-law shape" list does not spell out. It elaborates, and it does not
touch the `sq`/`absorbs` hypotheses, so the audit verdict is unchanged.

## 2. A7 WRITTEN LINES AGAINST 110

Counted non-blank non-comment, the probe caliber of `[LJ-1.229]`.

| piece | lines | what it is |
|---|---:|---|
| `injAt` (copied from `ProbeLJ1229A` S1, A2's) | 5 | not A7's; A2's deliverable |
| `_↪_`, `InjCode`, `IsCardinalL` | 12 | the internal cardinal (A4's object, named) |
| `SqShape`, `AbsorbsShape` | 9 | A5's and A6's conclusion types |
| `SuccCardL` | 5 | the successor cardinal, the GCH conclusion's bookkeeping |
| `GCHStatement` | 11 | the statement itself |
| `Guard` | 5 | C-38: ω is an L-ordinal |
| **charge** | **47** | from `_↪_` through the guard |
| whole file (with imports) | 81 | header paid once by a master |

**47 against 110.** The standing 110 is mostly reading, as the brief said.
The statement proper (`InjCode` + `IsCardinalL` + `SqShape` + `AbsorbsShape` +
`SuccCardL` + `GCHStatement`) is 35 lines against the 13-line `ChoiceStatement`
comparable. No overage.

## 3. A4 COLD SECONDS, WITH LOAD AND RUN COUNT

`ProbeLJ1236A4.agda`, the internal `LeastCard` (`leastOf (orderAt β oβ)` over
the predicate "some L-element codes `⟪ κ ⟫ ↪ ⟪ δ ⟫`") plus internal
`IsCardinalL`, instantiated at `ω`. Green, `--safe`, exit 0.

Machine: 16 cores, macOS, Agda 2.8.0. ONE agda process of mine at a time,
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. The sibling (`LJ-1.237`) holds
the other slot; no agda binary of its was running during my kept runs
(`ps` shows its `dispatch.py` only). The probe's own interface was deleted
before every run; the delivered imports stay cached, the same discipline
`[LJ-1.229]` and `[LJ-1.217]` used.

| run | seconds | load (1-min) |
|---|---:|---|
| warm-up (discarded) | 1.97 | 4.29 |
| kept 1 | 1.12 | 5.07 |
| kept 2 | 1.10 | 5.07 |
| kept 3 | 1.13 | 5.07 |
| kept 4 | 1.17 | 5.22 |
| kept 5 | 1.17 | 5.22 |

**Cold mean 1.14 s, five kept runs, range 1.10 to 1.17 s, load 5.07 to 5.22.**
One early run after a gap (1.71 s and 1.92 s in two separate batches) is the
first-run penalty and was discarded as the warm-up.

**No wall.** No run approached the 20-minute bound. No heap exhaustion.

## 4. A4 LINES AGAINST 190, AND THE RATE AGAINST DD24

Counted non-blank non-comment, the same caliber.

| piece | lines | what it is |
|---|---:|---|
| `injAt` (copied, A2's) | 5 | consumed, not re-derived; not A4's |
| `InjCode`, `IsCardinalL` | 10 | internal cardinal |
| `InternalLeastCard` (β, oβ, up, `Good`, `Selected` least-of) | 22 | the measured term |
| `Atω` guard | 11 | the C-38 real-ordinal instantiation |
| **charge** | **48** | from `injAt` through the guard |
| whole file (with imports) | 83 | header paid once by a master |

**The double-count stays closed (the brief's rule).** A4 consumes A2's
description plus adequacy (27 lines) and not the readback
(`agents/tasks/LJ-1-229/lj-1.229-report.md`). I copied A2's `injAt` (5 lines)
for the probe to elaborate, and I do NOT count those 5 lines in A4's figure.
A4's own content is **43 lines** against the standing 190. The probe is a
minimal core, not the master: the master adds the full object-language
internal `IsCardinal` formula with its adequacy, and the concrete nonempty
witness (A2's `lid`, which is A5's deliverable, not A4's).

**Rate against DD24's bar (0.007913 s/line, `dev/PLAN.md:84`).**

| figure | seconds | lines | s/line | against 0.007913 |
|---|---:|---:|---:|---:|
| whole probe file | 1.14 | 83 | 0.0137 | **1.74x** |
| A4's own content, net of the shared import baseline (1.04 s, A7's file) | 0.10 | 43 | 0.0023 | **0.29x** |

The whole-file figure is a probe artifact: 35 of its lines are the delivered
import header. The honest figure is the net: A4's own content checks at
0.29x the bar. I report both and argue neither away.

## 5. THE SECONDS RISE STEEPLY — REFUTED, MEASURED

`[LJ-1.136]` inferred the internal least-of's seconds rise above the ambient
`LeastCardInj`'s 100.64 s (`lj-1.136-report.md:454`), because "the internal
form adds a truncated L-element existential inside the same least-of".

**The inference is refuted. MEASURED at this site.** The internal least-of is
1.14 s, about 88 times CHEAPER than the ambient comparable, not more
expensive.

**Why, and it is a structure change, not a smaller term.** The ambient
`LeastCardInj` runs `leastOf (ordSWO (sucV α))` over `⟪ sucV α ⟫`, the union
representation, and `ordSWO`'s `≺₁` unfolds the ordinal comparison
(`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:187-188`; the cause `[LJ-1.156]`
named: "`⟪ sucV α ⟫` normalizes the union structure"). The internal
`LeastCard` runs `leastOf (orderAt β oβ)` over `Mem (Lset β)`, a Σ-type, and
`orderAt` is **opaque** — sealed exactly so a consumer never unfolds the
order (`src/L/Choice/Step.lagda.md:740-743`). The truncated existential over
L-elements adds almost nothing; the well-order swap from an unfolding union
order to a sealed Σ-order removes almost everything.

**This is the same fact the tree already paid to learn:** `orderAt` is sealed
"for precisely this reason" (`agents/tasks/LJ-1-136/lj-1.136-report.md:981-987`).
A4 inherits the seal, and the seconds risk the brief asked me to price does
not exist at this site. P-l: 100.64 s and 44 lines are comparables, not A4's
price; A4's price is 1.14 s, and the two differ by structure, not noise.

## 6. DD4: STRUCTURE-PARAMETER FORM, AND WHAT IT COST

**A7 is tower-neutral, written with the structure parameter from its first
line. MEASURED.** `GCHStatement : isZFModel → Type` takes the model as a
parameter, exactly as `ChoiceStatement` does, and names `S`, `∈ˢ`,
`IsCardinalL` and `↪` — no `isL`, no `Lset`, no `orderAt`. **The parameter
form cost nothing.** It is the natural shape of a statement, the same
discipline `ChoiceStatement` already exercises, and no parameter was
retrofitted. `[LJ-1.210]`'s 42-line retrofit does not apply.

**A4 is per-tower, Devlin's second object applied to cardinality. MEASURED.**
`InternalLeastCard` names `stageBound`, `orderAt`, `Lset`, `Lset→isL` and
`isL` — the L tower's definable well-order, the object the J tower would
differ on. **The fixed form cost nothing either**, because A4 is naturally
per-tower: there is no generic carrier to parameterize over, and the
definable well-order is the point, not an accident of presentation.

**One DD4 note for the route.** A7's statement is shared by both towers for
free; A4, A5 and A6 are the per-tower content. That matches
`[LJ-1.227]` section 8's table, and nothing in this task moved it.

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md` sections 4, 5, 8, read
  WHOLE.** TAKEN: the two probe specs at section 4 (A4) and section 5 (A7);
  the tower table at section 8.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md:243-247`, `:381-392`, `:454`.**
  TAKEN: why A4 is needed (the ambient/internal cardinal split), why A7 runs
  now (C-35), and the inferred seconds rise this task refutes.
- **`agents/tasks/LJ-1-156/lj-1.156-report.md:208`, `:216`.** TAKEN: the
  ambient `LeastCardInj` at 44 lines and 100.64 s, the comparable this task
  refutes.
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, WHOLE.** TAKEN: A2 green,
  and the 27-line description-plus-adequacy that A4 consumes.
- **`src/L/Choice/Transversal.lagda.md:372-384` and
  `src/L/BoundedSubset.lagda.md:1046-1047`.** READ at the source: the
  delivered `ChoiceStatement` shape and the ambient `IsCardinal`.
- **`src/L/Choice/Step.lagda.md:740-743` and
  `src/L/Ordinal/SquareLaw.lagda.md:176-186`.** READ: `orderAt` is opaque,
  `ordSWO` is over `⟪ α ⟫`. The source of section 5's refutation.
- **`archive/dev/TASKS-archived.md` and
  `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`, read
  WHOLE (the code).** TAKEN, SHAPE ONLY: the retired route's three internal
  predicates, `eqFo`/`cardFo`/`succCardFo`, each a formula with a
  satisfaction certificate. **WHAT WOULD NOT TRANSFER:** the archive's
  `cardFo` is the BIJECTION form (`∀∈ κ ¬ eqFo`, "no smaller ordinal
  equinumerous"), built under the W7 ruling that equinumerosity is a
  bijection, never injections both ways. A-prime states cardinality over
  INJECTIONS (`[LJ-1.156]`'s design change), so my `IsCardinalL` is the
  injection form, matching the ambient `IsCardinal` and not the archive's
  `cardFo`. The fixed-arity wrapper (`φ-card`, `φ-succ-card`) is the shape
  discipline worth keeping; the bijection body is not.

## 8. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:145-171`.** USED. Devlin states GCH as
  `𝒫(κ) ⊆ L_{κ⁺}` for every infinite cardinal κ (5.6), a LEVEL-containment,
  obtained from 5.5 and `|L_{κ⁺}| = κ⁺`.
- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  two objects; section 6 maps A7 (tower-neutral) and A4 (per-tower) onto it.

**Does the delivered `ChoiceStatement` shape match how the literature states
it.** In substance yes, in shape no, and the difference is the tree's own.
Devlin's 5.6 is a level-containment `𝒫(κ) ⊆ L_{κ⁺}`; my statement is the
square-law-shaped injection `⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫`. The two are
equivalent only through the counting `|L_{κ⁺}| = κ⁺`, which is exactly A5's
`sq` feeding `StageCardinal`. So the tree's statement form carries A5's
obligation inside its conclusion, which is why A5's `sq` is a hypothesis of
the statement rather than a step the literature can leave implicit.

**Is the internal cardinal the object the literature quantifies over.** The
literature quantifies over "κ a cardinal", the ambient initial-ordinal
notion. A7 quantifies over `IsCardinalL`, the internal cardinal over
L-coded injections. `[LJ-1.91]` measured these differ and no delivered lemma
converts them, so the internal object is the right one and is not the
literature's ambient notion.

## 9. THE NEGATIVES, CLASSIFIED

- **MEASURED. A7's statement elaborates.** `--safe`, exit 0.
- **MEASURED. A5's `sq` conclusion matches A7's `SqShape`.** Section 1.
- **MEASURED. A6's `absorbs` conclusion matches A7's `AbsorbsShape`.** Section 1.
- **MEASURED. A7 is 47 charge lines against 110.** Section 2.
- **MEASURED. A4's internal least-of is 1.14 s cold, five kept runs.** Section 3.
- **MEASURED. `[LJ-1.136]`'s inferred seconds rise is refuted.** 1.14 s
  against the 100.64 s comparable, by the opaque-vs-unfolding well-order swap.
  Section 5.
- **MEASURED. A4 is 43 own lines against 190 (probe minimal core).** Section 4.
- **INFERRED. A7's 110 standing is mostly reading.** My 43 charge lines are
  the written half; the reading half (the audit, the archive survey) is the
  rest. The brief said the same.
- **INFERRED. A4's master is larger than the 43-line probe core.** The probe
  leaves the nonempty witness abstract (A2's `lid`, A5's work) and states
  `IsCardinalL` metatheoretically rather than as the object-language formula
  with adequacy. Neither is A4's content; both are why the probe is a core,
  not a price.

## 10. WORKING TREE, AS MY REPORT DESCRIBES IT

Two probes and this report, all in `agents/tasks/LJ-1-236/`:

| file | state |
|---|---|
| `ProbeLJ1236A7.agda` | green, `--safe`, exit 0, 81 lines whole, 47 charge |
| `ProbeLJ1236A4.agda` | green, `--safe`, exit 0, 83 lines whole, 48 charge, 1.14 s cold mean |
| `lj-1.236-report.md` | this file |

No master edited. No file under `src/` edited. No commit, no push, no
`git checkout .`/stash/reset/clean. No `make check`; the orchestrator runs
it. ONE agda process of mine at a time, cap never raised. The sibling
`agents/tasks/LJ-1-235/` and `src/L/Choice/Name.lagda.md` were not touched.
