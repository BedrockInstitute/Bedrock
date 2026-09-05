# LJ-1.669: the soundness lemma at the statement's own shape

## VERDICT: NO-GO

The obligation `sound-at-arity4` cannot be built as a HoodSound-shaped
lemma. A Σ₁ transfer that avoids `mapΔ₀` exists at the class carrier,
at arity 4, with `K` in the environment, and it is green in this probe.
A HoodSound-shaped lemma starts at the collapse image and ends at
`v ≡ Lset γ`. That chain has two walls, each measured: `σ₁-up` cannot
run ambient to inner, and the chapter's `Σ₁-matrix` does not type as a
certificate at a foreign carrier. Either wall stops a transfer that is
both at Σ₁ and free of `mapΔ₀`. The mismatch is stated in full in
`review-of-sound-at-arity4.md`.

## 1. THE TERM, AND ITS ABSENCE

The brief asks for one term: a soundness lemma at arity 4 with `K` in
the environment, taking the chapter's `Δ₀-matrix`
(src/L/BoundedSubset.lagda.md:851-852), whose transfer runs at the Σ₁
statement and not through `mapΔ₀`. The probe `Probe669.agda` does NOT
state the obligation name. A qualified reference to an absent name is
the witness meter's `[NotInScope]`, and that reading is the NO-GO the
branch table prices. The probe instead states, green, every fact the
verdict rests on:

| Fact | Site |
|---|---|
| `matrix : Formula CS.S 4`, sealed | PART 1, `Probe669.agda:78-79` |
| `Δ₀-matrix : Δ₀ matrix` | PART 1, `Probe669.agda:81-82` |
| `count-matrix : countFo matrix ≡ 0 = refl` | PART 1, `Probe669.agda:87-88` |
| `Σ₁-matrix = σ-Δ₀ Δ₀-matrix`, arity 4, `K` free | PART 1, `Probe669.agda:92-93` |
| `Σ₁-step1 = σ-∃ Σ₁-matrix`, arity 3, `K` still free | PART 1, `Probe669.agda:101-102` |
| `transfer-at-arity4 = AbsL.σ₁-up Σ₁-matrix`, no `mapΔ₀` | PART 2, `Probe669.agda:117-121` |
| `reverse-at-arity4 = AbsL.π₁-down (π-Δ₀ Δ₀-matrix)`, Π₁ not Σ₁ | PART 2, `Probe669.agda:134-138` |

## 2. W3, ANSWERED

**Question:** whether the Σ₁ transfer can avoid `mapΔ₀` at arity 4.

**Answer: yes at the class carrier, no as a HoodSound-shaped lemma.**

At `AbsL`, the chapter's matrix already lives on `CS.S`. `𝒮ʟ = 𝒮ᵥ ↾ isL`
(src/L/Constructible.lagda.md:420-421), so `CS.S` is `AbsL.SM`.
`σ₁-up` consumes `σ-Δ₀ Δ₀-matrix` directly
(src/FOL/Absoluteness.lagda.md:182-184). The term is
`transfer-at-arity4` (`Probe669.agda:117-121`). It does not mention
`mapΔ₀`. First green run: 3.26 s, peak RSS 709967872 bytes
(`runs/floor-0.out`). Recheck after comment edits: 4.00 s
(`runs/final-0.out`). Both under the pane caliber `GHCRTS=[-A64m -I0 -M2g]`.

A HoodSound-shaped lemma is the 658 chain at this matrix
(agents/tasks/LJ-1-658/Probe658.agda:247-270):

    inner πX  --σ₁-up-->  ambient πX  --⊨-map-->  ambient L
              --π₁-down--> inner L    --reader-->  v ≡ Lset γ

Two walls stop that chain from being both at Σ₁ and free of `mapΔ₀`.

**Wall (i), direction.** `σ₁-up` is inner to ambient
(src/FOL/Absoluteness.lagda.md:182-183). The last leg of 658 is ambient
to inner (`Probe658.agda:269-270`, `sym (AbsL.abs₀ ...)`). The reverse
that typechecks at this carrier is `reverse-at-arity4`
(`Probe669.agda:134-138`), and it is `π₁-down`, not `σ₁-up`.
`Wall669.agda.txt` ascribes `AbsL.σ₁-up Σ₁-matrix` to the reverse type.
The run is `runs/wall.out`, exit 42, `[UnequalTerms]` at
`Wall669.agda:57.16-36`. Inferred type inner to ambient. Expected type
ambient to inner.

**Wall (ii), constant domain.** A collapse-image carrier is not `CS.S`.
The chapter's `Σ₁-matrix` is a certificate at `CS.S`. It does not type
as the argument of `σ₁-up` at a foreign image. The only delivered
construction that places a class-carrier Σ₁ certificate at an image is
`[LJ-1.161]`'s `mapΣ₁ Empty.rec* (erase-Σ₁ φ p s)`
(agents/tasks/LJ-1-161/ProbeLJ1161A.agda:83-86), and `mapΣₙ` is
`mapΔ₀` at the leaf (src/FOL/Manipulation/Relabelling.lagda.md:234).
`Wall669-ii.agda.txt` ascribes `Abs∅.σ₁-up Σ₁-matrix` at the empty
set, a delivered transitive dummy (`∅-trans`,
src/L/Constructible.lagda.md:89). The run is `runs/wall-ii.out`,
exit 42, `[UnequalLevel]` at `Wall669-ii.agda:48.17-23`:
`matrix` does not have type `Formula Abs∅.SM 4`.

The brief's estimate of 120 to 260 lines is void for the HoodSound-shaped
lemma: the mismatch is a direction fact and a carrier fact, not a price.
The class-carrier transfer that does work is 5 lines
(`Probe669.agda:117-121`). Nothing of the 120-to-260 length can be
wrong in a way a green check would not catch, because there is no
HoodSound-shaped term of the required transfer to write.

Premise 4 held: this dispatch does not demand `erase LsetGraph`. The
matrix's own count is `refl` (`Probe669.agda:87-88`).

## 3. W2

The transfer is the delivered `σ₁-up`
(src/FOL/Absoluteness.lagda.md:182-185), instantiated at the one
carrier the chapter's matrix already inhabits. The generic form is not
rewritten. Instantiation at any other carrier is wall (ii): the
certificate does not sit there without `mapΔ₀`.

## 4. THE C-42 SWEEP

The refutation measures one site: a HoodSound-shaped lemma at arity 4
whose transfer is at Σ₁ and free of `mapΔ₀`. The sweep asked how many
sites carry the same false shape. Count: **1**. Search: `soundP-from-pix`
and `HoodSoundP` over `src/` and the task homes. The delivered
`HoodSoundP` is arity 2 and goes through `mapΔ₀`
(`Probe658.agda:237-259`). That is a different shape. The arity-4 Σ₁
demand appears once, at this obligation. Full record:
`review-of-sound-at-arity4.md`, "Site count".

## 5. RUNS

One Agda process per run, wide caliber, guard 1500 s. Files under
`runs/`. Convention: `.out` carries GHCRTS, timestamps, agda stdout,
`/usr/bin/time -l -p`, and `EXIT=`.

| Run | What | Result |
|---|---|---|
| floor-0 | probe, first | **green**, 3.26 s, peak RSS 709967872 (`runs/floor-0.out`) |
| wall | `Wall669.agda.txt` via a temp copy, removed after | red: wall (i), `[UnequalTerms]`, exit 42 (`runs/wall.out`) |
| wall-ii | `Wall669-ii.agda.txt` via a temp copy, removed after | red: wall (ii), `[UnequalLevel]`, exit 42 (`runs/wall-ii.out`) |
| final-0 | probe after comment edits | **green**, 4.00 s, peak RSS 686243840 (`runs/final-0.out`) |

No heap wall. No second run of the same code. The wall files are
restructurings of the ascription, not reruns of the green probe.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **If the consumer reads at `L`.** `transfer-at-arity4` is delivered
   at arity 4, `K` free, no `mapΔ₀` (`Probe669.agda:117-121`). The
   reverse at the same carrier is `reverse-at-arity4`, and it is Π₁
   (`Probe669.agda:134-138`).
2. **If the consumer is HoodSound from the collapse.** The first leg
   needs a certificate at the image. The delivered construction is
   `[LJ-1.161]`'s `mapΣ₁` (`ProbeLJ1161A.agda:83-86`), which is
   `mapΔ₀` at the leaf. The last leg is Π₁, not Σ₁. A brief that
   demands both "at Σ₁" and "not through `mapΔ₀`" on that chain
   restates this NO-GO.
3. **The reader `v ≡ Lset γ` at the matrix is still the chapter's
   residue.** `[LJ-1.662]` measured that no theorem in `src/` relates
   `graphBndAt` to `LsetGraphAt`
   (agents/tasks/LJ-1-662/review-of-hoodexists.md:39-43). This
   dispatch does not close that residue. A class-carrier inner reader
   of the matrix would make `σ₁-up` unnecessary at `L`, because
   `Lset-only` already reads inner
   (src/L/Hierarchy.lagda.md:334-335).
4. **No route may demand `erase LsetGraph`.** Premise 4 stands. This
   dispatch did not touch that pin.

## 7. WORKING TREE

- `agents/tasks/LJ-1-669/Probe669.agda`: green, no hole, no obligation name.
- `agents/tasks/LJ-1-669/Wall669.agda.txt`: wall (i), named `.agda.txt`.
- `agents/tasks/LJ-1-669/Wall669-ii.agda.txt`: wall (ii), named `.agda.txt`.
- `agents/tasks/LJ-1-669/review-of-sound-at-arity4.md`: the NO-GO.
- `agents/tasks/LJ-1-669/runs/`: the four runs, `run.sh`, `log.md`.
- Nothing in `src/`. No generated file committed. The ratio bar is inert:
  the scope is a raw `.agda` probe with no in-fence lines.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` READ, then DECLINED for the mathematics.**
  `archive/dev/ORCHESTRATION.md:1` reads
  `# ORCHESTRATION: the orchestrator's operating rules`.
  Surveyed by grep for `hoodsound`, `Lset-only`, `levelhood`, `level-hood`,
  `soundP`, `mapΔ₀`, `σ₁-up`; zero hits. The archived process document
  carries no shape for this task.
- **`archive/dev/DD-archived.md` DECLINED.** Surveyed by grep, same
  keywords; zero hits. Not read. The archived decision list does not
  carry this lemma's type.
- **`archive/dev/PLAN-archived.md` READ at the predecessor's locator,
  then DECLINED for the mathematics.** `archive/dev/PLAN-archived.md:139`
  reads
  `first planned crossing has no Delta-0 witness, and route C's structural story`.
  That is the Phase 1 GCH-wing record, a different route. It confirms
  the family of a crossing with no Δ₀ witness. It does not price this
  transfer.
- **`archive/dev/STATUS-archived.md` READ, then DECLINED for the
  mathematics.** `archive/dev/STATUS-archived.md:87` reads
  `` `Lset-only`/`Lset-defines` and `hierL`; the fork was ruled 2026-07-29 option (ii) ``.
  That is the DONE record of the supplier's delivery. Its origin is in
  the tree (src/L/Hierarchy.lagda.md:334-335). The record adds nothing
  to the verdict.
- **`archive/dev/TASKS-archived.md` DECLINED.** Surveyed by grep, same
  keywords; zero hits. Not read. Off this route.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` | 3 in `Φ`, ONE closed |`, and
  `dev/literature/level-formula-slot-roles.md:28` reads
  `| 6 | Jech 13.14 | "The function `α → L_α` is Δ₁", from a Σ₁ step `∃W[...]` | 2 |`.
  **I used it to confirm the shape of the statement, not to price the
  transfer.** Row 4 is the Δ₀ form with a bound, closed to arity 1:
  that is the chapter's matrix at arity 4 with `K` free. Row 6 is the
  arity-2 level-hood, graded Σ₁ by an unbounded `∃`. The tree and the
  sources disagree on nothing here. The NO-GO is a transfer fact, not
  a literature disagreement.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Surveyed by grep; zero
  hits. The shelf list; the shelf is `level-formula-slot-roles.md`,
  which is read above.
- **`dev/literature/devlin-errata.md` DECLINED.** Surveyed by grep;
  zero hits. Errata for the Devlin extraction; the two rows used above
  are unaffected.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Surveyed by
  grep; zero hits on this task's terms. A glossary review; it settles
  terms, not transfers.
- **`dev/literature/primary-sources.md` DECLINED.** Surveyed by grep;
  zero hits. Source pointers; the rows used above carry their own
  locators.
