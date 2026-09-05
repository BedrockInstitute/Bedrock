# LJ-1.241 report: build φ₀ at arity two

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda process,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master edited. No commit, no
push. No `make check`. Written incrementally (C-22).

## 0. LEAD

**`φ₀` BUILDS AT ARITY TWO. MEASURED.** `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2` at
`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:145-146`, exit 0.

**`⊤̇` TYPECHECKS. MEASURED.** `φ₀⊤ : Formula (⊥* {ℓ-suc ℓ}) 2`, `φ₀⊤ = ⊤̇`,
at `ProbeLJ1241A.agda:149-150`. This is the brief's `φ₀ := ⊤̇`. It converts
`[LJ-1.240]`'s inhabitability finding from INFERRED to MEASURED.

The two abort lines are both green, so the recipe's step 4 has its instrument
and the fifth step can be sequenced. **STOP.**

## 1. WHAT I BUILT, AND ITS LINES

`ProbeLJ1241A.agda`, 150 physical lines, 77 non-blank non-comment.

- The twelve numeral definitions, tower-free, constant-free, over `⊥*`:
  `isZeroAt` (`:57-58`, "no members"), `sucAt` (`:61-65`, the two-inclusion
  successor atom), `numAt` (`:68-70`, the numeral `k` as nested successors).
- `base = Cnt.erase LH.levelHoodB refl` (`:102-103`): the constant-free
  matrix, arity `4 + 12 = 16`, `erase` preserving arity
  (`src/FOL/Count.lagda.md:598`).
- `LevelHood {12}` (`:85-98`) with the twelve tags `N0..N11 = 5..16`.
- The closure renaming `ρ` (`:106-111`) that keeps `v` and `γ` and closes
  everything else, and `pins` (`:124-137`) that pins the twelve tags to the
  twelve numerals 0..11.
- `closeN` (`:140-142`) and `φ₀ = closeN 14 (pins ∧̇ renamed)` (`:145-146`).

The numeral primitives, the renaming, `closeN`, and `pins` are 40 non-blank
lines. `base` and the instantiation are the rest.

## 2. THE SLOT TRACE, VERIFIED (C-44)

The pinning rests on one claim: **tag `Nk` is at levelHoodB slot `Nk - 1`.**
I did not trust it. I verified it in `ProbeLJ1241B.agda`, 132 physical lines,
by a free-variable walk over `base`.

**MEASUREMENT 1. MEASURED.** With `N0..N11 = 5..16` and every other parameter
zero, the deduplicated free slots of `base` are exactly
`{0, 1, 2, 3, 4, 5, ..., 15}` (`freeCheck = refl`, `ProbeLJ1241B.agda:121-123`).
So the structural slots `w v γ K` are 0..3, and the twelve tags occupy the δ
slots 4..15.

**MEASUREMENT 2, the order. MEASURED.** Moving `N0` from 5 to 6 drops slot 4
and only slot 4 (`freeCheck' = refl`, `ProbeLJ1241B.agda:130-132`). So `N0` is
the tag at slot 4, and the map is monotone: `Nk = 5 + k` is at slot `4 + k`.

**Therefore the pinning is correct**: `ProbeLJ1241A` pins slot `4 + k` to
numeral `k` for `k = 0..11`. This is the same as LJ-1.240's `n ≥ 11` estimate
read at the body environment; my measured floor is `n ≥ 12`, because the tag at
body slot `Nk` needs `Nk ≥ 5` to clear `w v γ K` and the bound witness.

## 3. THE ARCHIVE: WHAT TRANSFERRED, WHAT DID NOT

**The archive gave the SHAPE and the two primitives. It gave no discharge.**

| archive shape | live build | transferred? |
|---|---|---|
| `levelStory : Formula (⊥* {ℓ}) 2` (`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:600-601`) | `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2` (`ProbeLJ1241A.agda:145`) | **the arity-2 constant-free shape. YES.** |
| `zeroForm` (`:529-531`) | `isZeroAt` (`ProbeLJ1241A.agda:57-58`) | **the "no members" pin. YES, same shape.** |
| `sucAt` (`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md:567-571`) | `sucAt` (`ProbeLJ1241A.agda:61-65`) | **the successor atom. YES, same shape.** |
| `Cl = ⊤̇` (`Condensation.lagda.md:592-593`) | `pins` (`ProbeLJ1241A.agda:124-137`) | **NO.** The archive's closure clause is empty. My pins are not. |
| `σᴹ`, `σL` (`:768-769`, `:823-824`) | none in this file | **NO.** φ₀ is the formula only. Embedding at a carrier is the consumer's step. |
| `CrossOut σᴹ` never applied (`:167-169`) | none in this file | **NO, and still open.** It is `amb`, the fifth step. |

**What did NOT transfer, at file:line on both sides.**

1. **The story's clauses.** The archive's `levelStory` reads its own graph
   coding: `Ap = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ domForm ∧̇ limitForm`
   (`Condensation.lagda.md:585-586`) and `Rg` (`:589-590`). The live tree's
   matrix is a different coding: `isCodeBS` / `satGraphB` / `DefinesBS`
   (`src/L/Condensation.lagda.md:1733-1749`, `:2335-2350`). I took the
   arity-2 shape and built the content from the LIVE tree's `levelHoodB`
   (`src/L/BoundedSubset.lagda.md:108`), not from the archive's clauses.
   **MEASURED** by reading both.
2. **`Cl = ⊤̇`.** The archive's closure clause is the empty `⊤̇`
   (`archive/.../Condensation.lagda.md:592-593`). `[LJ-1.240]` warned of this.
   My `pins` is a conjunction of twelve numeral pins
   (`ProbeLJ1241A.agda:124-137`), so the hole the archive left open is filled
   from the live tree, not inherited. **MEASURED.**
3. **The discharge.** `CrossOut σᴹ` is stated and never applied
   (`archive/.../Condensation.lagda.md:167-169`). My build discharges nothing
   either: it builds the formula, not the proof that the pinned numerals make
   `amb` hold. That is the fifth step. **MEASURED** on both sides.

## 4. TOWER-NEUTRALITY OF φ₀ (DD4)

**`φ₀` is NOT tower-neutral. It is Def-tower content.** The numeral primitives
ARE tower-neutral, and the J tower pays them once.

- The primitives `isZeroAt`, `sucAt`, `numAt` (`ProbeLJ1241A.agda:57-70`) name
  no L-tower operation. They are pure FOL syntax over `⊥*`. Tower-neutral.
  **MEASURED.**
- `φ₀` itself is `closeN 14 (pins ∧̇ renameFo ρ (Cnt.erase LH.levelHoodB refl))`
  (`:145-146`). It is built on `levelHoodB`, the Def-tower's bounded matrix
  (`src/L/BoundedSubset.lagda.md:108`), which encodes `isCodeBS` / `satGraphB`
  (`src/L/Condensation.lagda.md:1733`, `:2294`). So `φ₀` names the Def-tower
  matrix. Not tower-neutral. **MEASURED.**

This agrees with the brief's DD4 note: `dev/literature/devlin-II5.md:375`
(row C2) says the J side is SYNTAX-FREE, so the numeral-closure lands in the
small per-tower half. The J tower reuses the primitives and supplies its own
matrix in place of `levelHoodB`.

## 5. SECONDS, LOAD, RUN COUNT

One process, `GHCRTS="-A64m -I0 -M8g"`, warm caches. Warm-up run discarded.
Three kept runs of `ProbeLJ1241A.agda`: **2.21 s, 2.17 s, 2.20 s** real.
Load at the close: **3.55** (two users). The bulk is loading cached interfaces
for `L.BoundedSubset` and `L.Condensation`; the probe's own 77 lines are cheap
parameterized content (P-m). No heap exhaustion. `ProbeLJ1241B.agda` re-checks
in the same order of seconds.

## 6. WHAT THIS TASK IS NOT, ANSWERED

- **Not the numeral-closure.** I built the formula. I did not prove that the
  pinned numerals make `amb` hold. `amb` is the decode-OUT direction
  (`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`), and it stays open.
  **MEASURED** at the consumer.
- **Not the supply of `lh`.** I built the formula the type needs, nothing more.
- **`sl` and `sc` not rebuilt.** They stay green over `φ₀` as a parameter
  (`agents/tasks/LJ-1-237/ProbeLJ1237A.agda:127-129`). **MEASURED** by reading.

## 7. C-36: THE TERM I COULD NOT WRITE

**None.** Every term this task names was written and typechecked. The term that
remains unwritten is the fifth step's discharge of `amb`, and it is a separate
dispatch, not this task.

## 8. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| `φ₀` builds at arity two | **MEASURED TRUE.** exit 0 |
| `φ₀ := ⊤̇` typechecks | **MEASURED TRUE.** `ProbeLJ1241A.agda:149-150` |
| tag `Nk` is at levelHoodB slot `Nk - 1` | **MEASURED TRUE.** `ProbeLJ1241B.agda:121-123`, `:130-132` |
| `erase` preserves arity on `levelHoodB` | **MEASURED TRUE.** `base : Formula (⊥*) 16` |
| `absFo` is the right instrument | **MEASURED FALSE.** `erase` preserves arity and applies |
| the archive discharges the level-hood | **MEASURED FALSE.** `Cl = ⊤̇`, `CrossOut σᴹ` never applied |
| the archive's story clauses transfer to the live tree | **MEASURED FALSE.** different codings, section 3 |
| `φ₀` is tower-neutral | **MEASURED FALSE.** built on the Def-tower `levelHoodB` |
| the twelve numerals are in Devlin | **INFERRED FALSE.** they are a slot-coding artifact |
| `LevelHood` has a consumer in `src/` | **MEASURED FALSE.** three grep hits, all definitions |

## 9. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-240/lj-1.240-report.md`, read WHOLE. TOOK the probe-1
  specification (section 6), the archive `file:line` map (section 4), and the
  `amb` finding (section 3).
- `agents/tasks/LJ-1-239/lj-1.239-report.md` and `ProbeLJ1239A.agda`, read
  WHOLE. TOOK `check-bounded = refl` (`ProbeLJ1239A.agda:66-67`) and the arity
  measurement.
- `agents/tasks/LJ-1-237/lj-1.237-report.md` and `ProbeLJ1237A.agda`, read
  WHOLE. TOOK the `φ₀ : Formula (⊥*) 2` type (`ProbeLJ1237A.agda:128`) and
  `sl`/`sc` over it as a parameter (`:178-181`).
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read
  `:525-605`, `:760-830`. TOOK `zeroForm` (`:529-531`), `Cl = ⊤̇`
  (`:592-593`), `levelStory` (`:600-601`), `σᴹ` (`:768-769`), `σL`
  (`:823-824`), `CrossOut` (`:167-169`). NOT edited.
- `archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md`, read `:560-580`.
  TOOK `sucAt` (`:567-571`). NOT edited.
- `src/L/BoundedSubset.lagda.md`, read `:74-146`, `:840-869`. TOOK
  `levelHoodB` (`:108`), `LevelHood0` (`:840-869`). NOT edited.
- `src/FOL/Count.lagda.md`, read `:585-626`. TOOK `erase` (`:598`). NOT
  edited.
- `src/L/Condensation.lagda.md`, read `:1120-1130`, `:1470-1500`, `:1733-1790`,
  `:2294-2350`, `:2483-2500`. TOOK the slot comment (`:1125`), `tagBS`
  (`:1484-1489`), `isCodeBS` (`:1733-1738`), `satGraphB` (`:2294-2295`),
  `DefBodyB` (`:2335-2349`). NOT edited.

## 10. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-105`.

**TOOK.** `:95-96` states the level-hood as `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`
with `Φ` a Σ₀ formula of arity 3. So `∃z Φ` is arity 2. **My `φ₀` IS that
statement**: `φ₀ : Formula (⊥*) 2` is the right-hand side `∃z Φ(z, v, γ)`, with
`v` at slot 0 and `γ` at slot 1, the witness bound inside.

**The twelve numerals do NOT appear in Devlin.** His `Φ` has the finite
ordinals defined inside LST (Σ₀-definable). Our tree made them environment
slots to keep every bounded formula constant-free
(`src/L/Condensation.lagda.md:1125`). So the twelve-numeral closure is the
price of the slot design, an artifact of the coding, not of Devlin's statement.
**INFERRED**, from the two presentations.

## 11. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`src/L/Choice/Name.lagda.md` not opened. No commit, no push, no `git
checkout`/`stash`/`reset`/`clean`. No `make check`. One Agda process at a time,
cap never raised.

**My files:** `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`,
`agents/tasks/LJ-1-241/ProbeLJ1241B.agda`,
`agents/tasks/LJ-1-241/lj-1.241-report.md`.

## 12. GATES

- `scripts/lint-agda.py --check` on both probes: clean.
- `scripts/lint-prose.py --check` on both probes: clean.
- `make check` not run, by the brief.
