# LJ-1.237 report: assemble `sl` and `sc`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda process,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master, brief or report edited.
No commit, no push. No `make check`. Written incrementally (C-22).

## 0. LEAD

**`sl` and `sc` BUILD, and the shared object is ONE precisely-typed term that
is NOT yet supplied. MEASURED.**

The two hypotheses assemble on top of a single shared object -- the
stage-carrier level-hood instantiation, the decode-in direction -- and nothing
else. `sl` is 14 non-blank lines, `sc` is 38, and the shared object's TYPE is
one line:

```agda
lh : (v b : SL) → IsOrd (fst b) → fst v ≡ Lset (fst b)
   → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩
```

The probe is `agents/tasks/LJ-1-237/ProbeLJ1237A.agda`, 255 physical lines, 168
non-blank non-comment. It typechecks, exit 0. **But `lh` enters as a module
parameter, not a proof.** Nothing in `src/` supplies it, and supplying it is the
carrier-move + bounded-decode assembly, which is the content `[LJ-1.228]` priced
at about 0.15k each. I did not close that assembly, so this is the thin layer
measured, and the meat named -- not a full build.

**The floor is not contradicted.** `[LJ-1.228]` said 0.25k to 0.35k joint, of
which the shared object is the dominant component. My 52 lines of `sl`+`sc` sit
entirely ON TOP of the shared object and are not part of its price, so the floor
still reads as a floor, direction UP.

## 1. WHAT I BUILT

`ProbeLJ1237A.agda`, three sections.

**SECTION 1, the generic pieces (56 non-blank lines):** `isOrdSlot`
(`:72`), `Δ₀-isOrdSlot`, `mapFo-ren` (the relabel/rename commutation, `:88`),
`wk23`, and `coverForm` (`:113`). All parameter-free, all tower-free. These
re-state the ordinal atom and the cover sentence exactly as `ProbeLJ1178A`
wrote them.

**SECTION 2, the shared object's consumers (37 non-blank lines):**
`embAmb`/`embAmb⁻¹` (`:139`, `:146`), the two directions of "the stage's outer
reading of a parameter-free formula is the ambient reading", built on the
delivered `embed-⊨` (`src/FOL/Manipulation/Relabelling.lagda.md:188`); `ord-out`
and `ord-in` (`:154`, `:159`), the stage ordinal read-off, built on `abs₀`
(`src/FOL/Absoluteness.lagda.md:122`), `mapΔ₀`, and `Amb.isOrdAt-out/in`
(`src/L/BoundedSubset.lagda.md:813-821`); and `ord-slot-in` (`:167`), the
ordinal atom at slot `suc zero`.

**SECTION 3, `sl` and `sc` (`module Build`, 52 non-blank lines):**

- `sl` (`:188`, 14 lines): the stage believes every ordinal has a level. Given
  `b : SL` with the stage believing `isOrdAt b`, read off `IsOrd (fst b)`
  (`ord-out`), get `fst b ∈ˢ α` (`ord∈Lset→∈`,
  `src/L/Ordinal/Stages.lagda.md:265`), get `sucV (fst b) ∈ˢ α` (`succα`), place
  the level `Lset (fst b)` in `Lset α` via `Lset∈suc` (`Lset-suc` +
  `𝒟ₒ-intro`, `src/L/Axioms/Basic.lagda.md:196`) and `Lset-mono`
  (`src/L/Constructible.lagda.md:355`), and discharge the level-hood with `lh`.

- `sc` (`:203`, 38 lines): the stage believes every set lies in a level. Unpack
  `x ∈ˢ Lset α` by `Lset-out` to a `δ ∈ˢ α` with `x ∈ˢ 𝒟ₒ (Lset δ)`; take
  `b = sucV δ`, `v = Lset (sucV δ)`; the ordinal atom by `ord-slot-in`, the
  level-hood by `lh`, the membership `x ∈ˢ v` by `Lset-suc`; and assemble the
  cover sentence through `SatM.⊨-rename` and `mapFo-ren`.

Both are stated over `succα : (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ sucV d ∈ˢ α ⟩`, which is
the brief's `succλ` at the site.

## 2. THE SHARED OBJECT, AND WHAT SUPPLYING IT NEEDS

The shared object is `lh`, the decode-in: the stage believes the level-hood of
`v` at `b` whenever `fst v ≡ Lset (fst b)` and `b` is an ordinal. **MEASURED:
nothing supplies it.** `git grep` finds no stage inner statement concluding the
level-hood; `hierL`/`hierAt` have no consumer outside `src/L/Hierarchy.lagda.md`
(the class carrier).

Supplying `lh` is the assembly of the two settled walls, in this order, every
piece delivered at `file:line`:

1. `Lset-defines` (`src/L/Hierarchy.lagda.md:646`): class-carrier belief in the
   unbounded graph `LsetGraphAt zero (suc zero)`, from `fst v ≡ Lset (fst b)`.
2. `graph-in` (`agents/tasks/LJ-1-124/ProbeLJ1124A.agda:205`): bounded
   `graphBndAt` from the unbounded graph, needs the `witnessK` site fact.
3. the witness is the internal hierarchy `hierL (fst b)`, placed in a stage by
   `hasReplacementL-bound` (`agents/tasks/LJ-1-235/ProbeLJ1235A.agda`), whose
   bound `βimg` must land below `α` via `succλ` and the level closure.
4. the carrier move class → stage over the Δ₀ matrix `graphBndAt`, via
   `mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`), `liftFo`
   (`src/FOL/Manipulation/Bounding.lagda.md:162`) and `abs₀`
   (`src/FOL/Absoluteness.lagda.md:122`).

This is Devlin's clause (b), the localized level-hood, and `dev/literature/devlin-II5.md:374`
classes it (row C1) as **PER-TOWER content** -- which is exactly where my
structure parameter stops: the joining layer (SECTION 3) is tower-free, and the
decode-in is the per-tower instantiation point.

**The concrete difficulty I met, named (C-36):** the level-hood formula at the
stage cannot be `Cnt.erase` of the class-carrier `LsetGraph`, because
`LsetGraph` carries coding constants (`numeralL`, the code tags,
`src/L/Coding/Model.lagda.md:586`), so `countFo LsetGraph ≢ 0` and the `refl`
erase `[LJ-1.233]` refuted is the only erase that is `refl`. The parameter-free
form is `absFo` (`src/FOL/Manipulation/Parameters.lagda.md:260`), which raises
the arity by `countFo`. So the decode-in must run over the lifted constants, not
over an erased closed sentence. **MEASURED** by reading `LsetGraph`'s
definition chain; the assembly itself is NOT written.

## 3. STRUCTURE-PARAMETER COST (DD4)

**Zero. MEASURED.** `sl` and `sc` are written from their first line over
`(α, ordα, φ₀, lh)`. The only L-tower names that enter SECTION 3 are `Lset`,
`Lset-suc`, `Lset-out`, `Lset-mono`, `ord∈Lset→∈`, `ord∈Lset-suc`, `Lset-cumul`
-- the level closure -- and they enter as arguments, not as a fixed carrier. The
J tower re-instantiates with its own level operation and its own `lh`. Nothing
in SECTION 1 or 3 names `isL`, `𝒮ʟ` or the definable-powerset presentation.

## 4. SECONDS, LOAD, RUN COUNT

One process, `GHCRTS="-A64m -I0 -M8g"`, warm caches (the `L.BoundedSubset` and
`L.Condensation` interfaces already exist in `_build`). Warm-up run discarded.
Three kept runs: **3.03 s, 2.19 s, 2.19 s** real. Load at the close: **4.95**
(two users, 16 CPUs). The bulk is loading cached interfaces for
`L.BoundedSubset` and `L.Condensation`; the probe's own 168 lines are cheap
parameterized content (P-m). No heap exhaustion.

## 5. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| `sl` and `sc` assemble on the shared object | **MEASURED TRUE.** exit 0 |
| `sl`'s own lines, on top of the shared object | **MEASURED.** 14 non-blank |
| `sc`'s own lines, on top of the shared object | **MEASURED.** 38 non-blank |
| the shared object's TYPE | **MEASURED.** the one-line `lh` above |
| the shared object is SUPPLIED in `src/` | **MEASURED FALSE.** nothing concludes the stage level-hood |
| the shared object is SUPPLIED by my probe | **MEASURED FALSE.** it enters as a parameter |
| the stage level-hood formula is the `refl` erase of `LsetGraph` | **MEASURED FALSE.** `LsetGraph` has constants |
| the structure-parameter form cost anything | **MEASURED FALSE.** written from the start, zero retrofit |
| the floor 0.25k to 0.35k is a complete price | **MEASURED FALSE.** my 52 lines are on top of it; its dominant component is unpriced |
| a fourth wall blocked the assembly | **MEASURED FALSE.** every piece is delivered; what remains is the assembly, which is the brief's own priced content |

## 6. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:365-394`, read whole.

`:374` row C1 classes the level-hood formula as **PER-TOWER content, same
shape** -- `Σ₁-with-Σ₀-matrix, uniform Δ₁, witness in carrier`. `:387-389` gives
the two-object verdict: the per-tower content is exactly the level-hood
certificate (Step C) and the definable well-order (Steps D, G). **My build
agrees with `[LJ-1.228]`'s reading**: `sl` and `sc` are ONE object, the
level-hood certificate's stage instantiation, and Devlin's clause (b), the
localized form. **Devlin PROVES clause (b), he does not assume it** -- he
derives it from clause (a) plus 1.9.15 (Σ₀ absoluteness at a transitive carrier,
`devlin-II5.md:96-100`). Our tree wrote a separate bounded syntax, so our clause
(b) is a syntactic assembly (the carrier move + bounded decode) where Devlin
pays one citation. **INFERRED**, from the two presentations.

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-233/lj-1.233-report.md`, read WHOLE. TOOK the wall verdicts
  (`:12-48`), the `liftFo`/`mkBoundedFo`/`satBridge` route (`:52-78`), the floor
  ruling (`:109-130`), and the DD4 finding (`:132-148`).
- `agents/tasks/LJ-1-235/lj-1.235-report.md` and `ProbeLJ1235A.agda`, read WHOLE.
  TOOK `hasReplacementL-bound` and `βimg`/`img∈βimg` (`ProbeLJ1235A.agda:37-59`).
- `agents/tasks/LJ-1-228/lj-1.228-report.md`, read WHOLE. TOOK the delivered map
  (`:32-42`), the band mapping (`:110-126`), the falsity check (`:129-160`), and
  the DD4 section (`:162-170`).
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda` and `lj-1.178-report.md`, read WHOLE.
  TOOK `StageLevels` (`ProbeLJ1178A.agda:360-361`), `StageCovered` (`:405-406`),
  `module Whole` (`:489-493`), and `coverForm`/`wk23`/`isOrdSlot`.
- `agents/tasks/LJ-1-124/ProbeLJ1124A.agda`, read WHOLE. TOOK `graph-out`/
  `graph-in` (`:199-209`) and the `witnessK` site fact (`:194-197`).
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read WHOLE. TOOK `clause-a`
  (`:355-365`) and the `free`/`embed-⊨` pattern (`:335-352`).
- `src/L/BoundedSubset.lagda.md`, read `:74-146`, `:780-869`, `:903-904`,
  `:1394`. TOOK `LevelHood`, `LevelHood0.Σ₂`, `isOrdAt`, `Amb`. NOT edited.
- `src/L/Hierarchy.lagda.md`, read `:300-660`. TOOK `Lset-only` (`:334`),
  `Lset-defines` (`:646`). NOT edited.
- `src/L/Hull.lagda.md`, read `:120-230`. TOOK `AtStage` (`:148`). NOT edited.
- `src/L/Axioms/Basic.lagda.md` `:150-215`, `src/L/Constructible.lagda.md`
  `:340-380`, `src/L/Ordinal/Stages.lagda.md` `:150-270` `:410-445`,
  `src/L/Axioms/Separation.lagda.md` `:120-180` `:430-460`,
  `src/FOL/Manipulation/Bounding.lagda.md` `:146-200`,
  `src/FOL/Absoluteness.lagda.md` `:100-190`,
  `src/L/Coding/Model.lagda.md` `:580-600`,
  `src/FOL/Manipulation/Relabelling.lagda.md` `:175-195`,
  `src/FOL/Manipulation/Renaming.lagda.md` `:91-150`,
  `src/FOL/Manipulation/Parameters.lagda.md` `:70-90` `:254-262`,
  `src/L/Condensation.lagda.md` `:2335-2495`. All read, none edited.
- `archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`:
  **NOT read.** The question is settled inside the live record; the route's
  shape (Devlin's clause (b)) is answered by the live `Hierarchy`/`BoundedSubset`
  sources. I state that plainly.

## 8. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`agents/tasks/LJ-1-236/` not touched. `src/L/Choice/Name.lagda.md` not opened.
No commit, no push, no `git checkout`/`stash`/`reset`/`clean`. No `make check`.
One Agda process at a time, cap never raised.

**My files:** `agents/tasks/LJ-1-237/ProbeLJ1237A.agda` and
`agents/tasks/LJ-1-237/lj-1.237-report.md`.

## 9. GATES

- `scripts/lint-agda.py --check agents/tasks/LJ-1-237/ProbeLJ1237A.agda`: clean.
- `scripts/lint-prose.py --check agents/tasks/LJ-1-237/ProbeLJ1237A.agda`: clean.
- `make check` not run.
