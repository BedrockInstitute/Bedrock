# LJ-1.239 report: supply `lh`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda process,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master, brief or report edited.
No commit, no push. Written incrementally (C-22).

## 0. LEAD

**`lh` is NOT SUPPLIED. MEASURED.** I wrote 0 lines of `lh`. The floor of
about 0.15k (`agents/tasks/LJ-1-228/lj-1.228-report.md:16-21`) is not
contradicted and is not the issue. The issue is that **the recipe's step 4
does not produce the formula the `lh` type names.** MEASURED at the source,
INFERRED for the consequence.

**The `lh` type takes `φ₀ : Formula (⊥*) 2`, a CLOSED parameter-free
two-variable level-hood.** Step 4's carrier move produces `graphBndAt` /
`levelHoodB`, which is constant-free (`countFo ≡ 0`, measured `refl`) but
reads its twelve tag numerals from ENVIRONMENT SLOTS
(`src/L/Condensation.lagda.md:1125`, `:1469-1471`). It therefore has free tag
slots and arity `4 + n`, never arity 2. The brief's own DIFFICULTY names the
same fact from the other side: the parameter-free form is `absFo`, which
raises arity by `countFo`. Both readings agree: **the stage level-hood
formula has arity greater than 2, so the `lh` type as stated is not
instantiable by the cited pieces.** The recipe is refuted at step 4.

## 1. WHAT I MEASURED

`ProbeLJ1239A.agda`, 67 physical lines, green, exit 0. Two measurements:

1. **Step 1 closes.** `step1` (`ProbeLJ1239A.agda:46-48`) applies the
   delivered `Lset-defines` (`src/L/Hierarchy.lagda.md:646`) at the
   two-slot environment `v ∷ b ∷ []`, giving class-carrier belief in the
   unbounded graph `LsetGraphAt zero (suc zero)` from
   `fst v ≡ Lset (fst b)`.
2. **The bounded matrix is constant-free.** `check-bounded = refl`
   (`ProbeLJ1239A.agda:66-67`) proves `countFo levelHoodB ≡ 0`.

The unbounded graph is NOT constant-free. A `refl` check of
`countFo LsetGraph ≡ 0` is refused; the error type normalizes `countFo
LsetGraph` to a large `suc (suc (...))`. MEASURED.

The two facts together are the C-44 finding. The brief's DIFFICULTY is about
the UNBOUNDED graph (`LsetGraph`), which carries coding constants
(`numeralL`, the code tags). Step 4 operates on the BOUNDED matrix
(`graphBndAt` / `levelHoodB`), which is constant-free. The difficulty as
written is about the wrong formula.

## 2. THE FOUR STEPS, EACH AT file:line

**Step 1, `Lset-defines`: CLOSES.** MEASURED. `ProbeLJ1239A.agda:46-48`,
one application of `src/L/Hierarchy.lagda.md:646`.

**Step 2, `graph-in`: green as a probe, not closed as an instantiation.**
`agents/tasks/LJ-1-124/ProbeLJ1124A.agda:205` is green today (re-verified by
`[LJ-1.235]`, exit 0). But `graph-in` sits in `module GraphBridge`, which is
parameterized by six site facts: the two leaf agreements, the two domain
agreements, the entry/satisfier-in-`K` facts, and `witnessK`. Supplying them
for a real `K` is the "28 pieces" `[LJ-1.233]` measured
(`agents/tasks/LJ-1-233/lj-1.233-report.md`, sections 5 and 6): `KValue`
(`src/L/Condensation.lagda.md:7222-7267`) builds the `KFacts` value and has
no consumer, and `KFacts` has no `witnessK` field. I did not close this
instantiation.

**Step 3, `hasReplacementL-bound`: green.** MEASURED.
`agents/tasks/LJ-1-235/ProbeLJ1235A.agda`, 18 lines, exit 0. The residual is
`βimg ∈ˢ α` from `succλ` and the level closure, a bounded assembly I did not
write.

**Step 4, the carrier move: REFUTED AT ITS OUTPUT.**
The move's machinery is delivered (`mkBoundedFo`
`src/L/Axioms/Separation.lagda.md:449`, `liftFo`
`src/FOL/Manipulation/Bounding.lagda.md:162`, `abs₀`
`src/FOL/Absoluteness.lagda.md:122`). But the formula it moves is
`graphBndAt` / `levelHoodB`, whose tag numerals are SLOTS
(`src/L/Condensation.lagda.md:1125`, `:1469`). `levelHoodB : Formula CS.S
(suc (suc (suc (suc n))))` (`src/L/BoundedSubset.lagda.md:108`) is arity
`4 + n`, and its slots `N0..t1 : Fin (5+n)`, `M0..s1 : Fin (7+n)`
(`:75-76`) need `n ≥ 7` before the twelve tags can be distinct. The
`LevelHood0` instance (`n = 0`) is a degenerate all-zero shape, measured only
for cost. **No step of the recipe closes the tag slots down to arity 2.**

## 3. THE C-36 NAME

**The missing term is the numeral-closure.** A closed arity-2
`φ₀(v, b)` must existentially bind the twelve tag numerals AND define each of
them as `# k` inside the formula ("`nₖ = # k`", the finite ordinal). No
delivered piece does this. The tree's bounded matrix reads the numerals from
slots and pays "the slot holds the numeral" at the site
(`src/L/Condensation.lagda.md:1469-1471`). The recipe's four steps move the
matrix to the stage but leave the slots open, so their output has arity
`4 + n`, not 2.

Equivalently: either the `lh` type is re-typed at the real arity
(`(v b : SL) → ... → ⟨ (v ∷ b ∷ [∷ tag-slots]) ⊨ᵐ ... ⟩`), or the
numeral-closure is built. The brief's `lh` type (`φ₀ : Formula (⊥*) 2`) is
an abstraction that no delivered formula instantiates. INFERRED from the
measured arities and the source's slot design.

## 4. DD4

- Step 1 (`Lset-defines`) is L-specific: it names `Lset` and `LsetGraphAt`.
- Step 2 (`GraphBridge`, `ProbeLJ1124A`) is tower-neutral. MEASURED by
  `[LJ-1.124]` section 9: it names no concrete tower.
- Step 3 (`hasReplacementL-bound`) is L-specific in its instantiation:
  `βimg` uses `stage` and `Lset` (`agents/tasks/LJ-1-235/lj-1.235-report.md`
  section 6).
- Step 4's machinery (`liftFo`, `abs₀`, `mkBoundedFo`) is tower-neutral.
- The missing numeral-closure is PER-TOWER: it is Devlin's C1 row
  (`dev/literature/devlin-II5.md:374`).

So the split is: steps 2 and 4 are shared machinery; steps 1, 3 and the
missing closure are the L instantiation.

## 5. SECONDS, LOAD, RUN COUNT

One process, `GHCRTS="-A64m -I0 -M8g"`, warm caches. Warm-up run discarded.
Three kept runs of `ProbeLJ1239A.agda`: **2.42 s, 2.41 s, 2.25 s** real.
Load at the close: **4.56** (two users, 16 CPUs). The control
`ProbeLJ1237A.agda` re-verified at **3.05 s** real, exit 0. The bulk of every
run is loading cached interfaces for `L.BoundedSubset` and `L.Condensation`;
the probe's own content is cheap. No heap exhaustion.

## 6. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| `lh` is SUPPLIED | **MEASURED FALSE.** 0 lines written; the report gives the reason |
| step 1 closes | **MEASURED TRUE.** `ProbeLJ1239A.agda:46-48`, exit 0 |
| the unbounded graph is constant-free | **MEASURED FALSE.** `refl` on `countFo LsetGraph ≡ 0` is refused |
| the bounded matrix is constant-free | **MEASURED TRUE.** `check-bounded = refl` |
| the bounded matrix is closed arity 2 | **MEASURED FALSE.** arity `4 + n`, tag numerals are slots |
| step 4 produces the `φ₀` the `lh` type names | **MEASURED FALSE.** its output is arity `4 + n` with free tag slots |
| the recipe's DIFFICULTY is about the formula step 4 uses | **MEASURED FALSE.** it is about `LsetGraph`, not `graphBndAt` |
| a closed arity-2 `φ₀` requires the numeral-closure | **INFERRED TRUE.** from the slot design and the measured arities |
| the floor 0.15k covers the whole object | **INFERRED FALSE.** it omits the numeral-closure layer; direction UP |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-237/lj-1.237-report.md` and `ProbeLJ1237A.agda`, read
  WHOLE. TOOK the `lh` type (`ProbeLJ1237A.agda:178-180`), the shared-object
  section (`lj-1.237-report.md` section 2), and the four-step recipe.
- `agents/tasks/LJ-1-235/lj-1.235-report.md` and `ProbeLJ1235A.agda`, read
  WHOLE. TOOK `hasReplacementL-bound` and `βimg`
  (`ProbeLJ1235A.agda:37-59`).
- `agents/tasks/LJ-1-233/lj-1.233-report.md`, read WHOLE. TOOK the wall
  verdicts (`:12-48`), the erase-route refutation (`:49-60`), the `KValue` /
  `KFacts` findings (sections 5 and 6).
- `agents/tasks/LJ-1-124/ProbeLJ1124A.agda`, read WHOLE. TOOK `GraphBridge`
  and `graph-in` (`:178-209`) and the `witnessK` parameter (`:194-197`).
- `agents/tasks/LJ-1-124/lj-1.124-report.md`, read WHOLE. TOOK the parameter
  list (`:77-93`) and the DD4 finding (`:137-148`).
- `agents/tasks/LJ-1-228/lj-1.228-report.md`, read WHOLE. TOOK the floor
  (`:16-21`), the supply search (`:39-54`), and the level-hood map.
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read WHOLE. TOOK `Crossing`,
  `φ₀ : Formula (⊥*) 2` (`:169-181`), `AmbientCross` (`:217-234`).
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read WHOLE. TOOK `clause-a`
  (`:355-365`) and `Machine.graph-only`.
- `agents/tasks/archive/LJ-1-50/ProbeDD25H5.agda` and
  `ProbeLJ150MatrixSlots.agda`, read WHOLE. TOOK `count-matrix = refl` and
  `count-Σ₂ = refl` (the bounded matrix is constant-free).
- `src/L/Hierarchy.lagda.md` `:300-660`, `src/L/Axioms/Separation.lagda.md`
  `:120-180` `:420-460`, `src/FOL/Manipulation/Bounding.lagda.md`
  `:120-210`, `src/FOL/Manipulation/Parameters.lagda.md` `:60-270`,
  `src/FOL/Absoluteness.lagda.md` `:60-190`, `src/L/Coding/Sequence.lagda.md`
  `:110-360`, `src/L/Coding/Model.lagda.md` `:560-600`,
  `src/L/Condensation.lagda.md` `:2330-2500` `:6360-6460` `:7050-7200`
  `:7222-7267`, `src/L/BoundedSubset.lagda.md` `:40-160` `:790-910`,
  `src/L/Hull.lagda.md` `:100-260`, `src/L/Ordinal.lagda.md` `:150-196`,
  `src/L/Stage.lagda.md` `:176-193`. All read, none edited.
- `archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`:
  **NOT read.** The question is settled by the live sources and a live
  measurement; I state that plainly.

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-120` and `:360-394`.

**Devlin PROVES the localized level-hood; he does not assume it.** He derives
(b) from (a) by one citation to 1.9.15 (Σ₀ absoluteness at a transitive
carrier), `devlin-II5.md:95-100`. His argument is NOT the four steps above.
His Σ₀ matrix `φ(z, v, γ)` has the finite ordinals (the tag numerals)
DEFINED inside the formula, because in his LST the finite ordinals are
Σ₀-definable. Our tree made the numerals SLOTS to keep every bounded formula
constant-free (`src/L/Condensation.lagda.md:1125`), and pays "the slot holds
the numeral" at the site. So where Devlin pays one absoluteness citation, our
tree owes a numeral-closure layer plus the carrier move. **INFERRED**, from
the two presentations.

## 9. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`agents/tasks/LJ-1-238/` not touched. `src/L/Choice/Name.lagda.md` not
opened. No commit, no push, no `git checkout`/`stash`/`reset`/`clean`. No
`make check`. One Agda process at a time, cap never raised.

**My files:** `agents/tasks/LJ-1-239/ProbeLJ1239A.agda` and
`agents/tasks/LJ-1-239/lj-1.239-report.md`.

## 10. GATES

- `scripts/lint-agda.py --check agents/tasks/LJ-1-239/ProbeLJ1239A.agda`:
  clean.
- `scripts/lint-prose.py --check agents/tasks/LJ-1-239/ProbeLJ1239A.agda`:
  clean.
- `make check` not run.
