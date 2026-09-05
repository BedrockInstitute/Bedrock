# LJ-1.230 report: the stage-carrier decode probe

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`.

**One Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No master,
brief or report edited. No commit, no push. No `make check`.** Every negative
is marked **MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

**NO-GO. THE PLACEMENT NEEDS NEW MACHINERY.**

The stage decode's written lines: **14 code lines close** (the level
placement, `ProbeLJ1230A.agda:73-77`), and **the decode itself does not
close** with `isL-Lset` + `Lset-suc` + `succλ`.

The three named facts close ONLY the level placement. The delivered
class-carrier decode `Lset-only` / `Lset-defines` decodes `LsetGraphAt`, the
**unbounded** graph, at the **class** carrier. The level-hood formula
`LevelHood0.Σ₂` consumes `graphBndAt`, the **bounded** graph. The two are
different formulas, and the three closure facts say nothing about the bound,
the internal hierarchy, or the carrier change.

## 1. WHAT THE DELIVERED CLASS-CARRIER DECODE GAVE, AND WHAT I WROTE

**`Lset-only` (`src/L/Hierarchy.lagda.md:334`) and `Lset-defines` (`:646`)
decode `LsetGraphAt` (`src/L/Coding/Sequence.lagda.md:291-292`), the
UNBOUNDED graph, at the CLASS carrier `CS.S = Σ[ x ∈ S ] ⟨ isL x ⟩`.**
MEASURED by reading both definitions: both conclude from and to
`⟨ γ ⊨ LsetGraphAt w b ⟩`.

**The level-hood formula consumes a different formula.** `LevelHood0.Σ₂`
(`src/L/BoundedSubset.lagda.md:855-856`) wraps `LH.levelHoodB`, and
`levelHoodB` (`:111`) is `∃̇∈ (var 3) (G.graphBndAt ∧̇ …)` where
`G = GraphB` (`:2490`, the BOUNDED graph with leaf `DefBodyB`). MEASURED.

**So the delivered decode does not decode the level-hood.** `graphBndAt` has
exactly one consumer, `levelHoodB` itself, and no two-way lemma against
`LsetGraphAt` or `Lset`. MEASURED by `grep -rn "graphBndAt" src/`: the only
hit outside its own definition is `:111`. `LevelHood0` has no consumer.
MEASURED by `grep -rn "LevelHood0" src/`.

**What I wrote, and what closed:** the level closure fact, 14 code lines:

- `Lset∈Lset : (b : S) → IsOrd b → b ∈ˢ lam → Lset b ∈ˢ Lset lam`
  (`ProbeLJ1230A.agda:73-77`), from `𝒟ₒ-intro` + `defSet⊤≡A` +
  `Lset-suc` + `succλ` + `Lset-mono`. **This is exactly the three named
  facts, and it typechecks.** MEASURED.
- `Lv`, `stageOrd∈lam`, `inCL` (the stage member of the level, the ordinal
  reader, and the natural inclusion `SL → CS.S` via `Lset→isL`). All
  typecheck. MEASURED.

## 2. WHETHER THE BOUND PLACED INTO `Lset lam` WITHOUT NEW MACHINERY

**No. Three walls, none closed by the three named facts.**

**Wall (a): the bounded↔unbounded bridge.** `graphBndAt` (leaf `DefBodyB`)
and `LsetGraphAt` are not joined by a delivered lemma. The machinery that
would join them is DELIVERED-AS-MACHINERY (`LeafAgree` / `SatGraphAgree` /
`KFacts`, `src/L/Condensation.lagda.md:6802-7230`) but NOT assembled.
MEASURED by grep: no `graphBndAt`-against-`LsetGraphAt` or `-against-`Lset`
lemma exists. The assembled lemma is `[LJ-1.123]`'s "bounded level-graph
decode, both ways", banded there at 0.10-0.25k. INFERRED (not assembled here).

**Wall (b): the carrier change.** `mapFo` needs a TOTAL map
(`src/FOL/Manipulation/Relabelling.lagda.md:54-55`:
`(K → K') → Formula K n → Formula K' n`). To move `Σ₂ : Formula CS.S 1` to
`Formula SL 1` one needs `CS.S → SL`, a constructible set into `Lset lam`.
No such total map exists: a constructible set need not lie in `Lset lam`.
MEASURED (type fact). The constant-free erase route (`FOL.Count`,
`Cnt.erase`) plus `embed` would bridge it, but that is machinery beyond the
three named facts.

**Wall (c): the internal hierarchy.** The write direction must exhibit the
approximation witness `f = hierL b` inside the bound `K`. `hierL b` is built
by `hasReplacementL` (`src/L/Hierarchy.lagda.md:594-595`), and **no master
states where the replacement image lands in the tower.** MEASURED by grep:
`hierL` is defined at `:621` and consumed only inside `Lset-defines` (`:656`).
There is no `hierL b ∈ Lset …` fact.

**C-36 name.** The missing term is the **internal-hierarchy stage-placement
fact**: a lemma pinning the replacement image, e.g. `hierL b ∈ Lset
(sucV (sucV b))` or the rank bound `rank (hierL b) ∈ sucV (sucV b)`, so
`succλ` iterated twice climbs it into `Lset lam`. Beside it, the assembled
`graphBndAt ↔ LsetGraphAt` decode (wall (a)). These two are the phase's real
blockers.

## 3. SECONDS, LOAD, RUN COUNT

One agda process, `GHCRTS="-A64m -I0 -M8g"`. Warm caches (the tree was built
before; `.agdai` present). Warm-up discarded: **2.50 s**. Three kept runs:
**1.76 s, 1.70 s, 1.76 s**. Load at the close: **3.61 / 4.39 / 4.97**,
two users, 16 CPUs. The probe file is 122 lines total, 45 non-blank
non-comment lines; the 14-line closure fact is the only decision-bearing
code and it is a typecheck, not a normalization wall.

## 4. THE STRUCTURE PARAMETER THE J TOWER WOULD NEED (DD4)

`dev/literature/devlin-II5.md:374` classes the level-hood formula row C1 as
PER-TOWER, and `:387-389` says the per-tower content is exactly two objects
(level-hood certificate, definable well-order). `sl`/`sc` are one object: the
level-hood certificate's stage instantiation. MEASURED for the structure.

The structure parameter, following `LJ-1-184`'s `ReadOff` tower axis
(`agents/tasks/LJ-1-184/ProbeLJ1184A.agda:56-83`):

- the tower's level operation and step (`Tow`/`Dee` = `Lset`/`𝒟ₒ` on Def)
  and its two legs (`Tow-in`/`Tow-out`);
- the tower's code-set leaf (`DefBodyB` on Def; on J, the sixteen op-graphs,
  syntax-free, SZ p. 10 — `devlin-II5.md` row C2);
- the two stage-closure facts (`isL-Lset`-analog = level-in-stage,
  `Lset-suc`-analog = step-is-the-definable-powerset).

Writing the decode with these as module parameters from the start costs
nothing; retrofitting one costs about 42 lines on a 1,288-line module
(`[LJ-1.210]`). The J tower re-instantiates with its own four and its own
leaf.

## 5. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-106` and `:365-395`.**

Devlin states (a) at the ambient carrier (`:93-96`: `∀v∀γ [v = L_γ ↔ ∃z
Φ(z,v,γ)]`) and derives (b), the localized form, by 1.9.15 (`:98-100`:
`(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]`). **`sl` and `sc` are
clause (b)'s two directions at the stage.** Devlin **proves** (b) from (a)
plus 1.9.15 (Σ₀ absoluteness); he does NOT assume it. MEASURED by reading
`:93-106`. `[LJ-1.228]`'s reading is supported.

The per-tower verdict at `:374` (row C1) and `:387-389` (two objects) places
`sl`/`sc` inside the single level-hood certificate object. Section 4.

## 6. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-228/lj-1.228-report.md`**, read WHOLE. TOOK the
  delivered-component map (`:20-38`), the band mapping (`:110-150`), the
  falsity check (`:160-200`), and the probe statement (`:120-130`).
- **`agents/tasks/LJ-1-123/lj-1.123-report.md`**, read WHOLE. TOOK the four
  bands (`:30-36`), the named class-carrier probe (`:150-190`), and the
  delivered-agreement list (`:180-230`).
- **`agents/tasks/LJ-1-178/ProbeLJ1178A.agda`**, read `:120-500`. TOOK
  `StageLevels` (`:360-361`), `StageCovered` (`:405-406`), `module Whole`
  (`:489-493`), `Crossing`/`Bel` (`:124-147`).
- **`agents/tasks/LJ-1-184/ProbeLJ1184A.agda`**, read WHOLE. TOOK the
  `ReadOff` tower axis (`:56-83`) and `clause-a` (`:355`).
- **`agents/tasks/LJ-1-160/`**, read the report. TOOK the 16-line assembly
  and its section 3.3 (three open face facts).
- **`src/L/BoundedSubset.lagda.md`**, read `:60-180`, `:820-930`, `:1380-1420`.
  TOOK `LevelHood` (`:74-146`), `levelHoodB` (`:111`), `LevelHood0.Σ₂`
  (`:855-856`), `HullStage.succλ` (`:904`). NOT edited.
- **`src/L/Hierarchy.lagda.md`**, read `:1-80`, `:300-360`, `:500-670`. TOOK
  `Lset-only` (`:334`), `Lset-defines` (`:646`), `hierL`/`hierL-spec`
  (`:621-626`), the `hasReplacementL` build (`:594-595`).
- **`src/L/Condensation.lagda.md`**, read `:400-430`, `:2230-2500`,
  `:6790-7230`. TOOK `ride-only`/`ride-defines` (`:419-428`), `GraphB`/
  `graphBndAt` (`:2483-2493`), `SatGraphAgree` (`:6802`), `LeafAgree`
  (`:7066`), `KFacts`.
- **`src/L/Coding/Sequence.lagda.md`**, read `:41-60`, `:281-340`. TOOK
  `LsetGraphAt` (`:291-292`).
- **`src/L/Axioms/Basic.lagda.md`**, read `:95-235`. TOOK `isL-Lset`
  (`:154-157`), `Lset-suc` (`:196`).
- **`src/L/Constructible.lagda.md`**, read `:300-360`, `:376-412`. TOOK
  `Lset-mono` (`:355`), `Lset→isL` (`:395`), `isL` (`:377`).
- **`src/L/Ordinal/Stages.lagda.md`**, read `:255-270`. TOOK
  `ord∈Lset→∈` (`:265-268`).
- **`src/FOL/Absoluteness.lagda.md`**, read `:57-190`. TOOK `Single`
  (`:57-78`), `abs₀` (`:122`), `σ₁-up` (`:182`).
- **`src/FOL/Manipulation/Relabelling.lagda.md`**, read `:54-56`. TOOK the
  `mapFo` total-map signature.
- **`src/L/Axioms/Full.lagda.md`**, read `:277-282`. TOOK `hasReplacementL`.

## 7. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| the three facts close the stage decode | **MEASURED FALSE.** They close the level placement only (14 lines, typechecks); the decode does not close |
| `Lset-only`/`Lset-defines` decode the level-hood | **MEASURED FALSE.** They decode `LsetGraphAt` (unbounded); the level-hood consumes `graphBndAt` (bounded) |
| a `graphBndAt ↔ Lset` decode lemma is delivered | **MEASURED FALSE.** `graphBndAt` has no consumer outside `levelHoodB` |
| the internal hierarchy's stage placement is delivered | **MEASURED FALSE.** `hierL` is built by `hasReplacementL`, no placement fact exists |
| a total map `CS.S → SL` exists | **MEASURED FALSE.** Constructible sets need not lie in `Lset lam` |
| the level closure `Lset b ∈ Lset lam` closes | **MEASURED TRUE.** 14 lines, typechecks |
| the bounded↔unbounded bridge costs the `[LJ-1.123]` band | **INFERRED.** The machinery is delivered, the assembled lemma is not; not assembled here |
| the hierarchy placement is a rank fact | **INFERRED.** Not derived; the shape follows from `hierL` being a replacement image |

## 8. RULES, ANSWERED

- **D-1.** Abort criterion fixed before the run (the brief's four branches);
  verdict NO-GO on the placement.
- **P-l.** The stage is an opaque atom to the elaborator (`AtStage`), so the
  statements are cheap; the cost is naming the transparent bound and
  hierarchy in the type, which is exactly what does not close.
- **D-10.** The truth is not re-checked; the probe measures the decode's
  lines, not the truth of `sl`/`sc`.
- **C-36.** Section 2 names the missing term: the internal-hierarchy
  stage-placement fact, beside the assembled `graphBndAt ↔ LsetGraphAt`
  decode.
- **C-22.** This file was written first and filled incrementally.
- **DD8.** One figure: 14 code lines close; the decode does not. Basis
  named.
- **DD4.** Section 4: one per-tower object, structure parameter named.
- **C-12.** One agda process under the stated cap; load reported beside
  every figure.

## 9. PROHIBITIONS, ANSWERED

No master edited. `src/Everything.lagda.md` not opened.
`src/L/Choice/Name.lagda.md` not opened. Sibling directories
`agents/tasks/LJ-1-226/`, `LJ-1-229/` not touched. No commit, no push, no
`git checkout`/`stash`/`reset`/`clean`. No `make check`. No probe under
`src/`. `scripts/lint-agda.py --check` and `scripts/lint-prose.py --check`
both clean on my two files.

**My files:** `agents/tasks/LJ-1-230/ProbeLJ1230A.agda` and
`agents/tasks/LJ-1-230/lj-1.230-report.md`.
