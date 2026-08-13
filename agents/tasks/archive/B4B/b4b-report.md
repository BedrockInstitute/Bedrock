# Task B4b report: the pinning theorem, the fill, and the step

**Date:** 2026-08-02. **Scope:** B4b on `godel-route` — de-privatize Closure's
level family, delete the local restatement, then the B4a §5 worklist:
`layerIn`, `prefix-pins`, the fill, the step both ways, prose, `make check`,
and this report. **Files touched:** `src/L/Godel/Closure.lagda.md` (the one
bounded de-privatization), `src/L/Godel/Levels.lagda.md` (rewire + layer
machinery + the clause-level reader), `_build/b4b-report.md`. No git, no
postulates, no holes, no `TERMINATING` in the delivered code.

## 1. What is delivered, and the honest state

The chapter is **green end to end** (`agda src/L/Godel/Levels.lagda.md` and
`src/Everything.lagda.md`; `make check` passes the typecheck, i18n, prose, and
Agda-lint gates — the `reuse lint` step fails only on the sandbox's
`os.sysconf("SC_SEM_NSEMS_MAX")` `PermissionError`, the exact environmental
failure B4a already recorded). What is delivered:

1. **The de-privatization** (brief's first item) — done and green.
2. **The rewire** (delete the local level-family restatement, import
   `module C = L.Godel.Closure`) — done and green.
3. **`layerIn`** (B4a §5.1) — the `LayerIn` module with the per-tag layer
   builders and the `layerIn` dispatcher — green.
4. **The successor clause's reverse direction** `SucClauseRev` (needed to
   make the entry at a successor key a definite description) — green.
5. **`suc-clause`** — a new clause-level successor reader that reads both
   clauses at the binder numerals (any column), returning the previous entry,
   the layer, the union equation, and both per-member layer directions as
   direct projections of the clause bodies' witnesses — green.
6. **The pinning theorem, the fill, and the step are blocked** by a
   formula-level inconsistency in the B4a layer disjunction, itemized in §2.
   This report is written against that honest state.

## 2. The blocker: the values clause at arities ≥ 1

The layer disjunction `LayerDisjAt e p l k a` ends in
`∨̇ ValuesDisjAt e p l` **at every arity**. The meta step, however, has a
values image **only at arity zero**: in Closure, `tagValues : StepTag 0` and
`stepImage {n} {zero} tagValues m = values (⟪ slice n 1 ⟫↪ m)`. Consequently
`C.step A m k₀` for `k₀ ≥ 1` contains no values image, while the layer's
values clause reads the arity-one shelf at `(m , 1)` — present by `DomAdeq`
and generally non-empty — and describes members `values X` that are **not in**
`step A m k₀`. Both per-member directions of the layer identification break:

- **Out (layer ⊆ step):** a member of `L` satisfying `ValuesDisjAt` is
  `values X`, and `disj→step` has no `StepTag` of arity `k₀` to target
  (`C.tagValues : StepTag A 0`, so the values case is untypeable at
  `k₀ ≥ 1`).
- **In (step ⊆ layer):** the fill's `SucClauseRev` would have to put every
  values-satisfying member into its layer `step A m k₀`, which is false.

So `PrefixAt` is unsatisfiable at arities ≥ 1 for any table with a non-empty
arity-one shelf; the pinning theorem is **false as stated**, and the fill
(which certifies `PrefixAt`) and the step (which spends the pin at arity one)
are blocked on the same flaw. The B4b draft's own `layerIn-tag` carried the
same defect — its `layerIn-tag C.tagValues …` case is untypeable at a variable
arity — which is one reason the B4b draft region never compiled.

**Fix path (recorded for the follow-on):** remove the values disjunct from
`LayerDisjAt` (and from the clause-level `layerDisjCl`). The step's `B ≡ 𝒟ₒ A`
does not need a layer values clause: `step-out` reads `B`'s members per-member
and lands them via `Closure.cut-sound` (`u ∈ slice n 1 → values u ∈ 𝒟ₒ A`),
and `step-in` spends `cut-complete` then the fill's entry memberships. After
the removal, the pinning recursion only ever shops on shelves at the same
arity, one up (shift), and one down (extension) — the arity-one shelf is no
longer read by the layers at `k₀ ≥ 2` — and the dispatch chains in `suc-out`,
`suc-out-rev`, `LayerIn`, and the new pinning machinery each lose one case.
That is a mechanical but wide edit over green code, plus a full rewrite of the
pinning induction; it was not completed inside this session's budget.

## 3. The formulation trail for the pinning (what was tried, and why)

The pinning draft was rebuilt from scratch after the B4b draft's `finish`
region proved unrecoverable. The trail, item by item:

- **The `k`/`k₀` shadowing trap.** The B4b draft mixed the statement-level
  arity `k₀ : ℕ` with the section's slot index `k : Fin n` (`# k`,
  `C.step A m k`, `module LIC = LI {m} {k} ql qk qa`). Since `k : Fin n`,
  `# k` is ill-typed; the whole `finish` region (lines ~2078–2491 of the B4b
  draft) was never compileable. Every occurrence must be the numeric `k₀`.
- **The base/successor readers' unused equalities.** `baseS-out`'s `qk` and
  `domadeq-out`'s `ql qk` parameters are unused in their bodies (the key
  conversions use `numeralL-fst`); both were dropped, and the call sites that
  passed `numeralL-fst k′` where `fst (lookup k γ) ≡ # k′` was declared were
  the visible symptom of that dead parameter.
- **The goal-level recursion cannot pin other columns.** The environment's
  arity slot is fixed: `qk : fst (lookup k γ) ≡ # k₀`. Pinning the shift
  shelf at `(m , suc k₀)` would need `fst (lookup k γ) ≡ # (suc k₀)`, which
  contradicts `qk` by `#`-injectivity. So a per-column recursion at the goal
  level cannot supply the shelves the layer's shift/ext clauses read.
- **The clause-level reading.** The clause's layer disjunction reads the
  binders (`suc⁸ zero` = level numeral, `suc⁷ zero` = arity numeral), so the
  layer machinery can be instantiated over the clause environment with
  `LayerLaws {suc⁸ n} zero (sh8 t) (suc⁷ zero) (suc⁶ zero) (sh8 a) env` and
  binder equalities `numeralL-fst m`, `numeralL-fst k′` — no environment arity
  equality needed, and the shelves are at the (level, arity) keys of the
  table. The two layer directions are then literally the clause bodies'
  `∀̇` witnesses (`hLayer`, `hLayerRev`), with no CLI/RDI conversion.
  This is delivered as `suc-clause`, green.
- **The environment-abstractness trap.** Passing the clause environment as an
  opaque `env` parameter prevents `lookup (sh8 t) env` from reducing to
  `lookup t γ`; the layer machinery's shelves would not typecheck. The fix is
  to pass the environment *pieces* (`s₁ κ₁ κ₂ E'c E L`) and rebuild the
  concrete environment (`clEnvF`), which is what `suc-clause` outputs.
- **The arity condition.** The B4b draft's `suc k₀ < b₀` is insufficient for
  the recursion: pinning the shift shelf at `(m , suc k₀)` requires the
  recursion at column `suc k₀`, whose own condition is
  `m + suc (suc k₀) < b₀` — equal to `suc m + suc k₀ < b₀`, not derivable
  from `suc k₀ < b₀`. The correct condition is
  `n₀ + suc k₀ < b₀` (level plus arity below the bound); the shift chain
  then stays constant (`n₀ + k₀ + 1 < b₀`) down to the base at level zero,
  where `Base0`/`BaseS` apply without any condition. The extension shelf at
  `(m , k₀ ∸ 1)` needs a separate arity-one theorem when `k₀ = 2` and the
  full pinning when `k₀ ≥ 3` (a dispatch on `2≤k→k≡sucsuc`); the values
  shelf at `(m , 1)` would need its own arity-one theorem — all of which the
  values-clause blocker makes moot at `k₀ ≥ 2` until the clause is removed.
- **The step's top-level pin.** Even with the corrected condition, the
  arity-one pin at the top level `(b₀ , 1)` fails `b₀ + 2 < b₀`; the step's
  bound must sit a few levels above the pinned entry (or the step pins a
  level below the bound). This is a formulation decision for the step section,
  which remains blocked upstream.

## 4. The layer machinery (delivered)

- **`LayerIn`** (brief item 1): per-tag builders `inter-layer` …
  `values-layer` over the environment, each taking its own entry `W`,
  entry-membership `eW`, and entry-equals-slice proof `qW`; plus the
  dispatcher `layerIn : (t : StepTag A k₀) (pp : StepPayload A n₀ k₀ t) →
  ∥ Σ[ lZ ] ⟨ (stepImage t pp , lZ) ∷ γ ⊨ LayerDisjAt … ⟩ ∥₁` supplied by a
  per-arity entry family. Green.
- **`SucClauseRev`** (the reverse ∀̇, added to `PrefixAt` as the sixth
  conjunct): every member the layer disjunction describes is in the layer.
  The forward-only `SucClause` admits junk tables whose layer omits the
  images, which would break the pinning; the conjunction makes the successor
  entry a definite description. Green.
- **`suc-clause`** (new): reads `SucClause` and `SucClauseRev` at the binder
  numerals `(m , k′)`, returning the previous entry, the layer, the union
  equation, and both directions as direct projections. Green.

## 5. Which InL names were public vs restated

Public and used directly (no restatement): `capL`, `cupL`, `diffL`,
`selectMemberL`, `selectEqualL`, `allTuplesL`, `shiftDownL`, `extendFamilyL`,
`valuesL` from `L.Godel.InL`; `sglL` from `L.Coding.InL`; `numL` from
`L.Coding.Model` (private in `L.Godel.InL`). The fill's packing surface
(`stageFam`, `finSet`/`FinOf.finSetL`) was imported for the packed table and
removed again with the blocked fill, so the deliverable's import list is
exactly the used names. Restated locally (B1/B2 precedent): `sglAt′` and the
`SglDesc.singletonsAt` description. The local `singletons` family from B4a is
**deleted**: after the de-privatization, `C.singletons A` is used throughout.

## 6. Timings

Whole-file checks on this machine: `Levels` cold ≈ 30 s, warm ≈ 2 s;
`Closure` after the de-privatization ≈ 1.5 s warm (cold ≈ 5 s with warm
interfaces; **no material timing change** — the `private` removal touches no
definitional content). Per-section cold timings from the session (each a
full-file cold check): rewire (import + `C.singletons` replacement) ≈ 16 s;
`SucClauseRev` ≈ 17 s; `LayerIn` ≈ 9–27 s across its iterations;
`suc-out-rev` ≈ 26–34 s; `suc-clause` ≈ 30 s. The 180 s wall was never hit;
the expensive pieces are the layer disjunct chains, not any single definition.

## 7. LESSONS

P-d (direction pairs: every reader has its in/out pair; the successor clause
gained its reverse), P-c (sealed-at-birth discipline for the fill's packed
table — deferred with the fill), Rule 1 (discharge substitutions at variable
arguments), Rule 8 (name `PT.rec` payloads), Rule 10 (named helpers for case
splits into membership), Rule 20 (composites factor by factor; the layer chain
is factored into per-disjunct readers), D-2 (junk excluded by construction),
C-8 (linters run explicitly; the glossary and marker checks need `.venv`'s
Python 3.11), and the wall rule (a blocker binds LESSONS and the report
records the formulation trail — this report is the record).

## 8. Surprises

1. **The values clause at arities ≥ 1** (this report's §2) is inconsistent
   with the meta step: `tagValues : StepTag 0` only, while `LayerDisjAt`
   carries `ValuesDisjAt` at every arity. This is a B4a-legacy formula flaw,
   and it blocks the pinning, the fill, and the step.
2. **The goal-level recursion cannot pin other columns** (§3): the
   environment's arity slot fixes one column, so the layer's neighbouring
   shelves must be read at the clause level (the binders), not the goal level.
3. **The Fin/numeric `k` shadowing** (§3) made the entire B4b draft `finish`
   region uncompilable from the start.
4. **The arity condition must carry the level** (§3): `n₀ + suc k₀ < b₀`,
   not `suc k₀ < b₀`, or the shift chain fails at the first step down.
5. **The successor reverse direction** `SucClauseRev` is required for
   determination, and its layer sits in a *different* clause environment than
   the forward clause's (the two layers are bridged at the union level, not
   identified).
6. **Abstract clause environments defeat `lookup` reduction** (§3); the
   environment must be passed as its pieces.
7. **`make check`'s `reuse lint` cannot run in this sandbox**
   (`os.sysconf` `PermissionError`), exactly as B4a recorded; the other four
   gates pass.

## 9. Prose

The chapter's prose stands at the B4a state (the layer section and the
prefix-table description, en + zh). The pinning, fill, and step sections were
not written because those blocks are not delivered; the follow-on should add
them (钉住定理 in zh, per the B1–B3 usage) once the §2 fix lands.
