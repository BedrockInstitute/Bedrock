# R2a report: the ordinal-arithmetic side module (`L.Rud.OrdArith`)

Task `[L3.31-R2a]`, wave-1 agent report. Scope: create
`src/L/Rud/OrdArith.lagda.md` plus this report, nothing else. Outcome:
**thin gap module, delivered and green**. The survey confirmed that nearly
everything the S-recursion needs from ordinals already exists; the module
adds only the case-structure material that nothing in the delivered ordinal
chapters provides: the successor and limit predicates as hProps, the
zero/successor/limit trichotomy, and the successor interaction lemmas.

## 1. Survey: what the Def tower needed from ordinals, and where it got it

The Def tower's needs from ordinal theory were minimal, and every one was
met by existing code:

| need | where it got it | file:line |
|---|---|---|
| the tower-index predicate `IsOrd` + its propositionality | defined inside `L.Constructible` itself, not `L.Ordinal` | `src/L/Constructible.lagda.md:141` to `:145` |
| the tower recursion | membership recursion (`∈-induction`) over every set, one equation covering zero/successor/limits, no ordinal arithmetic anywhere | `LsetStep` `:215`, `Lset` `:222`, `Lset-compute` `:227`; the recursion engine `regularityV`/`∈-induction` at `src/V/Hierarchy.lagda.md:139`, `:177` |
| the layer predicate and transitivity of stages | `data isLayer` `:175`, `layer-trans` `:183` (ordinal-free closure principles) | `src/L/Constructible.lagda.md` |
| the class `isL` / `Lset→isL` | consume `IsOrd` + `isPropIsOrd` as the index predicate | `:376`, `:395` |
| stage bounds for closure arguments | `∅-ord` `:77`, `suc-ord` `:96`, `setUnion-ord` `:125`, `boundingOrd` `:154`, `bound2` `:185`, consumed by `L.Axioms.Basic:54`, `L.Axioms.Full:50`, `L.Axioms.Power:57`, `L.Axioms.Separation:58`, `L.Axioms.Infinity:23` | `src/L/Ordinal.lagda.md` |
| downward closure | `mem-ord` `:221` | `src/L/Ordinal.lagda.md` |
| comparison / trichotomy | `ord-tri` `:136`, classical through the `(lem : LEM (ℓ-suc ℓ))` telescope, consumed by `L.Ordinal.Stages` and `L.Stage:49` | `src/L/Ordinal/Linear.lagda.md` |
| ordinals at stages | `ord∈Lset-suc`, `ord∈Lset→∈`, consumed by `L.Axioms.Infinity:24` | `src/L/Ordinal/Stages.lagda.md` |

**Conclusion.** The Def tower itself needed almost no ordinal theory; the
delivered supply (predicate, closure, bounds, downward closure, comparison)
carried it. What the S-mirror adds is a genuinely new requirement: the
recursion is written with explicit zero, successor, and limit clauses (the
memo's module-separation decision, SZ Definition 1.6, digest section 3), so
it must *classify* ordinals before running. No delivered module has a limit
predicate or a zero/successor/limit case split, so those are the gaps. The
sup/union fact for the limit clause is **not** a gap: `setUnion-ord`
(`Ordinal.lagda.md:125`) instantiates directly at the small family `⟪ α ⟫`
of members, so nothing was added for it (a good outcome, not a failure).

## 2. Gap list delivered

All in `src/L/Rud/OrdArith.lagda.md` (98 code lines including header and
imports; 72 non-blank lines of definitions; stop-line 400 respected).

| item | code lines | role |
|---|---:|---|
| `sucV-inj-ord` | 27 | successor is injective on ordinals; makes the successor witness a proposition (supporting lemma, see surprises) |
| `isSucc` | 6 | hProp "α is the successor of an ordinal", witness = predecessor + its ordinality + the equation |
| `predecessor-mem` | 2 | successor clause descent: `β ∈ˢ α` from `sucV β ≡ α` (hands the recursion its membership witness) |
| `predecessor-ord` | 2 | successor clause: `IsOrd β` from `IsOrd α` and the equation |
| `succ-not-zero` | 3 | disjointness of the zero and successor cases |
| `isLimit` | 4 | the limit-ordinal predicate as an hProp: ordinal, not zero, not a successor |
| `isLimit-ord`, `isLimit-not-zero`, `isLimit-not-succ` | 6 | the three reads of the limit predicate |
| `succ-not-limit` | 2 | successor-limit interaction: a successor is never a limit |
| `limit-mem-ord` | 2 | limit clause: members of a limit are ordinals (downward closure), so the recursion's hypothesis applies at each member |
| `ord-case` | 13 | the zero/successor/limit trichotomy, LEM spent here (two decisions), the recursion's case split |
| **total** | **67** | definitions (98 including header/imports) |

Module header: `module L.Rud.OrdArith {ℓ : Level} (lem : LEM (ℓ-suc ℓ))`,
the classical-cone telescope of `L.Ordinal.Linear`; no abstract module
parameters beyond it, per the brief (concrete ordinal material). The
trichotomy is the only classical statement; everything else is
constructive.

## 3. Per-item sizes and timings

- Cold check of the whole module: **0.92 s** (`--profile=definitions` total,
  first dependency-cold run 1.08 s); warm recheck ~1.0 s. Every definition
  is far below profile granularity (`Miscellaneous` absorbs the total), so
  per-item timing is not meaningful; per-item *sizes* are in section 2.
- No definition approaches the 180 s wall; no wall, no NO-GO trail.
- Linters on the new file (run explicitly per C-8, since `git ls-files`
  skips untracked files): `lint-prose.py` 0 violations, `weave-i18n.py
  --check` green, `lint-agda.py` 0 violations (OPTIONS header, import
  necessity, no forbidden constructs).

## 4. LESSONS applied

- **I-2**: every hProp-valued expression in a signature is `⟨_⟩`-wrapped
  (`⟨ isLimit α ⟩`, `⟨ isSucc α ⟩`); the hProps themselves are built as
  pairs with explicit proposition-hood proofs.
- **P-i / record discipline (named helpers)**: the successor-injectivity
  case split names every branch (`β∈`, `γ∈`, `excl₁`, `excl₂`, `mem₁`,
  `mem₂`, `go`) with stated types instead of inlining heavy membership
  types under the case eliminator, the pattern `L.Ordinal.Stages` uses for
  the same reason.
- **R-34**: every `L.*`/`V.*` import pins the universe level explicitly
  (`{ℓ}`); no open level metas.
- **C-8**: new-file linters run by hand (see section 3).
- **Classical-cone discipline** (STYLE-agda §1): LEM is a module parameter,
  visible in the header, spent only in `ord-case`; no postulates anywhere.

## 5. Surprises (with lesson candidates)

1. **`Σ[ β ∈ S ] (sucV β ≡ α)` is not automatically a proposition.**
   A Σ over a set with propositional fibers is a proposition only when the
   fibers are *provably at most one*; here that is successor injectivity,
   which nothing in the delivered ordinal chapters had. The hProp
   construction for `isSucc` forced `sucV-inj-ord` (27 lines) into the
   module, a gap the brief did not list but the trichotomy cannot run
   without. Lesson candidate: before LEM can decide a witness-shaped
   proposition, verify at-most-one witnesses; injectivity is often the
   missing lemma.
2. **No `Lift`/`lowerLEM` needed.** `S = V ℓ` lives one universe up, so all
   propositions in this cone sit at `ℓ-suc ℓ`, exactly the level of the LEM
   parameter; `lem (α ≡ ∅ , isSetS α ∅)` and `lem (isSucc α)` decide
   directly. I had planned `lowerLEM`; the first typecheck made the level
   bookkeeping plain and the transfer lemma unnecessary.
3. **The limit clause needs no new union fact.** `setUnion-ord`
   (`Ordinal.lagda.md:125`) already bounds the clause at the small family
   `⟪ α ⟫`; verifying rather than assuming dropped a planned lemma. This is
   the "thin re-export with gap lemmas" outcome the brief names as good.
4. **Subst direction bug in the self-membership contradiction.** The first
   formulation of `excl₁`/`excl₂` substituted the path the wrong way
   (`γ != β` from the checker); the fix transports along `sym`, since the
   membership's left endpoint is fixed and the path must move the right
   endpoint. Lesson candidate: when transporting a membership with a fixed
   left argument, the path must run in the second argument, i.e. `sym` of
   the equality as stated.

## 6. Terminology surfaced (per AGENTS.md)

- "limit ordinal" is not in `dev/glossary.toml`; this module uses zh
  极限序数 (ja would be 極限順序数), chosen by meaning, awaiting the owner's
  ruling if the term becomes load-bearing.
- The interim rendering for the rudimentary class, 「rud 函数」, is not used
  here; prose refers to the rud development only as `rud 开发` / `rud
  层级`, and the S-recursion's cases as 零/后继/极限, consistent with the
  existing ordinal chapters' vocabulary (情形, 三歧, 排中律).

## 7. Files and hygiene

- Created: `src/L/Rud/OrdArith.lagda.md` (248 lines total, prose en + zh,
  markers balanced, no em dash, zh full-width punctuation, long zh
  paragraphs on one line).
- Created: `_build/r2a-report.md` (this file).
- Not touched: `src/Everything.lagda.md`, the other wave-1 files
  (`Ops`, `Images`, `Realize`), `.claude/`, git (no commits).
