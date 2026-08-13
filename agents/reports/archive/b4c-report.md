# Task B4c report: the guarded clauses, the pinning, and the honest state

**Date:** 2026-08-02. **Scope:** B4c on `godel-route` — fix the values clause
with the arity-zero guard (not a removal), then the pinning, the fill, and the
step, per the brief. **Files touched:** `src/L/Godel/Levels.lagda.md`,
`_build/b4c-report.md`. No git, no postulates, no holes, no `TERMINATING`.

## 1. Status

The chapter is **green end to end** (`agda src/L/Godel/Levels.lagda.md` and
`agda src/Everything.lagda.md`; the prose linter, the i18n marker check, the
Agda-code linter, and the glossary check all pass; `reuse lint` is the one
environmental failure recorded in §8, unchanged from B4a/B4b).

Delivered:

1. **The values guard** (brief's first item) — exactly as prescribed: the
   `ValuesDisjAt` keeps the values disjunct and gains one conjunct pinning the
   layer's arity slot to the zero numeral (`var (sh4 k) ≐ con (numeralL 0)`).
   All machinery adjusted: the LayerLaws readers both directions carry the
   guard (the out-reader returns the zero pin `k₀ ≡ 0` as data; the in-reader
   takes it), `LayerIn.values-layer` supplies the pin at the `tagValues` case
   (where `k₀` is forced to zero, so the pin is `refl`, and the in-reader
   assembles the object-level guard witness with `numeralL-fst 0`), and the
   `suc-out`/`suc-out-rev` dispatch chains carry the zero pin through.
2. **The extension guard** (a blocker discovered during the brief-mandated
   clause-by-clause check, see §2) — `ExtDisjAt` gains one conjunct pinning the
   source slot away from the zero numeral
   (`¬̇ (var (suc⁴ zero) ≐ con (numeralL 0))`), so the disjunct is refuted at
   layer arity one (where the meta step has no `tagExt` image) and satisfiable
   at every arity from two on, exactly matching `tagExt`'s positive-source
   one-up shape. All readers, the `LayerIn` extension builder, and both
   dispatch chains adjusted; the out-reader additionally returns the successor
   witness `sucV (fst s) ≡ # k₀` (needed by the pinning's extension case).
3. **The pinning theorem** `prefix-pins` (brief item 1 of the worklist) — at
   full strength: every entry at every key `(n₀, k₀)` with the combined
   condition `n₀ + suc k₀ < b₀` equals `C.slice A n₀ k₀`, by induction on the
   level numeral, consuming `suc-clause`'s outputs and the two per-member
   clause directions, with the per-disjunct layer-out landers and the per-tag
   layer-in builders described in §4. No weakening: the statement is exactly
   the trail's all-keys-at-once form with the level-plus-arity bound.
4. **Prose** (en + zh): the guarded layer paragraph pair, the pinning section,
   and the Recap (brief item 4).

Not delivered: **the fill** (`sliceL`, the packed prefix table, `prefix-fill`)
and **the step** (`StepAt`, `step-out`, `step-in`) — see §5 for the blocker
and the recorded formulation trail. This report is written against that honest
state, exactly as the B4b precedent.

## 2. The clause-by-clause meta-match check (brief's mandated table)

The check against `Closure`'s `StepTag`/`StepPayload`/`stepImage`:

| layer disjunct | meta tag | arities where it matches | mismatch |
|---|---|---|---|
| `InterDisjAt` | `tagInter`, same shelf | all | none |
| `UnionDisjAt` | `tagUnion`, same shelf | all | none |
| `DiffDisjAt` | `tagDiff`, same shelf | all | none |
| `SelMDisjAt` | `tagSelM`, same shelf, indices from the arity numeral | all | none |
| `SelEDisjAt` | `tagSelE`, same shelf, indices from the arity numeral | all | none |
| `AllTuplesDisjAt` | `tagAll`, `allTuples A k` from the numeral alone | all, including arity zero | none |
| `ExtDisjAt` (guarded) | `tagExt`, source one arity down, image one up | arities ≥ 2 (refuted at 0 by `sucAtL`-injectivity, refuted at 1 by the new guard) | **arity one before the guard** |
| `ShiftDisjAt` | `tagShift`, source one arity up | all | none |
| `ValuesDisjAt` (guarded) | `tagValues`, source the arity-one shelf, image the value shelf | arity zero (refuted at positive arities by the new guard) | **positive arities before the guard** |

The values mismatch was the brief's known blocker and is fixed exactly as
prescribed. The extension mismatch at arity one was **not** anticipated by the
brief ("the other eight disjuncts match the meta step at every arity
already"); the check surfaced it, and it is the same disease as values: at
layer arity one, `sucAtL` forces the source slot to the zero numeral, the
disjunct reads the arity-zero shelf, and describes `extendFamily` images that
the meta step at arity one does not contain (`StepPayload n (suc (suc k))
tagExt = Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] ⟪ A ⟫` has no solution for image arity
one). The empirical confirmation: the delivered `ExtDisj-in` reader
instantiates the arity-one disjunct satisfaction from a shelf-zero entry, a
carrier member, and the image equation (scratch test in §6). The fix is the
parallel positive-source guard (one conjunct, `¬̇ (source ≐ 0)`), which is
refuted at arity one by the numeral clash and leaves arities ≥ 2 untouched;
removing the disjunct would have been wrong for the same reason the brief
gives for values (it would falsify the successor union equation at the arities
where the meta does have extension images, and the fill's reverse clause would
break). This deviation from the brief's "the other eight already match" is
recorded here as the report's primary surprise; the pinning theorem itself is
delivered at the brief's full-strength statement.

## 3. The guarded values clause, in detail

`ValuesDisjAt e p l k` now reads: the member at `e` is `values X` for a member
`X` of the previous entry at the key `(l, n1)` with `n1` the numeral one, and
the layer's arity slot `k` pinned to the zero numeral. At arity zero the guard
is satisfiable and the disjunct reads shelf one exactly as the meta
`tagValues` does; at positive arities `#-inj′`-class numeral injectivity refutes
it, so the over-description disappears (refuted, not untypeable, which is what
the dispatch chains need). `LayerLaws.ValuesDisj-out` now takes `qk` and
returns `k₀ ≡ 0` as data alongside the shelf-one shape;
`LayerLaws.ValuesDisj-in` takes `qk` and the zero pin and assembles the
object-level guard witness via `numeralL-fst 0`. `LayerIn.values-layer` gains
the zero pin as a parameter; the dispatcher's `tagValues` case supplies it
(`refl`, since `tagValues : StepTag 0` forces `k₀` to zero there). The
`suc-out`/`suc-out-rev` chains carry the pin through their values case.

## 4. The pinning theorem

`prefix-pins : (h : ⟨ γ ⊨ PrefixAt t b a ⟩) → (b₀ : ℕ) → fst (lookup b γ) ≡
# b₀ → (qa : fst (lookup a γ) ≡ A) → (n₀ k₀ : ℕ) → n₀ + suc k₀ < b₀ → (E : S)
→ ⟨ pr (pr (# n₀) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩ → fst E ≡ C.slice A n₀
k₀`.

- **Base** (`n₀ = 0`): arity zero via `base0-out` plus `qa`; positive arity via
  `baseS-out` at the successor numeral, no condition needed beyond the bound.
- **Successor**: `suc-clause` at the binder numerals gives the previous entry,
  the layer, the union equation, and both per-member layer directions. The
  out-direction (`sub₁`) lands each layer member in the meta slice per disjunct
  via the matching `slice-in` law, spending the pin at the shelf the disjunct
  reads: same-arity shelf for the binary/selection disjuncts, the shelf one
  arity up for the shift, the shelf one arity down (via `∈#-elim`, with the
  zero-arity source refuted by the extension guard) for the extension, and the
  arity-one shelf (with the arity transported by the values pin) for values.
  The arithmetic toolkit (`cond-same`, `cond-shift`, `cond-ext`,
  `cond-values`) derives each sub-pin's condition from the level-plus-arity
  bound; the shift chain stays constant (`m + suc (suc k₀) ≡ suc m + suc k₀`
  up to `m+sn`), which is the trail's exact reason for the combined bound.
- **In-direction** (`sub₂`): `C.slice-out` splits the member into an old
  member (pinned previous entry, returned through the union equation) or a
  tagged step image; the per-tag builders (`step→layer`) rebuild the
  clause-level layer disjunction with the `LayerLaws` in-readers, spending the
  pins at the shelves the payload draws from (the same-arity entry is the
  reverse clause's own previous entry; the shift/extension/values shelves come
  from `domadeq-out` plus the recursion), returning the member to the entry
  through the reverse clause witness and the second union equation.
- The per-key equality is `extensionality` of the two per-member directions.

The k₀ discipline is as the trail demands: every arity in the statement is a
numeral `# k₀` with `k₀ : ℕ`; no `Fin` slot appears in the statement.

## 5. The fill and the step: the blocker and the trail

The fill is blocked on the constructibility of the meta level family itself.
`sliceL : (n k : ℕ) → ⟨ isL (C.slice A n k) ⟩` is needed for every packed
entry, and the successor case `slice A (suc n) k = slice A n k ∪ step A n k`
requires `⟨ isL (C.step A n k) ⟩` for the layer entry
(`step A n k = sett (Σ[ t ∈ StepTag k ] StepPayload n k t) stepImage`). The
`step` index is a sum over the finite tag set of **infinite fibers** of the
shelves, so no finite-family lemma (`stageFam`, `finSet`) applies, and the
general "sett of constructible elements is constructible" principle is **false**
(`sett (V ℓ) id` would be a constructible set containing every V-element,
contradicting that non-constructible elements exist). The remaining route is
`defSet→isL` with a defining formula over a stage containing the shelves (the
stage-refined layer disjunction, in the `InL.Vals`/`SftD` idiom), plus the
`defSet ≡ step n k` extensionality against the slice-in/slice-out laws — a
substantial multi-hundred-line definability argument that did not fit in this
session's budget. The step (`StepAt`, `step-out`/`step-in` under `WithLEM`)
consumes the pinning at the arity-one key and `Closure.cut-sound`/`cut-complete`
and is blocked downstream of the fill. No weaker substitute is shipped: the
pinning is full-strength, and the fill/step are recorded honestly, per the
brief's stop-and-report rule and the B4b precedent.

## 6. Which InL names were public vs restated

Public and used directly (no restatement): `capL`, `cupL`, `diffL`,
`selectMemberL`, `selectEqualL`, `allTuplesL`, `shiftDownL`, `extendFamilyL`,
`valuesL` from `L.Godel.InL`; `sglL` from `L.Coding.InL`; `numL` from
`L.Coding.Model`. `C.singletons`, `C.singletons-in`, and the closure level
family (`C.slice`, `C.step`, `C.StepTag`, `C.StepPayload`, `C.stepImage`, the
`C.slice-*` laws, `C.slice-out`, `C.slice-old`) are all public after B4b's
de-privatization and are used directly. Nothing new was restated. (The fill's
`sliceL` was to restate nothing either; it is blocked, not restated.)

## 7. Timings and walls

No definition crossed the 180 s wall. Whole-file cold checks of `Levels` ran
~30–60 s in the session (the pinning region dominates); warm checks ~2–10 s;
`Everything` warm ~3 s. The per-definition budget was respected throughout.

## 8. LESSONS

Applied: P-d (direction pairs; the pinning's two per-member directions), P-c
(the fill's packed-table seal, deferred with the fill), Rule 1 (discharge
substitutions at variable arguments), Rule 8 (named `PT.rec` payloads), Rule 10
(named helpers for the disjunct dispatch), Rule 20 (the layer chain factored
per disjunct; the pinning's landers and builders factor the same way), D-2
(junk excluded by construction: the extension guard is this doctrine applied
to the discovered arity-one over-description), C-8 (linters run explicitly; the
glossary/marker checks need the venv's Python 3.11). Newly recorded: the
extension-at-arity-one over-description (surprise 1), and the step
constructibility blocker with its trail (§5). The `reuse lint` stage fails
only on the sandbox's `os.sysconf("SC_SEM_NSEMS_MAX")` `PermissionError`, the
recorded environmental failure from B4a/B4b.

## 9. Surprises

1. **The extension disjunct over-describes at arity one** (parallel to the
   values blocker): the brief's claim that the other eight disjuncts already
   match at every arity fails for `ExtDisjAt` at arity one, where the source
   slot is forced to the zero numeral and the meta step has no `tagExt` image.
   Confirmed empirically by instantiating the delivered `ExtDisj-in` reader at
   arity one (scratch module in `/private/tmp/ext-test.agda`, since removed
   from the tree). The fix is the parallel positive-source guard, recorded in
   §2.
2. **The meta step's constructibility is not a free lemma**: `sett` over the
   tag-sum of infinite fibers is not covered by any existing isL machinery and
   the general principle is false; the fill's `sliceL`/`stepL` needs the
   stage-definability route (§5).
3. `# (suc n) ≡ sucV (# n)` is definitional in the scratch context but did not
   reduce in the chapter's deep memberships; the proof carries explicit
   numeral witnesses throughout (the B4a "opaque numerals" note holds in
   practice).
4. The `PT.rec` eliminator's domain is the untruncated sum of the disjunction
   satisfaction, so the pinning's dispatch chain takes truncated satisfaction
   inputs and eliminates inside; the `suc-clause` output's single outer
   truncation is unpacked once and destructured by nested patterns.

## 10. Verification

`agda src/L/Godel/Levels.lagda.md` and `agda src/Everything.lagda.md` are
green; `lint-prose.py --check`, `weave-i18n.py --check`,
`check-glossary.py --check`, and `lint-agda.py --check` pass on the tree. The
only failing gate is `reuse lint` (environmental, recorded above).
