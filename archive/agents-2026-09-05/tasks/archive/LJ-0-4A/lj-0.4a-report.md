# LJ-0.4a: compression block A, the dead names and one shortened proof

Status: COMPLETE. No commit, no push. The tree is as this report describes.

## 1. THE NUMBER

Standing before: 17,492 non-blank in-fence lines over 75 masters. Source:
`scripts/ledger.py --brief`, 2026-08-10.

Standing after: 17,252 non-blank in-fence lines over 75 masters.

Net lines: minus 240.

The target band is minus 226 to minus 296. The measured reduction is inside
the band.

How the after figure was measured: `scripts/ledger.py` reads HEAD only
(`scripts/ledger.py:84-88`). I cannot commit. I ran the ledger's own count
function with `at_head=False` on the working tree. The algorithm and the fence
caliber are the same. The before figure from `--brief` matches the HEAD sum of
the same count.

## 2. WHAT I DELETED

Method, stated once: I rebuilt the name-flow scan over the 75 masters. The
scan extracted declaration names and counted boundary-aware occurrences in
` ```agda ` fences. A candidate was dead only when all of these held:

- no boundary-aware occurrence existed outside its own declaration block;
- no mention appeared in `_build/lj-1.1-recon.md`;
- no mention appeared in `src/Everything.lagda.md`, `src/README.md`, `README.md`
  or `docs/` prose;
- no rendered mixfix form appeared in any fence.

I read every candidate block and every occurrence line. I deleted 48 names.
The declaration lines total 229. Dead import lines add 11. The ledger
measures minus 240.

| Name | File:line | Lines | How verified |
|---|---|---:|---|
| `codesT-complete` | FOL/Coding.lagda.md:198-200 | 3 | dead only with `codes-complete`; whole-tree grep after edit |
| `codes-complete` | FOL/Coding.lagda.md:202-214 | 13 | zero boundary-aware consumers |
| `codesT-canon` | FOL/Coding.lagda.md:216-218 | 3 | dead only with `codes-canon`; whole-tree grep after edit |
| `codes-canon` | FOL/Coding.lagda.md:220-236 | 17 | zero boundary-aware consumers |
| `∅-spec` | FOL/ZFModel.lagda.md:270-271 | 2 | zero consumers, no prose name |
| `⋃-spec` | FOL/ZFModel.lagda.md:282-283 | 2 | zero consumers, no prose name |
| `_⁺` | FOL/ZFModel.lagda.md:288-289 | 2 | rendered form `x ⁺` absent from all fences; prose trimmed |
| `𝒫-spec` | FOL/ZFModel.lagda.md:300-301 | 2 | zero consumers, no prose name |
| `ω-spec` | FOL/ZFModel.lagda.md:393-394 | 2 | zero consumers, no prose name |
| `mereSetOf→isContr` | FOL/ZFModel.lagda.md:419-420 | 2 | zero consumers; prose claim removed |
| `x∉x` | FOL/ZFModel.lagda.md:422-423 | 2 | zero consumers; prose claim removed |
| `DefAt-𝒟ₒS` | L/Coding/Powerset.lagda.md:729-733 | 5 | zero consumers, no prose name |
| `allCodes-spec` | L/Coding/Base.lagda.md:99-101 | 3 | zero consumers, no prose name |
| `code∈allCodes` | L/Coding/Base.lagda.md:103-104 | 2 | zero consumers, no prose name |
| `allCodesTerm` | L/Coding/Base.lagda.md:106-107 | 2 | dead only with `allCodesTerm-eval`; whole-tree grep after edit |
| `allCodesTerm-eval` | L/Coding/Base.lagda.md:109-110 | 2 | zero consumers, no prose name |
| `envOf` | L/Coding/Environment.lagda.md:88-89 | 2 | zero consumers, no prose name |
| `env-spec` | L/Coding/Environment.lagda.md:91-95 | 5 | zero consumers, no prose name |
| `Δ₀-memPairAt` | L/Coding/Environment.lagda.md:145-146 | 2 | zero consumers, no prose name |
| `memPairAt-adequate` | L/Coding/Environment.lagda.md:148-163 | 16 | zero consumers; recap claim trimmed |
| `seqSet-spec` | L/Coding/Environment.lagda.md:259-263 | 5 | zero consumers, no prose name |
| `seqSet-mem` | L/Coding/Environment.lagda.md:265-267 | 3 | zero consumers, no prose name |
| `codeFreeL` | L/Coding/InL.lagda.md:153-155 | 3 | zero consumers, no prose name |
| `Key` | L/Coding/Closed.lagda.md:282-283 | 2 | private; used only by the dead section |
| `cd` | L/Coding/Closed.lagda.md:285-286 | 2 | private; used only by the dead section |
| `ct` | L/Coding/Closed.lagda.md:288-289 | 2 | private; used only by the dead section |
| `kk` | L/Coding/Closed.lagda.md:291-292 | 2 | private; used only by the dead section |
| `nn` | L/Coding/Closed.lagda.md:294-295 | 2 | private; used only by the dead section |
| `atKey` | L/Coding/Closed.lagda.md:297-300 | 4 | private; used only by `closureLeast` |
| `sub` | L/Coding/Closed.lagda.md:302-308 | 7 | private; used only by `closureLeast` |
| `two` | L/Coding/Closed.lagda.md:310-320 | 11 | private; used only by `closureLeast` |
| `closureLeast` | L/Coding/Closed.lagda.md:322-357 | 36 | zero boundary-aware consumers; the whole last section died with it |
| `slot-in` | L/Coding/Table.lagda.md:321-322 | 2 | zero consumers, no prose name |
| `val-key` | L/Coding/Uniform.lagda.md:349-351 | 3 | zero consumers; recap names removed |
| `defStage-misses` | L/Choice/Stage.lagda.md:291-296 | 6 | zero consumers, no prose name |
| `bound-limit` | L/Choice/Stage.lagda.md:338-340 | 3 | zero consumers, no prose name |
| `bound-self` | L/Choice/Stage.lagda.md:342-343 | 2 | zero consumers, no prose name |
| `bound-below` | L/Choice/Stage.lagda.md:345-348 | 4 | boundary-aware grep excludes `bound-below₂` |
| `NameAt-out` | L/Choice/Internal.lagda.md:714-725 | 12 | zero consumers, no prose name |
| `isPropBundle` | L/Choice/Table.lagda.md:676-685 | 9 | zero consumers, no prose name |
| `bornOrd` | L/Choice/Faithful.lagda.md:432-433 | 2 | zero consumers, no prose name |
| `limitS-fst` | L/Choice/Limit.lagda.md:409-410 | 2 | zero consumers, no prose name |
| `val∈table` | L/Recursion.lagda.md:236-237 | 2 | zero consumers, no prose name |
| `fn∈table` | L/Recursion.lagda.md:349-350 | 2 | zero consumers, no prose name |
| `table→fn` | L/Recursion.lagda.md:352-355 | 4 | zero consumers, no prose name |
| `isPropHierOf` | L/Hierarchy.lagda.md:537-541 | 4 | zero consumers, no prose name |
| `βω-ord` | L/Reflect.lagda.md:488-489 | 2 | zero consumers, no prose name |
| `subFo-is-⊆` | L/Axioms/Power.lagda.md:101-102 | 2 | zero consumers, no prose name |

Line numbers are the original HEAD positions. The ledger deltas per file are
the measured totals. FOL/Coding minus 36, FOL/ZFModel minus 15, Powerset
minus 5, Base minus 9, Environment minus 34, InL minus 4, Closed minus 76,
Table minus 2, Uniform minus 3, Stage minus 15, Internal minus 12,
Choice/Table minus 9, Faithful minus 2, Limit minus 2, Recursion minus 8,
Hierarchy minus 4, Reflect minus 2, Power minus 2.

## 3. WHAT I KEPT FOR THE FUNDED PLAN

Names in `_build/lj-1.1-recon.md`:

| Name | File:line | Where the plan uses it |
|---|---|---|
| `Sat-out` | L/Coding/Bridge.lagda.md:577-583 | recon section 2.1 names it as part of the delivered bridge |
| `σ₁-up` | FOL/Absoluteness.lagda.md:182-186 | recon section 2.2 and Block 1 ride it |
| `π₁-down` | FOL/Absoluteness.lagda.md:187-190 | recon section 2.2 and Block 1 ride it |

Names kept because `src/Everything.lagda.md` prose names them and that file
is off-limits to me:

| Name | File:line | Everything prose |
|---|---|---|
| `AllCodes-spec` | L/Coding/CodeSet.lagda.md:578-579 | :504, :945 |
| `Codes-spec` | L/Coding/CodeSet.lagda.md:489-490 | :504, :945 |
| `Lset-μ` | L/Choice/Stage.lagda.md:286-290 | :631, :953 |
| `asPure₁` | FOL/Manipulation/Parameters.lagda.md:475-478 | :193, :276 |
| `codeFree-limit` | L/Choice/Internal.lagda.md:392-399 | :709, :957 |
| `denote-table` | L/Choice/Name.lagda.md:478-484 | :659, :955, :960 |
| `endExtension` | L/Choice/Step.lagda.md:843-845 | :692, :956 |
| `ix-fill` | L/Choice/Table.lagda.md:905-908 | :754, :958 |
| `ix-rep` | L/Choice/Table.lagda.md:909-911 | :754, :958 |
| `leastPin` | L/Choice/Adequate.lagda.md:910-916 | :960 |
| `val-defSet` | L/Coding/Uniform.lagda.md:390-395 | :525, :946 |
| `witnessInModel` | L/Recursion.lagda.md:139-141 | :622, :952 |

`Codes-spec` is a judgement call. I kept it. The reasons: it is the closing
round-trip theorem of the code set, the `[LJ-1.2]` NO-GO analysis is about the
code set, and `src/Everything.lagda.md:504` names it in prose I cannot edit.
Deleting it would leave stale prose in an off-limits file. `AllCodes-spec`
shares both reasons.

Names kept because `src/README.md` names them:

| Name | File:line | README line |
|---|---|---|
| `Def-spec` | L/Definability.lagda.md:137-140 | src/README.md:73 |
| `A∈Def` | L/Definability.lagda.md:195-197 | src/README.md:73 |

Names kept because they are prose-only after their spec lemmas died, and
`src/Everything.lagda.md` names them:

| Name | File:line | Everything prose |
|---|---|---|
| `memPairAt` | L/Coding/Environment.lagda.md:142-143 | :233, :287 |
| `seqSet` | L/Coding/Environment.lagda.md:256-257 | :234, :287 |
| `allCodes` | L/Coding/Base.lagda.md:96-97 | :228, :286 |

Live false positives the scan or I initially flagged:

| Name | File:line | Why it lives |
|---|---|---|
| `_⊆ᵇ_` | L/Ordinal/Linear.lagda.md:73-74 | rendered form `A ⊆ᵇ B` used at :77, :79 |
| `isSet⟪_⟫` | V/Model.lagda.md:444-445 | rendered form used at :462 |
| `⌜_⌝ᵗ` | FOL/Coding.lagda.md:104-106 | rendered form used throughout the chapter |
| `covers` | L/Choice/Finite.lagda.md:876-883 | `open Over size points covers public` |
| `fo` | L/Ordinal.lagda.md:193-196 | where-helper of `bound2`, used at :195 |
| `inψ` | L/Coding/Slot.lagda.md:140-152 | where-helper, used at :145, :149 |
| `m≡m₀` | V/Model.lagda.md:497-502 | where-helper of `choice`, used at :500 |
| `reflect∀` | L/ReflectFo.lagda.md:420-463 | used by `reflectFo` at :461 |

## 4. `𝒟ₒ→isL`

Not shortened. The long proof stays.

The 2-line body is valid. I wrote a probe at `/tmp/ProbeO4a.agda`:

```agda
𝒟ₒ→isL′ : (σ : V ℓ) → IsOrd σ → (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩ → ⟨ isL x ⟩
𝒟ₒ→isL′ σ oσ x x∈ = isL-trans x∈ (isL-𝒟ₒ σ oσ)
```

It typechecks, exit 0. So the body is not the problem.

The blocker is the file order. `isL-𝒟ₒ` sits at
`src/L/Axioms/Basic.lagda.md:230`. `𝒟ₒ→isL` sits at :98. Agda has no forward
references outside a mutual block. Moving `isL-𝒟ₒ` earlier is impossible.
`isL-𝒟ₒ` depends on `isL-Lset` at :156, and `isL-Lset` depends on `𝒟ₒ→isL`
itself. The cycle is genuine:

`𝒟ₒ→isL` to `isL-𝒟ₒ` to `isL-Lset` to `𝒟ₒ→isL`.

The alternative route through `Lset-suc` is also blocked. `Lset-suc` sits at
:196, after `𝒟ₒ→isL`. The current 18-line proof uses only lemmas imported
before :98. This matches the `[LJ-0.4]` warning that the July file-order block
may still bind.

`src/L/Axioms/Basic.lagda.md` is unchanged. It typechecks, exit 0, 1.6 s.

## 5. TYPECHECKS

Every edited master, `GHCRTS=-M8g agda <file>`, one process at a time.

| File | Exit | Seconds |
|---|---|---:|
| src/FOL/Coding.lagda.md | 0 | 1.2 |
| src/FOL/ZFModel.lagda.md | 0 | 1.8 |
| src/L/Coding/Powerset.lagda.md | 0 | 90.7 |
| src/L/Coding/Base.lagda.md | 0 | 1.0 |
| src/L/Coding/Environment.lagda.md | 0 | 1.0 |
| src/L/Coding/InL.lagda.md | 0 | 1.2 |
| src/L/Coding/Closed.lagda.md | 0 | 1.1 |
| src/L/Coding/Table.lagda.md | 0 | 1.5 |
| src/L/Coding/Uniform.lagda.md | 0 | 1.6 |
| src/L/Choice/Stage.lagda.md | 0 | 1.2 |
| src/L/Choice/Internal.lagda.md | 0 | 35.2 |
| src/L/Choice/Table.lagda.md | 0 | 4.7 |
| src/L/Choice/Faithful.lagda.md | 0 | 3.7 |
| src/L/Choice/Limit.lagda.md | 0 | 2.9 |
| src/L/Recursion.lagda.md | 0 | 1.1 |
| src/L/Hierarchy.lagda.md | 0 | 1.6 |
| src/L/Reflect.lagda.md | 0 | 1.0 |
| src/L/Axioms/Power.lagda.md | 0 | 1.2 |

The first pass ran before the import cleanup. The table reports the second
pass, after the cleanup. Both passes were green.

Consumer sanity checks:

| File | Exit | Seconds |
|---|---|---:|
| src/L/Choice/Transversal.lagda.md | 0 | 32.3 |
| src/L/Coding/CodeSet.lagda.md | 0 | 1.4 |

The `𝒟ₒ→isL` probe: exit 0, 1.0 s.

`python3 scripts/lint-prose.py --check` on every edited file: clean.
`python3 scripts/lint-agda.py` on the tree: clean for all tracked masters.
The only remaining violations are in the untracked probe file
`src/ProbeLJ12.lagda.md`, which was already in the tree before this block.

## 6. GENERALIZATIONS I SAW AND DID NOT BUILD

For blocks B to G, recorded and not built:

1. The `codes-complete` and `codes-canon` pair is a completeness and
   canonicity pair around one relation. If a future consumer needs the round
   trip, revive the pair generically. I did not build it.
2. The `closureLeast` section is a least-closed-set lemma with twelve clauses
   and private clause readers. Blocks C and D build clause frames for
   `Sound` and `Unique`. A least-closure lemma could serve them if a consumer
   appears. I did not build it.
3. The `∅-spec`, `⋃-spec`, `𝒫-spec` and `ω-spec` lemmas are one projection of
   `℩-spec` each. The pattern is already the generic one. P-k says state a
   read lemma where its consumers use it. The wing should state spec lemmas
   only at consumer sites.
4. `isPropBundle` and `isPropHierOf` are the same record-uniqueness pattern:
   one uniqueness lemma, then `Σ≡Prop`. Block G's lex-order kit and the
   wing's records may need the same shape. I did not build a combinator.
5. `memPairAt`, `Δ₀-memPairAt` and `memPairAt-adequate` were an atomic-formula
   pair in the Δ₀ and adequate idiom. The wing's level story needs more such
   pairs. The idiom is delivered, not missing. Nothing to build.

## 7. ARCHIVE USED

- `_build/l3.32-t208-report.md` section 3.1: the 54-name, 210-line dead set,
  the scan method, and the named examples. I re-derived the set on today's
  tree instead of trusting the numbers.
- `_build/lj-1.1-recon.md` sections 2.1, 2.2 and 4, Block 1: the funded plan
  rides `Sat-out`, `σ₁-up` and `π₁-down`. I kept all three.
- `_build/lj-0.4-compression.md` section 3 (N8) and section 8: the `𝒟ₒ→isL`
  claim and the file-order warning. The warning bound.
- `dev/memos/simplification-register.md:33-38`: S13 to S18 verdicts. No
  reverted candidate was re-proposed.
- `dev/LESSONS.md` via `scripts/rules.py --for build`: C-12, C-22, D-10,
  P-k, P-l. I ran one Agda process at a time under `-M8g`. I wrote the
  report incrementally. I re-verified every candidate against today's tree.

## 8. ANYTHING I AM UNSURE OF

1. The keep decision for the 12 `Everything.lagda.md`-prose names. I could
   not touch that file. If the orchestrator rewires its prose, those 49 lines
   become deletable. The report lists them in section 3.
2. The keep decision for `Def-spec` and `A∈Def`. `src/README.md:73` names
   them, and `src/README.md` is outside my write scope.
3. `_⁺` deletion. The numerals paragraph keeps the informal `∅ ⁺` notation.
   The explicit `_⁺`{.Agda} reference is removed. The prose reads correctly,
   but a reader may look for the definition.
4. The scan is reference-level. A name re-exported through a module instance
   could hide a consumer. The boundary-aware whole-tree grep found no such
   use for any deleted name.
5. The after figure is the working-tree count by the ledger algorithm. The
   ledger tool itself reads HEAD, and no commit is allowed. The orchestrator
   will see 17,252 after committing.
6. `memPairAt`, `seqSet` and `allCodes` are code-dead after their spec lemmas
   died. I kept them because `src/Everything.lagda.md` prose names them. They
   are documented vocabulary with no consumer today.
