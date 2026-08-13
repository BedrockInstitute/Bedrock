# LJ-1.67: abstract the stack, one row, measured

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.67-report.md`.

## 0. THE VERDICT

**REGRESSED, and per the pre-fixed D-1 criterion the dispatch stops here.**
The row-level abstract-stack module in `NegAgree` measured **+2.82 s**
(after mean 103.818 s against before mean 100.996 s), three cold runs
each side, same session, gate caliber. The deciding claim is MEASURED.
The edit was reverted; the working tree is byte-identical to the
dispatch start. No other row, the chain, `levelIn` or `cover` was
attempted.

## 1. THE MEASUREMENTS

BEFORE (as-placed working tree, 6,390 in-fence lines), three cold runs,
same session, gate caliber (GHCRTS="-A64m -I0 -M16g", cold module, warm
dependencies, one process): 101.083 / 100.529 / 101.376 s, mean 100.996,
spread 0.847, load 2.42 to 4.35 (4 users).

AFTER (the abstract-stack row, 6,400 in-fence lines), three cold runs,
same protocol: 104.209 / 103.323 / 103.921 s, mean 103.818, spread 0.886,
load 3.30 to 4.01 (4 users).

| state | run 1 s | run 2 s | run 3 s | mean | spread | load |
|---|---:|---:|---:|---:|---:|---:|
| before (as-placed tree) | 101.083 | 100.529 | 101.376 | 100.996 | 0.847 | 2.42 to 4.35 |
| after (abstract-stack row) | 104.209 | 103.323 | 103.921 | 103.818 | 0.886 | 3.30 to 4.01 |

Delta: **+2.82 s**, in the wrong direction on every run. The two sides'
run ranges do not overlap (before 100.5 to 101.4 s; after 103.3 to
104.2 s), and the delta is about 3.2 times the larger within-side
spread. The after side ran at a slightly higher mean load, which
biases against the GO direction; the verdict does not depend on that
bias, because the direction is consistent and the magnitude is far
above the spread. The deciding claim is MEASURED.

The statements of `out` and `back` are unchanged: the only proof-body
edits were the module-binding spelling and the two instantiation lines.
MEASURED (the edited tree typechecked green, exit 0, in place; the
revert restored the tree byte-identically).

## 2. THE BUILD

The inner module `NegEnv` was placed inside `NegAgree`, immediately
after `body` and before `out` (the dispatch-start `out` sits at
`src/L/Condensation.lagda.md:3560`), parameterized by
`(γ' : S ^ (6 + m))` and the three site facts stated at `γ'`:

```agda
module NegEnv (γ' : S ^ (6 + m))
  (entryK' : ... → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (arSubK' : (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero)))) γ') ⟩
             → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK' : (z : S) → ⟨ (z ∷ γ') ⊨ envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
             → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  where
  module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                 (suc (suc (suc (suc (suc (suc B))))))
                 (suc (suc (suc (suc (suc (suc K)))))) γ' entryK' arSubK' envInK'
```

The `EnvSet` application happens once inside `NegEnv` at the abstract
`γ'`, where `lookup` cannot reduce. The two sites (dispatch-start
`:3563` and `:3590`) then instantiate the module at their own stacks:

```agda
module N = NegEnv (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) entryK (arSubK ya yc a ar c)
               (envInK ya yc a ar c E)
```

and use `N.E'.out`, `N.E'.back` and `N.E'.memE-bnd` exactly where the
baseline used `E'.out`, `E'.back` and `E'.memE-bnd`. The walk bodies are
otherwise verbatim. No statement changed; nothing was deleted; no
module-application layer was added on top of `EnvSet` (this is not a
third hoist; it is the same `EnvSet` application moved to an abstract
stack).

The edited tree typechecked green in place (exit 0, GHCRTS="-A64m -I0
-M16g"), so the shape is syntactically sound and the regression is not a
failed check.

## 3. THE ARITHMETIC AGAINST THE FAMILY PRICE

The row's two sites were to save a pro-rata share of 18.29 s: two of
eighteen sites at 1.016 s each, about 2.0 s. Instead the module moved
the WRONG way by 2.82 s. The saving is negative; the family price of
18.29 s (from `[LJ-1.66]`) stands. No arithmetic closes the 2.33 s
residual through this lever.

## 4. THE GENERALIZATION ANSWER

Structurally, the shape generalizes to the other eight rows: all
eighteen `EnvSet` applications share one spelling per depth
(`[LJ-1.66]` section 4), and the same inner-module parameterization
applies at depths 5, 6 and 7. That claim is INFERRED as a structural
claim; only `NegAgree` was built and measured. The seconds verdict at
this site is negative, so no other row was converted, and the
generalization was not funded. The shape is NOT special to `NegAgree` in
its spelling; it is special in having been the only one measured, and
the measured price is a regression.

## 5. THE DD4 ANSWER

The abstract-stack module is the more generic shape on the page: the
walk's facts are stated at an abstract environment and any tower could
instantiate them at its own stack. The row's statements and proofs are
unchanged, so nothing was traded away for the seconds. But the measured
price is wrong: instantiating the inner module at the concrete stack
still pays the concrete-argument work per site, and the added module
layer is pure overhead at this site, +2.82 s MEASURED. This is the same
verdict family as `[LJ-1.66]`'s frame: convergence-right, price-wrong,
at a new spelling (where the parameters are bound inside the row rather
than at top level). The edit was reverted, so the generic shape does not
stay in the tree.

## 6. THE CONVERGENCE ANSWER

The obligation is not renamed and the last named lever is now priced.
Row-level abstraction of the stack, the P-h spelling applied to the
band, measured **+2.82 s** (MEASURED FALSE) and was reverted. The
eighteen `EnvSet` applications remain individually expensive at 1.016 s
each (MEASURED, `[LJ-1.66]`), and neither a concrete hoist (+10.88 s,
MEASURED) nor an abstract stack at the row (+2.82 s, MEASURED) recovers
them at this site. The 2.33 s residual is not reachable through this
lever; `levelIn` and `cover` remain not discharged.

## 7. NEGATIVES AND THEIR STATUS

1. The row's two sites save 1.0 s or more: **MEASURED FALSE** (+2.82 s,
   three cold runs each side, same session, gate caliber; before mean
   100.996 s, after mean 103.818 s, ranges disjoint).
2. The abstract-stack module typechecks with unchanged statements:
   **MEASURED TRUE** (edited tree green, exit 0, in place; the only
   proof-body edits were the module-binding spelling).
3. The shape generalizes to the other eight rows: **INFERRED** as a
   structural claim (one spelling per depth), and the seconds verdict at
   this site is negative; no other row was converted.
4. The regression is an artifact of load: **MEASURED FALSE** (the after
   side ran at a slightly higher mean load, which biases against the GO
   direction; the direction is consistent on all three runs and the
   delta is about 3.2 times the spread).
5. The working tree is back to the dispatch start:
   **MEASURED** (6,390 in-fence lines; `git diff --stat` 956 insertions
   and 79 deletions, identical to dispatch start; no `NegEnv` remnant;
   fences and both linters clean; consumer re-check green).

## 8. ARCHIVE USED

- `_build/lj-1.66-report.md`, read WHOLE. TOOK the unit cost of one
  `EnvSet` application (1.016 s, section 2), the hoist's measured
  regression (+10.88 s, section 4), the eighteen-sites structural claim
  (section 4) and the gate-caliber protocol.
- `_build/lj-1.25-report.md`, read WHOLE. TOOK the abstract-the-source
  cure (12.8x, section 3) and the P-m rate bands.
- `_build/lj-1.24-report.md`, read WHOLE. TOOK arm 1's shape (the
  source abstracted into module parameters, section 3) and the
  stop-after-arm-1 discipline.
- `_build/lj-1.65-report.md`, read WHOLE. TOOK the gate-caliber
  protocol, the load-caveat discipline and the negative-status
  classification.
- `_build/diag-dd24-residual.md`, section 1. TOOK the band attribution
  (44.31 s over 2,196 lines; ~38.5 s un-attributed) and the residual
  arithmetic (2.33 s).
- `dev/LESSONS.md`: P-h (`:174`), P-l (`:2305`), P-m (`:2460`), P-t
  (`:2601`), P-q (`:2633`), read WHOLE each. TOOK P-h (module
  parameters stay abstract through the walk), P-l (a measured cure does
  not transfer by analogy; re-measure at every site), P-m (instantiation
  is the expensive content class), P-t (built formula trees unfold) and
  P-q (a line lever is not a seconds lever).
- `src/L/Condensation.lagda.md`: `NegAgree` (`:3520-3611`), `EnvSet`
  (`:2761-2870`), read in full at both sites (`:3563`, `:3590`), plus
  `unFullAt`/`UnFullDecode` (`:683-830`) and `Neg.negBndAt` (`:1146-1162`)
  for the satisfaction-component types.
- `archive/rud-route/`, SHAPE only (README and file list), per the
  brief.
- `scripts/rules.py --for build` and `--for probe`, every statement.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the final master.
`scripts/lint-agda.py --check` exit 0 on the final master.
`scripts/ledger.py --check` clean; standing 26,706 lines over 82
masters; `L.Condensation` counts 6,390 in-fence lines in the working
tree, the dispatch-start figure.
`L.BoundedSubset` re-checks green against the reverted master (exit 0;
the run re-checked `L.Condensation` first after the revert, then
`L.BoundedSubset`; real 114.58 s wall, load 6.63 at start).
No `make check` was run, per the brief. No `check-ratio --check` was
run, per the brief. No commit, no push. The working tree carries the
dispatch-start placement in `src/L/Condensation.lagda.md` and this
report; no probe file was left behind; no stash file was left behind.
Untouched: `src/L/Coding/`, `src/Everything.lagda.md`, all other
masters, all probes.
