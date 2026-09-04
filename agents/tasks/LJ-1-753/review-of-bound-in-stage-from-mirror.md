# review-of-bound-in-stage-from-mirror

## The statement this file is about

`agents/tasks/LJ-1-753/Probe753.agda.txt::bound-in-stage-from-mirror`,
the brief's exact signature: `StepKilledGen → (ca cp : Code) →
fst (val cp) ≡ ∅ → fst (val ca) ≡ Lset ∅ → BoundInStage ca cp`, with
the 673 `At` telescope as leading arguments and 746-SPLIT-SPLIT's
Amb7/PT vendored imports.

## The finding: a measured elaboration wall, not a NO-GO on the mathematics

The term is WRITTEN COMPLETE: nothing is postulated, no holes, every
row built. The type-check GROUNDS. Measured on the pane caliber
(`-A64m -I0 -M2g`, program-set):

- t=0 RSS 1.08 GB; t=5m RSS 2.27 GB (over the 2 GiB cap); t=15m RSS
  2.42 GB, CPU 15:34; killed ~17m with no completion
  (`runs/ground-snapshots.txt`, `runs/probe753-ground.out`).
- The check was killed once at 900 s and once at ~25 min in two
  independent runs with the same signature
  (`runs/probe753-37.out`, `runs/probe753-40.out`).

**The wall is localized by bisection.** With the domB-factor's
antecedent-type dummied, the checker proceeds to the next position in
**15.16 s** (`runs/bisect753b-1.out`). The ground lives in the
domB-factor's antecedent-type — the only place the term must SPELL the
erased appAt-subformula
`CntS.erase (∃̇∈ (var (suc (suc kk))) (appAt 2 1 0)) P` with its
21-deep count-proof chain (`W3.count-three` split 21 times).

## The answers the brief asked for

**AT.read: not required.** The construction never touches
`Probe652.AtTrans.read` or any carrier-absoluteness bridge. The
isOrd/transK/pins/domB/step rows are re-spelled at the SL carrier from
the green 732 rows, and the appAt-antecedent dies at its own guard:
its bound is `var 2` at `(v ∷ u ∷ n 0 ∷ γ15)`, and `var 2 = n 0 = ∅`
(`src/L/Coding/Model.lagda.md:160-161`,
`src/L/Coding/Base.lagda.md:285-287`).

**GraphAt: not required.** The named `GraphAt` type never appears; the
graph rows enter only through the mirror-cured split pieces
(`approx`'s two-kill domB row, the implication's guard-kill), all
inline.

**StepKilledGen: consumed vacuously.** The empty-instance reading
closes by ∅-slot kills without the vacuity hypothesis. This is the
surprising part the next brief should judge: the mirror package the
brief ordered consumed turns out to be unnecessary at the SL carrier,
because every quantifier of the domB/step rows ranges over a bound
whose slot content is ∅ or `Lset ∅` at the empty table.

## The wall's mechanism and the cure candidates

The domB-factor's antecedent-type must spell the erased appAt-subtree
`CntS.erase (∃̇∈ (var (suc (suc kk))) (appAt 2 1 0)) P` (the only
nameable ⊥*-form; the S-carrier `appAt` has the wrong type for the
`mapFo slide` position). Comparing that spelled term against the
demand's internally-built subtree is the b7-3 phenomenon
(`agents/tasks/LJ-1-746-SPLIT-SPLIT/runs/EraseIrr.agda:5-11`) at a new
site: the count-proof chain comparison normalizes the count terms over
the unfolded tree. Cure candidates for the next brief:

1. An `erase-cong`-style transport (the EraseIrr cure) applied to the
   domB-annotation: derive the demand's count-proof from `W3.count-three`
   by a computed cong and `subst` the row once, instead of spelling the
   chain.
2. Fix the inline-λ parse first (the ascribed-ant pattern + the
   where-layout interaction; `runs/probe753-41.out` through
   `runs/probe753-54.out`), then take the ant's type from the demand
   with no spelling at all.

## Instruments

- `runs/Bisect753.agda.txt` — the term with the graph region holed.
- `runs/Bisect753b.agda.txt` — the domB-antecedent-type dummied (the
  15.16 s run: `runs/bisect753b-1.out`).
- `runs/ground-snapshots.txt`, `runs/probe753-ground.out` — the wall.
- `runs/Floor753.agda.txt`, `runs/floor753-3.out` — the 5.65 s floor.
