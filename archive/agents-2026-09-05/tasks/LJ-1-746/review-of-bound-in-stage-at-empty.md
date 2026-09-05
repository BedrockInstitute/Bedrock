# review-of-bound-in-stage-at-empty: NO-GO

reviewer: coder (LJ-1.746, the dispatch that owns the term)
statement: `bound-in-stage-at-empty` at
`agents/tasks/LJ-1-746/Probe746.agda.txt:147-158` (the drafted shape; the
file is named `.agda.txt` because it cannot typecheck, this review is why)
verdict: **NO-GO at the wide caliber in this dispatch's shapes.**
The wall module is `agents/tasks/LJ-1-746/runs/Amb4.agda.txt`, the
erased-graph conjunction slot of `GraphAt`. The generic leaf itself is
GREEN: `agents/tasks/LJ-1-746/runs/Amb7.agda:69` spends the hypothesis
and typechecks rc 0 (`runs/amb7-746-1.out`, 657 MB peak). No GO is
claimed and `Completeness` / `completeness-from-pack` are not inhabited.

## What was measured (one Agda process at a time, pane caliber `-A64m -I0 -M2g` untouched)

| probe | what it prices | result |
|---|---|---|
| `runs/amb7-746-1.out` | `Amb7`, the named rewrite | **rc 0**, peak RSS 657 MB |
| `runs/eraseirr-4.out` | `runs/EraseIrr.agda:56`, the new erase-irrelevance lemma | **rc 0**, 0.84 s |
| `runs/amb4-746-3.out` | `Amb4`, direct term (732 shape + hypothesis) | **heap wall**: 342.78 s, `Heap exhausted` at the 2 g cap, peak RSS 2.4 GB, rc 251 |
| `runs/amb4-746-4.out` | `Amb4`, erase-cong bridge restructure | no completion in 240 s |
| `runs/b1.out` | `Amb4` type floor, term holed | rc 42 (expected metas) in **6.05 s** |
| `runs/b4.out` | `Amb4` slot structure, both rows holed | rc 42 (expected metas) in **3.33 s** |
| `runs/b7-3.out` | bare `refl` between the two count-proof spellings of the approx slot | no completion in 120 s |
| `runs/b8.out`, `runs/b10.out` | the isolated bridge, implicit then explicit split implicits | `[UnsolvedMetaVariables]` at **48.94 s** / **48.99 s** |
| `runs/b5.out`, `runs/b6.out` | assembly with one bridge holed | no completion in 180 s each |
| `runs/b12.out` | assembly with BOTH slot arguments GIVEN at the split spellings, no row terms, no substs | no completion in 150 s |

## The wall, named precisely

`GraphAt` (`agents/tasks/LJ-1-732/runs/Amb4a.agda:18-19`) is the reading of
`CntS.erase Mx.G.graphBndAt countGB` at `γ15`, and
`Mx.G.graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)`
(`src/L/Condensation.lagda.md:2493`). `erase` threads its count proof
through every clause (`src/FOL/Count.lagda.md:598-610`), so the conjunct
slots carry the plus-zero splits of `countGB`
(`src/FOL/Count.lagda.md:586-592`) while the green row modules name
`countA` / `countS`. Checking the `Amb4` assembly makes the elaborator
unify plus-split equations over the unfolded erased-graph tree: the
constraint dump in `runs/b8.out` shows `_a + (countFo Mx.G.A.approxBndAt + _b) = 0`
blocked on `_a`. B12 shows no row-term trick avoids it: the comparison of
the slot types themselves does not complete at this caliber.

## What survives for the next brief

- `runs/Amb7.agda` (rc 0): the leaf cure the 732 critic named works.
  `StepKilledGen` (`runs/Amb7.agda:55`) is the hypothesis named once and
  the instance call is one `Empty.rec` (`runs/Amb7.agda:69-70`).
- `runs/EraseIrr.agda` (rc 0): `erase-cong`
  (`runs/EraseIrr.agda:56`) is the machine form of the claim Amb2's 732
  comment made at prose level ("the erase result does not depend on which
  zero-count proof is passed down"): `erase φ p ≡ erase φ q`, O(|φ|) cong
  steps, no semantic normalization. It is green and unused so far.
- `Probe746.agda.txt` is the drafted probe: the 673 telescope, the alias
  form, the bridge and pins, the obligation threaded with the hypothesis.
  Its frame matches the 732 file's and needs no new mathematics; only its
  import chain (`Amb2` → `Amb4`) fails to check.

## What would reopen a GO

A shape in which no consumer spells the count-split terms and no
conversion descends into the erased-graph tree. Two candidates, either of
which is worth one dispatch:

1. Make `Amb1` (or a sibling run module) name the SPLIT-spelled row types
   once, checked there, so `Amb4`'s slots and rows share one spelling and
   the comparison is syntactic. The rows themselves would need to move to
   those spellings (erase-cong transports them once, inside the module
   that owns the spelling).
2. Decompose the graph reading only at head depth into a written mirror
   Sigma type and transport along a single head-level `refl` equality, so
   the conjunct formulas stay suspended. Requires matching the hProp
   algebra's exact pair conventions in the mirror.

A third, heavier option: re-land the whole chain under the heavy caliber
(`-M4g`), where the direct shape has four times the headroom. That needs
the owner's tier ruling and does not cure the unifier blocking; it only
widens the cap around it.
