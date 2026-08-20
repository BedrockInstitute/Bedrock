# Review of `amb-to-coded`

The obligation is a hole. This file is the obstruction, for the branch
`no-go-stated`.

## THE STATEMENT

```
amb-to-coded :
    (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
  → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
  → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁
```

It is `Probe414.agda:134-139`. Generic in `x` and `d`. No cardinal, no site,
no numeral except `ω`. Agda reports `UnsolvedInteractionMetas` at
`Probe414.agda:139` (`runs/amb-to-coded-hole.out`).

## D-10

NOT DECIDABLE in this tree. See `lj-1.414-report.md` section D-10. The
injection is a function on fibre types
(`src/L/Cardinal.lagda.md:47-48`). Nothing in that type is a `Formula`.

## HALF B IS NOT THE BLOCK

`code-from-graph` is GREEN (`Probe414.agda:115-128`,
`runs/code-from-graph.out`, exit 0, 1.64 s). Given `G` and the membership
readings in the shape `InclGraph` states them
(`src/L/InjChain.lagda.md:494-547`), the four conjuncts of `InjCode`
follow. The remaining bill is HALF A.

## HALF A, THE BLOCK

HALF A is the type `HalfA` at `Probe414.agda:65-66`:

    HalfA x d f = Σ[ G ∈ S ] GraphOf x d f G

`GraphOf` (`Probe414.agda:56-63`) is the two membership readings. There is
no producer for this type at an arbitrary ambient injection.

The two walls it inherits:

1. `[LJ-1.399]` wall 1 (`agents/tasks/LJ-1-399/lj-1.399-report.md:41-63`).
   An ambient function does not determine the members of an L-element.
2. `[LJ-1.399]` wall 2 (`agents/tasks/LJ-1-399/lj-1.399-report.md:83-91`).
   The tree has no `Formula` for an arbitrary map. `[LJ-1.400]`
   (`agents/tasks/LJ-1-400/lj-1.400-report.md:21`) measured the same door:
   it packages a graph the code does not supply.

The Def tower pays HALF A only when the map has a `Formula`. InclGraph,
Comp.K and ShiftGraph are those cases. An arbitrary element of `_↪_` is
not one of them. No chapter on the Def tower can pay the general type:
separation and replacement both take a `Formula`
(`src/L/Axioms/Full.lagda.md:144`, `:277`).

## WHAT WAS NOT DONE

No axiom, no postulate, no module parameter that asserts HALF A. The
obligation stays a hole.

## C-42

COUNT of `src/` sites that carve the graph of an ambient function as an
L-element: 6. COUNT of those with a `Formula`: 6. COUNT without a
`Formula`: 0. The table is in `lj-1.414-report.md` section 5. A
refutation of HALF A at one named map would still have required that
sweep. The sweep ran first.
