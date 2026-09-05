# LJ-1.482 review of `rank-coded`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`stop-stated` asks for. Evidence is `file:line` throughout. Writing
this file does not close the task. The critic reads it.

## THE OBLIGATION

The brief named one term in `agents/tasks/LJ-1-482/Probe482.agda`:

```
rank-coded :
    (Q a bnd b : S)
  → (readings hold as [LJ-1.478] delivers them)
  → InjCode (rank-graph Q a bnd) a b
```

The telescope from the probe that typechecked, not from the sketch,
is `[LJ-1.478]`'s delivered `rank-graph` at
`agents/tasks/LJ-1-478/Probe478.agda:105-109`:

```
rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))
```

`InjCode` wants an `S`, so the type this task would have to inhabit
is `Probe482.agda:149-152`:

```
RankCoded =
    (Q a bnd b : S)
  → InjCode (fst (rank-graph Q a bnd)) a b
```

There is no term named `rank-coded`. The witness meter reports
`1 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-482/runs/witness.out:1-2`).

## THE VERDICT

NO-GO. The rank carve cannot supply the four `InjCode` conjuncts
(`src/L/Cardinal.lagda.md:223-228`). The carve serves a description.
It does not serve a code. The description and a code need different
bounds.

This is not a refutation of the type. I did not build a term of the
negation. I did not postulate. I did not add a hypothesis to close
a conjunct.

## THE CONJUNCT W3 MEASURED: RANGE

`InjCode`'s fourth conjunct, `src/L/Cardinal.lagda.md:228`:

```
(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩
```

`[LJ-1.478]`'s `rank-graph-out` at `Probe478.agda:111-116` supplies

```
⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
```

W3 rebuilt that reading at the coded pair as `from-out`
(`Probe482.agda:125-132`). That term typechecks. It yields
`prʟ x y ∈ˢ bnd` and satisfaction of `rankFo`. It does not yield
`fst y ∈ fst b`.

A false close that returned `from-out x y h .fst` as the range
clause failed with `[UnequalTerms]`
(`runs/w3-false-close.out:2-8`):

```
fst (pairʟ (pairʟ x x) (pairʟ x y)) != fst y
```

The pair is not the second component. The inhabitant was then
removed. The green file keeps `RangeClause` as a type
(`Probe482.agda:136-140`) and does not keep a term of it.

The brief asked: if the clause needs the bound to be an ordinal
containing every rank, say so. That is not the shape. `bnd` is a
pair-bound (`Probe478.agda:105-109`,
`lj-1.478-report.md:62-80`). The missing condition is that the
second component of a pair in the graph lies in `b`. A later brief
may name that as a condition on `b` (every rank of a member of `a`
in `Q` is a member of `b`), or as a converse of `PairBound`
(`src/L/InjChain.lagda.md:276-299`) that is not delivered. I did
not add either hypothesis.

## THE OTHER THREE, FROM D-10, NO AGDA

`[LJ-1.460]` packed `SG.sv , SG.dm , SG.ij , SG.ran`
(`Probe460.agda:81-82`) because `ShiftGraph` exported them
(`src/L/Absorption.lagda.md:452-498`, opened publicly at `:605-606`).
`[LJ-1.478]` exports `rank-graph`, `rank-graph-out`, `rank-graph-in`
(`Probe478.agda:105-124`). It does not export the four conjuncts.

1. **svAt** (`src/L/Cardinal.lagda.md:225`). No uniqueness of the
   second component in 478's readings. `ShiftGraph` got `sv` from
   `pair-out` and `Fo.val-cong` (`src/L/Absorption.lagda.md:453-465`).

2. **domAt** (`src/L/Cardinal.lagda.md:226`). Totality needs every
   member of `a` to have a pair in the graph. `rank-graph-in`
   (`Probe478.agda:118-124`) needs `z ∈ˢ bnd`. `bnd` is a
   parameter. Existence of approximating functions is the adequacy
   `[LJ-1.475]` left as a separate bridge
   (`agents/tasks/LJ-1-475/lj-1.475-report.md:236-253`).

3. **injAt** (`src/L/Cardinal.lagda.md:227`). `[LJ-1.417]`'s
   `rank-inj` is at a generic `SWO` (`Probe417.agda:60`), not at a
   set `Q`. `[LJ-1.475]` recorded that bridging `Q` as a set to an
   `SWO` is a separate price
   (`agents/tasks/LJ-1-475/lj-1.475-report.md:249-250`).

No conjunct has a supplier at `file:line` in 478's delivered
readings. Range is the one W3 measured. The other three fail the
same D-10 test. I stop.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`RangeClause`, `svAt`, `domAt`, `injAt`, or `RankCoded`. No
inhabitant of `bnd`. No claim of a limit. No claim of `Residue`.
No import of a probe. Nothing in `src/`.

## C-42

This NO-GO measures ONE site: the four `InjCode` conjuncts over
`[LJ-1.478]`'s carved rank graph, at generic `Q a bnd b : S`.
It says nothing about `shift-coded` at
`src/L/Absorption.lagda.md:611-626`. Count of `rank-graph` in
`src/`: **0**. Count of `rankFo` in `src/`: **0**.
