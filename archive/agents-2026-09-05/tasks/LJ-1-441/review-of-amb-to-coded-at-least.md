# Review of `amb-to-coded-at-least`

The obligation is a hole. This file is the obstruction, for the branch
`no-go-stated`.

## THE STATEMENT

```
amb-to-coded-at-least :
    (a : S) (oa : IsOrd (fst a)) → ⟨ ω ∈ˢ fst a ⟩
  → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
  → (⟨ fst (κL a oa) ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁
```

It is `Probe441.agda:97-101`. There is no ambient-arrow hypothesis. The
arrow is `κ-injL a oa` (`Probe441.agda:64-65`, the four-projection seal
copied from `agents/tasks/LJ-1-433/Probe433.agda:89-90`). Agda reports
`UnsolvedInteractionMetas` at `Probe441.agda:107` after `PT.rec` on that
arrow, and at the W3 hole `Probe441.agda:86`.

## THE ONE DECLARATION THAT WOULD CLOSE HALF A AT THIS SITE

```
selected-graph :
    (a : S) (oa : IsOrd (fst a))
  → (f : ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
  → Σ[ G ∈ S ] GraphOf a (κL a oa) f G
```

That is `[LJ-1.414]`'s `HalfA` (`agents/tasks/LJ-1-414/Probe414.agda:65-66`)
at `x := a` and `d := κL a oa`, with `f` opened from `κ-injL`. Given that
term, `[LJ-1.414]`'s green HALF B (`Probe414.agda:115-128`) yields
`InjCode`, and `PT.rec` into the truncated goal is legal.

## SAME OBSTRUCTION AS `[LJ-1.414]`, NOT A NEW ONE

`[LJ-1.414]` met two walls at a generic pair
(`agents/tasks/LJ-1-414/review-of-amb-to-coded.md`):

1. An ambient function does not determine the members of an L-element.
2. The tree has no `Formula` for an arbitrary map. Separation and
   replacement both take a `Formula`
   (`src/L/Axioms/Full.lagda.md:144`, `:277`).

Both walls hold at this site. The selected arrow is still an element of
`_↪_` (`src/L/Cardinal.lagda.md:47-48`). `leastOf` delivers a truncated
ambient witness (`src/L/Cardinal.lagda.md:133-134`). It does not deliver a
`Formula`.

The two extra facts at this site do not close HALF A:

- `κ-min-at` (`src/L/Cardinal.lagda.md:140-141`) refutes
  `∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁` for `δ` a member of `κ`. That is a negative
  statement about smaller ordinals. It does not name the members of a graph
  and it does not write a `Formula`.
- `κ∈sα` (`src/L/Cardinal.lagda.md:129-130`) is membership of `κ` in
  `sucV (fst a)`. It is not a `Formula` for the selected map.

No third device in the chapter puts a `Formula` on `κ-inj`. Route 1 stops
at `selected-graph`. Route 2, through minimality, does not produce that
term.

So the ambient route is dead at its own site, not only at generality. The
obstruction is `[LJ-1.414]`'s obstruction, instantiated at the pair the
chain spends.

## WHAT WAS NOT DONE

No axiom, no postulate, no module parameter that asserts `selected-graph`
or `[LJ-1.414]`'s `amb-to-coded`. The obligation stays a hole. W3's
`half-a-at-least` stays a hole at the same `GraphOf`.

## C-42

This NO-GO measures ONE site: HALF A at `d := κL a oa` with the arrow
`κ-injL`. It does not inhabit `[LJ-1.414]`'s generic type. It says nothing
about the truncated route, whose supply is `[LJ-1.437]` and whose consumer
is `[LJ-1.434]`.
