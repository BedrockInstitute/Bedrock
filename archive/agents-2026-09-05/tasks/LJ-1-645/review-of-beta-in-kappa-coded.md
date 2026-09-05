# Review: `beta-in-kappa-coded` is uninhabitable

**Verdict: NO-GO.** The term `beta-in-kappa-coded : ⟨ β ∈ˢ κ ⟩` — the chapter's
`β∈κ` restated with the ambient `cardκ : IsCardinal κ` replaced by the coded
`cardκL : IsCardinalL (κ , isLκ)` — cannot be inhabited. This is a structural
obstruction, measured and cited below. It is not a proof that no code exists in
general; it is a proof that the SPECIFIC ambient composites this site builds
cannot be converted to codes.

## The obligation, in one line

At `src/L/BoundedSubset.lagda.md:1710-1719`, `β∈κ` refutes the ambient composite
injection `⟪ κ ⟫ ↪ ⟪ α ⟫` with `cardκ`. Each of its two `Empty.rec` branches
builds a DIFFERENT first leg and composes it with the SAME second leg `β↪α`:

```
branch `β ≡ κ`:  cardκ α α∈κ (comp-inj (transported id)   β↪α)   -- line 1713-1716
branch `κ ∈ β`:  cardκ α α∈κ (comp-inj (ord-emb κ β)       β↪α)   -- line 1717-1719
```

The coded restatement must PRODUCE a CODED injection `InjL κL αL` from each
ambient composite, and feed it to `cardκL`. Production of a code is possible
exactly when the ambient composite is MODEL-DEFINABLE, so its graph is a set in
`L` that `InjCode` can carve.

## Which leg carries a code

**`ord-emb` CARRIES a code.** Its element function is the ordinal inclusion
`x ↦ x`: `src/L/BoundedSubset.lagda.md:1371-1375`
(`f m = fiber b {x = ⟪ a ⟫↪ m} … .fst`), so the value in `β` is the same
underlying `V`-element. A definable relation; its graph (the diagonal over
`κ × β`) is a set in `L`. A code can carve it.

**`β↪α` DOES NOT carry a code.** The obstruction chain, with file:line:

1. `β↪α = comp-inj (subst … (SC.stage-card-lower β β-isOrd)) πX↪α`
   (`src/L/BoundedSubset.lagda.md:1693-1698`). The `stage-card-lower` leg is a
   definable presentation transport; the obstruction is in the `πX↪α` leg.
2. `πX↪α = λ p → CSel.h (IC.inv p)` (`src/L/BoundedSubset.lagda.md:1691`).
3. `CSel.h m = fst (leastOf w lem (cls m) (nonempty m))`
   (`src/L/BoundedSubset.lagda.md:1114-1115`). Here `w` is the ordinal's own
   well-order (`src/L/BoundedSubset.lagda.md:1634` instantiates `CodeSelect` with
   `SC.OrdSWO.ordSWO α ordα`), and `nonempty` is built from `mem-code`
   (`src/L/BoundedSubset.lagda.md:1111-1112`), a HOST-LANGUAGE code of the
   inductive type `HS.H.T.Code`.

`CSel.h` selects, for each hull element `m`, the least-count code among ALL
host-language codes that evaluate to `m`. The code type `HS.H.T.Code` is a
host-language inductive type, NOT a set in the model `L`. The model cannot
express the relation `m ↦ CSel.h m` as a set, so no `InjCode` can carve it. The
map `πX↪α`, and therefore `β↪α`, are not model-definable.

## Why the block is airtight at this site

Both branches share the `β↪α` leg. Even the branch whose first leg (`ord-emb`)
carries a code is blocked, because the COMPOSITE `comp-inj (ord-emb κ β) β↪α`
carries the obstruction through `β↪α`. A code cannot be glued from a definable
leg and a non-definable leg. So BOTH `Empty.rec` branches require a code the
site cannot produce.

The `InjL κL αL` the coded cardinal demands (defined in this probe as
`∥ Σ[ F ∈ S ] InjCode F (κ , isLκ) (α , isLα) ∥₁`, matching
`src/L/Cardinal.lagda.md:230-233`) is exactly the object the obstruction rules
out. Measured in `runs/floor-1.agda.txt` (the term with the two productions as
unsolved holes): the frame elaborates in 8.45s / 1.38GB and the only unsolved
metas are the two coded-injection productions.

## Consequence

The chapter CANNOT take `IsCardinalL` in place of `IsCardinal` at this site.
The refutation requires converting the ambient composite to a code, and the
`β↪α` leg defeats that conversion. Premise 5 of the brief holds: this is a
local, structural fact about the named piece `β↪α`, not the general
ambient→code crossing. The general crossing is a separate, larger question and
is out of scope here.

## What would change this

A code for `β↪α` would require an OBJECT-LANGUAGE definition of `CSel.h` — a
set in `L` computing, for each hull element, the least-count code by the
ordinal's well-order. No such object-language definition is present in the tree.
Introducing one is new architecture, not a restatement of this site, and is
therefore out of scope for this probe.
