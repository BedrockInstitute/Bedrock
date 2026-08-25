# LJ-1.399 review of `omega-pair-code`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-399/Probe399.agda:131-133` states `omega-pair-code` exactly
as the brief writes it: a truncated coded injection out of the internal square
`prodL ωL ωL` and into `ωL`, placed below `SiteBound.β (prodL ωL ωL)`.

## THE VERDICT

**NO-GO, and the failure is at TWO walls, both before any satisfaction fact.**

- **STEP 1 is YES.** The door + bridge assembly is green. `leg1-gives-sq`
  (`Probe399.agda:106-121`) is [LJ-1.386]'s `leg1-gives-sq`
  (`agents/tasks/LJ-1-386/Probe386.agda:294-302`) re-instantiated at
  `δ := ωL`. It takes the code as an argument and lands in `sq (fst ωL)`, and
  `omega-leg1` (`Probe399.agda:141-142`) is the closed instance of it. This
  proves nothing new, as the brief requires.
- **STEP 2 is NO.** `omega-pair-code` cannot be built. The file's ONLY error is
  the unsolved meta at the hole `Probe399.agda:133`, exit 42.

## WHICH STEPS FAIL, AND WHAT WOULD CLOSE THEM

### W1: the hypotheses do not determine the members of the internal square

**The failing step.** Assign a value in `ω` to every member of
`prodL ωL ωL`. `InjCode`'s `dom` conjunct (`src/L/Cardinal.lagda.md:223-228`)
demands it, and the hypotheses supply no way to read a member of
`prodL ωL ωL` back as a pair.

**Why the two hypotheses do not close it.** `prod-bridge` is an injection
(`_↪_` at `src/L/Cardinal.lagda.md:47-48`), not a surjection. A member of
`prodL ωL ωL` that is not in the bridge's image has no value under the natural
map, and the hypotheses do not say there are no such members.

**What WOULD close it.** The membership reading `prodL-out`
(`agents/tasks/LJ-1-388/Probe388.agda:307`), taken as a hypothesis: every
member of `prodL a b` is `pr x y` for some `x ∈ a`, `y ∈ b`. The brief said
"take both [prodL and prod-bridge] as module hypotheses and do not import that
probe", and handed over exactly two. `prodL-out` is a third, and it is not
derivable from the two.

**The statement is not even true at the given generality.** `prodL` is an
abstract function `S → S → S`, so `prodL ωL ωL` may be any constructible set.
At `prodL ωL ωL` an uncountable set, no injection into `ω` exists, and no
`omega-pair-code` exists. The hypothesis type alone does not carry the product.

### W2: the pairing formula needs arithmetic the tree does not hold

**The failing step.** Write the graph of the ambient pairing `pairω`
(`src/L/InjChain.lagda.md:184-185`) as an object-language `Formula`, so that
`hasReplacementL` or `hasSeparationL` can carve it as an L-element. This fails
before the placement probe `graph-lands` can even be stated: there is no graph.

**Why the coding vocabulary does not close it.** The pairing is the Godel
collapse: "compare the larger coordinate, then the first, then the second; with
the order-type reading that collapses each pair to the ordinal of its
predecessors" (`archive/src/2026-08-09-rud-route/Everything.lagda.md:296-299`).
Its value at `(a,b)` is `b² + a` for `a < b` and `a² + a + b` for `a ≥ b`. A
formula for it needs addition and squaring of numerals.

The tree's atoms are `sucAt` (`src/L/Coding/Environment.lagda.md:136`), the
pair atoms (`src/L/Coding/Base.lagda.md:254,285`), membership, equality and the
quantifiers. `grep` over `src/L` and `src/FOL` for an `addAt`/`multAt`/
`squareAt` formula returns NOTHING. There is no object-language addition and no
object-language multiplication.

**What WOULD close it.** Object-language numeral addition and squaring (a
`Formula` for `x + y = z` and for `x² = z`, with their adequacy and
functionality proofs), built from `sucAt` by the finite-computation encoding.
Then the collapse closed form above is a formula, and the graph carves. This is
a new piece of the coding layer, and it is not priced by this task: the brief's
estimate of about 150 code lines rests on `IdGraph`'s trivial identity formula
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`), and the pairing formula is not
the identity formula.

## THE SWEEP, BECAUSE A MEASUREMENT MEASURES ONE SITE (C-42)

This NO-GO is at `ω`, the cheapest site the campaign has. It does NOT say how
far the wall extends. It says two things, both at `ω` and only at `ω`:

1. The hypothesis shape the brief handed over is too weak to build a code whose
   domain is an opaque product.
2. The object language has no arithmetic, and the pairing needs it.

At a generic cardinal the collapse is a full ordinal order-type, not a numeral
count, so the W2 wall is no easier there. That is a note about what would
change, not a measurement at the generic site.

## WHAT IS NOT CLAIMED

- It is NOT claimed that the square law at `ω` is false. `squareω`
  (`src/L/InjChain.lagda.md:184-185`) is delivered, and the ambient pairing is
  real. The NO-GO is about the CODE, not the map.
- It is NOT claimed that `omega-pair-code` is false at the real `prodL` of
  [LJ-1.388]. At that real product the code should exist; it is underivable
  from the two hypotheses alone, and unbuildable without arithmetic.
- It is NOT claimed that `omega-leg1` is new. It proves nothing new, and the
  report says so.
