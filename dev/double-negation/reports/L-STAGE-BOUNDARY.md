# Constructible power sets, stage bounds, and Hartogs

Date: 2026-09-28. Research only; the full assumption-free internal ZF goal
remains open. No production mathematical source or Git state was changed.

## Actual dependency in main

`L.Model` installs `hasPowerL` in its `hasPower` field. The implementation in
`L.Axioms.Power` instantiates `V.Model.Power (LEM→ΩResizing lem)` (line 232).
For a constructible a it uses the ambient power set P of its underlying set
(line 311), resizes `isL` separately (line 330), and forms the small index
of constructible elements of P (line 349). Their stages are bounded using
`L.Ordinal.boundingOrd`. Separation inside this common stage produces the
internal power set (lines 553–598).

The final theorem assumes only LEM because it derives resizing from LEM.
This use of resizing is a fact about the current proof, not a proof that
every possible construction of L must mention Ω-resizing.

## A more targeted necessary and sufficient condition

For a constructible a, the relevant condition is

```text
there is an ordinal β such that every constructible x ⊆ a belongs to L_β.
```

Given stage separation, such a bound produces the power set by separating
the subsets of a from L_β. Conversely, if the power set p exists as a
constructible set, place p in some L_β. Transitivity of L_β then puts every
member of p in L_β. Thus uniform stage bounding is equivalent to power-set
existence relative to stage coverage, transitivity, and this separation rule.

`StagePowerBoundary.agda` checks both directions under double-negation
existence. It is generic over the carrier, membership, and stage indices;
it does not presume a tree representation, native equality, or resizing.
The separation and stage conditions are explicit parameters, not proved
properties of a newly completed internal model.

The same file proves a useful positive rule. Suppose each subset x lies,
under double negation, in some stage β in a designated bounded class of
indices. If one δ dominates every stage in that class and stage membership
is stable, then all such x belong to stage δ. No simultaneous selection
of the individual β's is required: each witness is eliminated into a stable
membership statement. Therefore a direct bound really could avoid the
particular small-index collection in the current power-set proof.

## Existing condensation supplies part of an alternative

`L.GCH.Assembly.InternalBoundedSubset` (lines 206–222), proved in
`L.GCH.BoundedSubset` (lines 684–701), places each constructible subset y of
an infinite internal cardinal κ in an L_β with a constructible injection
β → κ. This is a bound for each y, not yet a common ordinal bound.
A successor cardinal of κ would supply the next ingredient; extending this
to arbitrary a also needs the appropriate internal coding of a into a cardinal.
No full replacement power-set proof has been formalized here.

A source import graph inspection found no path from `L.GCH.BoundedSubset`,
`L.CardinalAbove`, or `L.Axioms.Full` to `L.Axioms.Power`. This excludes that
particular module cycle. It does not show that all used lemmas have already
been internally translated or that imports from `V.Model` never matter.

In particular, `L.CardinalAbove.Hartogs` uses:

```text
Rel = presentation(a) → presentation(a) → Bool          (lines 693–694)
WFR = transitive, well-founded members of Rel            (lines 719–722)
μ = union of successor order types indexed by WFR        (lines 893–894)
R x y = decB (lemℓ (PreT x y, proof it is a proposition)) (line 1070)
```

The last step produces an actual Boolean relation by host excluded middle.
Replacing only its logical statement with double-negated excluded middle
does not produce the same data interface. This route removes the explicit
Ω-resizing call only if its own relation/function and ordinal constructions
can be justified internally.

## Restricting to well-founded transitive relations still has a size cost

`HartogsRelationBoundary.agda` constructs, from every stable predicate P on A,
a stable relation on A + Unit:

```text
inl(a) < top  iff P(a); all other comparisons are false.
```

It proves this relation transitive and well-founded constructively. Every
chain has at most one strict edge. A small double-negation-dense family of
ALL stable transitive well-founded relations on this carrier would therefore
give a small dense family of all stable predicates on A, by evaluation at
(inl(a), top). The resulting conversion to `PredicateCover A` is checked.
For A = Nat, the previous modal-subcountability assumption refutes this cover.

This is not an impossibility theorem for every Hartogs construction. In
particular, it does not refute collecting only order types or bounding those
types without representing all relations. Nor does it show that the narrower
special relations `PreT` appearing in the existing contradiction argument
must exhaust our relation class. Those are still legitimate research targets.

## Definability alone cannot fill the bound

`L.Definability` already constructs Def(A) without a classical parameter:
its index is `Formula presentation(A) 1`, and small satisfaction is obtained
by structural interpretation in the small presentation. This handles one
fixed parameter domain and one fixed structure. It does not enumerate all
subsets of a that become definable at arbitrarily later constructible stages.

A precise classical counterexample rules out that shortcut in general.
Work in an ambient universe satisfying ZFC + V=L and let

```text
M = H_{ω₁} = L_{ω₁}.
```

M satisfies ZFC without Power Set, even with Collection, and internally
satisfies V=L. Its internal constructible hierarchy agrees with the ambient
one below ω₁. Every real is an element of M, but every set in M is countable
in that ambient universe. Thus no element of M can contain exactly all its subsets of ω:
it would be the ambient uncountable P(ω). Likewise no β < ω₁ contains all
these reals in L_β. Classical logic, definability at each stage, and the other
set axioms therefore do not automatically supply the missing bound.

Published ingredients: Gitman, Hamkins, Johnstone, *What is the theory ZFC
without power set?*, introduction pp. 1–3, proves the relevant H_κ examples
and distinguishes Replacement from Collection:
<https://arxiv.org/pdf/1110.2430>.
Welch, *Axiomatic Set Theory*, Theorem 4.18, gives H_κ=L_κ in L for infinite
cardinals κ:
<https://people.maths.bris.ac.uk/~mapdw/AST/current-axiomatic-set-theory.pdf>.
The counterexample and the failure-of-bound deduction above combine these
facts; they are a semantic argument, not a newly machine-checked model.

This counterexample is not a model of all allowed Cubical Agda primitives and
does not settle the full original goal. It establishes the narrower fact
that replacing a full smallness argument by an appeal to constructibility
and classical logic alone is insufficient.

## Verification

The new `StagePowerBoundary.agda` and `HartogsRelationBoundary.agda` were
checked sequentially with the pinned compiler, local Agda home, and
`GHCRTS='-A64m -I0 -M8g'`. Both exited 0 without warnings. Their options
retain `--cubical --safe --guardedness`; neither contains postulates or holes.
No Agda process was present before the checks. No full Origin or site check
was run, since the experiments do not change the production import graph.

Next: test whether a direct internal bound for the needed order types can
be constructed without a cover of all relation graphs, or find a theorem
excluding such a bound under the actual permitted foundation. The complete
internal universe, Ω-resizing interface, and ZF interpretation are not yet
constructed, and a universal impossibility theorem is not established.
