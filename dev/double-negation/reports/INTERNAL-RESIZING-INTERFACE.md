# The explicit internal-resizing rule and its consumers

Date: 2026-09-28. Goal remains active: obtain the full requested assumption-free
internal ZF construction and migration infrastructure, or a precise proof of
infeasibility. These experiments satisfy neither terminal condition.

## A proved proposition-level interface

`InternalResizing.agda` gives a concrete reading using the current negative
interpretation. For every stable proposition P at any level, it proves

```text
¬¬ (Σ Q:StableProp 0, Holds P ≃ Holds Q).
```

It also exposes the implication from `¬¬ Dec(Holds P)` to this statement.
The proof selects Unit or Empty under a decision, then maps that operation
under double negation. Both representatives are stable propositions.
No excluded-middle or resizing axiom is used.

The file provides a legitimate consumer: to prove a double-negation-stable
target B, it suffices to prove B given an actual representative. Such uses
compose for finitely many representatives by the double-negation bind rule.
This can live behind a separate resizing module; the logical rule is not
intrinsically ad hoc.

This proposition-level interface is not a construction of an internal type
universe. The ambient `StableProp ℓ` in its signature is a large host type.
It is not asserted to be a sheaf universe or a universe closed under all
required internal dependent type formers.

## What a full internal interface would additionally mean

In an adequately structured internal classical type theory, the intended
formulas are ordinary propositional resizing and Omega-resizing, interpreted
internally:

```text
∀P:Prop_U, ∃Q:Prop_V, P ↔ Q
∃Ω:U_V, Ω ≃ Prop_U.
```

An internal version of the usual excluded-middle argument would derive these
using internal Unit, Empty, Bool, equality and equivalence. This remains
conditional on the existence and closure properties of those internal
universes, rather than a way to construct them for free.

The proved pointwise rule cannot be projected to the old external resizing
interface. In particular, applying it to every member of a family yields
`∀i, ¬¬ ΣQ_i,...`, not automatically `¬¬ Σ(Q_i)_i, ∀i,...`.
The image and separation constructions inspected in earlier reports require
whole families of small indices. Reinterpreting these constructions in a
genuine internal dependent type theory could change the meanings of their
products, sums, trees and universes; merely substituting the pointwise rule
does not perform that work.

The small Boolean completion result in `COMPLETION-BOUNDARY.md` remains
relevant: a uniform universe-preserving completion with the stated extension,
density and equality properties would itself supply the external stable
proposition classifier. Such a classifier may be derived if possible, but
must not be introduced as an unexplained parameter under the user's boundary.

## New test of bounded output search

`ConditionalImage.agda` proves the following in the tree model. For a stable
extensional P and `a = sup A f`, define a modal relation sending input i to
`{f(i)}` when P(f(i)) and to the empty set otherwise. It is:

* modal-total, without deciding P externally;
* functional up to internal equality;
* extensional in its output;
* bounded by the explicit small tree indexed by `A + Unit`, containing all
  the singletons and the empty set.

If its image exists, taking that image's union gives a separation witness
for P on a. The same implication holds under double negation of image and
separation existence. The experiment proves the needed union and singleton
membership lemmas rather than assuming set-theoretic union as an axiom.

Thus finding a small output bound alone does not settle the general
replacement problem. A family of conditional outputs already has such a
bound but still carries the separation obligation. If P is a first-order
formula, this relation is first-order expressible using empty-set and
singleton specifications; a deep-syntax encoding and its semantic equivalence
have not yet been checked. The mathematical signature and actual constructors
of the existing `FOL.Syntax` and `FOL.Semantics` were inspected in this turn.

## Validation

Both `ConditionalImage.agda` and `InternalResizing.agda` were checked with
the repository compiler, `AGDA_DIR=_build/agda-home` (absolute path), and
`GHCRTS='-A64m -I0 -M8g'`, from this experiment directory. Final exits 0,
no warnings, `--safe`, no postulates or holes. ConditionalImage had intermediate
scope and definitional-reduction errors, fixed before the successful final
check. No whole-book gate was run because no book source was modified.

Next work should distinguish formula-specific negative semantics from a full
internal type-universe implementation, and pursue the former without treating
the pointwise resizing theorem as uniform size control. No full ZF model or
universal impossibility theorem has been established.
