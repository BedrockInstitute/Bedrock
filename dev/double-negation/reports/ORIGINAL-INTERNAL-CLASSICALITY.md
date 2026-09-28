# Internal classicality at the milestones

This note records the design investigation behind the branch
`internal-logic-milestones`. It distinguishes assumptions in the Cubical Agda
host from principles stated through the satisfaction relation of the deeply
embedded first-order language.

## Theorem 1: the ambient hierarchy

The published endpoint has type

```agda
V⊨ZF : LEM (ℓ-suc ℓ) → isZFModel
```

and currently factors through `ΩResizing (ℓ-suc ℓ) ℓ`. A weaker interface
can instead decide only satisfaction propositions:

```agda
InternalLEMᵥ =
  ∀ {n} (φ : Formula S n) (γ : S ^ n) →
  ⟨ γ ⊨ (φ ∨̇ ¬̇ φ) ⟩
```

This is sufficient. Semantically, object-language disjunction is propositional
truncation. Since `Dec P` is itself a proposition whenever `P` is a
proposition, that truncation can be eliminated into
`Dec ⟨ γ ⊨ φ ⟩`. This derived decision is used below; it is not part of the
assumption. Full separation needs decisions only for the
instances `(y ∷ []) ⊨ φ`; a decision gives each such proposition a Boolean
small representative. Power set needs decisions only for atomic membership.
For a fixed `a`, Boolean functions on the small presentation `⟪ a ⟫` enumerate
all subsets because internal excluded middle decides whether each presented
element belongs to a candidate subset. Empty set, pairing, union, replacement,
regularity and infinity retain their constructive implementations.

The host principle at level `ℓ-suc ℓ` implies this internal one because
satisfaction is proposition-valued. Conversely, the internal principle implies
host `LEM ℓ`: for `P : hProp ℓ`, form the conditional set
`{ ∅ | P }` and apply internal excluded middle to the atomic assertion that
`∅` belongs to it. This does not by itself recover host
`LEM (ℓ-suc ℓ)`, because a proposition at that higher level cannot be used as
the small index type of this construction without an additional resizing
principle.

## Theorems 3 and 4: the constructible universe

For `L`, the analogous internal principle decides formulas interpreted in
`𝒮ᴸ`. It immediately decides equality, membership and every explicitly
represented formula predicate. The current ZFC and GCH developments nevertheless
pass host `LEM` to interfaces that accept arbitrary host predicates. Examples
include least-stage descent, ordinal comparison and `leastOf` searches. Their
predicates are not uniformly accompanied by formulas and adequacy proofs.

An internal-classical proof of `L⊨ZFC` is therefore a credible further theorem,
but requires reworking those interfaces so that every classical decision is made
on a represented first-order predicate. It is not a parameter substitution in
the present dependency graph. An internal-classical proof of `L⊨GCH` depends on
that work and additionally requires internalizing the classical choices made by
the cardinal, hull, coding and least-witness developments, or formalizing the
object-theoretic proof that `V = L` implies GCH.

## Choice principles

Three choice interfaces must remain distinct.

1. `SetChoice` is a host principle for arbitrary h-set-indexed type families.
2. Formula choice is a metatheoretic schema over deeply embedded formulas with a
   set-sized domain; it returns a graph that is an element of the model. Over ZF
   this is an equivalent presentation of ordinary set choice.
3. Definable class choice has the whole model as its domain and returns a
   formula-defined class function. Ordinary first-order ZF has no class objects,
   so this must be a schema over formula codes or an interface in a class theory.

The second interface is the appropriate internal candidate for revisiting
Theorem 2. Calling it class choice would obscure the set-sized domain. The third
is genuine class choice and is stronger in form than the `C` field of the ZFC
model record.

## Acceptance criterion for revised milestone prose

Milestone wording changes only after checked declarations expose the new
assumptions in their types. In particular, Theorem 1 should be revised only when
an `InternalLEMᵥ → isZFModel` declaration typechecks without deriving host
`LEM` or unrestricted proposition resizing.
