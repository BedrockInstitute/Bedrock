# K8 assumption and endpoint ledger

The verification status of the complete source checkpoint is recorded in
`STATUS.md` and the per-module logs. These are isolated safe Agda proof probes,
not new production milestones.

## Public endpoints

`FullDeltaSystem.AtOmega.finite-delta` takes an ambient set `X`, a ground-coded
family `F` of internally finite subsets of `X`, and internal uncountability of
`F`. It returns a ground-coded uncountable subfamily and a common intersection
root. `finite-delta-with-root` additionally exhibits the root's internal
finiteness. Neither endpoint takes a delta-system or disjoint-subfamily theorem
as a hypothesis. The parameterized induction kernel remains separately usable
in `DeltaSystem.WithDisjoint`.

`Theorem.OverZFC.cohen-ccc` has conclusion
`K7.ChainConditions.CCC₂ᴵ C.carrier C.order w`, for the actual finite-map carrier
and reverse-inclusion graph of `K8.Cohen`. Its assumptions contain no CCC or
delta-system conclusion. Equal domains are handled by internally finite
fibers; they are not treated as equal conditions.

`Theorem.OverZFC.completion-ccc` has conclusion `CCC₂ᴵ` for the actual
`Certificate.Nonzero` carrier of the canonical completion and its coded subset
order. It uses `CertifiedCCCTransfer`, which constructs an actual
`Certificate.Property.PropertyTransfer`. The latter's named hypothesis record
contains ordinary internal `ChoiceSet`, and is explicitly inhabited from that
axiom. It is not a record populated with the desired transfer conclusion.

`coordinate-dense` and `distinct-dense` expose the existing actual coded `D`
and `E` sets and their density proofs. `D` asks for some value at a coordinate.
`E` asks for unequal values at one common natural coordinate for two distinct
indices. No predetermined-bit density claim is made.

## Ground assumptions

The full combinatorial and certified CCC endpoints use:

- A `ZFStructure (hPropAlgebra ℓ)` and ordinary Extensionality.
- An explicit realization of interpreted equality by paths in the model's
  set carrier. This is representation data, not asserted to follow from ZFC.
- Ordinary Pairing, Union, PowerSet, formula Separation, Collection and
  FoundationInduction.
- Explicit `LEM ℓ` and ordinary internal `ChoiceSet`.
- An actual ground set `w` satisfying `CardinalBridge.isOmega w`.

The Cohen index set `κ` is arbitrary. No hypothesis that it is a cardinal, no
CH/GCH assumption and no cardinal-arithmetic hypothesis is used. The full
delta-system theorem additionally takes an arbitrary seed set to instantiate
the ground constructors; the Cohen instance uses `κ` as that seed.

The generic finite-map and order constructions use fewer assumptions. Finite
countability does not need Collection or Choice. The canonical completion
certificate uses PowerSet and Separation with the representation assumptions
and LEM; it does not need Choice or Collection. Internal Choice is added for
the CCC-transfer theorem, not smuggled into the completion's structural fields.

## Internal versus host constructions

Finiteness is the model's Kuratowski finiteness, with formula-backed induction,
not an external list enumeration. Countability is the existence of an actual
ground-coded injection into `w`. Internal uncountability is the negation of
that predicate.

`DiagonalOrder` constructs a genuine injection `w × w ↪ w` by the internal
finite-initial-order argument. `CountableZFC` supplies this witness to the
generic countable-union theorem; consumers do not have to assume a pairing
injection.

`OmegaRecursion` constructs its recursion graph from finite ground-coded
traces, and `RecursionInduction` accepts only an actual first-order Formula as
its invariant. The closure orbit is a bounded ground image of `w`, not a host
sequence. The component construction takes a subset of that countable orbit
union. Choice is applied to a ground-coded family of disjoint nonempty
components, and the raw choice set is intersected with `F` before it is used
as the representative family.

There is no host Choice, external well-ordering of the model carrier, host
dependent choice, resizing, generic filter, Boolean fullness, or extra universe
axiom in these endpoints. No claim about the subsequent K9 real family or K10
forcing theorem follows merely from finishing K8.
