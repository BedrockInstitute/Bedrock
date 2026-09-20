# Internal check recursion, 2026-09-20

The singleton-weight check operation now has an actual construction from
ordinary ground axioms and membership accessibility. It does not take
`NameKernel.MemberImage`, a pre-existing recursive graph, or a choice principle.
`K9.BooleanSupport.Checked` uses this construction through its existing public
`check`, `check-name`, and `check-spec` interface.

## Assumptions and scope

`CheckRecursion` takes Extensionality, realization of ground equality as host
paths, host well-foundedness of ground membership, and a weight `w`.
`Construct` additionally takes Pairing, Union, Power Set, Separation,
Collection, and a seed set. Power Set is a formal parameter of the reused
`K8.GroundSets` infrastructure. No claim of its eliminability is made here.
Accessibility remains an explicit realization hypothesis, as in the existing
name kernel. It is not claimed to follow from ordinary Foundation induction.

The resulting equation is

```
z ∈ chk a  iff  there exists u ∈ a with z = ordered (chk u) w.
```

This is the singleton-weight Boolean check operation. The existing poset check
operation has entries at every condition and has a different equation. The new
result does not yet replace that operation, generic names, name translations,
or the arbitrary Boolean value-family capability.

## Why the recursion is internal

A table `F` records a value `v` at `x` when a coded ordered pair `(x,v)` belongs
to `F`. `Local F x v` requires a recorded value at every member of `x` and
requires the members of `v` to be exactly the weighted entries obtained from
those recorded values. `Good F` requires this local equation at every recorded
pair. Malformed elements of a table are irrelevant; they do not create a
recorded pair. The predicates have actual first-order formulas and proved
satisfaction readings, including the constants frozen into Collection and
Separation formulas. These are ordinary satisfaction readings in the ground model;
the construction assumes no Boolean formula compiler.

Membership induction proves that any two good tables agree at a common key.
To compare their values at `x`, take a member of one value, expose its smaller
key `u ∈ x`, obtain a value at `u` from the other table's local totality, and
apply the induction hypothesis. Extensionality then identifies the two values.
This proves compatibility before any attempt to merge tables.

For the existence step, Collection bounds witness tables for the members of
`a`. Its bound can contain unrelated elements, so Separation first retains
only good tables. The union of these retained tables is good: every recorded
pair comes from one constituent, and compatibility shows that other
constituents cannot add a different value at a key in that constituent's domain.
The union covers every member of `a`.

The existing `NameImage.CheckDischarge` formula then defines a unique weighted
entry at each member of `a`. `GroundDescription.hasImage′` uses ordinary
Collection and Separation to obtain its image `v`. Adjoining `(a,v)` preserves
goodness. If the table already records a value at `a`, its local equation
identifies that value with `v`; no fresh-key assumption is needed. Host
well-founded recursion now proves truncated existence of a witness table at
every `a`.

Existentially hiding a good table gives the first-order relation `Value v a`.
It is total and single-valued by the preceding proofs. The truncated witness
is eliminated into `isContr`, a proposition, so `chk a` is obtained by unique
existence rather than host choice. The proved `chk-spec` is the recursive
membership equation itself. `chk` is opaque; consumers use this equation and
the graph specification instead of reducing the witness-construction proof.

## Checked interfaces

* `CheckRecursion.Construct.check-graph` defines the actual `chk`.
* `check-internal` realizes the image of `u ↦ ordered (chk u) w` with image
  operation `chk` and the recursive specification `chk-spec`.
* `table-graph` defines `x ↦ ordered x (chk x)`. Its ordinary definable image
  supplies an actual canonical `table a`, `table-mem`, and `table-only`.
* `Discharged a` instantiates the original `NameImage.CheckDischarge.Stage`
  with those constructed suppliers. It assumes no stage table.
* `InternalCheck.check` is an actual `NameKernel.Name`, with proved
  `check-name` and `check-injective`. Its assumptions contain no MemberImage.
* `K9.BooleanSupport.Checked` now obtains its singleton-weight check from
  `InternalCheck`. The broader module still takes MemberImage for other
  constructions; this change removes one real use, not its entire parameter.

A read-only GPT 5.6 Sol review independently checked the induction, filtered
union, collision case, and unique-existence extraction. Compiler verification
and source hashes are recorded separately in `VALIDATION.md` and `checks.json`.

## Next mathematical obligations

The all-condition poset check needs an analogous recursion equation with the
additional bounded weight quantifier. Its stage must construct the entire
set of weighted entries, not falsely treat multiple weights as the output of
a single-valued entry formula. The present agreement and table-construction
argument provides a pattern, but this generalization remains to be proved.

After that, the generic-name map, recursive name translations, and the actual
Boolean value families each need their own definable graphs and adequacy
proofs. Neither `MemberImage` nor `ValueSets.attain` for arbitrary host functions
is a consequence supplied by this result. The endpoint extension axioms,
cardinal preservation and `inner-bot` obligations in `STATUS.md` remain open.
