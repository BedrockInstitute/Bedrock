# K10: partial proofs and a K7 interface obstruction

Historical checkpoint: the subsequent [K7 local-interface repair](k7-local-preservation-repair-2026-09.md)
fixes the interface described below and adds checked suppliers. Full K10
remains unfinished; this report preserves the original checkpoint scope.

K10 is **not complete**. On 2026-09-13, seven new isolated modules passed the
serial safe Agda gate, including their aggregate import. The 211 inherited
Agda files remain byte-for-byte unchanged. No production source was changed.

Persistent checkpoint:
`/Users/alsg/Agentic/bedrock-proofs-archive/k10-partial-2026-09-13`.
Its `K10-report.md` gives the detailed scope and remaining obligations;
`sh verify-k10-partial.sh` reruns the partial gate and records module logs.

Closed work:

- Internal cardinal contradiction and actual shared non-CH sentence
  satisfaction, conditional on explicitly stated cardinal data.
- Negated shared GCH omega-instance sentence agreement and satisfaction.
- Actual K9/K5 `check(w)` is omega, from ground omega and filter positivity.
- Actual translated Boolean pairs and graph: entry/support specifications,
  membership values and indexed functional/injective equality laws.
- A conditional formal obstruction for the unrestricted K7 possible-value
  antichain schema, using the actual chain-condition vocabulary.

The missing K7 supplier is not merely an unassembled theorem.
`K7/PossibleValues.agda:174-175` defines `valueFo f` as pair membership in
`f`, without functionhood. Its `valuesOf-spec` at lines 455-460 uses any
forcing condition. `K7/NoCollapse.agda:483-487` nevertheless demands a
value antichain for every name `f` and coordinate. Under CCC this would make
the possible values of every relation countable, including a relation with
one input and all members of an uncountable target as outputs.

`K10/PreservationBoundary.agda` formally proves the conditional obstruction:
the exact schema, a full-possible-values witness, actual CCC and target
uncountability imply bottom. It does not construct a full concrete
countermodel to the actual evaluator. Source inspection independently
confirms that the functionhood and common-condition restrictions are absent.

The repair needs possible values below a common condition `p`, together with
`p` forcing the relevant function/surjection property. Functionhood in one
generic extension alone does not constrain conditions outside that region.
The condition must be threaded through the covering and preservation
consumers. The inherited K7 snapshot is left intact pending that repair.

Other preservation suppliers remain unfilled: `FamilySet`, `InverseSpread`,
`ProvedRangeHolds` and checked-injection transfer. K8 supplies actual Cohen
CCC, not these obligations. Boolean formula-level graph injection,
checked-cardinal preservation and non-CH top value also remain unfinished.
The completed atomic Boolean lemmas must not be advertised as those results.

The K3 realization hypotheses remain explicit. No CH/GCH, continuum
arithmetic, host choice, generic existence or Boolean-top reflection is
assumed to bypass an unfinished conclusion. Both existing production
landmarks are untouched.
