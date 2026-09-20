# Research inventory and acceptance audit

Audit date: 2026-09-20. Historical completion reports describe isolated proof
gates, often with explicit capabilities. They do not establish the complete
ordinary-model constructor. None of K0-K11 has been integrated into the current
trilingual production tree by this preservation operation.

The final continuation regression passes 72 positive endpoint modules and
four expected-failure controls. This is verified component progress, not
completion of K10 or the full K11 integration contract.

| Package | Preserved result | Acceptance qualification |
| --- | --- | --- |
| K0 | Representation probes and final decision | Representation gate closed in the historical branch |
| K1 | Ordinary profiles, cardinal vocabulary, CH/GCH comparisons and L adapters | Historical isolated gate closed |
| K2 | Posets, regular-open completions and certificates | Historical report retains coded B⁺ order and one coded acceptance-instance exception |
| K3 | Names, valuation, translations, checked and generic names | Historical gate closed relative to explicit realization capabilities |
| K4 | Atomic Boolean values and fixed-formula compiler | Historical gate closed with separate witness/realization contracts |
| K5 | Poset semantics, agreement and truth lemmas | Historical report retains two exceptions and one unmeasured cost |
| K6 | Axiom-transfer lemmas and structure adapters | Conditional transfer library; full concrete Cohen instance not closed |
| K7 | Possible-value bounds and cardinal-preservation components | Local interface repair checked historically; consumers must supply the required functions/readings |
| K8 | Internal Cohen finite maps, density and ccc | Historical isolated gate closed, 62 modules reported |
| K9 | Set-coded family of distinct Cohen reals | Historical isolated gate closed, 19 modules reported; MemberImage and extension PowerSet remain explicit |
| K10 | Internal check recursion, compiler, atomic agreement, reverse translation, Boolean subset/powerset components, conditional theorem | OPEN: final assumptions listed below |
| K11 | Least-index construction, enumerated generic filter and carrier-enumeration corollaries | Generic construction exists; full K10 application/general API acceptance remains OPEN |
| K12-K15 | Roadmap only in this inventory | No completion claimed |

The detailed historical reports and roadmap are readable in `notes/`; original
bytes and intermediate snapshots are recoverable using `archive.py`.

## Exact remaining endpoint obligations

`active/K10/CohenTheorem.agda`, module `WithPreservedCardinals`, takes extension
PowerSet, Separation, Collection and Choice, plus preservation of the checked
ground cardinals. Its returned ZFC and non-CH proofs are genuine conditional
results. These inputs must be constructed from the accepted ground hypotheses
before claiming the general Cohen theorem. A supplied generic is legitimate
for K10's general theorem; constructing one belongs to K11's externally
countable-ground corollary, and is not an extra K10 defect.

`active/K10/CohenBooleanCHBot.agda`, module `FromParts`, initially takes
`omega-top`, `power-top`, and `inner-bot`. The current continuation has checked
suppliers for the first two and removes them from `FromParts`; only `inner-bot`
remains an input there. This closes the CH formula's omega and powerset-at-omega
clauses, not the general extension PowerSet axiom. The injection/cardinal
argument producing `inner-bot` still needs closure. Compiling a sentence does
not by itself prove that its value is top. The exact four injection-value
obligations and their current partial suppliers are recorded in
`reports/INNER-BOT-AUDIT.md`; this is a mathematical supply gap, not just
module assembly.

The K11 enumeration is an appropriate explicit hypothesis. No assertion is made
that an externally countable transitive ground exists. Its old Cohen wrappers
also take `NameKernel.MemberImage` through `K9.NameGround`, although the actual
generic construction in `K11.CountableGround` does not need this capability.
The new `K11.CountableCohen` interface removes that routing dependency and also
avoids Families and Accessibility. It uses the actual K8 empty condition and
the checked enumeration-to-generic constructor. Both the new interface and
the original `Corollary` consumer pass named Agda checks.

The current-source regression exposed a reversed equality transport in
`K10.CohenBooleanInjKPairFwd.kpair-sgl-rev`, producing `4 != 2 of type ℕ`.
The correction transports the two-slot singleton result back to the four-slot
pair context using `sym (sgl-match ...)`. The repaired module passes its named
check and the resumed regression. Original bytes and diagnostic are retained.

## Foundational limitation that must remain visible

`NameKernel.MemberImage` realizes images of **arbitrary host functions** on
members, not only internally definable functions. The actual theorem
`LInstanceImage.memberImage→subclass` proves that an L instance yields arbitrary
ambient subclass closure (with a seed). It is therefore not a proved consequence
of ordinary ground ZFC. K10 still exposes it. Supplying it without proof, or
silently changing the intended ground contract to include it, would not complete
the roadmap. The source-level replacement must realize the particular definable
images needed by the construction, or prove an adequate narrower interface.

## Internal check recursion now constructed

`active/CheckRecursion.agda` constructs good partial recursion tables, proves
compatibility by membership induction, and uses ordinary Collection and
Separation to collect and merge them. The resulting first-order value relation
is total and single-valued. Unique existence yields the actual `chk`, its
`check-graph`, and its recursive membership equation `chk-spec`, with no
MemberImage or supplied recursive graph.

The constructed canonical `table a`, `table-mem`, and `table-only` now discharge
`NameImage.CheckDischarge.Stage`. `active/InternalCheck.agda` additionally
proves actual NameKernel name validity and injectivity. These modules retain
explicit host membership accessibility and ordinary ground axioms. They do
not claim that ordinary Foundation supplies host accessibility.

`K9.BooleanSupport.Checked` now uses this new singleton-weight construction.
Its public check specification is preserved. The broader module still needs
MemberImage for other constructions; the parameter has not been removed
from the complete K10 interface. See `reports/CHECK-RECURSION.md` for the proof
argument and exact scope.

The next check obligation is the all-condition poset variant consumed by
`K9.NameGround`: each member contributes entries at every condition. Its
stage must construct that full set and prove the corresponding recursive
equation. A singleton-weight check cannot silently replace this different
operation. The generic-name map and name translations then need actual
narrow image suppliers of their own.

The Boolean side has a separate issue: `K4.ValueSets.ValueSets.attain` covers
every host function, whereas `ValueGraph` and `graph→valueSet` close one
particular definable family. Each actual consumer must supply that family's
formula, satisfaction proof, and uniqueness proof; a blanket replacement of
`MemberImage` by one fixed graph is not justified. The generic binary host
function in `K10.CohenTableGraph.Graph` has the same issue. Its atomic-equality
consumer needs an adequate formula for the actual equality-value function,
without circularly assuming the compiler that this table is meant to construct.

## Validation policy

Fresh logs and exit statuses are recorded in `reports/VALIDATION.md` when a
command finishes. Historical logs in the object store remain historical evidence.
The current endpoint regression covers its explicit list, not every archived
experimental file. Negative controls must fail for the expected type mismatch.
All new proof modules keep `--safe`; no postulates, unsafe termination flags,
new choice axioms, or unfilled holes are accepted.

The GLM 5.3 Flash read-only drafting attempt returned HTTP 429, code 1309,
expired subscription. No draft was produced and no retry loop was started.
Scoped GPT 5.6 Sol verification independently confirmed the endpoint assumptions
and the unnecessary K11 MemberImage dependency. Coordinator changes require
their own named Agda checks.
