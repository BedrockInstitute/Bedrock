# Forcing formalizations and an extensible Cubical Agda route

This survey predates the separate audit of Ian Klatzco's Lean 4 port. See the
[pinned Flypitch 4 source audit](flypitch4-source-audit-2026-09.md). Claims below
about the original Flypitch implementation concern Lean 3; the table is not a
complete inventory of current Lean versions. Architectural decisions belong to
the coordinating [system design](forcing-geology-design-2026-09.md); this note
records evidence for that design rather than an alternative plan.

Research note, verified against the linked sources on 2026-09-08. This is an
architecture survey, not a claim that Bedrock currently formalizes forcing.
"Complete" below always means complete for the stated exported theorem, not a
judgment that the project supplies every forcing construction in the literature.

## Findings that constrain the architecture

The two completed, inspectable formalizations make different foundational
choices and therefore establish different kinds of theorem.

| Development | Core representation | Verified endpoint | Explicit cost or assumption |
|---|---|---|---|
| Isabelle/ZF `Forcing` (2020) and `Independence_CH` (2022) | A forcing notion is a set-coded preorder with top in a countable transitive ground model; names, valuation, generic filters and the forcing relation are all ground-relative | A proper generic extension satisfying ZF/ZFC; later, generic extensions satisfying CH and its negation | The public endpoint assumes a countable transitive model. The development internalizes formulas needed for Replacement and Separation and obtains an external generic filter by countability. |
| Lean 3 Flypitch (2020) | Complete Boolean algebras, Boolean-valued first-order semantics, and an inductive type `bSet B` of Boolean-valued sets | `independence_of_CH : independent ZFC CH_f` | Lean's printed axioms are `propext`, `classical.choice`, and `quot.sound`. Its universe-sized type-theoretic construction is not a ground-relative set model or a construction of `L`. |
| Quirin's Coq/HoTT sheaf work | Lawvere-Tierney sheafification and type-theoretic forcing ideas | Computer-checked sheafification, not a completed ZFC forcing independence proof | The 2018 Isabelle survey reports only a candidate CH counterexample and explicitly says the non-surjection results remained future work. This is evidence for a possible semantic backend, not evidence for a completed set-forcing core. |

These are not merely two implementations of the same interface. Isabelle/ZF
proves facts about an actual `M[G]`, preserves its ordinals, and exposes the
ground-model obligations behind schemas. Flypitch proves an object-language
unprovability theorem by Boolean-valued soundness without constructing a ctm or
choosing a generic filter. Both designs are valuable, but neither result can be
silently read as the other.

## Isabelle/ZF: the strongest precedent for an operational core

The current AFP entry [Formalization of Forcing in
Isabelle/ZF](https://isa-afp.org/entries/Forcing.html) lists separate theories
for forcing notions, Rasiowa-Sikorski, internalization, names, forcing
recursion, the forcing theorems, individual ZFC axioms, ordinals, and proper
extensions. Its abstract states the precise completed result: from a countable
transitive model of ZFC it constructs a proper generic extension satisfying
ZFC.

The redeveloped [Independence of
CH](https://isa-afp.org/entries/Independence_CH.html) is a stronger completed
artifact. The entry says that, under the same ctm hypothesis, it constructs
proper generic extensions satisfying CH and its negation. Exact source
pointers are:

- [`Forcing_Main.extensions_of_ctms_ZF`](https://isa-afp.org/browser_info/current/AFP/Independence_CH/Forcing_Main.html#Forcing_Main.extensions_of_ctms_ZF)
  constructs a countable transitive proper extension, preserves the ordinals,
  proves ZF, and proves ZFC when the ground satisfies AC.
- [`Not_CH.not_CH`](https://isa-afp.org/browser_info/current/AFP/Independence_CH/Not_CH.html#Not_CH.not_CH)
  proves that the extension's `aleph_1` is not its continuum. The forcing
  notion is explicitly `Add_subs(kappa) = Fn(omega, kappa x omega, 2)` ordered
  by `Fnle`; the source first proves its ccc and preservation facts.
- [`CH.CH`](https://isa-afp.org/browser_info/current/AFP/Independence_CH/CH.html#CH.CH)
  proves equality of the extension's `aleph_1` and continuum. The later
  [`ctm_ZFC_imp_ctm_CH`](https://isa-afp.org/browser_info/current/AFP/Independence_CH/CH.html#CH.ctm_ZFC_imp_ctm_CH)
  packages this as a ctm of `ZFC + CH` with the same ordinals.

The source also records a useful engineering warning in `Not_CH`: it uses an
unrelativized finite-function poset because that theory predates `Fn_rel`, and
says the relative version would have been more appropriate. That is direct
evidence for making the ground-relative form primary and deriving convenient
absolute instances only after proving absoluteness.

The 2020 paper explains why formula syntax is not optional bookkeeping. Its
section "The Definition of `forces`" says the code maps internal formulas to
internal formulas, so that forcing is definable in `M`; the semantic forcing
relation is then proved equivalent to that internalized relation. See [Gunther,
Pagano and Sánchez Terraf, *Formalization of Forcing in
Isabelle/ZF*](https://arxiv.org/abs/2001.09715), especially Sections 4 to 6.
This is the closest verified model for Bedrock because Bedrock already has
deep formula syntax, satisfaction, relativized model predicates, ordinals, and
set-coded recursion.

Scope must remain exact. `Independence_CH` proves extension theorems from a ctm;
it does not export a first-order metatheorem saying that CH is syntactically
independent of ZFC. Conversely, its ctm construction gives much more direct
ground/extension information than Flypitch's final syntactic theorem.

## Flypitch: the strongest precedent for a Boolean semantic backend

Flypitch's public summary gives exact machine-checked endpoints in
[`src/summary.lean`](https://raw.githubusercontent.com/flypitch/flypitch/master/src/summary.lean),
`master` as fetched on 2026-09-08. GitHub's public page did not expose the HEAD
commit hash in this pass, so the mutable source claims below are pinned to this
access date, file, and line numbers; the completed-result claim is independently
pinned to the published CPP 2020 paper:

- lines 64 to 66: `boolean_valued_soundness_theorem`;
- lines 68 to 70: `fundamental_theorem_of_forcing`, stating that `bSet B`
  Boolean-satisfies ZFC for every nontrivial complete Boolean algebra `B`;
- lines 75 to 85: unprovability of CH and of its negation, combined as
  `independence_of_CH : independent ZFC CH_f`;
- lines 86 to 89: `#print axioms` reports propositional extensionality,
  type-theoretic classical choice, and quotient soundness.

The completed 2020 paper, [Han and van Doorn, *A Formal Proof of the
Independence of the Continuum
Hypothesis*](https://flypitch.github.io/assets/flypitch-cpp.pdf), uses Cohen
forcing for `not CH` and sigma-closed collapse forcing for CH. Section 1.1
explains the principal benefit: Boolean semantics bypasses Löwenheim-Skolem,
Mostowski collapse, ctms, and generic-filter existence, and separates into a
general Boolean semantics library, complete-Boolean-algebra calculations,
Boolean-valued sets, and application-specific forcing. The earlier [ITP 2019
paper](https://arxiv.org/abs/1904.10570) gives the exact `not CH` specialization:
the regular-open algebra of the Cantor space `2^(omega_2 x omega)`.

Flypitch is therefore positive evidence for a first-class Boolean interface,
for Boolean semantics as an effective initial proof home, and for automation of
Boolean truth-value calculations. The paper relies deliberately on
type-theoretic objects unavailable as sets in a first-order ground model:
cardinals and ordinals one universe above their representatives, an entire
universe of input types, and `bSet B` as a universe-indexed inductive type. Its
README also lists forcing over ctms and the constructible-universe proof of CH
as future work. A direct port would abandon the ground-relative definability
that Bedrock needs for geology and inner-model interaction.

## Classical routes and what each one asks us to formalize

Kunen's 1980 route is the operational baseline followed by the Isabelle work.
The verified table of contents in [*Set Theory: An Introduction to Independence
Proofs*](https://pages.jh.edu/rrynasi1/FoundationsOFMath/Literature/Set/Kunen1980SetTheory-AnIntroductionToIndependenceProofs.pdf)
locates the complete route in Chapter VII: generic extensions in Section 2,
forcing in Section 3, ZFC in `M[G]` in Section 4, finite partial functions in
Section 5, larger partial functions in Section 6, and embeddings, isomorphisms,
and Boolean-valued models only in Section 7. Definition VII.5.1 uses
`Fn(I,J)`, finite partial functions from `I` to `J`, ordered by reverse
inclusion. This ordering convention should be recorded at the boundary rather
than baked into every theorem.

Jech's third-millennium edition compresses the core into Chapter 14,
"Forcing," pages 201 to 224, followed by Chapter 15, "Applications of
Forcing," pages 225 to 265; the publisher's [official table of
contents](https://link.springer.com/book/10.1007/3-540-44761-X) verifies these
locations. Jech's Boolean completion presentation is useful for proving the
equivalence of dense embeddings, separative quotients, regular-open algebras,
Boolean values, and the generic model theorem. It is a good specification for
the equivalence bridge between the two full public interfaces; the poset
interface need not carry complete Boolean operations as fields.

Bell is the semantic baseline. The official [Oxford contents and
abstract](https://academic.oup.com/book/32627) place Boolean and Heyting
algebras in Chapter 0, Boolean-valued models in Chapter 1, forcing and
independence proofs in Chapter 2, generic ultrafilters and transitive ZFC
models only in Chapter 4, and cardinal collapsing in Chapter 5. Flypitch says
its `not CH` proof synthesizes Bell Chapter 2 with Manin, while its collapse
algebra is based on Bell Exercise 2.18. Bell supports the Boolean backend very
well, but its order of exposition answers a semantic question different from
the ground-relative operational question answered by Kunen.

## Completion, generic quotients, and class-size boundaries

For a set forcing `P`, the reusable bridges should be stated as separate
theorems:

1. take the separative quotient of `P`;
2. embed it densely into its regular-open Boolean completion `RO(P)`;
3. transport forcing statements and generic filters along a dense embedding;
4. identify Boolean truth values with the regular opens generated by forcing
   conditions;
5. only then relate a suitable generic ultrafilter quotient of `V^B` to an
   operational generic extension.

This separation prevents three unjustified collapses.

First, "complete in the ground" is not the same interface as a host operation
joining every host-indexed family. Ordinary set forcing needs joins for
families which the ground regards as sets. A Cubical Agda field of the form
`(I : Type ell) -> (I -> B) -> B` quantifies over all host families at that
universe, including families absent from the coded ground model. Requiring it
at the operational core would strengthen the datum and may force a successor
universe or resizing principle. The safe interface is ground-relative:
`Join` consumes a coded family in `M`, with closure and the least-upper-bound
law proved relative to `M`. A host-complete `TruthAlgebra` can be a later,
strictly stronger backend used when an example genuinely supplies it.

Second, quotienting by an arbitrary ultrafilter is not the operational theorem
`M[G]`. Genericity is what makes the external filter meet every dense subset
belonging to `M`, gives the truth lemma, and supports the identification with a
generic extension. Even where a full Boolean-valued universe modulo an
ultrafilter satisfies a transfer theorem, an arbitrary ultrafilter need not
give the intended ground extension and the quotient may be externally
ill-founded. The library should distinguish `Filter`, `Ultrafilter`,
`MGeneric`, the Boolean quotient relation, and the theorem identifying a
generic quotient with valuation by `G`.

Third, the collection of all names is generally a proper class in the
set-theoretic presentation. Each individual name is a well-founded set of
pairs `(name, condition)`, and a rank-bounded collection of names can be a set;
the total name hierarchy cannot be passed to a set constructor merely because
Agda can place an indexed representation in a type. For class forcing, the
carrier of conditions may be a proper class. Individual ordinary set-names
remain sets, while genuinely class-sized names are separate objects requiring
a class theory; neither kind licenses collecting all names into one set.
Holy, Krapf, Lücke, Njegomir and Schlicht prove that for class forcing both
definability and the truth lemma can fail, and that Boolean completions may
fail to exist or be nonunique. See [*Class forcing, the forcing theorem and
Boolean completions*](https://arxiv.org/abs/1710.10820), Theorem 1.2 and the
introduction. This rules out advertising a set-forcing completion API as a
class-forcing API without additional hypotheses.

## Architectural constraints established by the evidence

The system design requires two first-class full public interfaces, one for
posets and one for complete Boolean algebras, together with comprehensive
equivalence bridges. They must share canonical foundations and proofs, with
transport across dense embeddings, separative quotients, regular-open
completion, forcing values, and generic interpretation instead of two
independent complete theories. Boolean semantics is the preferred initial proof
home; the poset interface remains structurally complete for operational forcing
and geology. The numbered constraints below describe dependencies and public
obligations, not a competing implementation schedule.

1. **Shared syntax and relativization.** Reuse Bedrock's formula, renaming,
   satisfaction, coded-function, and model infrastructure. Add forcing-language
   arities and substitutions as syntax-level interfaces independent of a
   particular poset.
2. **Ground-relative forcing data.** Package a coded carrier `P in M`, its
   preorder and top, with closure/absoluteness facts. Choose one internal order
   meaning, preferably "stronger," and supply adapters for reverse-inclusion
   examples. Do not encode antisymmetry into the basic forcing notion: both AFP
   and standard texts begin comfortably with preorders.
3. **Set-coded names and valuation.** Define rank-bounded names first, prove
   monotonicity and cumulative closure, then expose the class predicate "is a
   `P`-name." Evaluation takes an external `M`-generic set `G`; no theorem should
   quantify over a supposed set of all names.
4. **Internal forcing recursion.** Define atomic forcing by well-founded
   recursion and compile arbitrary formulas to ground formulas. Prove
   definability, monotonicity, density, truth, and the semantic equivalence in
   separate modules. This mirrors the verified Isabelle dependency structure
   and keeps schema transfer reusable.
5. **Generic extension and axiom transfer.** Construct `M[G]` as the range of
   valuation, then prove transitivity, ground embedding, ordinal behavior, and
   ZF axioms. State the exact assumptions of generic existence separately:
   countability/DC is one external construction route, not a field of every
   forcing notion.
6. **Dense embeddings and separative quotient.** Make invariance under dense
   equivalence a public interface before building a catalog of forcing notions.
7. **Regular-open Boolean interface and bridge.** Construct `RO(P)`, prove the dense
   embedding and agreement between `p forces phi` and Boolean values. Provide
   two completeness records: ground-internal completeness for ordinary coded
   forcing and host completeness for Flypitch-style semantics. Never coerce the
   former silently to the latter.
8. **Boolean-valued semantics.** Build the generic first-order
   `TruthAlgebra` semantics and Boolean soundness layer as the initial preferred
   proof home. Export the corresponding poset results through the verified
   bridges whenever transport preserves the theorem's hypotheses and content.
9. **Examples and later stress tests.** The minimum reusable acceptance route
   needs a trivial forcing instance, invariance under a dense equivalence, and
   one two-step example; small forcing estimates and the generic extension
   theorem are enough to exercise the operational interfaces. Cohen forcing,
   ccc/cardinal preservation, `not CH`, closed collapse forcing, and CH are
   required acceptance cases as selected by the system design, while their
   particular cardinal machinery stays modular. Iterations, symmetric
   extensions, Boolean ultrapowers, and class
   forcing are later clients with additional explicit structures.

The survey exposes two independent axes. One is host-level versus internally
coded mathematics; the other is poset versus Boolean presentation. A theorem
may occupy either position on each axis. Bedrock should maximize convenient
host-language reasoning while supplying verified internal model-coding and
absoluteness adapters where ground-relative statements require them. The
dense-completion bridges relate the presentation axis; they do not by themselves
turn host-wide joins, arbitrary ultrafilters, or the class of all names into
set-coded objects of the ground model.

## Evidence limits

The verified completed set-forcing corpus found in this pass is concentrated in
Isabelle/ZF and Lean 3 Flypitch. The earlier Quirin work is relevant but partial
for CH, and the Agda projects returned by search concern type-theoretic or
orthogonal forcing rather than a completed ZFC generic-extension development.
No primary source found in this pass establishes a completed forcing
formalization in Cubical Agda. This is a dated search result, not a claim of
nonexistence.
