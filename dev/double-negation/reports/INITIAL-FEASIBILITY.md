# Double-negation migration: assumption boundary and feasibility

Status: blocked on the mathematical construction, 2026-09-28. No migration of
the source theorems has been completed. This document does not certify
feasibility or a universal impossibility theorem.

## Authorized objective

Construct an internal cumulative hierarchy satisfying classical ZF, without
external excluded middle or external resizing. The owner explicitly excludes
even a restricted small classifier for double-negation-stable propositions.
Retain coherent module boundaries for classical reasoning and resizing, and
preserve the book's broad mathematical organization.

The starting revision on `main` is
`d62ebaa641e6865fce4dd76e8a37cf2ee9e5a270`, marked by the local annotated tag
`double-negation-turn-2026-09-28`. The old research branch
`internal-logic-milestones` remains available for reference. Its formula-level
classicality assumption uses ordinary satisfaction; it is not a construction
of a double-negation internal world.

## Correction to the proposed route

In an adequately structured internal classical type theory, the usual proof
that LEM implies propositional and proposition-universe resizing can be carried
out internally. This conditional result does not construct that internal type
theory, its universes, or its cumulative hierarchy in the external theory.

Neither the existence of the proposition modality `A ↦ ¬¬ A` nor the internal
validity of excluded middle establishes the missing universe structure.
Consequently the earlier claim that the unconditional ZF migration only needs
an infrastructure implementation was not justified.

There is currently no verified assumption-free construction meeting the
objective. This is a foundational gap, not a remaining routine porting task.
The failures below concern specific constructions; they are not a proved
impossibility theorem for every feature accepted by Cubical Agda 2.8.0.

## Concrete distinctions

1. For every proposition `P`, intuitionistic reasoning proves
   `¬¬ (Dec P)`. A decision gives a small representative using the unit or empty
   type, hence also `¬¬ (hasSize ℓ-zero P)`.
2. This is pointwise double-negated existence. It does not supply
   `(P : hProp ℓ) → hasSize ℓ-zero P`, a single small classifier, or an
   equivalence of proposition universes. Moving double negation across an
   arbitrary dependent product is a further principle.
3. Assuming stability of `Dec P` for every proposition already yields external
   LEM. Assuming stability of `hasSize ℓ-zero P` for every proposition already
   yields external resizing. These cannot be treated as free elimination rules.
4. Cubical's `doubleNegationModality` has stable propositions as its modal
   types. It is not the full sheafification of sets or higher types. In
   particular, its reflection sends every type to a proposition.
5. Indexing nullification by all dense `ℓ`-small propositions gives an index
   type in `Type (ℓ-suc ℓ)`. The library's `Null` therefore returns a type at
   least at that higher level. Merely increasing every level reproduces the
   same gap. A different construction would need its own closure proofs.

## Relevant existing consumers

- `Base.Impredicativity.hasSize` returns an actual small proposition and an
  equivalence. `ΩResizing` returns an actual small type equivalent to the
  proposition universe.
- `Base.Classical.LEM→ΩResizing` constructs the equivalence with lifted Boolean
  codes using actual external decisions.
- `V.Model.Power` takes `ΩResizing (ℓ-suc ℓ) ℓ`. Its `𝒫V` indexes candidate
  subsets by functions into the small truth-value classifier. `separateFull`
  uses derived resizing on formula satisfaction, then `separateFromSmall`.
- `FOL.Semantics` uses ordinary truncated existential and disjunctive
  interpretations. A double-negation interpretation changes those operations
  and requires compatible atomic equality, substitution and quantifiers.
- `FOL.ZFModel.isZFModel` includes host `WellFounded` and contractible types of
  realizing sets, whose inhabitants can be projected to actual sets. These
  fields are stronger data than merely double-negated existence. An internal
  model interface must specify which operations are internal before such
  extraction is reused.

Thus the two foundational modules can retain distinct responsibilities, but
changing only their implementations cannot preserve all existing consumers.

## Direct-interpretation audit

A checked obstruction rules out keeping host equality while merely replacing
membership by its double negation. Work already at `V ℓ-zero` and write
`x ∈ⁿ a` for `¬¬ (x ∈ a)`. Suppose this relation has host-valued
extensionality:

```text
(∀ x, (x ∈ⁿ a ↔ x ∈ⁿ b)) → a ≡ b.
```

For any small proposition `P`, form the conditional singleton
`aP = sett P (λ _ → ∅)` and `oneV = {∅}`. Assuming `¬¬ P`, their modal
memberships agree at every `x`. The proposed extensionality gives the actual
path `aP ≡ oneV`. Transporting the ordinary witness `∅ ∈ oneV` backwards
along that path gives ordinary membership in `aP`, from which `P` follows
by eliminating propositional truncation into `P`. Thus the proposed
extensionality implies DNE for all small propositions and hence external LEM.

This is an implication proved in the current safe compiler, not a universe
inference failure. It rules out this particular direct interpretation under
the stated boundary. It does not rule out a different internal equality,
quotient carrier or recursively defined relation. Such alternatives require
new proofs of substitution, extensionality, separation, replacement and
powerset; the existing host-equality model record cannot simply be reused.

Direct negative interpretations also do not evade consistency strength merely
by returning double-negated model existence. For any types `Model` and
`ProofOfFalse`, a soundness map `Model → ¬ ProofOfFalse` extends to
`¬¬ Model → ¬ ProofOfFalse`. Consequently a sound model of classical ZF,
even given only double-negatively, would still establish consistency of ZF.
The checked lemma here is generic. The repository has no formal derivation
calculus and ZF soundness proof, so it is not itself a formalized ZF
consistency or impossibility theorem.

## Primary-source evidence

- Rijke, Shulman and Spitters, [Modalities in homotopy type theory](https://lmcs.episciences.org/6015/pdf),
  Example 1.9 and Theorem 3.37: distinguish the proposition modality from
  Lawvere-Tierney sheafification. Their construction in Theorem 3.37 assumes a
  small universe of propositions. It does not remove the relevant size premise.
- Swan, [Oracle modalities](https://arxiv.org/pdf/2406.05818), Section 3:
  the construction of zero-truncated double-negation sheaves uses a small
  classifier for stable propositions. The accompanying
  [Agda source](https://github.com/awswan/oraclemodality/blob/main/Axioms/NegativeResizing.agda)
  postulates the classifier and its operations. This route violates the owner's
  stated assumption boundary.
- Swan, [Double negation stable h-propositions in cubical sets](https://arxiv.org/abs/2209.15035):
  the relative consistency result transfers classifiers from the metatheory to
  cubical models. It does not establish a classifier as an assumption-free
  internal definition in this repository.
- van den Berg and Moerdijk,
  [Aspects of Predicative Algebraic Set Theory III: Sheaves](https://arxiv.org/pdf/0912.1242),
  introduction, page 4: arbitrary double-negation sheaves cannot preserve all
  the structure needed for CZF. Fullness fails in general; CZF plus LEM is ZF
  and has greater proof-theoretic strength. This rules out an automatic
  transfer argument over CZF, not every stronger constructive metatheory.
- Rathjen, [Proof Theory of Constructive Systems: Inductive Types and Univalence](https://arxiv.org/pdf/1610.02191),
  Theorem 6.5 and Corollary 6.7: ordinary MLTT with a hierarchy of universes and
  univalence has a proof-theoretic strength far below ZF. Applying this as a
  precise impossibility theorem for the present compiler requires an account
  of the additional inductive and higher inductive features being used.
- Swan's [discussion of HoTT consistency strength](https://mathoverflow.net/a/477408)
  explicitly places the proposed sheafification/free-injective construction
  of a ZF model in the case with propositional resizing. It is not a
  resizing-free construction. The discussion also explains why the choice of
  allowed higher inductive types matters.
- Gambino and Aczel,
  [The Generalised Type-Theoretic Interpretation of Constructive Set Theory](https://eprints.whiterose.ac.uk/113161/8/27588436.pdf),
  pages 95–96, Theorems 5.16–5.17: their predicative variant extends the
  small-proposition double-negation operator to large propositions using a
  distinct operator `J`; it need not equal ordinary double negation there.
  Preserving Subset Collection requires a set-presentability premise (DNSP in
  the double-negation case). The standard interpretation into IZF uses Full
  Separation in the treatment of Collection. This direct-interpretation
  literature therefore does not supply the missing assumption-free ZF model.

## Scoped machine checks

Generated experiments are under ignored
`_build/double-negation-investigation/`, separate from the book's import graph.
They use a local `.agda-lib` depending on pinned cubical 0.9.

Run from that directory, with the absolute repository compiler path:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home \
GHCRTS='-A64m -I0 -M8g' \
/Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda Boundary.agda
```

Exit 0. Under `--safe`, the file proves pointwise double-negated decisions and
small representatives, the two implications from assumed stability above,
and forms the large nullification indexed by all dense propositions.

The same command with `SameLevel.agda` exits 42, as expected. Its deliberately
invalid definition attempts to assign that large nullification a same-level
type. The exact diagnostic at `SameLevel.agda:8:16-28` is:

```text
error: [UnequalSorts]
Type (ℓ-suc ℓ) != Type ℓ
when checking that the expression LargeSheaf X has type Type ℓ
```

This checks the size of this expression only; a compiler rejection does not
prove that no alternative construction exists. No failing experiment belongs
to `src/`, and no source theorem has been changed or claimed complete.

The same compiler command with `ExtensionalityBoundary.agda` exits 0. It proves
`host-extensionality-implies-DNE`, `host-extensionality-implies-LEM` for actual
Cubical `V ℓ-zero`, and the generic
`double-negated-model-implies-consistency` implication above. All have complete
bodies, with no postulates or additional assumptions other than the explicit
antecedents of the implications. The file is an obstruction experiment, not
an implementation of a ZF model.

## Conditions for proceeding to source migration

Before changing the theorem signatures, a proposed route must exhibit:

1. An assumption-free interpretation of the internal types, universes and
   equality actually used by the model construction, or a direct set-model
   interpretation avoiding a full internal type theory.
2. Correct universe levels and internal smallness for the operations used by
   separation and powerset, without a supplied stable classifier or an
   equivalent hidden hypothesis.
3. The internal hierarchy and its induction/replacement principles, and a
   precise internal ZF satisfaction statement with sound logical rules.
4. A check of all ZF axioms and both schemas. Proving only a bounded fragment,
   conditional theorem or pointwise double-negated resizing is not completion.

If these conditions cannot be met in the permitted metatheory, report that
mathematical obstruction. Do not replace the owner's objective with a weaker
one, introduce a new size axiom under another name, or mark this investigation
as a completed predicative ZF construction.

## Blocked audit

The same missing mathematical construction persisted through three goal turns:
the assumption-boundary audit, the direct-interpretation audit, and the final
current-state revalidation. The first two produced concrete evidence and
checked implications, but neither supplied the internal smallness and model
closure needed to proceed. The third found no change in those premises.

The authoritative source still states
`V⊨ZF : ΩResizing (ℓ-suc ℓ) ℓ → isZFModel`; the convenience theorem still takes
external LEM. There is no new internal ZF theorem. The source tree and baseline
tag are unchanged, and no migration was committed or pushed.

No justified implementation step toward the full objective is currently
available. Porting elementary modal logic would not resolve this obstruction;
parameterizing a model by a stable classifier would violate the owner's
boundary. Further broad searches or repetitions of the local checks are not
evidence of progress.

Resumption needs a substantiated alternative mathematical route satisfying the
conditions above, or an explicit owner revision of the objective. The present
investigation does not request or assume permission to add a size principle.
The task is blocked rather than completed.
