# Forcing and ground-definability interface audit

This is a code audit, not a claim that the planned forcing development already exists. The current tree contains a reusable syntax and semantic evaluator, a concrete cumulative hierarchy, and a large internal development of `L`. It does not contain Boolean-valued membership, forcing names, a forcing relation, generic filters, grounds, or a ground-definability theorem. Architectural decisions belong to the coordinating [system design](forcing-geology-design-2026-09.md); the findings below are evidence and constraints for that design.

## 1. The reusable semantic boundary is narrow

`TruthAlgebra` is an operation-only signature. It contains a set-valued carrier `Ω`, three binary connectives, negation, top, bottom, and small-indexed meets and joins (`src/Base/Truth.lagda.md:65-72`). It contains no order, Boolean-algebra laws, distributivity, complements, arbitrary-index completeness theorem, or extensional characterization of its operations. Consequently it is already sufficient to *evaluate formulas* in a proposed Boolean-valued structure, but it cannot state or prove the forcing theorem, Boolean-valued equality laws, substitution, mixing, or fullness. The prose promise of a regular-open Boolean completion (`src/Base/Truth.lagda.md:161-174`) has no implementation behind it.

The genuinely generic portion is:

- `ZFStructure 𝕋`, whose carrier is an h-set and whose equality and membership take values in `Ω` (`src/FOL/ZFStructure.lagda.md:61-69`);
- `FOL.Semantics 𝕋 𝒮`, including environments, term evaluation, and formula evaluation by structural recursion (`src/FOL/Semantics.lagda.md:34-41`, `68-69`, `93-115` and the following clauses);
- the syntax and formula transformations, insofar as their imports remain parameterized by `𝕋`.

The present set-theory model interface is not generic in truth values. `FOL.ZFModel` fixes `𝒮 : ZFStructure (hPropAlgebra ℓ)` at its module boundary (`src/FOL/ZFModel.lagda.md:35-38`). Its classes, realization relation, and unique-description operator use equality of hProps and host contractibility (`src/FOL/ZFModel.lagda.md:92-99`, `113-146`). Its ZF record therefore cannot be instantiated by a Boolean-valued universe without a new model interface or a semantic translation theorem.

`FOL.Coding` is also specialized to an hProp-valued structure, although its actual data requirements are only an injective pairing and an injective natural-number encoding (`src/FOL/Coding.lagda.md:61-66`). Its code functions and `Codes` relation are reusable in shape (`src/FOL/Coding.lagda.md:97-104`, `126-155`, `179-184`), but forcing should not depend on the accidental hProp restriction.

## 2. What the current `ZFModel` theorem means

`isZFModel` is a strong external record about a particular hProp-valued carrier. It includes host-level extensionality and `WellFounded _∈ᵗ_` (`src/FOL/ZFModel.lagda.md:217-229`). Thus its regularity field is external well-foundedness, stronger than satisfaction of the first-order Foundation sentence. This strength is used directly for host recursion and induction. A nonstandard or ill-founded external model satisfying ZFC in the ordinary Tarskian sense cannot inhabit this record.

Infinity is externally standard as well. The record carries an actual host map `numeral : ℕ → S`, pins zero and successor membership, and requires a set whose members are *exactly* those host-indexed numerals (`src/FOL/ZFModel.lagda.md:396-425`). This rules out models with nonstandard natural numbers as inhabitants of the existing interface. The record is therefore suitable for the concrete well-founded hierarchy and its transitive submodel, but it is not a general interface for arbitrary models of ZFC.

This distinction controls the forcing theorem statement:

- A semantic CTM theorem must be conditional: given an externally countable, externally transitive, externally well-founded model satisfying the required fragment, plus a forcing notion and an external genericity hypothesis, construct or identify its extension and prove the desired satisfaction result. Countability and generic existence are external hypotheses. Nothing currently supplies them.
- A general internal ZFC theorem quantifies inside a model of ZFC and proves the forcing machinery there, typically as Boolean-valued semantics or as a theorem about names and the forcing relation. It neither asserts that an external generic filter exists nor yields an external countable transitive model. This is the appropriate theorem if the goal is preservation or ground definability over arbitrary internal models.

Calling the current `isZFModel` a generic model of ZFC without these qualifications would conflate those two results.

## 3. Universe completeness and smallness

The forcing use of `⋀` and `⋁` is restricted to index types in `Type ℓ` (`src/Base/Truth.lagda.md:65-72`). A complete Boolean algebra at the same semantic level will therefore need explicitly *small-indexed* suprema and infima, or a presentation showing that every join used by names and quantifiers has a small index. `TruthAlgebra` alone records operations and cannot express that they are the lattice suprema or infima.

The existing universe gap has precise names. `Resizing ℓ` says every hProp in `hProp (ℓ-suc ℓ)` has a small equivalent, while `HPropSmallness ℓ` gives a small type equivalent to the whole classifier `hProp ℓ`; `Impredicativity ℓ` packages the two (`src/Base/Impredicativity.lagda.md:61-62`, `85-100`, `125-129`). Full separation consumes `resizing`, and the power-set construction consumes `hPropSmallness`; these assemble `V⊨ZF-impredicative` (`src/V/Model.lagda.md:430-448`). A single `LEM (ℓ-suc ℓ)` produces that package and hence `V⊨ZF` (`src/Base/Classical.lagda.md:281-313`; `src/V/Model.lagda.md:466-467`).

This solves the hProp classifier problem classically. It does not provide a small carrier or completeness witness for an arbitrary Boolean algebra in `Type (ℓ-suc ℓ)`. A forcing design must name its analogous size obligation rather than hide it in completeness. For example, it could use a `SmallCompleteBooleanAlgebra ℓ` with carrier in `Type ℓ`, or a large carrier plus a small presentation and small-indexed joins. The choice affects whether quantification over names typechecks at the existing `TruthAlgebra ℓ ℓ'` boundary.

`V ℓ` itself is large, in `Type (ℓ-suc ℓ)`, but every set has a small presentation. The structure is `ZFStructure (hPropAlgebra (ℓ-suc ℓ))` (`src/V/Hierarchy.lagda.md:88-104`), while `V.Presentation` exposes the small member type `⟪ a ⟫`, its embedding, membership introduction, fiber recovery, and injectivity (`src/V/Presentation.lagda.md:28-44`). This is the existing tool for bounding quantifiers over the members of one set. It is not a proof that the class of all forcing names, all dense subclasses, or all truth values is small.

## 4. Truncation and choice

The hProp algebra interprets existential quantification by propositional truncation and universal quantification by a genuine dependent product (`src/Base/Truth.lagda.md:119-130`, `148-151`). The ZFC choice field also states only truncated existence of a choice set (`src/FOL/ZFModel.lagda.md:472-484`). These are internal semantic existences.

Host choice is separately named `SetChoice`. In the concrete hierarchy it selects indices from small member presentations; `ChoiceLemma` assumes `SetChoice ℓ` and returns the model's truncated choice-set conclusion (`src/V/Model.lagda.md:508-531`). The headline `V⊨ZFC` requires `SetChoice (ℓ-suc ℓ)`, using Diaconescu to obtain excluded middle and lowering the same choice instance for the member indices (`src/V/Model.lagda.md:564-592`).

For forcing, propositional truncation can hide an internal witness after a proposition has been proved, but it cannot manufacture an external generic filter or allow data-valued recursion from mere existence. Any CTM construction must state the host selection principle used to enumerate dense sets and choose descending conditions. Any internal forcing theorem should keep those external choices out of its statement and prove only the internal existence asserted by the modeled axioms.

## 5. Rank, stages, and existing `L` reuse

There are two different ordinal measurements in the current `L` development.

`L.Rank.rank : S → S` is the ambient von Neumann rank of any set in `V`. It is defined by external membership recursion, satisfies a computation rule, strictly increases along membership, is an ordinal, and fixes ordinals (`src/L/Rank.lagda.md:92-103`, `127-130`, `154-159`, `233-247`). Despite its module name, it is not rank inside `L` and does not require constructibility.

`L.Stage.stage : (x : S) → ⟨ isL x ⟩ → S` is the least ordinal α such that `x ∈ Lset α`. It is obtained by classical well-founded descent from truncated existence, and its public facts are ordinality, stage membership, and leastness (`src/L/Stage.lagda.md:137-156`, `183-200`). This birth stage depends on a proof that `x` is constructible. It is not the von Neumann rank, and no forcing-name rank should be identified with either one without a comparison theorem.

The constructible hierarchy itself is an external meta-level function `Lset` built by membership recursion, while later coding chapters construct internal tables and formulas that represent it. The restriction `𝒮ʟ = 𝒮ᵥ ↾ isL` inherits equality and membership from `V` (`src/L/Constructible.lagda.md:399-415`). `L.Hierarchy` explicitly compares internal tables with the external `Lset` values (`src/L/Hierarchy.lagda.md:121-150`). This external/internal bridge is a useful pattern for a forcing-name hierarchy, but none of its proofs is generic in an arbitrary model or truth algebra.

Reusable components already exercised by `L` include:

- ambient pairing and numeral coding from `V.Coding`; `VCode` instantiates generic `FOL.Coding` (`src/V/Coding.lagda.md:247`);
- model-internal coding `LCode`, plus `codeBridge` identifying its underlying codes with the ambient hierarchy codes (`src/L/Coding/Model.lagda.md:402-429`);
- uniform internal satisfaction over a whole stage code set, with an explicit bridge between hierarchy coding and model coding (`src/L/Coding/UniformSatisfaction.lagda.md:150-180`, `294-337`, `393-447`);
- generic ambient ordinal facts reused by cardinal and reflection modules, while cardinality, reflection, and internal satisfaction themselves are specialized to `𝒮ʟ` and `LEM (ℓ-suc ℓ)` (for representative dependency edges see `src/L/Cardinal.lagda.md:22-37` and `src/L/FormulaReflection.lagda.md:41-74`).

This is substantial reuse for ground definability *after* a ground predicate has been represented inside the relevant structure. What is missing is the forcing-specific bridge that produces such a predicate uniformly from a forcing extension.

## 6. Interface constraints

The audit supports two full public forcing interfaces, poset and Boolean, built
on common foundations and connected by comprehensive equivalence bridges. The
implementation should keep canonical proofs in one preferred home, initially
Boolean semantics where its algebraic calculations are strongest, and transport
them rather than grow two independent complete theories. The following are
constraints on that shared design.

1. Keep `TruthAlgebra` as the evaluator signature. Add a separate law-bearing Boolean interface extending or wrapping it: Boolean order/equality, Boolean-algebra laws, small-indexed join and meet specifications, and the distributivity/complement facts actually consumed by semantics. Do not burden ordinary hProp evaluation with forcing laws.
2. Generalize only the accidental hProp restriction in `FOL.Coding`, since its code shows that it needs a carrier, injective pairing, and numeral injection, not propositional truth. Retain the existing `Codes` and code-injectivity boundary.
3. Add a Boolean-valued model interface distinct from `isZFModel`. Its axioms should be truth-value equations or inequalities and should not import host `WellFounded`. Prove a soundness/transfer theorem to ordinary hProp satisfaction when a valuation or quotient supplies one.
4. Define forcing names from small presentations and give them their own well-founded name rank. State explicitly the smallness data used by each Boolean join. Prove comparison lemmas to ambient `rank` or constructible `stage` where a particular construction requires them.
5. Treat host versus internally coded mathematics and poset versus Boolean presentation as independent axes. Maximize use of the host language, while providing verified model-coding and absoluteness adapters for internally stated forcing and geology results. Keep external CTM assumptions such as countability, dense-set enumeration, and generic existence explicit.
6. For ground definability, expose a small semantic interface rather than importing the full `L.Coding` stack: a formula code, an internal satisfaction predicate with a correctness theorem, parameter coding, and a definable class predicate for the candidate ground. The current `LCode`/`VCode` bridge and uniform-satisfaction table are implementation models, not yet structure-polymorphic libraries.
7. Make dense embeddings, separative quotients, regular-open completion, Boolean forcing values, generic filters or ultrafilters, and generic interpretation into theorem-bearing bridges between the two public presentations.

No source change is made by this audit. A useful isolated Boolean probe is a lawful complete instance at the exact index universe demanded by `TruthAlgebra`, followed by substitution/congruence for Boolean-valued equality. This probe does not make ground-internal completeness into host-wide completeness. The coordinating [system design](forcing-geology-design-2026-09.md) owns ordering and acceptance criteria. A CTM existence theorem remains an explicitly conditional layer.

## 7. Inventory of absent forcing artifacts

No current module defines a forcing poset interface, separative quotient, regular-open completion, complete Boolean algebra laws, forcing names, name valuation, Boolean-valued membership or equality, forcing relation, generic filter, dense subset, truth lemma, generic extension, ground model predicate, approximation/cover hypotheses, or a ground-definability theorem. The reserved notation and prose in `Base.Truth` are architectural intent only. The existing proved results `L⊨ZFC` and `L⊨GCH` concern the constructible substructure and do not imply any forcing or geology theorem.
