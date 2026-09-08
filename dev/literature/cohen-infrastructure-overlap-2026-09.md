# Cohen forcing infrastructure overlap

Research date: 2026-09-08. Status: read-only infrastructure and application
evidence note. The authoritative architecture and schedule are in
[the forcing and geology system design](forcing-geology-design-2026-09.md).
This note records what the Cohen application demands from that design; it is
not a competing implementation plan or a claim that forcing has been
implemented in Bedrock. Source paths refer to the tree on the research date.

The first headline is now Cohen, followed by ground definability. The [detailed implementation roadmap](cohen-implementation-roadmap-2026-09.md) specifies K0-K11, including certified automatic completion, semantic transport and separate chain-condition certificates. The master plan retains authority over long-term architecture.

Scope update: the owner selected the semantic Cohen generic-extension theorem and subsequent geology. Comparisons below with syntactic independence describe different endpoints, not required roadmap work. Proof systems, proof-system soundness and PRA relative consistency are outside the committed program. See the master plan and K0 evidence ledger for current scope and status.

## 1. Recommended endpoint

The smallest useful Cohen application theorem is conditional on a ground model `W`, a
forcing notion in `W`, and a supplied generic filter. Take a ground cardinal
`κ > ω₁`, use

$$
\operatorname{Add}(\omega,\kappa)
  = \{p \mid p\text{ is a finite partial function }\kappa\times\omega\to 2\},
$$

ordered by reverse inclusion, and prove:

1. the generic extension satisfies ZFC;
2. `Add(ω,κ)` is ccc, so `ω₁` and `κ` remain cardinals and `ω₁ < κ` remains true;
3. for each `α < κ`, the generic union restricted to `{α} × ω` is a real;
4. the resulting `κ` reals are pairwise distinct;
5. hence there is an injection `κ ↪ 𝒫(ω)`, and CH is false.

For the intended example one can take `W = L` and `κ = ω₂^L`. The current
theorem `L⊨GCH` is more than this route needs. `L⊨ZFC`, the existence of the
successor cardinals `ω₁^L` and `ω₂^L`, and their strict comparison suffice.
There is no need to prove
`2^ω = κ`, count nice names, establish an upper bound on the continuum, or
assume GCH in the ground. If the project defines CH by equicardinality of
`𝒫(ω)` and `ω₁`, an assumed CH bijection composed with `κ ↪ 𝒫(ω)` would inject
`κ` into `ω₁`, contradicting preservation of `ω₁ < κ`. This also avoids proving
that every real has a nice name.

Distinguish the committed endpoint from an optional, out-of-scope endpoint:

- a semantic extension theorem, conditional on `G` being generic over `W`;
- a syntactic relative-consistency theorem, built with Boolean-valued soundness
  or a formal proof translation, which does not assert an external generic over
  the proper class `L`.

The distinction matters. The present `L` is a class predicate on the ambient
cumulative hierarchy, not an externally countable transitive set. Ordinary
Rasiowa-Sikorski construction only supplies a generic after the dense sets to
be met have been countably enumerated. Thus Bedrock cannot derive an actual
`L`-generic filter from `L⊨ZFC`. It must either assume a generic for a semantic
extension theorem, restrict to an externally countable set model, or use the
Boolean-valued/syntactic route for consistency.

These endpoints do not determine a poset-only architecture. The project requires
two complete usable public interfaces from the outset: a poset interface for
conditions, genericity and actual extensions, and a complete Boolean algebra
interface for semantic values and canonical logical proofs. A systematic
completion and transport layer must identify their common semantics. Shared
contracts and an initial bridge slice therefore precede this Cohen milestone,
even though the finite-condition lemmas below remain Cohen-specific.

## 2. Dependency matrix

| Cohen obligation | Current Bedrock asset | Disposition | Reason |
|---|---|---|---|
| Deep first-order syntax, substitution, relativization, and evaluation | `FOL.Syntax`, `FOL.Manipulation.*`, `FOL.Semantics` | Direct | The syntax and evaluator already abstract over a truth algebra. They are the common language for ZFC preservation, CH, and later ground definitions. |
| A law-bearing complete Boolean algebra semantics | `Base.Truth.TruthAlgebra`, `FOL.ZFStructure` | Required public interface | `TruthAlgebra` supplies operations but no order or Boolean laws. `ZFStructure` is suitably truth-valued, but forcing needs equality congruence, Boolean soundness and ground-indexed completeness with explicit size bounds. |
| An ordinary ZFC model interface for extensions | `FOL.ZFModel.isZFModel`, `isZFCModel` | Generalize via a new profile | The current record is hProp-valued and requires host `WellFounded` membership and the exact host-indexed numeral chain. It is suitable for the concrete `V` and `L`, not arbitrary internal or externally ill-founded models. |
| Small set presentations | `V.Hierarchy`, `V.Presentation` | Direct for ambient constructions | `⟪ a ⟫`, `member`, `fiber`, and `↪-inj` provide the existing small indexing pattern. They do not make all names, dense classes, or Boolean truth values small. |
| Ordered pairs and graphs | `V.Coding`, `FOL.Coding`, `L.Coding.Injection` | Generalize | Ambient pairing and generic coding shapes are reusable. `L.Coding.Injection`, `InjCode`, and `InjL` are specialized to constructible graph witnesses and satisfaction in `𝒮ʟ`; extension cardinal comparisons need structure-relative versions. |
| Injection composition and Cantor-Schroeder-Bernstein | `V.CantorBernstein`, `L.CantorBernstein`, `L.InjectionComposition` | Direct at type level; generalize internally | `V.CantorBernstein` is the reusable core. The `L.*` wrappers require constructible codes and should not become forcing prerequisites. |
| Ordinals, `ω`, ordinal comparison, and successor cardinals | `L.Ordinal`, `L.Ordinal.Linear`, `L.Cardinal`, `L.CardinalAbove` | Generalize the interface | Ambient ordinal facts are reusable. `IsCardinalL`, `SuccCardL`, and `InjL` explicitly mean cardinality inside `L`; forcing needs ground/extension-relative cardinal predicates and check-name or valuation preservation. |
| Ground example satisfying ZFC | `L.Model.L⊨ZFC`, `Landmarks.L⊨ZFC` | Direct theorem input after an adapter | This is the desired ground axiom package, but it supplies neither external countability nor a generic. |
| Ground GCH and condensation/counting stack | `L.GCH.*`, `Landmarks.L⊨GCH` | Outside the minimum | The Cohen lower-bound proof uses no condensation, hull counting, stage injection, exact power-set size, or nice-name count. Choosing `ω₂^L` does not require GCH. |
| Forcing poset, dense sets, filters, genericity, names, valuation, check names, forcing relation, truth lemma | none | Missing | These form one required public face of the common forcing core needed by both the Cohen theorem and future geology; shared semantic theorems should be transported from a canonical proof rather than independently duplicated. |
| Poset/Boolean completion and semantic equivalence | none | Missing | The second public face requires dense completion, translations of names and values, forcing agreement, generic transfer and explicit universe/ground indexing. The bridge is an initial architecture milestone, not an optional later comparison. |
| ZFC preservation and ordinal preservation | none | Missing | The extension must be shown to satisfy ZFC before `notCH` has the advertised strength. Ordinal preservation alone does not give cardinal preservation. |
| Finite partial functions and compatibility by union | no set-theoretic forcing interface | Missing | A finite-map library should expose domain, restriction, compatible union, and fresh-coordinate extension. The ccc and distinct-real arguments should consume this interface. |
| Delta-system lemma for uncountable families of finite sets | none | Missing | It is the standard combinatorial proof of ccc for `Add(ω,κ)`. It also requires a usable account of countability, `ω₁`, finite sets, and thinning. |
| ccc preservation of cardinals/cofinalities | none | Missing | The minimum needs enough preservation to retain `ω₁ < κ`. A theorem preserving all ground cardinals is a clean reusable endpoint, but the first consumer only requires these two cardinals and their order. |
| Coordinate Cohen reals and pairwise distinctness | none | Missing | For `α ≠ β`, below any condition a fresh natural coordinate can be assigned opposite bits at `α` and `β`; the corresponding dense set forces the two reals apart. |
| CH and not-CH sentences or semantic predicates | only `GCHStatement`, specialized to `L` and all infinite cardinals | Missing | Define CH once for a general model, preferably in the shared object language and with a semantic characterization. Do not specialize the new statement to `L`. |
| Grounds, approximation/cover, and ground definability | none | Missing | Names, valuation, forcing relation, and extension membership overlap. The geology uniqueness proof and parameter formula are separate later layers. |

## 3. The ccc proof package

The ccc proof should be factored into three reusable results after the shared
forcing contracts and initial poset/Boolean bridge slice are usable.

First, prove the delta-system lemma in the exact strength consumed: every
uncountable family of finite sets has an uncountable subfamily whose pairwise
intersections are one fixed root. This is cardinal combinatorics, not a fact
about forcing.

Second, prove a finite-map compatibility lemma. Apply the delta-system lemma to
the finite domains of an uncountable family of Cohen conditions. Thin once more
so all conditions give the same values on the common root. Any two remaining
conditions then have a consistent union, hence are compatible. This proves that
`Add(ω,κ)` is ccc. The formalization paper by Han and van Doorn uses precisely
this division: its Section 4.2 defines Cohen conditions as finite positive and
negative specifications, and Sections 4.4 and 5 use ccc and the delta-system
lemma to preserve cardinal inequalities.

Third, keep preservation as a theorem about arbitrary ccc forcing. For the
minimum Cohen result it is enough to expose:

$$
W\models \omega_1 < \kappa
\quad\Longrightarrow\quad
W[G]\models \check\omega_1 < \check\kappa.
$$

The proof should pass through the standard antichain argument for names of
functions. Each possible value is decided by a maximal antichain; ccc makes
each such set of possibilities countable. A more general theorem that ccc
preserves ground cardinals and cofinalities is desirable, but the public Cohen
theorem should depend only on the preservation result it uses.

The chain-condition bound and the geology parameter `δ` have different roles; their proof infrastructure can still share possible-value and internal-cardinality lemmas. In the
ground-definability route, `δ` is normally a regular cardinal above the size of
the forcing, used in the `δ`-approximation and `δ`-cover properties. In the Cohen
example, ccc preserves `ω₁`, but nontrivial Cohen forcing does not thereby gain
the `ω₁`-approximation property. The safe geology parameter for a set forcing
`P` is chosen above `|P|`, typically a regular successor such as
`(|P|^+)^W`, according to the exact approximation/cover theorem being used.
Do not identify that `δ` with the ccc witness `ω₁`, and do not infer approximation
from chain condition.

Likewise, replacing a poset by its regular-open completion preserves forcing
semantics only through the proved completion bridge. It does not make the two
carriers interchangeable for size, closure or chain-condition witnesses.
Statements about finite supports and fresh coordinates belong first to the
poset presentation; only consequences covered by a transport theorem may be
exported through the Boolean interface.

## 4. Distinct generic reals without continuum counting

Let `g = ⋃G : κ × ω → 2`. Totality uses the dense sets

$$
D_{\alpha,n}=\{p\mid (\alpha,n)\in\operatorname{dom}(p)\}.
$$

For `α < κ`, define `rα(n) = g(α,n)`. For `α ≠ β`, use

$$
E_{\alpha,\beta}=\{p\mid
  \exists n\;p(\alpha,n)\ne p(\beta,n)\}.
$$

Given a condition, choose an unused `n` and extend it by opposite bits at the
two coordinates. Thus `Eαβ` is dense, the generic meets it, and `rα ≠ rβ`.
This yields `α ↦ rα` as an injection `κ ↪ 𝒫(ω)`.

At this point the proof should stop counting reals. If CH held in the extension,
the chosen general-model formulation of CH would turn `𝒫(ω)` into size `ω₁`.
Composition would give `κ ↪ ω₁`, contradicting the preserved strict inequality.
The argument therefore requires neither an enumeration of all names for reals
nor an upper bound `|𝒫(ω)| ≤ κ`. Ground GCH is irrelevant to this contradiction.

## 5. Sharing with ground definability

The following capabilities should be common infrastructure rather than live under a
Cohen namespace:

- set-coded preorders, dense subsets, filters, and genericity;
- recursively presented names, name rank, valuation, and check names;
- the definability of forcing and the truth lemma;
- the extension carrier and its ZFC and ordinal-preservation theorems;
- model-relative formulas for functions, injections, cardinals, power sets, and
  CH;
- adapters between the strong current `isZFModel` profile and the new internal
  first-order or transitive-ground profiles.
- law-bearing Boolean semantics, regular-open completion and systematic
  equivalence transports between Boolean and poset names, formula values,
  forcing and generic valuation.

Ground relativity cuts across both public interfaces and is independent of
whether an implementation step uses Agda host constructions or internal syntax.
Host-level finite maps, recursion, Boolean operations and extension carriers
should be reused where they give the cleanest construction. Each public theorem
still needs a correctness adapter showing that the construction is coded in the
ground and agrees with the relevant object-language predicate. Internal syntax
alone does not supply that ground/ambient agreement.

Cohen-specific code should then contain only finite partial functions,
coordinate-density lemmas, the ccc proof, and the family of distinct reals.
Ground-definability-specific code begins after the common extension layer, with
the approximation/cover theorem, uniqueness of a ground from the relevant
parameter, and the uniform ground formula. This boundary allows the Cohen
extension to become a genuine test case for the shared forcing API without
making the geology theorem depend on CH or on Cohen forcing. Longer iterations,
symmetry and class forcing remain later scoped work, while their required
distinctions are anticipated in the initial contracts. In particular, class
forcing is not silently covered by the set-forcing theorem.

## 6. Comparison with Flypitch

Flypitch validates an informative Boolean proof decomposition. Han and van Doorn
split their development into Boolean-valued first-order semantics, complete
Boolean-algebra calculations, the recursively defined Boolean-valued universe,
and the particular forcing argument. Their `bSet B` construction is an
Aczel-Werner style inductive universe, closely related to recursive forcing
names. For `notCH`, they use the regular-open completion of the Cohen poset,
construct an internal injection from checked `aleph_2` into the power set of
the naturals, prove ccc using the delta-system lemma, and use ccc to preserve
cardinal inequalities. This is strong evidence for keeping logic, Boolean laws,
names, and Cohen combinatorics in separate packages, and for locating canonical
semantic proofs in a Boolean kernel when their algebraic form is clearest.

The overlap is architectural rather than a direct code port. Bedrock already
has deep syntax and truth-valued evaluation, but lacks Flypitch's law-bearing
complete Boolean algebra, Boolean equality congruence, Boolean soundness,
Boolean-valued set universe, and cardinal-preservation bridge. Conversely,
Bedrock's completed `L` is a useful ground example and its future goal includes
actual generic extensions and ground predicates. Flypitch explicitly avoids
ground models and generic filters for its Boolean-valued consistency proof.
Consequently its route can inform Bedrock's Boolean public interface, while the
semantic extension and geology layers still require ground-relative names,
valuation by a supplied generic, and a poset-facing truth theorem. The two
routes should meet through systematic equivalence bridges, not independently
duplicated logical machinery. Boolean semantics is the preferred initial proof
home, not a requirement that every proof be repeated there and at the poset
interface.

## 7. Exact source pointers

- Paul J. Cohen, [The Independence of the Continuum Hypothesis,
  I](https://pmc.ncbi.nlm.nih.gov/articles/PMC221287/), *PNAS* 50 (1963),
  1143-1148, DOI 10.1073/pnas.50.6.1143. Theorem 1 states the model results,
  and the paper introduces the ramified forcing language and generic object.
- Paul J. Cohen, [The Independence of the Continuum Hypothesis,
  II](https://www.pnas.org/doi/pdf/10.1073/pnas.51.1.105), *PNAS* 51 (1964),
  105-110, DOI 10.1073/pnas.51.1.105. Theorem 2 proves the generic structure is
  a model of ZF; Lemmas 6 onward formalize forcing and establish the truth and
  axiom-preservation machinery. These papers are historically primary, though
  their presentation is not the proposed modern module decomposition.
- Jesse Michael Han and Floris van Doorn,
  [A formalization of forcing and the unprovability of the continuum
  hypothesis](https://flypitch.github.io/assets/flypitch-itp-2019.pdf), ITP
  2019, Article 31. Section 2.3 defines Boolean-valued structures, Section 2.4
  proves Boolean soundness, Section 3 constructs `bSet B` and proves the
  fundamental theorem, Section 4.2 defines the Cohen poset, Section 4.3 builds
  the distinct Cohen reals, and Section 4.4 derives preservation of cardinal
  inequalities from ccc. Section 5 proves the delta-system combinatorics.
- Jesse Michael Han and Floris van Doorn,
  [A Formal Proof of the Independence of the Continuum
  Hypothesis](https://flypitch.github.io/assets/flypitch-cpp.pdf), CPP 2020.
  Definitions 5.3-5.6 and Section 5.2 give the concise ccc, Cohen-poset,
  regular-open, and delta-system route; the repository's
  [`src/summary.lean`](https://github.com/flypitch/flypitch/blob/master/src/summary.lean)
  records the checked endpoints. This is the primary report of the completed
  formalization.
- Emmanuel Gunther, Miguel Pagano, and Pedro Sanchez Terraf,
  [First steps towards a formalization of
  Forcing](https://arxiv.org/abs/1807.05174), 2018. Section 3 formalizes
  dependent choice and Rasiowa-Sikorski; Section 4 constructs generics over a
  countable transitive model; later sections define names, valuation, and the
  extension. It is a primary formalization source for the generic-existence
  boundary that the Boolean-valued Flypitch route omits.

## 8. Cohen application milestone

After the system design's shared contracts and initial equivalence bridge have
been accepted, a credible first Cohen application milestone ends with one
theorem of the following mathematical shape:

> Given a transitive ground `W` satisfying ZFC, ground cardinals
> `ω₁ < κ`, the Cohen poset `Add(ω,κ)` in `W`, and a filter `G` generic over
> `W`, the extension `W[G]` satisfies ZFC and not-CH.

Its proof dependencies should expose ZFC preservation, ccc, preservation of
`ω₁ < κ`, and the injection of `κ` into the extension power set of `ω`. The
statement must not claim existence of `G` for the class `L`. A separate corollary
may instantiate `W` with the existing constructible universe once the chosen
semantic profile and generic hypothesis are made explicit. A later syntactic
corollary may remove the external generic by proving relative consistency
through Boolean-valued soundness or proof translation.

This milestone proves only the lower bound needed for not-CH. It does not force
an exact value of the continuum, and neither nice-name counting nor a ground
GCH hypothesis belongs in its acceptance conditions. The master system design,
rather than this evidence note, decides the implementation order and the
acceptance criteria for the architecture as a whole.
