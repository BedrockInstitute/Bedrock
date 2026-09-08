# Bell 2005: reassessment of the forcing and Cohen roadmap

Review date: 2026-09-08. Sources: the user-supplied [local PDF](bell-2005-boolean-valued-models.pdf) and its [searchable extraction](bell-2005-boolean-valued-models.fulltext.md). References below are to printed pages; add 20 for the PDF page number. This is a targeted review of the foundational, completion, Cohen and generic-extension arguments, with selected future-extension results. It does not claim every proof or exercise in the book has been audited or formalized.

## 1. Decision

Keep T1/T2 as the proved L ZFC/GCH results, construct an actual ordinary non-CH model for T3, retain ground definability as T4, and keep the two public interfaces with certified completion and semantic transport. Bell provides a particularly direct textbook precedent: Chapter 1 builds Boolean semantics, Chapter 2 derives condition-based forcing from a dense basis of a complete Boolean algebra, and Chapter 4 constructs actual generic extensions relative to a ground model. In Theorem 2.12, the lower-bound proof itself combines Boolean names with finite-condition arguments. This supports the proposed division of proof ownership rather than two independent forcing developments.

Refine five contracts before K0: the compiler is a metalinguistic formula transformation, not an internal global truth predicate; complete embeddings have weaker logical transport than forcing equivalences; mixing, unique witnesses and the general maximum principle are distinct capabilities; Bell's axiom schema presentations need explicit equivalence adapters; and completion uniqueness must support alternative certified Boolean backends.

Do not copy Bell's chapter order literally. The model-relative correctness boundary must be present from K0 even though the book introduces it in Chapter 4. The third trophy does not require the upper-bound half of Theorem 2.12, the collapse chapter, Boolean-valued analysis or the categorical appendix.

## 2. Result ledger and concrete implementation consequences

| Bell location | Result or qualification | Consequence for Bedrock |
|---|---|---|
| pp. 17-20 | Alternative axiom schemas; results default to ambient ZFC | K1 proves schema equivalences and records internal versus host assumptions |
| Equations 1.10, 1.15-1.16, pp. 22-23 | Quantifier values and simultaneous atomic recursion | K0 probes a pair-of-names recursion and a set of attained truth values |
| Remark 1, p. 24 | No definable global truth-value map for the ambient set universe | K4 exports a host formula compiler with per-formula internal definitions |
| Theorem 1.17, pp. 24-28 | Equality, congruence, bounded quantifiers and logical validity | Canonical Boolean semantic kernel; avoid reproving logical laws in the poset client |
| Theorem 1.20 / Corollary 1.21, pp. 29-30 | Atomic and restricted-formula agreement for complete subalgebras | Do not grant arbitrary-formula elementarity to every complete embedding |
| Mixing Lemma 1.25, pp. 33-34 | Mixing compatible weighted families | Explicit-family construction is separate from selecting witnesses |
| Lemma 1.27 / Problems 1.29-1.30, pp. 35-37 | Maximum principle, unique-witness variant, and uniform AC equivalence | Separate three witness capabilities, with Choice in the correct model |
| Lemmas 1.36 and 1.38, pp. 38-42 | Rank-bounded Collection and normalized powerset names | Concrete K6 proof templates without circular extension axioms |
| Theorem 1.51, pp. 50-52 | ccc preserves checked cardinals and aleph identification | K7 targets identification as well as no collapse, in the ZFC profile |
| Lemmas 2.1-2.3 / Problem 2.4, pp. 55-57 | Dense completion, uniqueness, nonseparative reduction | K2 automatic completion and comparison of certified implementations |
| Theorem 2.5, pp. 58-59 | Poset clauses derived from Boolean values | K5 direct public clauses through a canonical semantic proof |
| Theorem 2.12, pp. 64-66 | Exact continuum under extra cardinal arithmetic | Extract the lower-bound argument; do not inherit its upper-bound assumptions |
| Chapter 4 opening, p. 88 | B can be internally complete but externally incomplete | Ground-relative joins are mandatory from the beginning |
| Theorem 4.1, p. 89 | Arbitrary-ultrafilter quotient truth, using the maximum principle | Distinct full-model theorem, not the hypothesis-minimal generic truth theorem |
| Theorems 4.22-4.23, pp. 97-98 | Actual extension, minimality, ordinals, countable-ground generic existence | K5/K6/K11 specifications; no generic-existence inference from L⊨ZFC |
| Problems 4.34-4.37, pp. 103-107 | Poset generics, iteration and intermediate submodels | F7 obligations, including exercises and external dependencies, not ready-made proofs |
| Chapter 3; Chapter 6, especially pp. 128-130 | Symmetry and iterated Boolean extensions | Boolean interface is a long-term structural interface, not merely a Cohen backend |

Bell's term "refined" here denotes the separativity property used by the completion construction. Keep the repository's terminology policy; the extraction retains Bell's original wording for search.

## 3. The compiler boundary is mathematically essential

Bell's Remark 1 on p. 24 explicitly distinguishes the value assigned to a fixed formula from a definable class function giving values for all formulas in the ambient universe. This must refine every occurrence of "internal formula compiler" in the design.

The desired architecture is schematically:

    compile : host syntax -> host syntax
    correctness(φ, M, B, parameters):
      satisfaction in M of the generated formula agrees with the externally
      specified Boolean/forcing semantics of this fixed φ.

The syntactic transformation can be uniform and formalized in Agda; a coded version of that syntax transformation can itself be a set-theoretic operation. The forbidden step is claiming one internal satisfaction relation for the model's entire own universe and all input formulas. Uniformity of syntactic compilation is not uniform internal semantic truth.

For each fixed φ, define its set of attained truth values as a subset of B, using the already-constructed definition for its subformula. Separation and the appropriate rank/Collection argument justify a join in M. This is the internal analogue of Bell's equation 1.10, not an arbitrary external indexed join. In a larger ambient setting, satisfaction for a set-sized model M can be uniform because M is a set there; that does not place M's self-truth predicate inside M.

A K0 boundary example is trivial forcing / the two-element algebra: an internal universal truth-value map for that presentation would already give an internal truth predicate for the ground. The probe should exercise the valid external compiler and its fixed-formula correctness, not attempt to inhabit the invalid internal contract. Geology's eventual uniform ground formula is one particular object-language formula; it requires no global truth predicate and remains compatible with this restriction.

## 4. Choice and witness management

Bell states on p. 20 that results are in ZFC unless otherwise indicated. A short or apparently explicit proof elsewhere in the book is therefore not evidence of a ZF or host-LEM-only result.

The Mixing Lemma 1.25 starts with an indexed family of names and weights satisfying a compatibility inequality. It constructs a name meeting the weighted equalities. This does not itself select a family of witnesses to arbitrary existential assertions. Lemma 1.27 makes the additional selection and disjoint-refinement steps explicit.

Problem 1.29 gives a no-AC witness theorem for unique existence, unique in Boolean-valued equality. It does not establish unique raw Agda names. Problem 1.30 identifies the maximum principle uniformly over all complete Boolean algebras with AC. This does not say every fixed algebra's instance implies full AC. Add a unique-witness package and distinguish it from both explicit-family mixing and unrestricted fullness. Bell's cores in Lemma 1.31 also select representatives; do not turn these cores into a globally chosen canonical raw-name representation without an assumption audit.

The first Cohen ground is ZFC, so its internal AC is a legitimate resource for the maximum principle and the corresponding Boolean axiom proofs. "ZF transfer" from a ZFC ground is not the same result as a transfer theorem requiring only a ZF ground. Record the ground profile on each theorem, even when the conclusion lists just ZF axioms. Future choiceless results must not inherit stronger hypotheses through a hidden helper.

Theorem 4.1 uses fullness for quotient truth under an arbitrary ultrafilter. Our generic-truth theorem can instead use genericity meeting the relevant ground-coded value families and the associated rank bounds. Retain that minimal-hypothesis theorem. A Bell-style full-model quotient theorem is now required as a separate capability for T3. Fullness and an actually constructed ordinary ultrafilter deliver the ordinary non-CH model; they do not strengthen the generic-truth contract. The exact LEM-only realization and internal-to-host witness extraction still require validation. If an implementation chooses the quotient/collapse route for the ZFC application, it must still prove the promised valuation agreement and generic-extension contracts. Countability is not required for the supplied-generic theorem.

## 5. Algebraic bridges require different logical strengths

Bell's Lemma 2.3 gives an explicit comparison between two completions of the same separative presentation: map b to the join of the images of all conditions lying below b. This should become the adapter's uniqueness/coherence theorem. It permits a canonical RO construction as fallback and a specialized Boolean representation when the application has one, with a certificate relating the two.

For Cohen, the finite-map basis identifies the completion with the regular-open algebra of the corresponding Cantor cube (pp. 57-58). A topology implementation is therefore a possible certified backend, not a second forcing engine. K2 requires the general comparison theorem; building both concrete Cohen backends before the third trophy is unnecessary.

Keep three transports distinct: Boolean isomorphism, dense forcing equivalence, and a proper complete-subalgebra inclusion. The first two support the appropriate full semantic correspondence. For the third, Theorem 1.20 and Corollary 1.21 provide atomic and bounded/restricted-formula agreement, not arbitrary-formula elementarity. Different extensions can have different CH values. Therefore morphism automation must carry a logical-strength contract as well as a structural map class. This restriction matters directly to F7 intermediate models and iterations.

Bell's default ZFC context does not supersede the choiceless chain-condition warning from Karagila-Schweber already recorded in the master design. Completion existence, semantic equivalence and CCC preservation remain separate certificates. Finite support, presentation size and closure also remain separate.

## 6. More concrete axiom and Cohen proof templates

Bell's "Replacement" on p. 17 is a Collection form, and "Regularity" is an induction schema. Implement the equivalences with the chosen first-order ZF schemas, including the surrounding axioms and classical logic needed. An internal induction schema must not be confused with Agda's external accessibility of membership. Do not rename one record field and pretend the equivalence is automatic.

For Collection, Lemma 1.36 bounds witness ranks for each member of a name's domain and then combines those bounds into a single stage. Promote this rank-bound construction to the shared library: it also funds quantifier witnesses and later ground-local arguments. For Power Set, Lemma 1.38 normalizes candidates to Boolean-valued functions on the original name's domain. The set of such functions is constructed in the ground; its size and membership correctness precede extension Power Set. These are stronger specifications than "prove Replacement and Power Set" and avoid an unnecessary representative-selection step in those particular constructions.

For Cohen, use Theorem 1.51 as the reference for checked cardinal/aleph identification. The lower-bound half of Theorem 2.12 defines coordinate real names, separates them with a fresh finite coordinate, and forms a named injection. That half does not need the hypothesis κ^ℵ₀ = κ used for the exact upper bound. Retain κ = ground ω₂ and the current not-CH target. Ground GCH and the upper-bound counting lemmas remain later enhancements, not prerequisites.

## 7. Changes to delivery and scope

K0 now explicitly probes pair recursion, the fixed-formula compiler boundary and separate witness capabilities. K1 adds the schema equivalences. K2 adds comparison of certified completions. K4 distinguishes explicit mixing, unique witnesses and general fullness, and marks logical transport strength. K6 uses the rank-bound and normalized-powerset proof templates, and records the ground theory separately from the extension conclusion. K7 and K9 use the cited lower-bound/cardinal specifications. K5 retains the generic truth contract while allowing a separately scoped full-model quotient theorem.

The owner has now selected the ordinary model constructor as T3, adding the Bell 4.1 quotient branch while retaining all general forcing dependencies. The main benefit is a sharper specification and fewer accidental overclaims. Chapter 4 is essential for our actual-extension endpoint; a literal port stopping after Bell's Boolean independence chapter would still be incomplete for this project.

The future program remains broader than this textbook. Chapter 3 and Chapter 6 validate the need for symmetry, Boolean-valued second-stage algebras, complete embeddings and iteration coherence. Problem 4.37 and its surrounding discussion include hints and cited results rather than a complete self-contained intermediate-model implementation. The book does not discharge ground-definability, advanced geology or arbitrary class-forcing obligations. Its Heyting-valued chapters suggest possible reuse of algebraic laws, but do not justify turning every current component into a universal abstraction before it has consumers.

## 8. Extraction and validation limits

The retrieval file contains all 211 page text slots, expands common ligatures and escapes unmapped control glyphs. PDF page 1 is image-only; its cover title was separately transcribed and labelled. Mathematical layout, accents and sub/superscripts are not reliably reconstructed. Original source wording, including possible typos, is preserved rather than silently corrected. The PDF is retained with a matching SHA-256 so exact formulas can be checked locally. Printed pages 24 and 36 were also visually checked for the truth-definition and Choice qualifications.

This task used direct PyMuPDF extraction after the owner rejected the readability-oriented skill. No skill conversion script was run. No source code or landmark statement was changed. Validation: all 211 consecutive page slots were checked; the 210 text-bearing pages exactly match the declared ligature/control-glyph/trailing-whitespace normalization of the PDF text layer. The image-only cover has a labelled title transcription. The retained PDF hash matches the upload. Four Markdown files passed local checks of fence balance and 27 relative links. Scoped prose and glossary gates passed on these files (exit 0). No Agda proof has been claimed from this review.
