# Flypitch 4 source audit and its fit with Bedrock

Audit date: 2026-09-08. This note inspects the Lean source at Ian Klatzco's
[`ad649f89e9f3107b7e2ea97a58b2eafdfc80b815`](https://github.com/ianklatzco/flypitch/tree/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4),
committed 2026-07-10. It uses the author's [May 2026 blog post](https://klatz.co/blog/flypitch/)
only as context. The conclusions below come from the pinned `.lean` files. I
downloaded and searched that source without executing it; I did not install its
toolchain, fetch its dependencies, or rebuild it.

## Verdict

The directory is an extensive Lean 4 port of the completed Lean 3 Flypitch
argument, not a sketch of a future port. Its source exports the same decisive
syntactic endpoint:

```text
independence_of_CH : independent ZFC CH_f
```

Here `independent T f` is exactly the conjunction that `f` and its object-language
negation are not derivable from `T`. The two halves are obtained from concrete
Boolean-valued models: the regular-open Cohen algebra forces `not CH`, and a
regular-open collapse algebra forces CH. The root library imports all 24 ported
modules, totaling 29,278 physical lines. The source contains no active `sorry`,
`admit`, or user-declared `axiom`; the two textual occurrences of `sorry` are in
comments. This is strong source-level evidence that the port is a real
replication.

It does not by itself supply Bedrock's forcing and geology framework.
It neither constructs a generic extension of a countable transitive model nor
defines grounds, forcing names relative to a ground, generic filters, a truth
lemma for an actual extension, or a ground predicate. Its result is deliberately
the Boolean-valued, syntactic route. It is strong evidence for making Boolean
semantics an initial preferred proof home within a design that also exports a
full poset interface and verified bridges between the two.

## Toolchain and reproducibility evidence

The pinned project requests the prerelease toolchain
`leanprover/lean4:v4.30.0-rc2`. Its `lakefile.toml` names Mathlib's mutable
`master`, but `lake-manifest.json` resolves Mathlib to
[`83a5988a25fdd78621774a57af7e1f5c55f24289`](https://github.com/leanprover-community/mathlib4/tree/83a5988a25fdd78621774a57af7e1f5c55f24289)
and pins the inherited packages. The manifest, rather than the mutable input
revision, is the reproducible dependency record.

The repository contains `VALIDATION.md`, `VALIDATION2.md`, statement-shape
checks, and an axiom-audit file. Those files report successful local `lake build`
and validation runs. They are maintainer records, not independent CI evidence.
At the audit date the GitHub Actions API reported zero workflow runs for this
repository and the downloaded tree contained no `.github/workflows` files.
Consequently there is no public hosted-CI run tied to the pinned commit. This
audit also did not reproduce the local build claims.

## Exact theorem route

The endpoint chain is visible in the pinned
[`Summary.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean#L96-L138).
Besides `independence_of_CH`, it exports first-order completeness,
Boolean-valued soundness, the assertion that `bSet β` models ZFC for every
nontrivial complete Boolean algebra, and syntactic consistency of ZFC. The
fundamental theorem here is a Boolean-valued ZFC theorem. It is not the usual
poset forcing theorem or the truth lemma for `M[G]`.

The final bridge is in pinned
[`Zfc.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean#L752-L792).
`CH_f_sound` identifies the interpretation of the object-language CH sentence
with the internal Boolean value `CH₂`. The Cohen calculation gives
`V_𝔹_cohen_models_neg_CH`, and Boolean soundness turns it into
`CH_f_unprovable`. The collapse calculation gives
`V_𝔹_collapse_models_CH`, and the same soundness argument turns it into
`neg_CH_f_unprovable`. `Summary.lean` conjoins these results.

This matters when reading the blog's broad description of the Gödel and Cohen
independence result. The inspected Lean 4 proof does not construct `L` and does
not use an `L` model for the positive consistency side. It forces CH with a
collapse algebra. Bedrock already proves the distinct, stronger inner-model
facts `L⊨ZFC` and `L⊨GCH`, each from the single hypothesis `LEM (ℓ-suc ℓ)`.
Flypitch 4 neither duplicates that constructibility development nor connects
its `PSet` and `bSet` universes to Bedrock's `L`.

## The `Bool` route is classical topology, not a finite truth-value model

Pinned
[`CantorSpace.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/CantorSpace.lean#L20-L61)
puts the discrete topology on `Prop` and the product topology on
`Set α`, definitionally `α → Prop`. It then defines a noncomputable
`Prop_to_bool` using `Classical.propDecidable`, proves a classical equivalence
`Prop ≃ Bool`, and uses that equivalence to obtain encodability and separability.
Thus `Bool` supports the countability/topology argument. It is not the carrier
of the forcing semantics and does not turn the construction into computational
two-valued evaluation.

Pinned
[`Forcing.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Forcing.lean#L166-L179)
defines the Cohen algebra as the regular opens of
`Set (pSet_aleph2.Type × ℕ)`. It proves ccc, defines one Cohen real for each
index below its `aleph2` representative, and constructs an injection into the
Boolean-valued continuum. The resulting `neg_CH₂` is the source used by
`Zfc.lean`. This is the actual source route behind the informal phrase "two
copies" or `Bool`: a Cantor cube presented as predicates, followed by its
regular-open complete Boolean algebra.

The CH side is separate. Pinned
[`ForcingCH.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/ForcingCH.lean#L802-L826)
defines `𝔹_collapse` from the regular opens of a collapse space from the type of
the `aleph1` representative to the type of the powerset-of-omega
representative. Its final [`CH_true` and `CH₂_true`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/ForcingCH.lean#L1329-L1341)
feed the other unprovability theorem.

## Trust boundary

The source's `#print axioms independence_of_CH` is followed by the recorded
output `[propext, Classical.choice, Quot.sound]`. A separate
[`validation/AxiomAudit.lean`](https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/validation/AxiomAudit.lean)
asks Lean to print the dependencies of the final and critical intermediate
theorems. Because this audit did not run Lean, it verifies that the checks are
present and that no source-level holes or custom axioms were found; it does not
independently certify the recorded `#print axioms` output. The explicit
classical dependencies are also unsurprising in the code: choice selects
witnesses throughout Boolean-valued collection and the collapse argument,
propositional extensionality is used in the Cantor-space presentation, and
quotient soundness enters through quotient constructions.

The central imported dependency is Mathlib, especially complete Boolean
algebras, topology, cardinals and ordinals, and Mathlib's `PSet`/ZF
infrastructure. The project supplies its own first-order syntax, proof system,
completeness development, Boolean semantics, `bSet`, ZFC realization, regular
opens, Cohen calculation, and collapse calculation. A replication assessment
must therefore count both the ported code and the pinned Mathlib foundation;
it should not describe the result as a small wrapper around an existing Mathlib
CH-independence theorem.

## CTMs, extensions, and geology

Source searches for countable transitive models, generic filters, generic
extensions, grounds, mantles, and geology find no such API or endpoint. Some
definitions use the word `transitive` for ordinals or sets, and some comments
say "ground-model" when comparing a checked `PSet` object with its
Boolean-valued copy. Neither usage constructs a transitive model `M`, a filter
`G`, or an extension `M[G]`. The Boolean-valued type `bSet 𝔹` is the semantic
universe used to refute derivability.

For Bedrock this makes the engineering choice fairly sharp:

| Goal | What Flypitch 4 supplies | What Bedrock still needs |
|---|---|---|
| Replicate syntactic CH independence | A detailed, hole-free source route through complete Boolean algebras, Boolean-valued ZFC, Cohen forcing, collapse forcing, and proof-theoretic soundness | A Cubical Agda implementation of those interfaces and proofs, plus an explicit account of how Lean's host-wide completeness and classical choice translate across universe and truncation boundaries |
| Reuse existing `L⊨ZFC` and `L⊨GCH` | No constructible-universe component and no bridge to `L` | Keep the existing `L` theorems as the positive inner-model result; connect any Flypitch-derived Boolean semantics to the shared forcing foundations and equivalence bridges |
| Build operational set forcing | Regular-open algebras and Boolean-valued sets provide valuable specifications | Ground-relative posets, set-coded names, valuation, forcing definability, generic filters, the truth lemma, `M[G]`, axiom preservation, and ordinal preservation |
| Prove geology and ground definability | No ground or extension relation | The full ground-relative framework, approximation and cover arguments, a uniform ground formula and parameter, and the first-order geology API described in the Bedrock design |

A direct line-by-line port would be a credible replication project for CH
independence, but it would leave the geology-critical interfaces absent. The
source is evidence for reusing the regular-open construction, Boolean soundness
decomposition, `bSet` equality/membership recursion, ccc argument, and collapse
reflection lemmas as specifications for Bedrock's first-class Boolean
interface. The full poset interface must be connected through comprehensive
dense-completion and forcing-equivalence bridges, with canonical proofs shared
by transport instead of duplicated.

The source also keeps two design axes distinct. Its host-level Boolean
presentation does not decide whether an operational theorem should be stated
with posets or Boolean algebras, and choosing a poset presentation does not by
itself internalize the construction in a ground model. Bedrock can maximize
host-language reasoning while adding verified internal model-coding and
absoluteness adapters for geology. The coordinating
[system design](forcing-geology-design-2026-09.md) is authoritative; this audit
records source evidence rather than a competing implementation order.

This division also avoids duplicating Bedrock's strongest completed asset.
`L⊨GCH` already supplies CH inside a canonical inner model and supports the
constructibility narrative. Reimplementing Flypitch's collapse side is useful
as a forcing stress test and as half of a syntactic independence proof, not as
a new proof of the existing `L` result. Conversely, `L⊨GCH` cannot replace the
Cohen side, the metatheoretic soundness argument, or any of the machinery
needed to recognize arbitrary grounds in a forcing extension.
