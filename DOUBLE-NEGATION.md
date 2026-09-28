# Double-negation research archive

This is the unified entry point for the investigation preserved on
`internal-logic-milestones`. The full objective remains unresolved. Neither a
complete migration of Bedrock to internal classical ZF nor an impossibility
theorem covering every permitted interpretation has been established.

The baseline is commit `d62ebaa641e6865fce4dd76e8a37cf2ee9e5a270`. Its former
local marker was `double-negation-turn-2026-09-28`; this archive records the
commit permanently so that retaining the temporary Git tag is unnecessary.
The research branch incorporates that main revision and preserves the earlier
research commit `053e89ff` in its ancestry and as source snapshots.

## The original requirement

Use excluded middle expressed by the existing deeply embedded first-order
language, interpreted internally through double negation, to derive an
appropriate internal proposition-universe resizing principle. That principle
must support the actual downstream set-theoretic constructions, including
full internal ZF, while preserving a coherent separation between classical
logic and resizing modules. No external excluded middle, external resizing,
or assumed small stable-proposition classifier is permitted.

The intended logical starting point is:

```text
∀ {n} (φ : Formula S n) (γ : Vec S n), γ ⊨⁻ (φ ∨̇ ¬̇ φ).
```

Changing the interpretation of satisfaction is part of the investigation;
replacing this premise by an unrelated excluded-middle condition for every
host proposition is not. Internal type theory and relational semantics were
explored, but their results do not complete the original requirement without
a proved connection to this deep first-order premise and its consumers.

## Start here

1. [Consolidated results and boundaries](dev/double-negation/ROUTES.md): every
   explored route, its positive results, hypotheses, failures and open questions.
2. [Archive layout and reproduction](dev/double-negation/README.md): preserved
   proof sources, historical reports, validation instructions and warnings.
3. [Current deep-FOL result](dev/double-negation/reports/DEEP-FOL-OMEGA.md): the
   candidate that returns to the exact Formula-based premise.
4. [Evidence inventory](dev/double-negation/EVIDENCE.md) and
   [hash manifest](dev/double-negation/MANIFEST.json): an exhaustive source map,
   including the intentionally rejected universe-level experiment.
5. [Archive validation](dev/double-negation/VALIDATION.md): checks performed on
   the relocated evidence, separate from historical success reports.

## What was achieved, and what was not

| Route | Established result | Limit |
| --- | --- | --- |
| [Original internal classicality](dev/double-negation/ROUTES.md#original-formula-classicality-with-ordinary-satisfaction) | Formula satisfaction decisions reconstruct separation and powersets for the original HIT-V, conditional on its ordinary-satisfaction LEM | Does not construct a double-negation internal world |
| [Direct negative sets](dev/double-negation/ROUTES.md#direct-negative-set-interpretations) | Stable recursive equality, modal membership, extensionality, small separation, stable induction and negative foundation; quotient variant | Full separation, replacement and general powersets remain open |
| [Smallness and completion](dev/double-negation/ROUTES.md#pointwise-resizing-and-sheaf-completion) | Pointwise negative resizing; Boolean completion is equivalent to stable propositions; precise extraction requirements | Pointwise witnesses do not give a whole small classifier or witness family |
| [Power and function covers](dev/double-negation/ROUTES.md#powersets-predicate-covers-and-function-objects) | Coverage characterizations, finite instances, binary fullness equivalence, conditional diagonal obstructions | No general small cover constructed; conditional obstructions are not universal no-go theorems |
| [Replacement and separation](dev/double-negation/ROUTES.md#separation-replacement-and-small-supports) | Exact local representation/support conditions and supported image constructions | Required support families for arbitrary deep formulas not obtained |
| [Internal type theory candidate](dev/double-negation/ROUTES.md#relational-semantics-and-the-internal-type-theory-detour) | Relational proposition-universe isomorphism with Boolean; function rules and substitution, with levels exposed | Different LEM premise; no complete small dependent universe or bridge to the original goal |
| [L-specific route](dev/double-negation/ROUTES.md#constructibility-and-stage-bounds) | Uniform stage bound characterizes powersets under explicit background conditions; Hartogs size audit | A local alternative, not generic resizing; the common bound is unproved |
| [Deep first-order truth resizing](dev/double-negation/ROUTES.md#return-to-the-original-deep-first-order-premise) | Formula LEM yields an internal truth set and unique truth representatives for every deep formula; instantiated in modal trees | Does not yet provide sets of all internal functions or full ZF |
| [Semantic and proof-theoretic exclusions](dev/double-negation/ROUTES.md#semantic-and-proof-theoretic-boundaries) | Several exact obstructions for particular universes, interfaces or base theories | None covers every allowed Cubical Agda construction and interpretation |

The most recent candidate uses `0 = ∅`, `1 = {0}`, `Ω = {0,1}` and proves,
in the negative interpretation of the existing first-order syntax:

```text
∀p. p ∈ Ω ↔ p ⊆ 1
for each formula φ(x): ∀x. ∃p ∈ Ω. (0 ∈ p ↔ φ(x)).
```

Representatives are unique up to internal equality. This is a candidate
first-order truth-class resizing interface, not host `hProp` resizing and not
yet a replacement for every use of `Base.Impredicativity`.

## How to continue without changing the question

Keep the exact Formula-based premise and the same negative satisfaction
relation. Investigate the first-order replacement/collection and function-set
principles needed to consume the truth-set result. Track their proof
obligations explicitly instead of importing host function-space closure or
assuming that a relation-calculus theorem automatically applies to V.

Historical reports contain old restart suggestions, goal-state language and
claims scoped to earlier experiments. They are preserved as evidence, not as
instructions to resume a superseded route. The user explicitly corrected the
internal-type-theory detour; this entry and ROUTES.md record that correction.

This branch is a research archive. Its mathematical sources and reading catalog
follow the recorded main baseline; `src/README.md` receives only the table
caption required by the current commit gate. The older research chapters are preserved
under `dev/double-negation/legacy`, rather than added to Origin or presented
as newly accepted textbook results.
