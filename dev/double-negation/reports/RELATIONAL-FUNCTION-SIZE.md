# Relational function rules and the remaining size obligation

Date: 2026-09-28. Continuation of `RELATIONAL-PROP-UNIVERSE.md`.
This is isolated research, not a production migration or a completion claim.

## A constructed function object, with its level exposed

`RelationalLargeFunctions.agda` supplies products of relational objects and,
for `A B : Object ℓ ℓ`, constructs

```text
Functions A B : Object (suc ℓ) ℓ
Carrier (Functions A B) = Map A B ℓ
Equal (Functions A B) F G = MapEq F G.
```

Map equality is stable and proposition-valued. Evaluation has graph
`evaluate (F,x) y = graph F x y`, still at level ℓ. For contexts whose
carrier and equality are at level ℓ, every level-ℓ map
`F : Γ × A → B` has a level-ℓ relational abstraction
`curry F : Γ → Functions A B`. Its graph says that the corresponding row
of F agrees with the named map. It has actual row witnesses for modal totality;
no choice or external classical principle is used.

Uncurrying is defined for maps into Functions at any graph level s:

```text
uncurry K (γ,x) y = ¬¬ Σ R : Map A B ℓ, K(γ,R) × R(x,y).
```

The graph is at `max (suc ℓ) s`, because the quantified map carrier is large.
The file checks totality, single-valuedness, invariance, and stability, and:

* beta: `uncurry (curry F)` is graph-equivalent to F;
* uniqueness: if `uncurry K` is graph-equivalent to a level-ℓ F, then K is
  graph-equivalent to `curry F`, even when K has a higher-level graph;
* substitution: `curry F ∘ σ` agrees with `curry (F ∘ (σ × id))` for
  level-ℓ substitutions between level-ℓ contexts.

The uniqueness statement is the precise checked eta property. It does not
assert that an arbitrary higher-level uncurried graph already has a level-ℓ
representative. Consequently this is a representation theorem for level-ℓ
maps, not an unrestricted exponential for the union of every graph universe.

In particular the constructed function object Nat → Boolean has its carrier
in Type₁ and its equality in Type₀. The construction does not provide a carrier
in Type₀. This is a size accounting result, not proof that every alternative
small presentation is impossible.

## Raising isomorphism graphs alone does not remove the existing obstruction

`RelationalSmallFunctionAudit.agda` strengthens the previous boundary result.
Suppose E has a Type₀ carrier, with equality at ANY level e. Suppose it has:

1. an isomorphism to `Functions Natural Boolean`, with forward and backward
   graphs at ANY levels r and s;
2. a level-zero evaluation map `E × Natural → Boolean`;
3. evaluation compatibility: whenever the forward graph relates i to F,
   the evaluation row at i is graph-equivalent to F.

Then E's evaluation rows construct a `SmallHomPresentation`. The proof uses
the forward/backward round-trip law at each F to obtain, under double negation,
an i related to F. It does not select a representative map for every i.

The previous diagonal theorem therefore proves that the carrier of E cannot
be subcountable. `ModalAllSmallSubcountable` rules out these three conditions
together. The strengthening is that neither internal equality nor either
isomorphism graph is required to be level zero. Only the carrier and the
evaluation graph have that requirement.

This is still conditional. Modal subcountability has not been proved for the
full permitted Agda foundation. Furthermore this theorem does not rule out
representations whose evaluation graph itself lives at a higher level. Such
a proposal would need to explain internal smallness, comprehension, dependent
closure, and how its evaluation predicates support the eventual set model;
one cannot simply treat the higher graph as a host-small proposition.

## Consequence for the original migration

The earlier relational proposition-universe isomorphism to Boolean remains a
positive checked result. This round shows that function abstraction and its
compatibility with substitution are constructible too. What has NOT been
supplied is a universe closed under these function objects while preserving
the chosen notion of smallness.

This matters at the concrete consumer: `V.Model` indexes a powerset by
`presentation a → Ω`. Replacing Ω by an internally equivalent Boolean object
still requires a sufficiently small object of ALL interpreted functions from
that index. The newly constructed Functions object has the right checked
level-ℓ function behavior but currently a higher-level carrier.

The next open candidate is therefore a small presentation that permits higher
evaluation graphs, together with a coherent definition of internal smallness
and comprehension. It must actually construct that presentation, not assume
it as a stable classifier or fullness parameter. No global impossibility or
full internal ZF model has been established.

## Validation

Both new files passed the repository compiler with exit code 0, no warnings,
and `--cubical --safe --guardedness`. Commands ran sequentially from this
research directory:

```sh
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda RelationalLargeFunctions.agda
AGDA_DIR=/Users/alsg/Agentic/Bedrock/_build/agda-home GHCRTS='-A64m -I0 -M8g' /Users/alsg/Agentic/Bedrock/_build/outcrop-agda/bin/outcrop-agda RelationalSmallFunctionAudit.agda
```

The process inventory found no existing Agda process before the first check.
Intermediate development errors were a name collision with HLevels.extend,
context parameters fixed too early in an anonymous module, and unresolved
implicit row context arguments. These were fixed by renaming, moving the
substitution proof to its own module, and explicit context arguments. One
invocation from the repository root failed module-name lookup; final checks
ran in this directory with its library registry. No holes, postulates, or
resizing assumptions were introduced to repair any of these errors.

`git diff --exit-code -- src` exited 0. Main and the pre-existing untracked
`dev/DOUBLE-NEGATION.md` are unchanged. All new files are ignored research
artifacts. No full-book, browser, or website checks were run.
