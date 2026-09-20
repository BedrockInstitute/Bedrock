# K10 canonical good tables and the atomic graph

K10 remains incomplete. This continuation starts from the 2026-09-15 GLM 5.3
pause and the [internal-rank checkpoint](k10-rank-2026-09.md). Proof sources
live in the isolated archive `k10-k11-resume-2026-09-18`.

## Canonical recurrence

`K10/CohenGoodProof.agda` proves that the canonical equality table on a
child-closed domain is good. The named check

```
GHCRTS='-A64m -I0 -M8g' agda K10/CohenGoodProof.agda
```

exited 0 on 2026-09-18, with no other Agda process running. The proof reuses
`CohenImageValue.ImageChar.Closed` for image totality, leastness and agreement,
and `CohenWeightMeet.weight-meet-promote` to lift raw entry meets to the
support weight. Lower bounds use Bell (1.16) in the form `≈ᴮ-lbˡ` / `≈ᴮ-lbʳ`;
greatestness uses `≈ᴮ-glb`. The object formula `goodΔ` does not mention host
atomic values.

## Arbitrary good tables

`K10/CohenCompare.agda` then identifies every good table on a closed domain
with those host atomic values. Pair recursion is on both orientations at once,
because a right lower bound reads equality at the swapped child pair. The
named check

```
GHCRTS='-A64m -I0 -M8g' agda K10/CohenCompare.agda
```

exited 0 on 2026-09-18. Two good tables, possibly on different closed domains,
therefore agree at every pair that belongs to both: each equals the same
atomic value. This is `eq-unique` / `mem-unique` at the end of that file.

## Closed pair domains and the graph

`K10/CohenDomain.agda` assembles a child-closed domain containing two names
from K3 hereditary families and K4 `closed-union` of their join. The canonical
table on that domain is a `ValueTable` whose readout is the atomic pair, and
it is `Adequate`. `TableSupply` follows by truncation. The named check

```
GHCRTS='-A64m -I0 -M8g' agda K10/CohenDomain.agda
```

exited 0 on 2026-09-18 and produces `atomicGraph = table→graph tc supply`.
The `goodAt` slot order is adapted from `(w,c,h)` to the AtomicGraph consumer
`(c,h,w)`.

## The compiler

`K10/CohenCompile.agda` applies `K5.InstanceValue.Compiler` to `atomicGraph`,
the name recogniser from `NameSpace.Instantiate` at the Cohen algebra, and
the Boolean atomic values. It exports `val` and the fourteen clause laws
(`InterpLaws`). The named check

```
GHCRTS='-A64m -I0 -M8g' agda K10/CohenCompile.agda
```

exited 0 on 2026-09-18 in 32.6 s, with no other Agda process running.

A first attempt to instantiate `CohenPreservation.Engine` with those laws,
and a second attempt that only imported `K6.TruthSeam` beside the compiler,
each exhausted the 8 GiB heap (exit 251). Those files were removed. Filling
the Engine telescope needs a narrow seam, of the same kind as
`CohenAgreementSeam`, that does not load the preservation engine and the
compiler in one module.

## Packaged endpoints

`K10/CohenValSeam.agda` opaques `val` and the fourteen laws so a consumer
does not unfold `K4.Compile`. Its named check exited 0. Instantiating
`CohenPreservation.Engine` with that seam still exhausted 8 GiB (exit 251);
that fill file was removed.

`K10/CohenPairUnion.agda` fills pairing and union at `M[G]` from
`K6.ElementaryAtNames` at the generic filter. Named check exited 0.

`K10/CohenZFC.agda` assembles `OrdinaryZFC` at `M[G]`: extensionality,
pairing, union, infinity and foundation are filled; Power, Separation,
Collection and Choice remain engine-conditional. Named check exited 0.

`K10/CohenTheorem.agda` packages the supplied-generic poset result:
`extension-ZFC`, `extension-not-CH`, `extension-not-GCHω`, the internal
κ-to-powerset injection, checked omega, and `checked-omega1` identifying
the extension successor of checked omega with the checked ground ω₁.
Named check exited 0.

`K10/CohenBooleanSubset.agda` exports `subsetVal`, the Boolean check
name of ω, and a check-name of the ground power set of ω. Named check
exited 0.

`K10/CohenNameIntro.agda` exports opaque `mkListing` and `mkName`, with
the name-intro body checked only against variables. Named check exited 0.

`K10/CohenBooleanPower.agda` builds the candidate-weighted code `powerB`
by `image` and does not call `name-intro`. Named check exited 0.

`K10/CohenBooleanNamed.agda` applies those opaque maps to `powerB` and
exports `powerNm : Nameᴮ` for the candidate image. Applying a
parameterized `FromListing` module to the same image did not return
under 8 GiB; the function application typechecks. Named check exited 0.

`K10/CohenBooleanPowerMem.agda` proves the Atomic upper bound:
`subsetVal(trᴮ σ) ⊓ (τ ≈ᴮ trᴮ σ) ≤ τ ∈ᴮ powerB` for each candidate σ.
Named check exited 0.

`K10/CohenBooleanNotCH.agda` erases the constant-free CH sentences,
proves `val(¬CH) ≡ ⊤ᴮ` from `val(CH) ≡ ⊥ᴮ`, and reduces the compiled
matrix at an arbitrary power-set name to three compiled parts
(`IsOmega`, `IsPowerSet`, and the inner injectability universal).
Named check exited 0.

`K10/CohenBooleanCHBot.agda` instantiates that reduction at
`Named.powerNm`. Unconditional `val(¬CHsent) ≡ ⊤ᴮ` remains the three
part hypotheses of `FromParts`. Named check exited 0.

`K10/CohenBooleanRename.agda` proves `val (renameFo ρ φ) ν ≡ val φ (renameEnv ρ ν)`
from the fourteen compiler laws. Named check exited 0.

`K10/CohenBooleanOmegaPart.agda` reduces the two-variable compiled
`IsOmega` conjunct to `val` of erased `IsOmegaφ` at `omegaNm ∷ []`.
Named check exited 0.

`K10/CohenBooleanCheckMem.agda` re-exports `check-∈-top`. Named check
exited 0.

`K10/CohenBooleanSubst.agda` instantiates Bell 1.17(vii) at the sealed
evaluator as `subst-head` / `subst₁`. Named check exited 0.

`K10/CohenBooleanDelta0.agda` instantiates the restricted check-Δ₀
theorem at `VS.val`. Applying that theorem to the concrete inductive
formula exhausted 8 GiB. Named check of the unapplied instance exited 0.

`K10/CohenBooleanInductive.agda` proves the empty-set conjunct of
compiled `IsInductiveφ` at `check(w)` by the compiler laws and
`check-∈-top`. Named check exited 0.

`K10/CohenCorrespondence.agda` re-exports poset/Boolean equality and
membership agreement together with the sealed evaluator. Named check exited 0.

`K11/Corollary.agda` exports `from-enumerations`, `from-carrier`, and
`from-carrier-truncated` with telescopes distinct from the supplied-generic
theorem. Named check exited 0.

## Remaining K10 and K11 work

`CohenPreservation.Engine` cannot be applied under the 8 GiB cap in the
same module as the compiler. The four schema fields of `extension-ZFC`
therefore remain K6 parameters. Sentence-level Boolean
`val(¬CHsent) ≡ ⊤ᴮ` remains open on the three compiled parts at
`Named.powerNm`: `IsOmega`, `IsPowerSet`, and the inner injectability
universal.

No production source, landmark, commit or push is changed.
