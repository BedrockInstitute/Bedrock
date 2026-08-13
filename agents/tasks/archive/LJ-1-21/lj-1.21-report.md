# LJ-1.21 report: the carrier-level descent for the level size

## 1. THE VERDICT

DELIVERED: the descent, the limit half, and the assembly, all GREEN in one
master. The master is `src/L/StageCardinal.lagda.md`. It checks at 42.03
seconds cold for 484 in-fence lines. The whole-file rate is 0.087 seconds
per line. The new content is 310 in-fence lines. No new master was created.

The upper half `⟪ Lset α ⟫ ↪ ⟪ α ⟫` is delivered at every infinite ordinal
α, conditional on one priced piece: the finite-stage injections into ω. The
successor half needs neither `fin-inj` nor `Init`. `Init` is never used. The
archive's 52-line anchor holds.

## 2. WHICH α YOUR DELIVERY COVERS

The successor step covers every infinite ordinal α. Its hypotheses are only
`IsOrd α` and `infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥`. Both hold at ω. `Init ω`'s
uninhabitedness never enters. The step gives
`⟪ Lset (sucV α) ⟫ ↪ ⟪ α ⟫`. The composition gives
`⟪ Lset (sucV α) ⟫ ↪ ⟪ sucV α ⟫`.

The limit half covers every infinite ordinal α. It takes a branch injection
at every member stage. One step serves successor and limit ordinals.

The assembly covers every infinite ordinal α by ∈-induction. It takes
`fin-inj`, the finite-stage injections
`(δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫`.

The chain's α is any infinite ordinal below κ (5.5) and κ⁺ (5.6). These
include ω and every limit ordinal. The delivery reaches them after
`fin-inj`. `fin-inj` is priced at 50 to 100 lines in section 9.

The `Init` restriction is a formalization artefact of the archived
SquareLaw. It is not a real gap. The module parameter `sq` removes it from
the descent. The square law at every infinite α remains the standing module
parameter. LJ-1.6 priced it separately.

## 3. WHAT `StageCardinal` ALREADY LEFT

`Bound` delivered the counting bound. It injects `Formula K 1` into
`⟪ β ⟫` at an infinite ordinal β. It takes an injection `K ↪ ⟪ β ⟫` and the
square law at β.

`Lower` and `stage-card-lower` delivered the lower half. They inject
`⟪ α ⟫` into `⟪ Lset α ⟫` at every ordinal α.

The module parameter `sq` supplies the square law at every infinite set.
The remaining obligation was the upper half. It had three parts: the
descent, the limit half, and the assembly.

## 4. THE NUMBER

`src/L/StageCardinal.lagda.md`: 484 in-fence lines, ledger caliber. The
delivered file had 174. The new content is 310 in-fence lines.

Blocks, in-fence non-blank lines:

| block | lines |
|---|---:|
| header imports | 8 |
| descent: `OrdSWO`, `Successor`, `op-step`, `successor-step`, `SucUpper`, `stage-card-suc` | 133 |
| limit half: `LimitStep`, `limit-step` | 115 |
| assembly: `Upper` | 54 |

The successor mechanism (`Successor` plus `op-step` plus `successor-step`)
is 65 lines with comments, 61 without. The archive anchored 52. The
difference is the explicit `infα` parameter and the longer signature.

No new master was created under `src/L/`.

Definition sites, `src/L/StageCardinal.lagda.md`:

| definition | line |
|---|---:|
| `OrdSWO` | 223 |
| `Successor` | 270 |
| `successor-step` | 325 |
| `SucUpper` | 335 |
| `stage-card-suc` | 358 |
| `LimitStep` | 373 |
| `limit-step` | 489 |
| `Upper` | 501 |
| `stage-card-upper` | 562 |

## 5. SECONDS AND RATE

All measurements are cold. The module's own interface was stashed. The
dependencies were warm. One Agda process ran with
`GHCRTS="-A64m -I0 -M8g"`.

| milestone | seconds | lines | rate |
|---|---:|---:|---:|
| delivered file | 2.42 | 174 | 0.014 |
| after the descent | 10.37 | 304 | 0.034 |
| after the limit half | 41.41 | 423 | 0.098 |
| final | 42.03 | 484 | 0.087 |

Marginal rates:

| block | seconds | lines | rate |
|---|---:|---:|---:|
| descent | 7.95 | 130 | 0.061 |
| limit half | 31.0 | 115 | 0.270 |
| assembly | about 0.6 | 54 | about 0.011 |

WHY THE ARCHIVED DESCENT RAN AT 0.246. The archive attributed the whole
probe's 12.8 seconds to the 52-line mechanism. The mechanism itself is
parameterized content. At a variable carrier, nothing unfolds. My successor
mechanism runs at 0.061 seconds per line. That is far below the band.

The limit half lands at 0.270 seconds per line. That is inside P-n's band.
The mechanism is not P-n's instantiation. The profile shows the hot
definitions. Their statements mention the transparent `DefOf.defSet
(Lset ...)`.

The profile (`agda --profile=definitions`, total 40.6 seconds):

| definition | seconds |
|---|---:|
| `LimitStep.defset-stable` | 6.2 |
| `LimitStep.defset-stable-δ` | 5.5 |
| `LimitStep` `mk` | 5.3 |
| `LimitStep` `eq-defset` | 5.3 |
| `Successor` `go₂` | 4.5 |

That is the R-38 class: a transparent imported operation in statement
position. `defSet` is a `sett`, delivered transparent by `Definability`.
The cost is not satisfaction at a concrete carrier.

The re-derivation does not avoid the band for the limit half. It locates
the mechanism. R-38's seal at the `defSet` birth site is priced, not
applied. See section 9.

## 6. WHAT THE J TOWER SUPPLIES (DD4)

The L-specific ingredients are `Lset`, `𝒟ₒ`, `𝒟ₒ-inv`, `Lset-suc`, and
`Lset-out`. `𝒟ₒ-inv` is the step operator's membership characterization.
`Lset-suc` is the successor identity. `Lset-out` is the union membership.

The shared ingredients are the count, the well-order, the least-of, the
J-stability pattern, and the assembly shape. `OrdSWO` needs only
`ord-tri`, `mem-ord`, `regularityV`, and `∈-irrefl`. No stage appears in
its types. The J tower can instantiate it unchanged.

The J tower supplies its own step operator, its own membership
characterization, and its own successor identity. It inherits the count,
the well-order, the least-of, and the assembly shape.

The modules are parameterized (P-h). The statements are about variable
carriers (P-l). Nothing states object-language formulas at a concrete
carrier.

## 7. LITERATURE USED

`dev/literature/devlin-II5.md` sections 1.4 and 1.5. They record 5.4's
counting and the 5.5 to 5.6 chain. The chain consumes the level size at the
carrier. It uses the upper half at α and the lower half at γ.

`_build/literature/dev2.txt:1357-1360`. This is 5.4's proof. It is one
line: the language has max(|X|, ω) many formulas.

`_build/literature/dev2.txt:1369-1388`. This is 5.5 and 5.6. 5.5 picks α
with ω ≤ α < κ. 5.6 applies at κ⁺.

WHAT DEVLIN ASSUMES AT LIMITS. Devlin does not prove ordinal arithmetic.
1.1(vii) is stated for all α. Its limit case assumes the union bound:
|λ| many sets, each of size at most |λ|, union to size at most |λ|. In this
tree that assumption surfaces as three pieces. The square law at α is the
module parameter `sq`. The finite-stage injections at ω are `fin-inj`. The
branch injections come from the ∈-induction hypothesis. The `Init`
restriction is a formalization artefact, not a real gap.

WHY NOT. `jech13.txt` was skipped. The digest records the chain's shape in
full. Devlin is the primary source. `devlin-errata.md` was skipped. Its
Chapter II list does not reach II.5.

## 8. ARCHIVE USED

`_build/l3.32-t85-report.md:108`. This is the 52-line anchor. It holds.
My successor mechanism is 61 non-comment lines.

`_build/l3.32-t85-report.md:245`. This is the limit half's 150-to-220
price. It is refined. The count instantiation and the least-of assembly are
delivered. The J-stability lemmas replace the feared transport wall. The
wall's 80-to-150 lines became about 20. The delivered limit half is 115
lines. The ω instance adds `fin-inj`. The archive's price excluded ω,
because its `Init` requires `ω ∈ α`.

`archive/dev/TASKS-archived.md:120`. This is the T85 row.

`_build/lj-1.6-review.md`. Sections 2.2 to 2.6 and 4 were read. The
least-value route is the right cure. The review's qualification holds: the
probe does not compile against today's tree. Its imports
`L.CardinalCount`, `L.Ordinal.SquareLaw`, and `L.Ordinal.Pairing` are
archived.

`_build/lj-1.6-report.md`. This is the refusal. Its Init-based prices are
superseded.

`src/ProbeTowerInd2.agda:99-159`. This is the green cure. It was
re-derived, not copied. `Bound`'s infinite witness is now `β ∉ ω`. The
pairing comes from `sq α infα`. `Init` was dropped.

`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:78-109`. This is the
`ordSWO` re-derivation source. The current tree's `ord-tri` returns a
nested sum. The case analysis differs.

`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:918-963`. This records
the `Init` definition and its non-initial gap. The gap does not bind here.
`sq` is a module parameter.

`dev/LESSONS.md`. P-h, P-l, P-m, P-n, R-35, R-38, R-40, I-5, and D-10 were
read.

## 9. WHAT I AM NOT SURE OF

`fin-inj`'s exact price. It is 50 to 100 lines by estimate. The base exists:
`Choice/Finite` delivers a `Tally (Lset σ)` at numerals. The extraction is
the least index over the tally, then `Fin → ℕ`, then the numeral injection.
The import cost of `Choice/Finite` is unmeasured. P-l forbids transferring
it by analogy. Measure it when funded.

R-38's seal at the `defSet` birth site. It is priced, not applied.
`Definability` is a delivered master. Sealing it risks its own
re-measurement. The limit half's 0.270 rate may drop under the seal.

The consumer check. `src/Everything.lagda.md` imports `L.StageCardinal`.
It is the orchestrator's wiring step. The tree holds the sibling's
in-flight `src/L/Ordinal/StageArith.lagda.md`. A whole-tree check is not
stable today. My file adds names only. No export was removed.

The assembly's rate. It is about 0.011 seconds per line. The measurement
sits in the noise band. Re-measure it on a quiet machine.
