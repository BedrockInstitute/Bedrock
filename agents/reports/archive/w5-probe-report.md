# W5p probe report: the Mostowski collapse over the HIT V, priced in miniature

**Verdict: GO.** The D-1 probe of `[L3.31-W5p]` builds the collapse's four
decisive pieces over the cubical cumulative hierarchy `V ℓ`: the set-valued
∈-recursor with its computation law, image transitivity, extensional
injectivity on a transitive carrier, and the iso reading, both directions.
All four typecheck, constructively, with no postulate, no hole, no LEM, no
impredicativity, and no consumer-side seal: 125 code lines (171 file lines,
31% of the 400-line stop-line), whole-file cold check under 1 s wall
(0.7 s user, `GHCRTS=-M8g`, one agda process at a time). The wall-potential
piece (piece 3) did not wall: the double induction is a single `∈-induction`
whose hypothesis is quantified over the other argument, and the R-27
predictor (1 induction × 2 truncation eliminations) matched the sub-second
check. The recursion-principle question the brief names is settled in the
probe's favour: `V.Hierarchy.∈-induction` carries a set-VALUED recursion
directly, no graph/fixpoint route needed; the tree's own `Lset` is the
standing precedent, and the probe re-instantiates that pattern with a
filtered small index.

Probe file: `src/ProbeCollapse.agda` (untracked, new; no master touched,
no git commit). Checked with `GHCRTS=-M8g agda src/ProbeCollapse.agda`,
one check at a time, from this worktree. Report: this file.

## 1. What the probe prices

For a fixed ambient set `u : V ℓ`, the collapse map is defined by
∈-recursion over the **filtered small index**

    Fiber x = Σ[ m ∈ ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ m ∈ₛ u ⟩
    step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (mem p))
    π = ∈-induction step

i.e. `π x` is the set of `π`-images of the members of `x` that lie in `u`,
indexed at the small-member level exactly as `LsetStep` indexes its union
(`L.Constructible`). The four pieces are:

1. **The recursor** (`π`, `π-compute`): set-valued through `∈-induction`
   with `P x = V ℓ`; computation law
   `π-compute : (x : S) → π x ≡ step x (λ y _ → π y)`, a propositional path
   in the h-set codomain, in the exact `Lset-compute` shape.
2. **Image transitivity** (`π-member`): every member of `π x` is the
   `π`-image of a member of `u ∩ x`; the range class is transitive. Notably
   `x ∈ u` is not even needed: the filter carries the `y ∈ u` witness.
3. **Extensional injectivity** (`π-inj`, in the `Inj` module over
   `uTrans : isTrans u`): `x, y ∈ u → π x ≡ π y → x ≡ y`, by `∈-induction`
   with the hypothesis quantified over the other argument; both inclusions
   go through `extensionality`, direction 1 firing the IH at the input
   member `z ∈ x`, direction 2 at the witness `b ∈ x` extracted from the
   collapsed membership.
4. **The iso reading** (`π∈-fwd`, `π∈-bwd`, `iso`):
   `y ∈ x ↔ π y ∈ π x` for `x, y ∈ u`, both directions. Forward needs only
   `y ∈ x` and `y ∈ u`; backward consumes `π-inj` and `uTrans`, as the
   classical proof does.

The whole miniature is assumption-free: the only hypothesis anywhere is the
`uTrans` parameter of the `Inj` module. No `LEM`, no `Impredicativity`,
no `SetChoice`, no `hPropSmallness`, no resizing appears in the import list.

## 2. Per-piece price table

Code lines exclude blanks and comments; timings are the whole-file cold
check (no single definition clears the profile granularity; `--profile=
definitions` reports everything under "Miscellaneous", 738 ms total).

| Piece | Probe lines | Cold time | What it is |
|---|---|---|---|
| shared (OPTIONS, imports, `isTrans`, module heads) | 17 | - | two structure/hierarchy imports, the transitivity predicate |
| **recursor** (`Fiber`, `step`, `π`, `π-compute`) | 14 | sub-second | the filtered small index, the `sett` step, `∈-induction` at `P x = V ℓ`, the computation law as an opaque-unfolding read lemma |
| **transitivity** (`π-member`) | 9 | sub-second | one `PT.map` over the classified membership; `∈ₛ`→`∈ˢ` on the witness |
| **iso forward** (`π∈-fwd`) | 13 | sub-second | `∈-asFiber` extraction, `subst` of `y ∈ u` to the index, one truncation witness |
| **extensional injectivity** (`P`, `in⊆`, `out⊆`, `step-inj`, `π-inj`) | 53 | sub-second | the double-induction shape: one `∈-induction`, two inclusion helpers, two `PT.rec` recoveries |
| **iso backward + iso** (`π∈-bwd`, `iso`) | 18 | sub-second | `π-inj` at the extracted witness, the pair of directions |
| **totals** | **125** | **< 1 s wall cold** | stop-line 400, used 31% |

Per-piece verdicts: GO / GO / GO / GO. The piece the recon flagged as the
real wall potential (piece 3, "nested inductions + hProp-valued
membership") is the largest block at 53 lines and checked instantly; the
two `PT.rec` recoveries are the only truncation eliminations in the file.

## 3. Which recursion principle carried the recursor

`V.Hierarchy.∈-induction` (`WellFoundedInduction.WFI.induction` over
`regularityV`), instantiated at `P x = V ℓ` with `ℓ' = ℓ-suc ℓ`. This is
exactly the set-valued instance the tree already banks at `Lset`
(`L.Constructible.LsetStep : (α : S) → (∀ β → β ∈ᵗ α → S) → S`); the probe
re-derives it with the `u`-filter inside the index. **No graph/fixpoint
route was needed**, and the HIT's own `ElimSet` was not the carrier: the
recursion runs on well-foundedness, not on the `seteq` constructor.

The computation law's shape: `π-compute : (x : S) → π x ≡ step x (λ y _ → π y)`
is a **propositional path** in the h-set `V ℓ` (the codomain's set-hood
makes this the honest law), delivered as an `opaque unfolding π` read lemma
and consumed exclusively through `subst` in the four pieces (R-36); no
consumer unfolds `π`. `π` itself is sealed `opaque`, mirroring `Lset`.

## 4. What the replacement-style set former costs

The step is `sett` over `Fiber x`, the replacement-style image
(`V.Model.replaceImage`'s `sett ⟪ a ⟫` pattern) with the `u`-filter inside
the index. The load-bearing finding: the filter uses the library's **small**
membership `∈ₛ` (`hProp ℓ`), the free smallness atom of `V.Smallness.small-∈`
(`src/V/Smallness.lagda.md`), so `Fiber x : Type ℓ` and **no resizing,
impredicativity, or LEM is spent anywhere**; `∈∈ₛ` bridges to the big
membership in the statements. The D-7 constructive-intersection question
never fires: the filter is membership-based, not a derived
difference-intersection. Cost: 14 lines including the recursion law.

## 5. Walls and formulation trail

**No wall.** No 180 s+ event, no heap event, no killed process, no
`TERMINATING` pragma, no hole. Two first-attempt formulation fixes
(recorded per the probe doctrine; neither consumed a second cure):

1. **Transport direction in `in⊆`'s final step.** Moving `by : ⟨ b ∈ y ⟩`
   along `z ≡ b` needs `sym z≡b` (`b ≡ z`), not `z≡b`; the first attempt
   expected `by` at `⟨ z ∈ y ⟩`. One `sym`, fixed.
2. **The IH fires at the witness, not the input, in direction 2.** For
   `y ⊆ x`, the `∈-induction` on `x` cannot supply a hypothesis at `z ∈ y`;
   the classical proof extracts `b ∈ x` from `π z ∈ π x` and fires the IH
   there. The first attempt (a symmetric `ih4y` over members of `y`) was
   untypeable against the IH's domain; restructuring into `in⊆`/`out⊆` over
   the same IH-on-x dissolved it. Second, `P`'s hypothesis order had to
   match `π-inj`'s declared order (`x ∈ u` before `y ∈ u`), which is what
   the declaration-driven unification checks.

Neither is a LESSONS-class wall (no conversion explosion, no truncation
storm, no meta search); both are statement-shape discipline of the I-4/I-5
family, applied first.

## 6. LESSONS carried

- **R-36 (opaque-unfolding read lemma)**: `π` sealed at birth; `π-compute`
  is the only read, consumed via `subst` everywhere.
- **R-35 (small indices)**: all constructions live at `⟪ x ⟫`; no
  union-representation extraction, no fiber extraction over `⟪ ⋃ x ⟫`.
- **R-37 (no transported memberships in statements)**: every lemma states
  memberships at variable arguments; transports happen inside proofs.
- **I-5 (written branch types)**: every `PT.rec`/`PT.map` branch and every
  `where` binding carries a written type.
- **I-4 (carrier-level combinators)**: the four pieces are carrier-level
  functions over explicit memberships; no implicit inverted through a
  content-of projection.
- **C-11 / R-34-class hygiene**: parameterized module bodies indented
  deeper than their headers; levels explicit through the telescope.
- **D-1, D-6, D-10, C-12**: probe doctrine, ×3 production factor (next
  section), target-truth check (§8), `GHCRTS=-M8g` with one process.

## 7. Shape multiplier and the D-6 x3-calibrated production band

The miniature fixes one ambient transitive set `u` and works over plain
`V`-membership. The wing's full collapse statement replaces `u` by a
transitive carrier set `X ⊆ Lset γ` (γ an ordinal), forms the range as a
set, and packages the four pieces into the Mostowski statement. The
recursion itself is unchanged (`u := X` instantiates `Collapse` verbatim);
the multiplier is entirely the L-tower integration that the miniature
deliberately did not touch.

| Probe item | Probe lines | Production multiplier | What the multiplier covers |
|---|---|---|---|
| recursor | 14 | 2-3.5× | same recursion at `u = X`; the range-set former `πX = sett ⟪ X ⟫ (λ m → π (⟪ X ⟫↪ m))`; the L-bounding companion induction "`π y ∈ Lset δ`" and the image-in-L step |
| transitivity | 9 | 2-3× | `π-member` restated for the range SET `πX`; `πX` transitive and `πX ⊆ Lset δ'` |
| extensional injectivity | 53 | 1.2-1.5× | proof shape identical; statements gain `X ⊆ Lset γ`, `IsOrd γ` context |
| iso reading | 31 | 1.2-1.5× | same, plus L-membership bounding on both sides |
| shared | 17 | 1-1.5× | L-tower imports and the carrier-set telescope |
| new: uniqueness + packaging | 0 | n/a | Mostowski uniqueness (two collapses agree, a second small induction), the isomorphism packaging |
| **totals** | **125** | **1.5-2.2×** | **≈190-280 probe-discipline lines** |

Applying the D-6 production factor (readers both directions, dispatch,
environment plumbing, at the measured ×3): the **collapse half of W5
prices at roughly 570-840 lines**, center ≈ 700. That brackets the recon's
300-600 collapse sub-band ([gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md:25),
[revival-recon.md](/Users/alsg/Agentic/Bedrock/_build/revival-recon.md:89))
from above: the recursion machinery the recon called "the only genuinely
new recursion machinery" is not the cost (the tree's `Lset` pattern carries
it; the probe re-proves it in 14 lines), but the L-tower statement
integration, the range-as-a-set with its image-in-L proof, and the
uniqueness half are real additions the recon's 300-600 did not itemize.
With the condensation half (350-650, priced separately by the wing plan),
the honest W5 band moves from 650-1,250 to roughly **900-1,500**, center
≈ 1.2k: the recon's band holds only at its top half. The D-6 caveat from
the G2p precedent applies: this probe already pays both-direction adequacy
and the full double induction, so the factor sits closer to 2.5-3 than to
the rule's nominal 3.

## 8. Is the target right? (D-10)

Yes. The probe does not question the classical mathematics (the literature
settles the Mostowski collapse); it prices only our departure, the cost of
the ∈-recursion-defined collapse over the cubical HIT hierarchy, and that
departure checked out green on all four decisive shapes, constructively and
assumption-free at the miniature scale. Three corrections the probe forces
onto the wing's shape:

1. **The recursor is not a new-machinery risk.** `∈-induction` at
   `P x = V ℓ` plus `∈-induction-compute` is the delivered `Lset` pattern;
   the wing should state the collapse by the same global ∈-recursion with
   the filter set to `X`, exactly the probe's `Collapse X` instantiation,
   and spend its estimate on the L-membership side, not on recursion.
2. **`uTrans` is the only hypothesis the collapse core needs, and it is
   consumed only by injectivity and the backward iso.** The recursor,
   transitivity, and forward iso are transitive-carrier-free; the wing
   telescope should carry `X`-transitivity into exactly those two pieces.
3. **The D-7 (constructive intersection) concern does not fire.** The
   `u`-filter is the small `∈ₛ` atom, a free smallness witness; no
   difference-derived intersection and no resizing enter the collapse.

## 9. What the miniature did NOT exercise

1. **The tower carrier `X ⊆ Lset γ`**: all L-membership, `IsOrd γ`,
   ordinal bookkeeping, and the statement that collapse values land in
   `Lset` stages were absent; the probe works over plain `V` with a fixed
   transitive `u`.
2. **The range as a set and its L-membership**: `πX = { π y | y ∈ X }`
   formed by the image former, `πX` transitive as a set statement, and
   `πX ∈ Lset δ` / the image-in-L step (the tower's union/sep kit at
   `Lset` level).
3. **L-bounding of `π` values**: the companion induction
   "`π y ∈ Lset δ`" along the recursion (R-36-style read lemmas at
   `Lset`-indexed memberships).
4. **Mostowski uniqueness** and the isomorphism packaging (the statement
   "`π : X → πX` is an isomorphism onto a transitive set").
5. **All condensation content** (π(x) ≤ x, image = Lset β, β ≤ γ): W5's
   second half, priced separately per the brief.
6. **Arbitrary extensional relations `⟨X, ∈⟩`**: the wing collapses
   `V`-membership substructures only (Devlin II.5 route); skipped per the
   brief, and the well-foundedness hypotheses are likewise unexercised
   (`V`'s own regularity supplies `∈-induction`).
7. **Truncation at `Lset`-scale statements**: the probe's indices are
   `⟪ x ⟫` for plain `V`-sets; the wing's memberships bind at
   `⟪ Lset γ ⟫`-level statements, where R-35 discipline is the standing
   watch.
