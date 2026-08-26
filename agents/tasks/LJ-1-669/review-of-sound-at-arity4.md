# Review of `sound-at-arity4`

**Verdict: NO-GO.** The obligation cannot be built. A Σ₁ transfer that
avoids `mapΔ₀` exists at the class carrier and is green in the probe.
A HoodSound-shaped lemma at arity 4, taking the chapter's `Δ₀-matrix`,
whose transfer runs at the Σ₁ statement and not through `mapΔ₀`, is
stopped by two walls. Each wall is measured.

## What the obligation needs

`[LJ-1.661]` named the shape
(agents/tasks/LJ-1-661/lj-1.661-report.md:124-129): a soundness lemma
that speaks at arity 4 with `K` in the environment, takes the chapter's
`Δ₀-matrix` (src/L/BoundedSubset.lagda.md:851-852), and whose transfer
runs at the Σ₁ statement, not through `mapΔ₀`. The sound half of the
hood is `[LJ-1.658]`'s `HoodSoundP` (agents/tasks/LJ-1-658/Probe658.agda:226-230):
from a collapse-image reading, conclude `v ≡ Lset γ`. The 658 chain is
four legs (`Probe658.agda:247-270`):

    inner πX  --abs₀+mapΔ₀-->  ambient πX  --⊨-map-->  ambient L
              --abs₀+mapΔ₀-->  inner L     --Lset-only-->  v ≡ Lset γ

The obligation is that chain at the chapter's matrix, with `abs₀+mapΔ₀`
replaced by Σ₁ transfer.

## Wall (i): direction

`σ₁-up` has type
`(δ : SM ^ n) → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ map fst δ ⊨ᵛ φ ⟩`
(src/FOL/Absoluteness.lagda.md:182-183). Inner to ambient.

658's last leg is the opposite arrow (`Probe658.agda:269-270`):
`inner = subst ⟨_⟩ (sym (AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) γL)) amb-L`.

At the class carrier the reverse typechecks, and it avoids `mapΔ₀`,
and it is not Σ₁. It is `π₁-down (π-Δ₀ Δ₀-matrix)`
(`Probe669.agda:134-138`, src/FOL/Absoluteness.lagda.md:187-190).

The ascription of `σ₁-up` to the reverse type is red:
`runs/wall.out`, exit 42, `[UnequalTerms]` at `Wall669.agda:57.16-36`.
Inferred type: inner to ambient. Expected type: ambient to inner.

So a transfer that is at Σ₁ cannot run the last leg. The last leg is Π₁.

## Wall (ii): constant domain

`σ₁-up` at a carrier `M` consumes `Σ₁ φ` for `φ : Formula SM n`
(src/FOL/Absoluteness.lagda.md:182). The chapter's `Σ₁-matrix` is
`Σ₁ matrix` for `matrix : Formula CS.S 4` (`Probe669.agda:78-93`).
`CS.S` is the class carrier (`𝒮ʟ = 𝒮ᵥ ↾ isL`,
src/L/Constructible.lagda.md:420-421). A collapse image is
`Σ[ x ∈ S ] ⟨ x ∈ˢ P ⟩`. Those are different constant domains.

The ascription of `Σ₁-matrix` to `σ₁-up` at a dummy image (the empty
set, transitivity delivered as `∅-trans`,
src/L/Constructible.lagda.md:89) is red: `runs/wall-ii.out`, exit 42,
`[UnequalLevel]` at `Wall669-ii.agda:48.17-23`. The checker asked for
`Formula Abs∅.SM 4` and was given `matrix`.

The only delivered construction that places a class-carrier Σ₁
certificate at an image is `[LJ-1.161]`'s
`Abs.σ₁-up (mapΣ₁ Empty.rec* (erase-Σ₁ φ p s))`
(agents/tasks/LJ-1-161/ProbeLJ1161A.agda:83-86). `mapΣₙ` is `mapΔ₀` at
the leaf (src/FOL/Manipulation/Relabelling.lagda.md:234). So the first
leg of a HoodSound-shaped chain is through `mapΔ₀`.

## What the NO-GO establishes

The class-carrier half of W3 is GO: `transfer-at-arity4`
(`Probe669.agda:117-121`) is Σ₁ transfer at arity 4, `K` free, no
`mapΔ₀`, green at 3.26 s (`runs/floor-0.out`). That term is not the
obligation. The obligation is the sound half of the hood. Closing
`HoodSoundP` on this route is not an instantiation of
`transfer-at-arity4`. It requires a certificate at the image (wall ii)
and an ambient-to-inner arrow (wall i). Neither is a Σ₁ transfer that
avoids `mapΔ₀`.

Fork (b), the ambient form of `Lset-only`, is out of this price:
`dev/ARCHIVE.md:285` measures its old cost at 138.2 s of a 150.2 s
chapter profile, 92 percent. This dispatch does not trigger that route.

Premise 4 held. The zero-count of the matrix is `refl`
(`Probe669.agda:87-88`). No route here demanded `erase LsetGraph`.

## Site count (the C-42 sweep)

The false shape is "a HoodSound-shaped lemma at arity 4 whose transfer
is at Σ₁ and free of `mapΔ₀`". The demand occurs in one site: this
obligation. The delivered `soundP-from-pix`
(agents/tasks/LJ-1-658/Probe658.agda:237-259) is arity 2 and uses
`mapΔ₀`. The sibling `HoodExistsP`
(agents/tasks/LJ-1-653/Probe653.agda:283-288) takes no Δ₀ input and is
the existential half. Count: 1.
