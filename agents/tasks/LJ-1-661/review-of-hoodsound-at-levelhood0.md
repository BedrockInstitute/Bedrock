# Review of `hoodsound-at-levelhood0`

**Verdict: NO-GO.** The obligation cannot be built. The delivered leg 2
instantiates at the level-hood pin, and the pin's `Δ₀` input has no inhabitant.
The mismatch between the level-hood shape and the leg 2's slots is a fact about
the chapter's own residue, stated here for the first time.

## What the obligation needs

`soundP-leg2-from-pix` (agents/tasks/LJ-1-658/Probe658.agda:317-325) is generic
in one pin `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2` and takes two inputs at it:

- `Δ₀ φ₀`, the Δ₀ certificate;
- `LsetOnlyAt φ₀`, the class-carrier supplier.

The obligation `hoodsound-at-levelhood0` is one term at one pin with both
inputs supplied. There is no pin with both inputs inhabited. The two candidate
pins are stated below; each fails at a different input.

## Site A: the pin the supplier covers

The only delivered supplier for the `LsetOnlyAt φ₀` hole is `Lset-only`
(src/L/Hierarchy.lagda.md:334-335). Its premise is the satisfaction of
`LsetGraphAt w b`, read at `w = zero`, `b = suc zero` (agents/tasks/LJ-1-658/
Probe658.agda:219-224). So the supplier covers exactly one pin:

    φ₀ = Cnt.erase LsetGraph p

At this pin the obligation fails twice — in statement and in type — one
after the other:

- **The pin term is unstateable (measured).** Its erasure needs
  `p : countFo LsetGraph ≡ 0`, and the count does not compute: `LsetGraph`
  unfolds to its body, but the count recursion is stuck on the opaque core
  `satGraphAt` (src/L/Coding/Graph.lagda.md:203-205), whose official
  unfoldings are the readers `graphAt-in` / `graphAt-out`, not a rewrite
  (src/L/Coding/Graph.lagda.md:207-216). `refl` fails; the failure is
  measured in runs/floor-1.out (`[UnequalTerms]`, `suc (suc …)` against
  `zero`). The tree has no zero-count lemma for this formula; its only
  successful zero-count proofs are for the chapter's normal-form matrix
  (agents/tasks/LJ-1-651/Probe651.agda:73-74, 115-116). The campaign
  measured the grade before, too: 2,287 unbounded `∃̇` and 2,159 unbounded
  `∀̇` in the expansion (agents/tasks/LJ-1-646/lj-1.646-report.md:82).
- **Even assuming `p`, the Δ₀ input is uninhabited (structural).**
  - `LsetGraph = LsetGraphAt zero (suc zero)`
    (src/L/Coding/Sequence.lagda.md:353-354);
  - `LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
    (src/L/Coding/Sequence.lagda.md:291-292, transparent): the leading
    constructor is the unbounded `∃̇` that quantifies over the approximating
    set; runs/floor-1.out shows the count unfolding to exactly that body.
  - `Δ₀` is inductive with one constructor per allowed shape, and the
    unbounded `∃̇` and `∀̇` have none (src/FOL/LevyHierarchy.lagda.md:47-57:
    the ten constructors are δ-∈, δ-≐, δ-∧, δ-∨, δ-⇒, δ-¬, δ-⊤, δ-⊥, δ-∀∈,
    δ-∃∈);
  - erasure preserves the shape, `erase (∃̇ φ) p = ∃̇ erase φ p`
    (src/FOL/Count.lagda.md:607).

So `Δ₀ (Cnt.erase LsetGraph p)` has a leading `∃̇` and matches no case of
`data Δ₀`, and the term that would carry it cannot even be written. Both
holes live in Wall661.agda.txt (run: runs/wall.out, the two
`[UnsolvedInteractionMetas]`). The chapter itself grades the level-hood
statement Σ₁: its section 1 is titled "THE SIGMA-1 LEVEL-HOOD AT THE CLASS
CARRIER" (src/L/BoundedSubset.lagda.md:66).

## Site B: the chapter's own bounded shape

`LevelHood0` (src/L/BoundedSubset.lagda.md:840-859) exports the bounded matrix
at arity 4, env `w ∷ v ∷ γ ∷ K`, slot zero unused, `v` the value, `γ` the
ordinal index, `K` the one free bound (src/L/BoundedSubset.lagda.md:69-71,
847-849), certified Δ₀ (`Δ₀-matrix`, src/L/BoundedSubset.lagda.md:851-852).
Its unbounded projection is the chapter's own `Σ₂ : Formula CS.S 1`
(src/L/BoundedSubset.lagda.md:855-856), certified Σ₁ by the chapter itself
(`Σ₁-Σ₂ = σ-∃ (σ-∃ (σ-Δ₀ (δ-∃∈ Δ₀-matrix)))`,
src/L/BoundedSubset.lagda.md:858-859). The leg 2's arity-2 hole cannot hold
this shape:

1. Arity. The delivered leg 2 demands `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2`.
   The chapter exports arity 4 (the matrix) and arity 1 (`Σ₂`, `reverse`).
   It exports no arity-2 formula. Probe661 PART 2 builds the arity-2
   reading itself (`step3 = ∃̇ (renameFo rot (∃̇ LH0.matrix))`, value slot 0,
   ordinal slot 1) to show that the reading exists at the supplier's
   convention — and that it is Σ₁, not Δ₀.
2. Grade. Any arity-2 reading of the statement closes its value slot by an
   unbounded `∃̇` and is Σ₁ (the chapter's own certificate above), while the
   leg 2's input is `Δ₀ φ₀`; no constructor of `Δ₀` matches `∃̇`
   (src/FOL/LevyHierarchy.lagda.md:47-57). Probe661 grades the arity-3
   reading green (`Σ₁-step1 = σ-∃ (σ-Δ₀ Δ₀-matrix)`); the arity-2
   certificate is stated but not built, because the tree has no
   rename-preservation lemma for `Σ₁` (the search of
   src/FOL/Manipulation/*.lagda.md came up empty).
3. Slots. The `LsetOnlyAt` convention is value at slot zero, ordinal at slot
   one, and no slot for a bound (agents/tasks/LJ-1-658/Probe658.agda:219-224;
   src/L/Hierarchy.lagda.md:334-335). The chapter's matrix carries the bound
   `K` as a free variable, and its machinery shares that bound
   (src/L/BoundedSubset.lagda.md:69-71). `Lset-only` has no reading at which
   it speaks of a formula with a free bound.

## What the NO-GO establishes

The last dispatch of the [LJ-1.658] route cannot fire. Closing `levelIn` on
this route is not an instantiation. It requires a soundness lemma reshaped to
the statement's own shape: one that speaks at arity 4 with `K` in the
environment and takes the chapter's `Δ₀-matrix` certificate
(src/L/BoundedSubset.lagda.md:851-852), and whose transfer steps run at the
Σ₁ statement rather than through `mapΔ₀`. That is the chapter's own named
residue, "the level-hood instantiation at the hull"
(src/L/BoundedSubset.lagda.md:901-904), and it is priced, not zero-cost.

Fork (b), the ambient form of `Lset-only`, is out of this price:
dev/ARCHIVE.md:285 measures its old cost at 138.2 s of a 150.2 s chapter
profile, 92 percent.

## Site count (the C-42 sweep)

The false shape is "a demanded `Δ₀` certificate at a level-hood pin". The
demand occurs in one site: this obligation, the leg-2 input
(agents/tasks/LJ-1-658/Probe658.agda:317-325). The sibling half of the same
route, `HoodExistsP` (agents/tasks/LJ-1-653/Probe653.agda:285-288), takes no
Δ₀ input. Count: 1.
