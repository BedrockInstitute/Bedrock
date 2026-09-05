# LJ-1.16 report: the criterion at hull parameters, refused

## 1. THE VERDICT

Refused with all three prices. No shape delivers the criterion at hull
parameters. The recorded residue depends on the internal order formula at
the carrier. That formula is not expressible over X-parameters. The archive
prices it at 1.0 to 2.7 thousand lines. The block re-prices [LJ-1.5]. No
source file changed. No commit was made.

## 2. THE THREE PRICES

These prices were written before any build. Each price names its basis. All
three shapes price above 430 lines, or fail to close the criterion.

### 2.1 Shape 1: full substitution. 200 to 350 lines. It does not pay.

A general substitution operator replaces variables by terms. The criterion
needs hull constants replaced by X-definitions. A hull member's definition is
a formula, not a term. The syntax has no function symbols. Full substitution
cannot express the replacement. A delivered operator leaves the criterion
unclosed.

Basis: the parameterized class. Renaming is 67 in-fence lines.
`FOL.Manipulation.Parameters` is 175 lines and checks at 0.0054 seconds per
line. A substitution operator is a similar structural recursion. The class
stays parameterized at 0.005 to 0.01 seconds per line.

### 2.2 Shape 2: constants-only substitution. 100 to 160 lines. It does not pay.

The operator bakes an environment into constants. It is the inverse of the
deconstantification in `FOL.Manipulation.Parameters`. `placeFo` and `⊨-place`
deliver the constants-to-variables face
(`src/FOL/Manipulation/Parameters.lagda.md:226`, `:362`). The inverse is a mirror
recursion plus a twelve-clause correctness proof. The n-ary assembly at the
hull adds the baking and the relabelling
(`src/L/Hull.lagda.md:73-217`). The class is parameterized.

The shape is a component. The bridge still needs the leastness encoding. The
encoding needs the order as an inner formula over X-constants. The order is
not X-expressible. The criterion stays unclosed.

### 2.3 Shape 3: the leastness-encoding route. Blocked. It does not pay.

The route reduces hull parameters to X-parameters. The reduction needs the
leastness formula. The leastness formula needs the order as an inner formula
over X-constants. The order data are not members of X. The order element
`relL α` has rank α+1. The carrier `Lset α` holds sets of rank below α. So
the order element is not in the carrier. The packaged formula cannot be an
X-formula. `hull-closed`'s conclusion needs an X-formula index
(`src/L/Hull.lagda.md:293-297,350-360`). So the criterion cannot close.

The archive records the same wall. T44 names three gaps
(`_build/l3.32-t44-report.md:165-180`). T48 prices the general-level order
formula at 1.0 to 2.7 thousand naive lines
(`_build/l3.32-t48-report.md:237-238`). The class is satisfaction at a
concrete carrier, P-n's floor. The rate is 0.22 to 0.297 seconds per line.
At 1.0 to 3.0 thousand lines, the check runs 220 to 890 seconds. The DD24
bar is 0.013193 seconds per line. The shape blows the bar by 17 to 23 times.

## 3. THE STATEMENT

The consumer needs the Tarski-Vaught criterion at the carrier Hull. It is
the `TarskiVaught` type at `M := Hull` in `AtM`
(`src/L/Hull.lagda.md:88-93`):

```agda
TarskiVaught-Hull : (n : ℕ) (φ : Formula HullSM (suc n)) (δ : HullSM ^ n)
  → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ φ)) ⟩
  → ∥ Σ[ q ∈ HullSM ] ⟨ (inL q ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL φ) ⟩ ∥₁
```

Here `HullSM` is `Σ[ x ∈ S ] ⟨ x ∈ˢ Hull ⟩` and `inL` moves a hull member
into the stage. The one-ary form over the hull's own code set is
`hull-closed` at `⟪ Hull ⟫`:

```agda
hull-closed-Hull : (φ : Formula ⟪ Hull ⟫ 1) → ⟨ [] SmallH.⊨ᵐ (∃̇ φ) ⟩
  → ∥ Σ[ a ∈ SL ] (⟨ fst a ∈ˢ Hull ⟩ × ⟨ (a ∷ []) SmallH.⊨ᵐ φ ⟩) ∥₁
```

The D-10 truth check corrected the target. The recorded target needs the
internal order formula at the carrier. The order data are not members of X.
The corrected target holds only for a parameter set that contains the order
data. The condensation's X does not contain them. The corrected target does
not serve the consumer.

## 4. THE NUMBER

Zero in-fence lines delivered. No source file changed. The refusal is the
deliverable.

## 5. SECONDS AND RATE

Baseline measurements, cold, at the DD24 caliber
`GHCRTS="-A64m -I0 -M16g"`, one process:

| file | lines | seconds | rate |
|---|---:|---:|---:|
| `FOL.Manipulation.Parameters` | 175 | 0.94 | 0.0054 |
| `L.Hull` | 372 | 2.65 (contended) | 0.0071 |

`LJ-1.14` measured `L.Hull` at 1.53 to 1.63 seconds. The difference is under
the noise rule, and the sibling `LJ-1.15` ran Agda during my measurement.
The parameterized class runs at 0.005 to 0.01 seconds per line. Shape 3's
content is the P-n floor at 0.22 to 0.297 seconds per line. Against the bar
0.013193, the delivered baselines pass. Shape 3 blows the bar by 17 to 23
times.

## 6. TEMPLATE OR PER-TOWER (DD4)

Shapes 1 and 2 are generic. The J tower could reuse a bake operator and a
substitution operator. Neither closes the criterion. Shape 3 is per-tower.
The leastness encoding is specific to the L-side hull. The internal order
formula is per-tower too. The L-side order at `Lset α` is not the J-side
order. T44's `σ_<` lives at the S-tower. Its relocation to `⟪ Lset α ⟫` is
unprobed. DD4 does not rescue a blocked route.

## 7. WHAT THE RETIRED ROUTE DECIDED

The retired route decided against substitution. The journal records that
parameters enter as an environment, not by substitution
(`archive/dev/JOURNAL-archived.md:3988`). The decision transfers. The tree
still has renaming, not substitution
(`src/FOL/Manipulation/Renaming.lagda.md:8-18`). T40's second obstruction is
outdated. `FOL.Manipulation.Parameters` now delivers the
constants-to-variables face. The first obstruction stands. The internal
order formula is the real residual.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md` section 1.3. Devlin 5.3's least-witness
mechanism. The criterion is proved at X-parameters. The substitution step
is implicit. Used for the statement and the encoding shape.

`dev/literature/devlin-II5.md` section 2.4. Step D. The digest states that
the order must be a uniformly Δ₁-definable well-order. The leastness is
encoded as `φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`. This tree's order is a meta
object, not a formula. That difference is the blocker.

`_build/literature/dev2.txt:1329-1356`. Devlin 5.3's proof. Used for the
criterion's shape.

`dev/literature/devlin-errata.md`. Not used. It does not cover Chapter II
section 5. `LJ-1.14` checked that at `_build/lj-1.14-report.md:107-108`.

## 9. ARCHIVE USED

`_build/lj-1.14-report.md:83-87`. The commissioning residue. Took the
statement that `TV→elem` at the hull needs the criterion at hull parameters.

`_build/lj-1.3-report.md:114-131`. The three standing pieces. Took the 210
to 430 band.

`_build/lj-1.12-report.md` section 5. Confirmed that the bridge is owed.

`_build/l3.32-t40-report.md:109-135`. The two residues. Took the internal
order formula as the first obstruction.

`_build/l3.32-t44-report.md:165-180`. The three gaps. Took the general-level
formula and the carrier relocation.

`_build/l3.32-t48-report.md:237-238`. The price of the internal order
formula. Took 1.0 to 2.7 thousand naive lines.

`archive/dev/JOURNAL-archived.md:3988`. The substitution decision.

`archive/rud-route/src/L/Hull.lagda.md:414-440`. The closing notes. Took the
naming of the two consequences and the `σ_<` residual.

`dev/LESSONS.md` through `scripts/rules.py --for build`. Took P-h, P-l, P-m,
P-n, D-10, C-12, and C-22.

## 10. WHAT I AM NOT SURE OF

1. The rank claim. The order element `relL α` has rank α+1, so it is not in
   `Lset α`. The tree has no lemma about the order element's stage. Piece
   one is open. A probe could settle the claim.
2. The narrower Σ₁-transfer route. The consumer may need only
   Σ₁-elementarity. A Δ₀-matrix criterion at hull parameters may be
   buildable through the ambient reading. I did not price it. The recorded
   target is the full criterion.
3. The birth-decomposition order. For a limit α, the step tables at δ < α
   may live in `Lset α`. A birth-based internal order may exist at the
   carrier. The mixed-domain blocker still stops the X-parameter packaging.
   This is unprobed.
4. My measurements are contended. `LJ-1.15` runs Agda. The `L.Hull`
   baseline matches `LJ-1.14` within the noise rule.
