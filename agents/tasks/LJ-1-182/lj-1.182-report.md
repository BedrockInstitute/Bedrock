# LJ-1.182 report: adversarial review of `[LJ-1.162]`

tier: pi (override). DD25 review of a negative return. No master, no brief and
no report of another task was edited. No Agda was run. No commit, no push.
Written incrementally (C-22). Every negative is marked **MEASURED** or
**INFERRED**.

## 0. VERDICT

**UPHELD.** The NO-GO on price is correct on its own numbers, the measurement
is sound, the brief did not cause it with a false premise, and no
verdict-flipping cure is missed.

## 1. QUESTION 1: is the refusal correct on its own numbers?

**YES. MEASURED.**

The report claims leg 3 is 125 in-fence lines. I re-derived the count from the
probe, not from the report's account of it.

`agents/tasks/LJ-1-162/ProbeLJ1162A.agda`:

| module | lines | my count |
|---|---:|---:|
| `Leaf` | 85-131 | 37 |
| `Step` | 132-190 | 48 |
| `Approx` | 191-207 | 14 |
| `Graph` | 208-226 | 15 |
| `Leg3` | 227-238 | 11 |
| **leg 3** | | **125** |

Each count is non-blank, non-comment code lines, the module header included,
exactly the report's convention. 37 + 48 + 14 + 15 + 11 = 125. The report's
telescope/proof split (52 / 73) also re-derives: Leaf 13+24, Step 13+35,
Approx 10+4, Graph 10+5, Leg3 6+5.

The refusal survives every generous recount. **MEASURED:** if I exclude all 52
telescope lines and keep only the 73 proof lines, the leg is still 73, which
exceeds 60. The negative does not rest on the counting convention.

## 2. QUESTION 2: is the measurement sound?

**YES. MEASURED.**

The decision rests on one figure: 125 against the 60-line gate. A line count is
mechanical. It has no measurement band. The ratio is 2.08, far outside the
`check-ratio.py` noise band of at least ±12.8%.

The protocol holds. The report ran ONE agda process under
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. It ran seven times and recorded
run 7 as the standing result: exit 0, 14.5 s, no unsolved meta, no hole, no
postulate. The load (3.06 to 3.18) is recorded beside the seconds. The load
cannot move a line count, and the wall-clock is not the gate.

One figure sits inside the noise band, and I say so. The report's
generic-versus-fixed delta is about 6 lines, 4.8% of 125. That is inside
±12.8%, so it is no measurement. **The report already marks it as a hypothesis
and not a price** (`lj-1.162-report.md` section 6.3, C-40). No decision rests
on it.

## 3. QUESTION 3: did the brief cause the outcome?

**NO. The brief's premise was TRUE, and the report confirmed it.**

The brief's premise is that the repair is delivered:
`graphBndAt` and `Δ₀-graphBndAt` at `src/L/Condensation.lagda.md:2489-2493`.
I read it. It exists. The report MEASURED that the bounded graph carries the
identification: the whole leg typechecks, exit 0.

Both NO-GO branches were tested. The first branch (the bounded graph cannot
carry the identification) is MEASURED FALSE. The third branch (the two graphs
do not agree) is MEASURED FALSE in the direction leg 3 needs. The only thing
that fired is the line count, which is what a price gate is for.

The brief did under-price one thing, and I name it. The brief's repair covers
only the ambient-to-inner arrow, 2 of the 125 lines. The brief never priced the
bounded-to-unbounded bridge, which is 114 of the 125. **That is a missing
estimate in the brief, not a false premise.** The brief's own obligation
statement says to close leg 3 from the transferred ambient reading, so the
bridge was always in scope.

The cause is correctly attributed. The report names the two `extAt` frames as
the cost (`lj-1.162-report.md` sections 1.2 and 4.2). I checked the frame
signatures:

- `extAt y φ = ∀̇ (z ∈ y ⇒ φ) ∧ ∀̇ (φ ⇒ z ∈ y)` (`src/L/Coding/Model.lagda.md:662-664`)
- `extAtB y K φ = ∀̇∈ y φ ∧ ∀̇∈ K (φ ⇒ z ∈ y)` (`src/L/Condensation.lagda.md:100-102`)
- `extAtB→extAt` takes `fwd`, `bwd` and `inK` (`src/L/Condensation.lagda.md:2511-2519`)

The two conjuncts differ, so a bounded-to-unbounded move pays two directions
and a membership fact. Leg 3 crosses two such frames: `leafB` against `DefAt`,
and `stepBndAt` against `StepAt`. The report's attribution is correct.

## 4. QUESTION 4: is there a cure the return missed?

**NO cure that flips the verdict. The report named the two real forward items.**

The report names the generic frames (`lj-1.162-report.md` section 11) and the
unsupplied `powK` obligation (section 12.1). Neither flips the verdict.

I tested the two routes a cheaper leg would have to take.

**Route 1, generic frames.** The report's own inference puts the generic form
about 6 lines cheaper, so about 119, still above 60. It did not write that
form and correctly refuses to price it (C-40). A 47% cut would be needed to
reach 60, and the cost is in the two `extAt` frames, which are structural and
do not disappear under abstraction.

**Route 2, skip the bridge.** A bounded `Lset-only` would prove `v ≡ Lset b`
directly from the bounded graph and avoid `LsetGraphAt` entirely. That means
re-proving `Lset-only`'s content (`step-Lset`, `approx-val`,
`src/L/Hierarchy.lagda.md:334-360`) at the bounded matrix. That is a chapter,
not a cure.

The one obligation the report flags is real. **MEASURED:** `𝒟ₒ` does not occur
in `src/L/Condensation.lagda.md`, and the `KFacts` record
(`src/L/Condensation.lagda.md:6033-6071`) has no field that bounds a definable
power. So `powK` (`𝒟ₒ w ∈ K`) has no supplier in the site-fact bundle. The
report marks its satisfiability INFERRED, and I confirm the mark.

## 5. C-42, BOTH DIRECTIONS

**Does the negative reach FURTHER than it claims? YES, and it understates.**

The 125 lines state the 52 telescope lines but do not discharge them. The one
with no supplier anywhere is `powK`. The true cost to close leg 3 in the tree
is at least 125 plus the discharge of the telescope, which is unpriced. The
negative is conservative.

**Does it reach LESS far? NO. MEASURED.**

Excluding every telescope line leaves 73 proof lines. 73 still exceeds 60. The
negative survives the most favorable recount, so it does not overreach.

## 6. DD4: did it price the fixed shape when the generic prices differently?

**It priced the fixed shape, and the generic shape does not flip the verdict.**

The report priced the leg at the Lset/Def instance. Its own classification
(`lj-1.162-report.md` section 6) says 103 of 134 gated-plus-kit lines are
template and 31 name a tower. The generic form is INFERRED about 6 lines
cheaper, which is no measurement by the brief's own band rule.

The 8.4-times figure the brief cites does not transfer here. **MEASURED:**
`[LJ-1.159]` line 263 is a factor in SECONDS, 100.64 s to 11.92 s, from naming
a transparent construction in a type. This gate counts LINES. The cost driver
here is the `extAt` frame structure, which abstraction does not remove.

So DD4 does not overturn the negative. It leaves one small unmeasured delta,
correctly marked C-40.

## 7. WHAT THIS UNBLOCKS OR CONFIRMS

**CONFIRMS.** The 125-line leg-3 figure and the 163-line `CrossOut` total are
sound and can be built on. **CONFIRMS** that `CrossOut` is NO-GO at 60 lines
for a structural reason, the two `extAt` frames, not a presentation accident.
**CONFIRMS** that `powK` is a real unsupplied obligation that must be
discharged before `CrossOut` closes.

**UNBLOCKS.** Funding the generic-frames gate (report section 11) and the
`powK` supplier are both sound next steps. Neither changes the NO-GO.

## 8. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-162/LJ-1.162.md`, `lj-1.162-report.md`,
  `ProbeLJ1162A.agda` — read whole. I re-counted the probe at `file:line`
  (Leaf `:85-131`, Step `:132-190`, Approx `:191-207`, Graph `:208-226`,
  Leg3 `:227-238`).
- `agents/tasks/LJ-1-161/lj-1.161-report.md` — read for the leg 1 and leg 2
  figures, 20 and 18 lines, at `:96` and `:183`.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:168-170, :208` —
  verified `CrossOut` is a module hypothesis in `Assembly` and is never
  discharged. `grep` over the archive finds `CrossOut` only as statement or
  hypothesis, none a proof.
- `dev/PLAN.md:736-737` — the campaign's recorded verdict matches the report.
  `dev/PLAN.md:758` — this review's row. Section 0.0 — the campaign now records
  `levelIn` and `cover` BUILT by `[LJ-1.178]`; the standing wall is
  `AmbientRead`, not leg 3.
- `agents/tasks/LJ-1-159/lj-1.159-report.md:263` — the 8.4-times figure is in
  seconds, used in section 6.

## 9. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:88-125` and `:205-265` — Devlin's step (a) is
  `v = L_γ ↔ ∃z Φ(z, v, γ)` with `Φ` a Σ₀ matrix; only the outer `∃z` is
  unbounded. This settles what the negative leaves open about the repair: the
  bounded graph is Devlin's own form, and the delivered `Lset-only` at the
  unbounded graph is the bridge's destination, not Devlin's (a). It does NOT
  settle the line count, which is tree-specific.
- `dev/literature/devlin-errata.md` — NOT used. `[LJ-1.136]` measured the
  errata touch no part of II.5.
- `dev/literature/j-hierarchy.md`, `dev/literature/rudimentary-functions.md` —
  NOT used. This negative sits at the Lset/Def instance. The J tower and the
  rud route do not bear on a line count at this site.
