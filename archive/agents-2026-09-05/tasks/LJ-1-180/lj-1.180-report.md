# LJ-1.180: adversarial review of the `[LJ-1.172]` negative

status: COMPLETE. Written from a skeleton (C-22).

## VERDICT

**UPHELD.** The negative is correct on its numbers: `envSetK` at an
unrestricted `ar` is false at the bound `HullStage` gives, and every
load-bearing citation checks out at commit `07aed79`.

## Q1: is the refusal correct on its own numbers?

**YES. I re-derived every load-bearing citation at the commit the report
measured, which is `07aed79`.** A sibling edits these masters now, so each
check below reads `git show 07aed79:<file>`, not the working tree.

| the report's claim | its citation | my re-read at `07aed79` | verdict |
|---|---|---|---|
| `envSetK` quantifies `ar` over ALL of `S`, restricted only by the `K` slot | `src/L/Condensation/TwelveAgree.lagda.md:271-275` | `envSetK : (B ar : S) → ... → ⟨ fst (Generic.envSetGen B ar) ∈ fst (lookup ... K ... γ') ⟩`, verbatim, in `record TFacts` (`:128`) | **CONFIRMED** |
| `envSetGen` is carved from the full L-power | `src/L/Coding/EnvSet.lagda.md:441-442`, `:456-457` | `powamb = hasPowerL amb .fst .fst`; `envSetGen = hasSeparationL powamb envFoGen .fst .fst` | **CONFIRMED** |
| the members have domain EXACTLY `ar` | `src/L/Coding/Model.lagda.md:278-280` | `domAt f d = ∀̇ ((inDomAt ⇒̇ ∈ d) ∧̇ (∈ d ⇒̇ inDomAt))`, an equivalence | **CONFIRMED** |
| the description asks single-valued, domain `ar`, values in `B` | `src/L/Coding/Model.lagda.md:483-485`, `EnvSet:450-453` | `envOverAt e d B = svAt e ∧̇ (domAt e d ∧̇ (valuesInAt e B ∧̇ pairsInAt e d B))`; `envFoGen` pins `ar` and `B` by constants | **CONFIRMED** |
| the ambient covers every pair, so the carve does not thin the space | `EnvSet:420-433` | `amb = LsetS (pairBound ...)` over `stageFor (⟪ar⟫ × ⟪B⟫)`, and `pair∈amb` puts every pair in it | **CONFIRMED** |
| `HullStage` gives a successor-closed limit and nothing stronger | `src/L/BoundedSubset.lagda.md:903-905` | `module HullStage (lam : S) (ordλ : IsOrd lam) (succλ : ...) (X : S) (X⊆L : ...) (∅∈λ : ...)` | **CONFIRMED** |
| the witness ordinal exists in the tree's vocabulary | `src/L/Ordinal/StageArith.lagda.md:41`, `:48`, `:76-78` | `+ω`, `+ω-in`, `+ω-ord`, all present | **CONFIRMED** |
| nothing in `src/` bounds `envSetGen` in a stage | grep, four hits outside its master | my own grep over every file at `07aed79`: `TwelveAgree:274`, `Sound:288`, `:300`, `:304`. Exactly four, none a bound | **CONFIRMED** |
| the other three hits take an identification as a hypothesis | `src/L/Coding/Sound.lagda.md:287-290`, `:298-300` | `AmbientHoldsGen` carries `qE : lookup Ei γ ≡ fst (Generic.envSetGen B ar)`; `NumeralFromGeneric.derived` proves an equation | **CONFIRMED** |
| `mkReflect` returns an equality of satisfactions under `Below β γ` | `src/L/ReflectFo.lagda.md:525-529` | `Σ β, oβ, δ∈β, ((γ : S ^ n) → Below β γ → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ))` | **CONFIRMED** |
| `Below` is a hypothesis on the environment | `src/L/Reflect.lagda.md:112-114` | `Below σ (p ∷ ρ) = ⟨ fst p ∈ Lset σ ⟩ × Below σ ρ` | **CONFIRMED** |
| the numeral family is bounded at a FIXED iterate | `src/L/Coding/Key.lagda.md:71-81` | `paramEnv∈ : ... → ⟨ paramEnv h ∈ˢ T (sucIter 3 σ) ⟩`, uniform in `k` | **CONFIRMED** |

**The inference itself, re-derived.** The one INFERRED step is section 15.3,
and the report marks it. I re-derive it with a weaker premise than the
report's: one witness suffices, not a rank of the whole space. `Lset lam` is
transitive. If `envSetGen B ar ∈ Lset lam` then `envSetGen B ar ⊆ Lset lam`.
So ONE constructible function `Lset ω → Lset ω` outside `Lset (+ω ω)` refutes
the membership. Classically such a function exists: `L_(ω+ω)` is countable,
the constructible reals are not, and a real's characteristic function is a
function `L_ω → L_ω` that appears at the same stage as the real. **So
the field, demanded uniformly in `lam` at the join, is false in the intended
model, and no proof can supply it.** The report's stronger rank claim
(`(ω₁)^L`) is more than the refutation needs, and nothing rests on the excess.
INFERRED, as the report itself classifies it.

## Q2: is the measurement sound?

**SOUND.** The refutation does not rest on a seconds figure. It rests on two
parts. The first part is a set of structural reads, each at a `file:line`.
The report marks each read MEASURED. I re-read every one at commit `07aed79`,
and every one matches. The second part is one rank argument, section 15.3.
The report marks it INFERRED. The inference is sound classical math. The
witness exists in the tree's own vocabulary.

The Part Two refutation ran zero Agda processes. It stopped on three reads
and one inference. That is the correct D-10 move: price the truth of a
residue before pricing its proof. The downstream task `[LJ-1.173]` re-read
the same declarations and confirmed them.

The one seconds figure in the report is section 10.1. It measures the
`KFacts` value's marginal cost as negative. The report publishes no figure
for it and says the delta is below noise. That is the correct handling. The
report's own spread estimate of 2.5 percent understates the instrument's
known band. `check-ratio.py` prints the band as at least 12.8 percent. This
does not change the verdict, because the refutation does not rest on that
figure.

## Q3: did the brief cause the outcome?

**NO.** The brief's Part Two named the `envSetK` gate before funding step 6.
Its GO condition was `envSetGen B ar ∈ Lset lam` closing through `mkReflect`.
Its NO-GO condition was the description failing `mkReflect`'s form. The
report found NO-GO and then found the deeper fact: the field is false at a
general `ar`. The stop is the named gate failing on genuine grounds.

Two sentences in the original brief were wrong. Row 4 said steps 1 to 3
supply `powIter`. The report measured that false. The brief treated step 1's
drop-in as a code question. The report found DD23 blocks it. Neither error
caused the step-6 stop. The stop is a genuine refutation, not a false
premise.

## Q4: is there a cure the return missed?

**NO.** The return named the cure in section 19: restrict `envSetK` to a
numeral arity. It named the fallback: the fourth `HullStage` hypothesis.
`[LJ-1.173]` ran the gate, applied the restriction, and swept the disease to
21 fields. The return missed no cure.

One qualification. The return's gate for the cure was one declaration at 40
lines. `[LJ-1.173]` measured the join at about 165 lines. That is a cost
correction, not a missed cure.

## C-42 both directions: does the negative reach further, or less far?

**FURTHER:** the return did sweep past the one named field. Section 17 finds
the same power-closure fact under six names. Section 18 finds the level-hood
certificate gap that would still block steps 7 and 8.

**LESS FAR:** the return named one field. `[LJ-1.173]` found 21 fields across
three records. The disease has two mechanisms, not one. Five fields fail on
power closure. Four fields fail on transitivity alone. The return's "one
fact" diagnosis covers the first mechanism. It does not cover the second.

The negative does not overreach. It scopes itself to the one field and the
one fact. It under-reaches the disease's extent, which C-42 says a refutation
will. The sweep follows it.

## DD4: did the negative price a fixed shape?

**NO.** The negative refused the unrestricted arity. That is the over-general
shape, and it is false. The cure is a restriction to the numeral shape. That
is the reverse of the DD4 failure mode, which is a NO-GO on a fixed shape
where the generic shape is cheaper. Here the general shape is the false one.
The return also named the generic alternative, a power-closed bound. So it
did not silently fix the shape.

## WHAT THIS UNBLOCKS OR CONFIRMS

It CONFIRMS the refutation that funds `[LJ-1.173]`'s 21-field cure. The ten
cured declarations in `src/` rest on a correct refutation. It confirms that
step 6 at the original shape was unbuildable. It confirms the correction to
`[LJ-1.168]`'s `mkReflect` route.

One correction it carries. The report's ARCHIVE section claims its grep over
the retired route's `L/Coding/` returns nothing. The grep returns two files:
`Powerset.lagda.md` and `Sequence.lagda.md`. Both carry `DefOK` or `PowOK` as
hypotheses. The substantive conclusion survives: the archive holds no supplier
for the fact. But the stated evidence is MEASURED FALSE.

## ARCHIVE USED

- `agents/tasks/LJ-1-172/lj-1.172-report.md`, READ WHOLE. Took the refutation
  at sections 15 to 19, the six-name family at section 17, and the cure with
  its gate at section 19.
- `agents/tasks/LJ-1-172/LJ-1.172.md`, READ WHOLE. Took the chain table and
  the Part Two gate.
- `src/L/Condensation/TwelveAgree.lagda.md` at `07aed79`:272-276, the original
  `envSetK` field, `(B ar : S)` with no restriction.
- `src/L/Coding/EnvSet.lagda.md`:420-433, `amb` covers every pair, and
  `:441-442`, `:456-457`, `envSetGen` carved from the full power.
- `src/L/Coding/Model.lagda.md`:278-280, `domAt` is an equivalence, and
  `:483-485`, `envOverAt`.
- `src/L/BoundedSubset.lagda.md`:901-905, the `HullStage` telescope, and
  `:111`, the one `graphBndAt` consumer.
- `src/L/Coding/Sound.lagda.md`:287-304, the two identification lemmas and
  the numeral equation.
- `src/L/ReflectFo.lagda.md`:525-531, `mkReflect` returns a satisfaction
  equality.
- `src/L/Ordinal/StageArith.lagda.md`:41, `:48`, `:76-78`, the witness
  ordinal.
- `archive/src/2026-08-09-rud-route/L/Coding/Powerset.lagda.md`:445-446 and
  `Sequence.lagda.md`:130-131, `DefOK` and `PowOK` as hypotheses. This is the
  correction to the report's grep claim.
- `dev/PLAN.md` section 11, rows LJ-1.172, LJ-1.173, LJ-1.180, and section
  0.0.
- `agents/tasks/LJ-1-173/lj-1.173-report.md` sections 1, 3, 31, 36, 37, READ
  for the downstream confirmation and the sweep.

## LITERATURE USED

- `dev/literature/devlin-II5.md`, READ. `:523` states II.2.4's Δ₁ claim for
  `D(v, u)` hands the details to the reader. `:336-355` tables the Def-side
  engine. `:246-247` states `D(v, u)` is Σ₁. This settles the negative's
  characterization: Devlin asserts the closure and leaves the proof.
- `dev/literature/devlin-errata.md`, READ its section index. `:125-143`
  covers Chapter II, but amenability in section 10 only. It touches no part
  of II.5. It does not settle the question.
- `dev/literature/j-hierarchy.md`, NOT USED. It covers the J tower's
  stratification. The negative is about the Def tower's power-closure at
  levels.
- `dev/literature/rudimentary-functions.md`, NOT USED. It covers the rud
  step functions of the J tower, not the Def tower's closure at limits.
