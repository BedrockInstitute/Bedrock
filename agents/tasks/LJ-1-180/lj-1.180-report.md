# LJ-1.180: adversarial review of the `[LJ-1.172]` negative

status: IN PROGRESS. This skeleton fills incrementally (C-22).

## VERDICT

PENDING.

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
| the ambient covers every pair, so the carve does not thin the space | `EnvSet:435-440` | `amb = LsetS (pairBound ...)` over `stageFor (⟪ar⟫ × ⟪B⟫)`, and `pair∈amb` puts every pair in it | **CONFIRMED** |
| `HullStage` gives a successor-closed limit and nothing stronger | `src/L/BoundedSubset.lagda.md:903-905` | `module HullStage (lam : S) (ordλ : IsOrd lam) (succλ : ...) (X : S) (X⊆L : ...) (∅∈λ : ...)` | **CONFIRMED** |
| the witness ordinal exists in the tree's vocabulary | `src/L/Ordinal/StageArith.lagda.md:41`, `:48`, `:76-78` | `+ω`, `+ω-in`, `+ω-ord`, all present | **CONFIRMED** |
| nothing in `src/` bounds `envSetGen` in a stage | grep, four hits outside its master | my own grep over every file at `07aed79`: `TwelveAgree:274`, `Sound:288`, `:300`, `:304`. Exactly four, none a bound | **CONFIRMED** |
| the other three hits take an identification as a hypothesis | `src/L/Coding/Sound.lagda.md:287-290`, `:298-300` | `AmbientHoldsGen` carries `qE : lookup Ei γ ≡ fst (Generic.envSetGen B ar)`; `NumeralFromGeneric.derived` proves an equation | **CONFIRMED** |
| `mkReflect` returns an equality of satisfactions under `Below β γ` | `src/L/ReflectFo.lagda.md:525-529` | `Σ β, oβ, δ∈β, ((γ : S ^ n) → Below β γ → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ))` | **CONFIRMED** |
| `Below` is a hypothesis on the environment | `src/L/Reflect.lagda.md:112-114` | `Below σ (p ∷ ρ) = ⟨ fst p ∈ Lset σ ⟩ × Below σ ρ` | **CONFIRMED** |
| the numeral family is bounded at a FIXED iterate | `src/L/Coding/Key.lagda.md:71-81` | `paramEnv∈ : ... → ⟨ paramEnv h ∈ˢ T (sucIter 3 σ) ⟩`, uniform in `k` | **CONFIRMED** |

**The inference itself, re-derived.** The one INFERRED step is section 15.3,
and the report marks it. I re-derive it with a weaker premise than the
report's: transitivity is enough, cardinality is not needed. `Lset lam` is
transitive. If `envSetGen B ar ∈ Lset lam` then `envSetGen B ar ⊆ Lset lam`.
So ONE constructible function `Lset ω → Lset ω` outside `Lset (+ω ω)` refutes
the membership. Classically such a function exists: `L_(ω+ω)` is countable,
the constructible reals are not, and a real's characteristic function is a
function `L_ω → L_ω` that appears finitely many stages after the real. **So
the field, demanded uniformly in `lam` at the join, is false in the intended
model, and no proof can supply it.** The report's stronger rank claim
(`(ω₁)^L`) is more than the refutation needs, and nothing rests on the excess.
INFERRED, as the report itself classifies it.

## Q2: is the measurement sound?

PENDING.

## Q3: did the brief cause the outcome?

PENDING.

## Q4: is there a cure the return missed?

PENDING.

## C-42 both directions: does the negative reach further, or less far?

PENDING.

## DD4: did the negative price a fixed shape?

PENDING.

## WHAT THIS UNBLOCKS OR CONFIRMS

PENDING.

## ARCHIVE USED

PENDING.

## LITERATURE USED

PENDING.
