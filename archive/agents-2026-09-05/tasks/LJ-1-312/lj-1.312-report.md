# LJ-1.312 report: settle `φ₀`'s slot roles by machine

## 0. LEAD

**REFUTED.** `[LJ-1.310]`'s off-by-one is REAL, and it is now **MEASURED**.
`φ₀`'s two free slots are the graph's ORDINAL and the graph's machinery BOUND.
They are not the VALUE and the ORDINAL. `q'` needs the VALUE and the ORDINAL.
So `[LJ-1.302]`'s `Composite` carries a wrong type, and the 470-line price in
`dev/PLAN.md` section 0.0 rests on it.

**THE TERM THAT REFUSES**, `agents/tasks/LJ-1-312/ProbeLJ1312C.agda:39`:

```
delivered-is-cured : V.levelHoodB ≡ C.levelHoodB
delivered-is-cured = refl
```

```
ProbeLJ1312C.agda:39.24-28: error: [UnequalTerms]
zero != suc zero of type Fin (suc (suc n))
when checking that the expression refl has type
V.levelHoodB ≡ C.levelHoodB
```

`V` is the VERBATIM copy of the delivered `LevelHood`. `C` is the same module
with the two cured lines. `V.levelHoodB ≡ D.levelHoodB` holds by `refl`
(`ProbeLJ1312A.agda:171-172`), so the refusal is about the delivered formula
and not about a copy that drifted.

The second refusal, `agents/tasks/LJ-1-312/ProbeLJ1312B.agda:45`, states the
COMMENT's reading of `src/L/BoundedSubset.lagda.md:70-73` and gets
`zero != suc zero of type Fin (suc (suc (suc (suc n))))`.

**THE ROUTE IS NOT DEAD.** The cure is small, and one form of it never touches
`src/`. Section 6 prices both forms.

## 1. WHAT RAN, AND AT WHAT COST

| file | lines | code lines | exit | wall | machine load |
|---|---:|---:|---:|---:|---:|
| `ProbeLJ1312A.agda` | 398 | 212 | **0** | **14.60 s** | 2 Agda processes, one sibling and me |
| `ProbeLJ1312B.agda` | 45 | 21 | 42, EXPECTED | 2.71 s | 2 |
| `ProbeLJ1312C.agda` | 39 | 20 | 42, EXPECTED | 2.75 s | 2 |

`GHCRTS="-A64m -I0 -M8g"`, one process at a time. I ran
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` before every
invocation. It returned 1 every time, so I never exceeded C-12's cap of two.
No heap exhaustion. No wall.

`ProbeLJ1312A.agda` holds 21 `refl`s. Each one is a MEASUREMENT.
`ProbeLJ1312B.agda` and `ProbeLJ1312C.agda` are NEGATIVE CONTROLS. They exist
because a `refl` that holds proves nothing until a wrong statement of the same
shape refuses.

## 2. THE EIGHT LINKS, EACH RE-DERIVED

| # | link | verdict | evidence |
|---:|---|---|---|
| 1 | `∃̇∈` binds at slot 0 and shifts the environment up by one | **VERIFIED** | `src/FOL/Semantics.lagda.md:103`, `γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))`. The bound term reads the OUTER environment and the body reads the shifted one |
| 2 | `levelHoodB`'s body environment is `x ∷ w ∷ v ∷ γ ∷ K ∷ δ` | **VERIFIED, MEASURED** | `ProbeLJ1312A.agda:237-282`, the `lookup` block, and the arity `4 + n` at `src/L/BoundedSubset.lagda.md:108` |
| 3 | `GraphB`'s arguments are body slots 0, 2 and 3 | **VERIFIED, MEASURED** | `src/L/BoundedSubset.lagda.md:105`; `ProbeLJ1312A.agda:177-180` pins the whole term by `refl` |
| 4 | `GraphB`'s parameter roles are (value, ordinal, bound) | **VERIFIED**, and settled inside `src/` | see section 3 |
| 5 | the `≐` at `:111` is `w ≐ x` | **VERIFIED, MEASURED** | `ProbeLJ1312A.agda:177-180` pins `var (suc zero) ≐ var zero`; `ProbeLJ1312B.agda:45` REFUSES `var (suc (suc zero)) ≐ var zero` |
| 6 | value is `w` at slot 0, ordinal is `v` at slot 1, bound is `γ` at slot 2 | **VERIFIED, MEASURED** | sections 3 and 4 below |
| 7 | `ρ` sends base slots 1 and 2 to 14 and 15 | **VERIFIED** | `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111`. `Agrees ρ γ δ = ∀ i → lookup (ρ i) γ ≡ lookup i δ` at `src/FOL/Manipulation/Renaming.lagda.md:101-102`, so base's slot `i` sits at slot `ρ i` |
| 8 | `closeN 14` closes slots 0 to 13 | **VERIFIED** | `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:140-146`. `closeN (suc k) φ = closeN k (∃̇ φ)`, and `∃̇` removes slot 0 |

**NO LINK OF THE EIGHT FAILS.** `[LJ-1.310]`'s derivation is correct at every
step.

## 3. LINK 4, THE WEAKEST JOINT, SETTLED INSIDE `src/`

`[LJ-1.310]` settled link 4 against a probe file and called it its own weakest
joint. It is settled inside `src/`, by a chain of definitions:

1. `GraphB {m} ψs ψa (w b K : Fin m)`, `src/L/Condensation.lagda.md:2483-2485`.
2. `module S = StepB {1 + m} ψs (suc w) (suc b) zero (suc K)`, `:2487`. So
   `GraphB`'s `w` becomes `StepB`'s `v`, and `GraphB`'s `b` becomes `StepB`'s
   `b`.
3. `StepB {m} ψ (v b f K : Fin m)`, `:2389-2390`.
4. `stepBndAt = extAtB v K witB`, `:2415`.
5. `extAtB y K φ = ∀̇∈ (var y) φ ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))`,
   `:100-102`. The formula says that the set at slot `y` holds exactly the
   satisfiers of `φ`. **So `y` is the VALUE.**
6. `bodyB`'s first conjunct is
   `var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b))))`, `:2403`. The index
   ranges in the set at slot `b`. **So `b` is the ORDINAL.**

The delivered unbounded machine has the same shape.
`StepAt v b f = extAt v (∃̇ (∃̇ (∃̇ (StepBody b f))))`,
`src/L/Coding/Sequence.lagda.md:119-120`, and
`StepBody b f = (var (suc (suc zero)) ∈̇ var (sh4 b)) ∧̇ ...`, `:114`.
`GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`,
`agents/tasks/LJ-1-238/GenSequence.agda:166-167`.

**MEASURED, by machine**, `ProbeLJ1312A.agda:185-205`:

- `census-graph` pins `G.graphBndAt` to
  `∃̇∈ (var (suc (suc (suc zero)))) (A.approxBndAt ∧̇ Sb.stepBndAt)`, where `A`
  and `Sb` are the same `ApproxB` and `StepB` applications that `GraphB` makes.
- `census-step` pins `Sb.stepBndAt` to
  `extAtB (suc zero) (suc (suc (suc (suc zero)))) Sb.witB`.
- `census-wit` pins `Sb.witB`'s outermost bounded existential to
  `var (suc (suc (suc (suc zero))))`.

## 4. THE FOUR SLOTS, MEASURED

The environment arithmetic is `ProbeLJ1312A.agda:237-282`, seven `refl`s at
`n = 0` over the environment `a ∷ b ∷ c ∷ d ∷ []`.

| outer slot | ROLE, MEASURED from the syntax | role in the COMMENT at `:70-73` |
|---:|---|---|
| 0 | the **VALUE** | the witness |
| 1 | the **ORDINAL** | the value |
| 2 | the **bound of the graph machinery** | the ordinal |
| 3 | the **bound of the value witness** | the bound |

Read the table across. The syntax and the comment differ by one position at
every slot.

**THE CONSEQUENCE FOR `φ₀`.** Links 7 and 8 keep base slots 1 and 2.

- Under the syntax that pair is (ORDINAL, machinery bound).
- `q'` needs (VALUE, ORDINAL).
- `ProbeLJ1241A.agda:105`'s own comment says "v ↦ 14, γ ↦ 15", and it names
  those two by the file comment's roles and not by the syntax.

So `φ₀(a, b)` says "the level at ordinal `a` exists inside bound `b`", exactly
as `[LJ-1.310]` reported. `q'` asks for "`a` is the level at ordinal `b`".
**Empty set and a limit separate the two**, and `[LJ-1.310]` gives that
counterexample. I did not re-derive the counterexample by machine, because the
type is already wrong and a wrong type needs no model. **INFERRED**, that step
only.

## 5. THE SECOND ANOMALY: TWO BOUNDS IN ONE FORMULA

**REAL, and MEASURED.**

- `levelHoodB`'s own bounded existential ranges over OUTER slot 3.
  `ProbeLJ1312A.agda:177-180`, the term `var (suc (suc (suc zero)))` at arity
  `4 + n`.
- `G.graphBndAt`'s bounded existential ranges over BODY slot 3, which is OUTER
  slot 2. `ProbeLJ1312A.agda:185-188`, the term `var (suc (suc (suc zero)))` at
  arity `5 + n`.
- The step's own bound is GRAPH-BODY slot 4, which is OUTER slot 2 again.
  `ProbeLJ1312A.agda:194-196`.

The same numeral 3 names two different slots, because the two environments sit
one binder apart. The value witness is bounded by slot 3. All the machinery is
bounded by slot 2. **A bounded matrix with two independent bounds is not a
design.** It is the signature of the off-by-one, and it is independent of the
role census.

**THE CURE MAKES THE TWO BOUNDS ONE.** `ProbeLJ1312A.agda:348-351` measures
that the cured formula bounds its witness and its machinery by the same OUTER
slot 3.

## 6. THE CURE, PROVED IN A COPY, AND WHAT IT BREAKS

### 6.1 FORM 1, `[LJ-1.310]`'s cure: two lines in a delivered file

`agents/tasks/LJ-1-312/ProbeLJ1312A.agda:297-329` holds the cured module. It is
`LevelHoodV` with two lines changed and no other line changed.

| site | delivered | cured |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:105` | `zero (suc (suc zero)) (suc (suc (suc zero)))` | `zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))` |
| `src/L/BoundedSubset.lagda.md:111` | `var (suc zero) ≐ var zero` | `var (suc (suc zero)) ≐ var zero` |

**WHAT THE CURE COSTS, MEASURED.** Nothing in certificates.
`Δ₀-levelHoodB = δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt V.Δ₀-ψs V.Δ₀-ψa) δ-≐)` typechecks
unchanged (`ProbeLJ1312A.agda:323`), and so does
`Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)` (`:329`). The two leaf contents
`ψs` and `ψa` do not change, because `GraphB`'s three structural parameters
never enter them (`src/L/Condensation.lagda.md:2483-2490`).

**WHAT THE CURED SLOTS BECOME, MEASURED**, `ProbeLJ1312A.agda:340-397`:

| outer slot | role after the cure |
|---:|---|
| 0 | UNUSED |
| 1 | the VALUE |
| 2 | the ORDINAL |
| 3 | the one bound |

Then `ρ` keeps base slots 1 and 2, which are the VALUE and the ORDINAL, and
`q'` gets the pair it needs.

**WHAT IT BREAKS DOWNSTREAM, MEASURED by grep over the tree:**

- `GraphB` has exactly ONE application in `src/`: `src/L/BoundedSubset.lagda.md:81`.
- `LevelHood` has exactly ONE application in `src/`:
  `src/L/BoundedSubset.lagda.md:844`, inside `LevelHood0`.
- `LevelHood0` has NO consumer in `src/` outside its own definition at `:840`.
- `L.BoundedSubset` has NO importer in `src/` except
  `src/Everything.lagda.md:383`.

**So the cure breaks nothing in `src/`.** It changes the probes that read
`LevelHood`: `ProbeLJ1241A.agda:85`, `ProbeLJ1241B.agda:52` and `:63`, and
`ProbeLJ1239A.agda:57` through `LevelHood0`. A probe is evidence and never
proof, so each is a re-run and not a repair.

**PRICE.** Two lines. The re-check of `src/L/BoundedSubset.lagda.md` costs about
**17 s**: 1,409 in-fence lines (`dev/ledger.toml:3126`) at 0.0121 s per line
(`dev/ledger.toml:2751`). **The basis is the ledger's own per-module rate, and
that rate is a comparable and not a measurement of this edit** (P-l).

### 6.2 FORM 2, and it never touches `src/`

The delivered syntax is CONSISTENT as a formula. Its four slots are all used
and all meaningful. Only the RENAMING reads them wrongly. So the same repair is
available one line lower, in a file that was never landed:

- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111` defines `ρ`.
- Today `ρ` sends 0 to 0, 1 to 14, 2 to 15 and 3 to 1.
- A `ρ'` that sends 0 to 14, 1 to 15, 2 to 0 and 3 to 1 keeps the VALUE and the
  ORDINAL free, and closes both bounds.
- `ρ'` is a permutation of `Fin 16`, exactly as `ρ` is, so `renameFo` accepts
  it on the same terms.

**INFERRED, not MEASURED.** I did not build `ρ'` and I did not typecheck the
`φ₀` it makes. The two forms also differ in meaning. Form 1 closes one bound.
Form 2 closes two independent bounds. Which one `q'` can actually be proved
against is a mathematics question, and this probe does not settle it.

**MY RECOMMENDATION, and it is a recommendation and not a finding.** Price Form
2 first. It edits a probe and not a delivered master, so it is cheaper to try
and cheaper to abandon. Form 1 is the one that matches Devlin's shape, so Form
1 is the one to land if both work.

## 7. THE DEVLIN READING (LITERATURE, DD18)

**VERIFIED.** `dev/literature/devlin-II5.md:95-96` quotes Devlin 2.7:

> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

`[LJ-1.310]` reports this correctly. Φ carries THREE slots. Clause (a) closes
ONE of them, `z`, at position 0. The two that stay free are `v` at position 1
and `γ` at position 2. The conclusion `v = L_γ` uses them as VALUE and ORDINAL.

**Bedrock copies clause (a) exactly.**
`levelHoodΣ₁ = ∃̇ levelHoodB`, `src/L/BoundedSubset.lagda.md:142-143`, closes
slot 0 and keeps slots 1 and 2. **So Devlin's shape is the specification, and
it demands slot 1 = VALUE and slot 2 = ORDINAL.** The delivered syntax gives
slot 1 = ORDINAL and slot 2 = BOUND. **The delivered formula fails the
specification**, and Form 1 of the cure makes it meet the specification exactly.

This is the strongest outside check available, and it agrees with the machine.

**WHY NOT, for what I did not use.** I did not use Devlin's clause (b) at
`:99`. Clause (b) is the relativized form at a limit `α`, and it settles a
transfer and not a slot order. I did not use `:214-215`, the summary row,
because it repeats `:95-96` and adds no slot information.

## 8. WHY NOBODY CAUGHT IT, EACH REASON CHECKED

- **`ProbeLJ1241B.agda:120-133` measured the free-variable SET and the tag
  ORDER, never the ROLES. CONFIRMED, MEASURED by reading.** `freeCheck` pins
  `dedup (freeFo base)` to a 16-element list, and `freeCheck'` pins the effect
  of moving `N0`. Neither statement mentions a role. **I did not cite it as
  settling anything.**
- **`[LJ-1.52]` dropped the `≐` half. CONFIRMED**, and it is worse than
  `[LJ-1.310]` reported. `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:45-53`
  states `GraphAgree` at the body environment `x ∷ w ∷ v ∷ γ ∷ K`, and it
  asserts that `graphBndAt` there implies
  `LsetGraphAt {5} (suc zero) (suc (suc (suc zero)))`. That machine graph reads
  its VALUE at body slot 1 and its ORDINAL at body slot 3. **The bounded graph
  beside it reads its VALUE at body slot 0 and its ORDINAL at body slot 2**
  (section 3). So `GraphAgree` asserts an agreement that is off by one in BOTH
  arguments. `GraphAgree` is a `Type` and never a term, so nothing ever
  checked it. **This is C-45 exactly: a wrong type survives forever as a
  hypothesis.**
- **The comment at `src/L/BoundedSubset.lagda.md:70-72` names the slots one
  position off the syntax. CONFIRMED, MEASURED.** `ProbeLJ1312B.agda:45` states
  the comment's reading and Agda refuses it. **I read the syntax and I never
  used the comment as evidence.**

## 9. THE EXTENT (C-42): TWO SITES, NOT ONE, AND NOT MORE

A refutation measures ONE site. Here is the sweep, with each filter named.

| search | result |
|---|---|
| `grep -rn "GraphB {" src/` | ONE application, `src/L/BoundedSubset.lagda.md:81`. **MEASURED** |
| `grep -rn "LevelHood {\|LevelHood0" src/` | `LevelHood` applied once, at `:844`; `LevelHood0` defined at `:840` and applied nowhere. **MEASURED** |
| `grep -rn "L.BoundedSubset" src/` | one importer, `src/Everything.lagda.md:383`. **MEASURED** |

**A SECOND SITE INSIDE THE SAME FILE, and it is MEASURED.**
`LevelHood0.Σ₂ = ∃̇ (∃̇ (∃̇∈ (var (suc (suc zero))) levelHoodB))`,
`src/L/BoundedSubset.lagda.md:855-856`, measured by `census-Σ₂` at
`ProbeLJ1312A.agda:226-227`. The bounded existential ranges over slot 2 of an
arity-3 environment. **That slot is the ONE slot that stays free in `Σ₂`.** The
comment at `:854` says the existential ranges over `K`, and the same expression
BINDS `K`. So the same off-by-one appears twice in one file.

`LevelHood0`'s comment at `:847` says the matrix sits at `w ∷ v ∷ γ ∷ K ∷ []`,
while `Σ₂` builds `w ∷ v ∷ K ∷ γ`. **The comments in this file disagree with
each other as well as with the syntax.**

**THE SHAPE DOES NOT EXTEND FURTHER.** `StepAtB`, `ApproxB` and `SatGraphB`
have their own consumers inside `src/L/Condensation.lagda.md`, and those
consumers pass their arguments through the module telescope and never through a
comment. **I did NOT audit them, so this is INFERRED and not MEASURED.**

## 10. DD4, AND MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One
rule, two ends, no metric and no checker.

**MY AXIS is AC-against-GCH**, DD4's own axis, fixed in code at
`scripts/measure/ledger.py:50`.

`levelHoodB`, `GraphB`, `StepB` and `extAtB` are FOL and bounded-set machinery.
They name no tower stage and no trophy carrier. So a defect there is shared by
construction, and a cure there is shared by construction.

**DOES THE CURE TOUCH THE AC END? NO, and not the GCH end either, TODAY.
MEASURED.** `src/L/BoundedSubset.lagda.md` has no importer in `src/` except
`src/Everything.lagda.md:383`, so it lies in neither trophy closure. The ledger
says the same thing independently: `dev/ledger.toml:2749-2751` records that
`L/BoundedSubset` is one of six masters that "sit OUTSIDE the Landmarks cone and
are reachable only through `src/Everything.lagda.md`, so no trophy statement
imports them".

**AND THE LEDGER'S OWN QUALIFICATION APPLIES HERE.** `dev/ledger.toml:204` says
the GCH closure is read from a STATEMENT whose proof is not wired, so it
UNDERSTATES, and a file outside the closure today can be inside it once `sq` is
supplied. **`q'` is exactly the route that would pull `levelHoodB` into the GCH
closure.** So the cure lands on a file that is GCH-bound and AC-free, and the
DD4 gain is the shared FOL layer under it and not this file.

## 11. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `φ₀`'s free pair is not (value, ordinal) | **MEASURED**, `ProbeLJ1312C.agda:39` and `ProbeLJ1312A.agda:171-205` |
| The comment's reading is not the syntax | **MEASURED**, `ProbeLJ1312B.agda:45` |
| `levelHoodB` does not use one bound | **MEASURED**, `ProbeLJ1312A.agda:177-196` |
| The cure does not cost a Δ₀ or Σ₁ certificate | **MEASURED**, `ProbeLJ1312A.agda:323` and `:329` |
| `GraphB` has no second consumer in `src/` | **MEASURED**, grep in section 9 |
| `LevelHood0` has no consumer | **MEASURED**, grep in section 9 |
| `src/L/BoundedSubset.lagda.md` is in no trophy closure | **MEASURED**, grep plus `dev/ledger.toml:2749-2751` |
| `[LJ-1.52]`'s `GraphAgree` was never checked | **MEASURED**, it is a `Type` at `ProbeLJ152A.agda:48-53` |
| `q'` is false at the delivered `φ₀` | **INFERRED**. The type is wrong, so I did not build the model counterexample |
| Form 2 of the cure works | **INFERRED**. I did not build `ρ'` |
| The shape does not extend past `LevelHood` and `LevelHood0` | **INFERRED**. I did not audit `StepAtB` or `SatGraphB` |
| The 470-line price is now wrong | **INFERRED**. The price rests on a wrong type, but I did not re-price it |

## 12. PREMISES, ANSWERED (C-44)

- **"The eight links are `[LJ-1.310]`'s, from a reading with no Agda."**
  CORRECT. Every link is now re-derived, and every one holds.
- **"`φ₀ = closeN 14 (pins ∧̇ renamed)`, arity two."** VERIFIED,
  `ProbeLJ1241A.agda:145-146`.
- **"`[LJ-1.302]`'s `Composite` typechecks with `comp` as a MODULE
  PARAMETER."** VERIFIED by reading `ProbeLJ1302A.agda:72-75`. **C-45 is the
  whole story of this task.** `Composite` typechecks and always would, because
  a parameter is an assumption. `[LJ-1.52]`'s `GraphAgree` is the same failure
  at an earlier date, and it survived two years of readers.

## 13. WHAT I DID NOT SETTLE

- **Whether `q'` can be proved after either cure.** The cure fixes the TYPE. It
  does not supply the proof.
- **Which cure form to land.** Section 6.2 gives my recommendation and marks it
  as one.
- **The new price of the GCH route.** `[LJ-1.302]`'s `Composite` needs a new
  type before anybody re-prices it.
- **Whether `LevelHood0.Σ₂`'s own binder order needs a third change.** Section 9
  measures the anomaly and does not cure it.

## 14. ARCHIVE USED (DD18)

One line read per file.

- `agents/tasks/LJ-1-310/lj-1.310-report.md`, sections 7 and 13 read WHOLE.
  **Line read:** `:258-259`, "CLAIM (INFERRED, never MEASURED): `φ₀`'s two free
  slots are the graph's ORDINAL and BOUND." TOOK the eight links and the two
  candidate cure lines. **CORRECTED nothing.** **EXTENDED it** with link 4's
  settlement inside `src/`, with the `LevelHood0.Σ₂` second site, and with
  cure Form 2.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read `:45-80`. **Line
  read:** `:46-47`, "the bounded graph implies the machine graph at the value
  slot w (slot 1) and the index slot γ (slot 3)". TOOK the archived slot
  reading. **It is off by one in BOTH arguments against the syntax**, and
  section 8 measures that.
- `agents/tasks/LJ-1-241/ProbeLJ1241B.agda`, read `:95-133`. **Line read:**
  `:124`, `freeCheck : free ≡ (3 ∷ 1 ∷ 2 ∷ 5 ∷ ... ∷ [])`. TOOK the
  confirmation that it measures a SET and an ORDER and never a ROLE. **I did
  not cite it as settling the roles.**
- `archive/dev/TASKS-archived.md`, read `:58-75`. **Line read:** `:68`, the
  `L3.32-T33` row, "Condensation crossing | DELIVERED". **TOOK SHAPE ONLY.**
  **WHAT WOULD NOT TRANSFER:** that route ran at the class carrier with `q` as
  a syntactic identity, and `[LJ-1.293]` refuted `q` by machine. So its TERM
  cannot be re-used and none of its figures transfer. Only the fact that a
  crossing was once assembled transfers, and that fact prices nothing.

## 15. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:95-96`, Devlin 2.7 clause (a). **USED** as the
  outside specification for the slot order. Section 7 gives the reading.
- `dev/literature/devlin-II5.md:99`, clause (b). **NOT USED.** It states a
  relativized transfer at a limit ordinal and it fixes no slot order.
- `dev/literature/devlin-II5.md:214-215`, the summary row. **NOT USED.** It
  repeats `:95-96` and adds nothing about slots.

## 16. PROHIBITIONS, ANSWERED

- I wrote only inside `agents/tasks/LJ-1-312/`. `check-probes.py` is clean.
- I did NOT apply the cure to `src/L/BoundedSubset.lagda.md`. The cure lives in
  `ProbeLJ1312A.agda:297-329`, and the orchestrator lands it.
- I did not touch `src/L/GCH.lagda.md`, `src/`, `dev/`, `AGENTS.md` or another
  task directory.
- I did not commit, push, `git checkout .`, `git stash`, `git reset --hard` or
  `git clean`. I did not run `make check`.
- `lint-prose.py --check` exits 0. `lint-agda.py --check` exits 0.
- One Agda process at a time, under `GHCRTS="-A64m -I0 -M8g"`. The cap was
  never raised.
