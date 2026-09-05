# LJ-1.314 report: adversarial DD25 review of `InjData`'s NECESSITY

tier: opus (pi-subagent-mode), the ADVERSARIAL row. Target: `[LJ-1.305]`.
A REVIEW: nothing lands, all writes in `agents/tasks/LJ-1-314/`. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those
words. ASD-STE100 applies.

## 0. LEAD

**SPLIT.**

**The target's core verdict HOLDS, and its widest claim is REFUTED.**

1. **Attack 1. `leastOf` does NOT derive `InjData`, and the side
   condition is MEASURED.** `leastOf` takes the MEMBER for free, and the
   tree already does it (`src/L/Cardinal.lagda.md:116-134`). It cannot
   take the INJECTION, because `leastOf` demands a predicate
   `P : A → hProp` (`src/L/WellOrder/Base.lagda.md:159`) and every
   delivered `SWO` carries a member type, never a function type.
2. **AND THE RESIDUE IS NOT A NEW PRINCIPLE.** MEASURED by a green
   probe: the tree's own cure for this exact shape, select the CODE and
   read it back, untruncates without any principle. The one missing
   input is a stage-bounded `AmbientToCode`, which is the project's
   ALREADY-RECORDED independent crossing (`dev/PLAN.md:423-426`).
   `agents/tasks/LJ-1-314/CodeUntrunc.agda`, 135 non-blank, exit 0, 2 s.
3. **Attack 5. `「one ruling covers all three sites」` is REFUTED,
   MEASURED.** `src/L/Cardinal.lagda.md:256-258` is a CODED site and it
   untruncates today, `CodeUntrunc.agda:99-104`, green. The three sites
   are TWO debts, and one of the three is not a debt.
4. **Attack 2. The ambient face does NOT rescue the trophy.** MEASURED:
   the delivered consumer needs the untruncated law at EVERY ordinal
   below the site, not only at cardinals
   (`src/L/StageCardinal.lagda.md:17-19`,
   `src/L/BoundedSubset.lagda.md:1388-1390`).
5. **Attack 4. `InjData` does NOT reach the AC closure**, MEASURED on
   DD4's own axis. It is an AMBIENT untruncation principle, not an
   internal one, and INFERRED strictly stronger than `lem`.
6. **Attack 3. The countermodel re-runs green and its scope is
   narrower than the target's sweep sentence.** It refutes the AMBIENT
   spelling. The tree's own `isPropLeastOf` PROVES that a least-code
   spelling IS an hProp.

**WHAT THE OWNER SHOULD BE ASKED.** Not「admit a new principle」. The
question is the CARDINAL FACE, which is already on the owner's list at
`dev/PLAN.md:410-431`. `InjData` is the ambient-side patch for that same
crossing.

## 1. ATTACK 1: DOES `leastOf` DERIVE `InjData`?

**It derives the MEMBER. It does not derive the INJECTION. MEASURED.**

### 1.1 The tree already runs half the derivation

`src/L/Cardinal.lagda.md:61-154`, module `LeastCardInjL`, is exactly the
construction attack 1 asks about:

- `w : SWO (⟪ sucV (fst α) ⟫)` at `:91-92`, the ordinal's own well-order.
- `InjP γ = ∥ Inj γ ∥₁ , squash₁` at `:66-67`. **The injection is
  TRUNCATED here, and that truncation is what makes `InjP` an `hProp`.**
- `least = leastOf w lem InjP' nonempty` at `:117`.
- `κ = up γ-card` at `:122-123`: **the least member, as DATA, with no new
  principle.**
- `κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁` at `:132-134`. The tree's own
  comment on `:132` reads「The witness, an injection, still truncated,
  still not an hProp」.

So `InjData`'s `Σ` has two components and the FIRST IS FREE. Its content
is the second component alone.

### 1.2 The side condition, at `file:line`

`leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`) demands two things:

1. **A well-order on the carrier**, `w : SWO A` at `:127`.
2. **A PROPOSITION-valued predicate**, `P : A → hProp ℓ''` at `:159`. The
   returned payload is `⟨ P a ⟩` (`IsLeast` at `:130-131`), so **every
   payload `leastOf` can return is a proposition by construction.**

An injection is not a proposition (section 3). So the payload road is
closed. The other road is to make the injection the CARRIER, and that
needs an `SWO` on a function type.

**MEASURED: no `SWO` in the tree carries a function type.** Every
delivered instance carries a member type or a product of member types:
`⟪ α ⟫` (`src/L/Ordinal/SquareLaw.lagda.md:176`,
`src/L/StageCardinal.lagda.md:258`), `Mem (Lset β)`
(`src/L/Choice/Transversal.lagda.md:191`,
`src/L/Choice/Order.lagda.md:690`), `ℕ`
(`src/L/Choice/Finite.lagda.md:596`), `Name`
(`src/L/Choice/Name.lagda.md:804`), `New δ`
(`src/L/Choice/Step.lagda.md:383`), `Point n`
(`src/L/Choice/Finite.lagda.md:884`), `Limit`
(`src/L/Choice/Finite.lagda.md:1114`), and the products `prodSWO`,
`lex2`, `lex3`, `godSWO` (`src/L/Ordinal/SquareLaw.lagda.md:127`, `:282`,
`:285`, `:308`).

**This is not an accident of the port.** A well-order on two extensions
gives no well-order on the functions between them. The classical device
that does is the well-order of `L`, and it orders SETS. An ambient
function is not a set of the model until its graph is coded.

### 1.3 The tree's own cure, and it is the answer

**The delivered pattern for this exact shape is: never select the
function, select its CODE.** A code is a member, so `leastOf` takes it,
and「F codes an injection」is a PROPOSITION.

- `Canonical` at `src/L/Cardinal.lagda.md:182-210` runs it:
  `chosen = leastOf (orderAt β oβ) lem Good h` at `:195`, with `Good A` a
  conjunction of satisfaction facts at `:188-190`, all `Ω`-valued. **Its
  outputs `sv`, `dm`, `ij` at `:203-210` are UNTRUNCATED.**
- `Small` at `src/L/Coding/Injection.lagda.md:123-152` reads a code back
  to an honest ambient injection, `small` and `small-inj` at `:147-152`.

**MEASURED, by a green probe of my own:**
`agents/tasks/LJ-1-314/CodeUntrunc.agda`, exit 0, 2 s.

- `untruncAt` (`:64-72`): `leastOf` untruncates ANY existence over a
  well-ordered carrier whose payload is a proposition.
- `isPropInjCode` (`:81-86`): `InjCode`
  (`src/L/Cardinal.lagda.md:223-228`) IS a proposition. Three
  satisfaction facts and one bounded implication, all hProp carriers.
- `codeData` (`:99-104`): the truncated CODED existence becomes data.
- `codeInj` (`:122-128`): and `Small` reads it back to an UNTRUNCATED
  ambient injection.

**So the untruncation and the readback are both DELIVERED.** The single
missing input is the truncated existence of a stage-bounded CODE.

### 1.4 What the residue actually is

`bridge→data` at `CodeUntrunc.agda:127-133`, green:

```agda
BoundedToCode = (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
              → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
                  ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up β oβ F) a b ∥₁

bridge→data : BoundedToCode
            → (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁ → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
```

**MEASURED: a stage-bounded ambient-to-code bridge discharges the atom
that `InjData` was asked for.** The bound is needed because
`AmbientToCode` as spelled at `agents/tasks/LJ-1-299/NoInj2.agda:131-133`
returns `Σ[ F ∈ S ]`, unbounded, and no `SWO` in the tree carries `S`, so
`leastOf` cannot take it. The tree already POSITS the bounded form at
`src/L/Cardinal.lagda.md:239-240`.

**INFERRED: `InjData` follows from `BoundedToCode` plus `LeastCardInjL`.**
I did not build that composite, because it needs `κ ∈ˢ α` from
`∥ Wat α ∥₁` by leastness, about 20 further lines. The two halves are
each measured; the join is not.

### 1.5 The answer to D-10

**The recorded residue is TRUE as a statement about the AMBIENT
descent, and FALSE as a statement about the mathematics.** The target
says the residue is「the proof architecture's limitation」. I sharpen
that: the limitation is the AMBIENT-against-CODED face, and the project
already has that fork open (`dev/PLAN.md:410-431`).

## 2. ATTACK 2: THE AMBIENT FACE

**It does not rescue the trophy. MEASURED, three ways.**

### 2.1 The bonus is real, and it is narrower than `SqShape`

`sq-initial` at `agents/tasks/LJ-1-305/Untruncated.agda:280-282` gates on
ambient `IsCardinal α`. `SqShape` (`src/L/GCH.lagda.md:44-47`) quantifies
over EVERY ordinal outside ω, cardinal or not. **So the bonus cannot
supply `SqShape` at any face.** MEASURED, by reading the two types.

### 2.2 The delivered consumer needs the law at every ordinal below

**This is the decisive measurement and the target does not carry it.**
The square law is consumed by two DELIVERED module parameters, both
untruncated and both quantifying over every ordinal below the site:

- `src/L/StageCardinal.lagda.md:17-19`:
  `sq : (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → ⊥) → Σ[ f ∈ ... ] ...`
- `src/L/BoundedSubset.lagda.md:1388-1390`, `Devlin55.BoundedSubsetAt`,
  the same shape, used at `:1397` and `:1410`.

**Most `δ ∈ sucV α₀` are not cardinals and are not ambient-initial.** So
`sq-initial` supplies neither consumer, at either face. MEASURED.

### 2.3 The ambient face covers a SUB-CLASS of the trophy's cardinals

- ambient `IsCardinal` at `src/L/BoundedSubset.lagda.md:1046-1047`
  refutes an AMBIENT injection.
- coded `IsCardinalL` at `src/L/Cardinal.lagda.md:230-233` refutes a
  CODED one, and `GCHStatement` names `IsCardinalL κ` at
  `src/L/GCH.lagda.md:82`.
- `amb→code : IsCardinal (fst κ) → IsCardinalL κ` is DELIVERED as a probe
  term at `agents/tasks/LJ-1-299/NoInj2.agda:103-111`. **MEASURED: the
  reverse has no term** (`dev/PLAN.md:421`).

So the ambient cardinals are a SUB-CLASS of the L-cardinals. **INFERRED:
a trophy stated at the ambient face quantifies over fewer κ than
`L ⊨ GCH` needs, so it is a different theorem.** I built no separating
model; `[LJ-1.300]` already recorded the separation as INDEPENDENT
(`agents/tasks/LJ-1-300/lj-1.300-report.md:198-206`).

### 2.4 What the target actually said

**The target is HONEST here and the brief's suspicion is only half
right.** `lj-1.305-report.md:433-437` names the face gap itself:「Its
face is ambient `IsCardinal`; the trophy's use site gates on
`IsCardinalL`」. It does NOT claim the bonus is an alternative to
`InjData`. **What it does not say is 2.2: that the bonus cannot supply
`SqShape` at any face, because the delivered consumers need every
ordinal below the site.** That is new and it closes the fork's payoff
question: **the ambient face buys NOTHING toward `SqShape`.**

## 3. ATTACK 3: THE COUNTERMODEL, RE-RUN AND SCOPED

**RE-RUN, GREEN.** `agents/tasks/LJ-1-305/NotProp.agda`, exit 0, **3 s**,
1-minute load 6.65, dependencies warm, one agda process,
`GHCRTS="-A64m -I0 -M8g"`, 0 slots before. The target reported 2 s. The
calibers agree.

### 3.1 What it refutes

`sq-not-prop : ((g h : sq ω) → g ≡ h) → Empty.⊥` at
`NotProp.agda:203-204`. The device is a transposition of two numeral
points of `⟪ ω ⟫` (`swap`, `:107-108`), post-composed on the first
coordinate of the delivered pairing (`twisted`, `:169-170`), and refuted
against it (`twisted≢square`, `:182-198`).

**The refuted site is the AMBIENT-FUNCTION SPELLING of `sq`.** The
argument is post-composition with a non-trivial permutation of an
infinite codomain. It refutes every spelling whose elements are
functions. MEASURED at ω; INFERRED at every other ordinal that holds two
numerals, exactly as the target marks it (`lj-1.305-report.md:170-171`).

### 3.2 Where the target's sweep goes further than C-42 allows

`lj-1.305-report.md:172-173` reads「Route 1 is closed at every site the
descent or `SqShape` names」. That is TRUE for the sites AS SPELLED.

**But a re-spelling reopens route 1, and the tree PROVES it.**
`isPropLeastOf` at `src/L/WellOrder/Base.lagda.md:136-144` proves that

```agda
Σ[ a ∈ A ] IsLeast P a
```

**IS a proposition**, for any hProp-valued `P` over a well-ordered `A`.
So「the LEAST code of an injection」is an hProp, while「an injection」is
not. **MEASURED, and it is the same fact my probe uses in section 1.3.**

**So route 1 is closed for the ambient spelling and OPEN for the
least-code spelling.** The countermodel measures the site it names
(C-42) and the target's sweep sentence reads wider than the site.

## 4. ATTACK 4: LOGICAL STRENGTH, AND THE AC CLOSURE

### 4.1 What `InjData` is

**`InjData` is an AMBIENT untruncation principle, not an internal one.**
It is an instance of the schema `∥ X ∥₁ → X` at a family of SETS. It is
not countable choice, not dependent choice, and not global choice: it
selects at a family indexed by the ordinals and it does not act inside
`L`.

**INFERRED: it is strictly stronger than the module's `lem`.** The
argument, which I did not formalise:

1. `InjData` at a non-initial infinite ordinal α returns δ ∈ α and an
   injection `⟪ α ⟫ ↪ ⟪ δ ⟫`. Iterating on δ terminates by
   `regularityV`, so `InjData` yields, UNIFORMLY IN α, an injection of α
   into an initial ordinal.
2. At the countable α that is an injection into ω, uniformly, so the map
   `α ↦ (its transported order)` injects the countable ordinals into a
   power set.
3. In classical set theory without choice that statement is not
   provable. It is `ℵ₁ ≤ 2^ℵ₀`, and it FAILS under the axiom of
   determinacy.

**So `InjData` is not a book-keeping device. It is a set-theoretic
assumption with ambient cardinal-arithmetic consequences.** INFERRED: I
built no model, exactly as the target says of itself
(`lj-1.305-report.md:233-237`). **The target's INFERRED marking is
CORRECT and I could not upgrade it to MEASURED.** What I add is the
named classical obstruction, which the target does not have.

### 4.2 Does it reach the AC closure?

**NO, MEASURED, on DD4's own axis (`scripts/measure/ledger.py:50`).**

- **MEASURED: `InjData` occurs zero times in `src/`.** It is probe-only.
- Import closures computed with `ledger.py`'s own `closure()` over the
  declared roots (`dev/ledger.toml:170`, `:203`):

| master | AC closure | GCH closure |
|---|---|---|
| `src/L/Ordinal/SquareLaw.lagda.md` | NO | YES |
| `src/L/Cardinal.lagda.md` | NO | YES |
| `src/L/Coding/Injection.lagda.md` | NO | YES |
| `src/L/Absorption.lagda.md` | NO | YES |
| `src/L/InjChain.lagda.md` | NO | YES |
| `src/L/BoundedSubset.lagda.md` | NO | NO |
| `src/L/WellOrder/Base.lagda.md` | YES | YES |
| `src/L/Choice/Step.lagda.md` | YES | YES |

Every import the descent adds lands GCH-only. **So `InjData` does not
touch the delivered `L ⊨ AC` proof today, and the first trophy is not
re-priced.**

**TWO CAVEATS, and both are the ledger's own.**
`dev/ledger.toml:204` says the GCH closure is read from a STATEMENT whose
proof is not wired, so it UNDERSTATES. `src/L/BoundedSubset.lagda.md` is
in NEITHER closure today and it is where the square law is actually
consumed. **So the GCH side will grow when `[LJ-1.8]` lands, and the
answer above is for today's tree.**

**The AC side is NOT understated**: `ac_root` is the delivered endpoint
`src/L/Model.lagda.md` (`dev/ledger.toml:170-171`), a proof and not a
statement. **So「`InjData` does not reach the AC end」rests on a real
closure, not on a hypothesis-shaped one.**

### 4.3 The reading cost (DD9)

**A module parameter is a permanent reading cost on every consumer.**
`InjData` as a parameter of the descent's master makes every downstream
import carry a set-theoretic assumption in its type. `Base.Classical`'s
doctrine (`src/Base/Classical.lagda.md:52-57`) is what makes that
acceptable for `lem`: the debt is visible at every import.

**The asymmetry the target does not price:** `lem` is a LOGICAL
assumption that the reader already carries for the whole tree.
`InjData` is a SET-THEORETIC assumption at one family, and section 4.1
says it is not implied by `lem`. **A reader who sees two parameters must
now ask which theorems need which**, and the tree has no device that
answers it.

## 5. ATTACK 5: THREE SITES OR ONE DEBT?

**REFUTED. They are TWO debts, and one of the three named sites is not a
debt at all. MEASURED.**

The target's sweep (`lj-1.305-report.md:175-180`) reads: the refuted
shape is「a truncated classical existence whose payload is data」, found
at `src/L/Cardinal.lagda.md:132` and `:256`, plus the descent, and「one
ruling on `InjData` covers all three」.

| site | payload | discharged today |
|---|---|---|
| `src/L/Cardinal.lagda.md:132-134`, `κ-inj` | AMBIENT injection, a function | **NO.** No `SWO` reaches it |
| `agents/tasks/LJ-1-301/Descent.agda:163-175`, J1 | the same | **NO.** Same debt |
| `src/L/Cardinal.lagda.md:256-258`, `δ-inj` | `Σ[ F ∈ Mem (Lset β) ] InjCode ...` | **YES, MEASURED** |

**Why `:256` is different.** Its payload is a `Σ` whose FIRST component
ranges over a WELL-ORDERED carrier, `Mem (Lset β)`, and whose SECOND
component is a PROPOSITION, `InjCode`. That is exactly `leastOf`'s shape.
`agents/tasks/LJ-1-314/CodeUntrunc.agda:99-104` untruncates it, green,
with `lem` and `orderAt` only, both already in `L.Cardinal`'s telescope.

**The shape the target swept by is too coarse.**「payload is data」does
not discriminate. The discriminating property is「does the data live in a
well-ordered carrier under a propositional payload」. **That is the C-42
lesson at this site: a refutation measures the site it names, and the
NAME must be the discriminating property, not a family resemblance.**

**A fourth citation is loose.** The target cites「the gate `[LJ-1.156]`
registered at `dev/PLAN.md:1068`」. **MEASURED: that row records a SIZE
and TIME gate,「the new gate is LeastCardInj: 44 lines, 100.64 s」, and
names no truncation.** The `[LJ-1.299]` citation at
`agents/tasks/LJ-1-299/lj-1.299-report.md:209-218` is CORRECT: it does
frame the same choice, in those words.

**So the owner is being asked for one ruling where the honest count is
one ruling and one repair.** The repair is `:256`, and it is free.

## 6. DD4, AND MY AXIS (C-46)

**MY AXIS IS AC-AGAINST-GCH, DD4's own, fixed in code at
`scripts/measure/ledger.py:50`.**

**The target's DD4 claim is:「the descent names no tower, is
tower-blind, lands in the GCH closure under P-k, and both proofs share it
wholesale」.**

- **Tower-blind: VERIFIED.** `Untruncated.agda` names no stage
  presentation. Its type-level vocabulary is `V ℓ`, `IsOrd`, `_∈ˢ_`,
  `⟪_⟫`, `_↪_`. P-l is satisfied: nothing transparent about a stage
  enters a statement.
- **Lands in the GCH closure: VERIFIED**, section 4.2's table. Every
  descent import is GCH-only except `L.WellOrder.Base` and
  `L.Choice.Step`, which are already SHARED.
- **「Both proofs share it wholesale」: NOT VERIFIED, and MEASURED
  otherwise.** The AC closure does not contain the square law today, at
  any master. `ledger.py --reuse` prints AC 73 masters and 17,197 lines,
  GCH 51 and 9,967, SHARED 44 and 7,632, 39.1 percent. **The descent
  adds lines to the GCH side and to the SHARED side only if a consumer
  on the AC side appears, and none exists today.** The claim is a
  PREDICTION about a proof that is not wired, not a measurement.
- **`dev/ledger.toml:204` applies and I state it:** the GCH closure is
  read from a STATEMENT, so it UNDERSTATES, and the understatement sits
  in the GCH total and not in the intersection.

**The DD4 consequence of this review is positive.** Section 1.3's route
runs on `L.Coding.Injection` and `L.Choice.Step`, and `L.Choice.Step` is
SHARED. **A coded discharge reuses the AC wing's own selection machinery;
an ambient `InjData` reuses nothing.**

## 7. WHAT I DID NOT DO

- **No master was touched.** Nothing under `src/`, `dev/` or `AGENTS.md`.
  My writes are `agents/tasks/LJ-1-314/lj-1.314-report.md` and
  `agents/tasks/LJ-1-314/CodeUntrunc.agda`.
- **`agents/tasks/LJ-1-305/` was NOT edited.** Two of its files were
  RE-RUN, `NotProp.agda` and `Untruncated.agda`, both green.
- **No independence model was built** for `InjData` against `lem`.
  Section 4.1 is INFERRED and says so.
- **The composite `BoundedToCode → InjData` was not built**, only its
  atom (`bridge→data`) and the member half separately. Section 1.4.
- **No countermodel was built** for the least-code spelling being an
  hProp; `isPropLeastOf` is a delivered THEOREM and I cite it, not a
  model I made.
- **`make check` not run**, as the brief orders.
- **No `dev/` figure was edited.**

## 8. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap
never raised. **Slots counted before every invocation with
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`.** The machine
was NOT quiet: the 1-minute load moved between 4.74 and 6.65.

| run | slots before | exit | elapsed s | 1-min load |
|---|---:|---:|---:|---:|
| `LJ-1-305/NotProp.agda`, re-run | 0 | **0** | **3** | 6.65 |
| `CodeUntrunc.agda`, `isProp×` not in scope | 0 | 42 | 2 | 5.24 |
| `CodeUntrunc.agda`, wrong module for `isProp×` | 0 | 42 | 2 | 4.92 |
| `CodeUntrunc.agda`, parts 1 to 4 | 0 | **0** | **3** | 4.74 |
| `CodeUntrunc.agda`, with part 5 | 0 | **0** | **2** | 5.11 |
| `LJ-1-305/Untruncated.agda`, re-run | 0 | **0** | **3** | 5.00 |

**MEASURED FALSE: any invocation past 30 minutes.** The longest was 3 s.
**MEASURED FALSE: any heap exhaustion.** C-51's medicine was not needed,
because this probe uses projections and never a `with`-pattern on a
record-returning function.

**Sizes, counted as non-blank lines:** `CodeUntrunc.agda` 135,
`agents/tasks/LJ-1-305/Untruncated.agda` 322. The second matches the
target's own figure exactly.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-305/lj-1.305-report.md`, read WHOLE.** Line read
  `:233-237`,「Necessity is MEASURED at the eliminator level and INFERRED
  at the theory level」. TAKEN: the exact claim under review, and the
  admission that no model was built.
- **`agents/tasks/LJ-1-301/lj-1.301-report.md`.** Line read `:128`, the
  section 4 heading「WHY TRUNCATED, AND WHAT THE UNTRUNCATED FORM OWES」.
  TAKEN: the two data-consuming branches, and that the non-initial one is
  the recorded wall.
- **`agents/tasks/LJ-1-299/lj-1.299-report.md` and `NoInj2.agda`.** Line
  read `NoInj2.agda:131-133`, the `AmbientToCode` type. TAKEN: the exact
  spelling, and the measurement that it returns `Σ[ F ∈ S ]` unbounded,
  which is why `leastOf` cannot take it (section 1.4).
- **`agents/tasks/LJ-1-300/lj-1.300-report.md`.** Line read `:198`,
  「INFERRED: `AmbientToCode` is TRUE whenever the ambient universe
  satisfies V = L」. TAKEN: INDEPENDENT is the right word, so section
  1.5 does not call the residue false.
- **`archive/dev/TASKS-archived.md`, read for SHAPE and never a claim.**
  Line read `:298`, the `L3.32-T156` row,「General beta is AC-forced by
  the choice quantifier; all five terms stay BOTH」. TAKEN, SHAPE ONLY:
  the retired route priced a choice-shaped obligation by RE-SPLITTING the
  terms rather than by admitting a principle. **WHAT WOULD NOT TRANSFER:**
  that obligation lived inside one device's own telescope; this one is a
  face crossing between an ambient universe and a coded model, and the
  retired route had no such crossing.

## 10. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`.** Lines read `:259-264`, Step D:
  「a definable well-order of L_α, used to pick the `<_L`-least witness of
  each formula」, with the leastness encoded as
  `φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`. Also `:275-284`, Step F, which
  consumes `|L_α| = |α|` for infinite α as an INPUT.

  **TAKEN, and it settles attack 1 from the outside.** **Devlin needs
  nothing of `InjData`'s shape at the corresponding step, and the reason
  is exact: his object to be selected is an ELEMENT of `L_α`, and `<_L`
  orders elements.** His least-witness trick makes the selected object
  UNIQUE, which is why no choice is spent: uniqueness is a proposition.
  **That is the same device as `isPropLeastOf`
  (`src/L/WellOrder/Base.lagda.md:136-144`), and it is why my section 1.3
  probe is green.**

  **So Devlin's well-order DOES do the work our truncation blocks, but
  only after the object is an element of the model.** The port's residue
  is therefore not a missing choice principle in the mathematics. It is
  the ambient-to-code crossing, and it exists because this development
  builds `L` inside an ambient `V` that Devlin does not have.

- **WHY NOT the rest of the digest.** Sections 1.4, 2.5, 2.7, and the
  errata and Jech cross-check: they cover the counting, the Σ₁ transfer
  and the OCR corrections. None touches selection of a function, data
  against proposition, or truncation.

## 11. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **`InjData` IS DERIVABLE from delivered machinery. HALF-FIRES.** The
  MEMBER half is derivable and already delivered
  (`src/L/Cardinal.lagda.md:116-134`). The INJECTION half is not, at the
  ambient face. Section 1.
- **IT IS NECESSARY AND I MEASURE WHY. FIRES.** The side condition is
  `P : A → hProp` at `src/L/WellOrder/Base.lagda.md:159`, plus the
  MEASURED absence of any `SWO` on a function type. Section 1.2.
- **THE AMBIENT FACE AVOIDS IT. DOES NOT FIRE.** It cannot supply
  `SqShape` at any face, because the delivered consumers need every
  ordinal below the site. Section 2.2.
- **IT IS A CHOICE PRINCIPLE TOUCHING THE AC END. DOES NOT FIRE.**
  MEASURED: zero occurrences in `src/`, and every import the descent adds
  is GCH-only. Section 4.2.
- **A WALL. DOES NOT FIRE.** Longest invocation 3 s. Section 8.

## 12. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check`: exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check`: exit 0.
- **MEASURED: no em dash in any file I wrote** (grep, zero hits in all
  three files of `agents/tasks/LJ-1-314/`).
- `.venv/bin/python scripts/dispatch/rules.py --for review`: run, and
  `dev/LESSONS.md:1333` (D-10) opened in full.
- Every agda invocation under `GHCRTS="-A64m -I0 -M8g"`, one process at a
  time, slots counted first, cap never raised.

## 13. FOR THE ORCHESTRATOR

1. **Do not put「admit a new principle」to the owner.** Put the CARDINAL
   FACE, which is already question two on the owner's list at
   `dev/PLAN.md:410-431`. `InjData` is the ambient-side patch for that
   same crossing, and section 1.4 measures the coded-side discharge.
2. **One free repair is available now:** `src/L/Cardinal.lagda.md:256-258`
   can export untruncated data. `CodeUntrunc.agda:81-104` is the term, 24
   non-blank lines, green in 2 s. **It is not part of any ruling.**
3. **The ambient face buys nothing toward `SqShape`.** Section 2.2 is the
   measurement the fork was missing.
4. **`[LJ-1.305]`'s green build stands** and I re-ran it: exit 0, 3 s,
   load 5.00.
5. **One lesson candidate, at your numbering.** A refutation swept by
   「payload is data」over-reaches; the discriminating property is
   「payload is a proposition over a well-ordered carrier」. Section 5
   measures the over-reach and the probe repairs the site.
