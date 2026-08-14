# LJ-1.240 report: DD25 review of `[LJ-1.239]`

tier: opus (deepseek-subagent-mode). The switch's ADVERSARIAL row. The target's
author is pi, so DD17's invariant holds.

**No Agda run. No master, brief or report edited. No commit, no push. No
`make check`.** Every negative is marked **MEASURED** or **INFERRED**. Written
incrementally (C-22).

## 0. VERDICT

**UPHELD.**

**NO. `sl` and `sc` are NOT green over an uninhabitable hypothesis. The
hypothesis is inhabitable, `[LJ-1.237]`'s type is the right type, and what
`[LJ-1.239]` refuted is the four-step RECIPE, not the type.**

**The refutation is correct at every point I could check. The escalation is
not.** `[LJ-1.239]` wrote 「the `lh` type as stated is not instantiable **by the
cited pieces**」 (`agents/tasks/LJ-1-239/lj-1.239-report.md:23-24`). The brief
drops the last four words (`agents/tasks/LJ-1-240/LJ-1.240.md:16`), and
`dev/PLAN.md:47` then reads 「`[LJ-1.239]` REFUTED `lh`'s TYPE」 and 「`sl` and
`sc` may be green over an uninhabitable hypothesis」. **That escalation is
FALSE. MEASURED at the source.** The report is not the defect. The brief and
the screen are.

**This is NOT a seventh 「UPHELD BUT MISATTRIBUTED」.** `[LJ-1.239]` attributed
the cause correctly, to the recipe. The misstatement of the refutation's TARGET
happened after the report, in the brief and in the screen (C-42: a refutation
measures the site it names, never its extent).

| claim | my verdict |
|---|---|
| the stage level-hood carries arity `4 + n` | **UPHELD. MEASURED.** `src/L/BoundedSubset.lagda.md:108` |
| `lh` demands arity 2 | **UPHELD. MEASURED.** `agents/tasks/LJ-1-237/ProbeLJ1237A.agda:128`, `:180` |
| the four cited steps do not close the gap | **UPHELD. INFERRED**, and no line of `src/` contradicts it |
| the numeral-closure is the missing term | **UPHELD**, with one refinement in section 3 |
| the `lh` type is not instantiable | **REFUTED. INFERRED.** the arity-2 target is reachable, and Devlin states it at arity 2 |
| `sl`/`sc` stand on an uninhabitable hypothesis | **REFUTED. MEASURED** at three definitional clauses, section 2 |
| the floor no longer describes `sl` and `sc` | **REFUTED. MEASURED.** `sl` and `sc` do not change, section 3 |
| 「No delivered piece does this」, of the numeral-closure | **REFUTED for the corpus. MEASURED.** the archive holds the shape, section 4 |

**THE ARCHIVE DECIDES THIS REVIEW, AND TWO REPORTS DECLINED IT.** The retired
route WROTE an arity-2 constant-free level-hood and read it at a set carrier
through the same `embed` architecture. **Section 4 gives it at `file:line`.**
`[LJ-1.237]:191-194` and `[LJ-1.239]:170-172` both record the archive as
**NOT read**. Both said so plainly, which is honest. **Both were wrong that it
did not bear.**

## 1. QUESTION 1: IS THE ARITY CLAIM CORRECT?

**YES, and I re-derived both halves at the source.**

**The arity. MEASURED.** `src/L/BoundedSubset.lagda.md:108` declares
`levelHoodB : Formula CS.S (suc (suc (suc (suc n))))`. That is arity `4 + n`.
The module header at `:74-76` takes 14 tag slots into `Fin (5 + n)` and 14 more
into `Fin (7 + n)`. `src/L/BoundedSubset.lagda.md:847-849` names the four
structural slots: `w ∷ v ∷ γ ∷ K ∷ []`.

**2 is what `lh` demands. MEASURED.** `ProbeLJ1237A.agda:128` declares
`φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2`. `:180` reads it at the two-element environment
`(v ∷ b ∷ [])`.

**The constant-free measurement. MEASURED, and narrower than the report says.**
`ProbeLJ1239A.agda:66-67` proves `countFo LH0.matrix ≡ zero` by `refl`. But
`LH0` is `LevelHood0` instantiated with 28 `zero` arguments
(`ProbeLJ1239A.agda:57-59`). So the measurement is at `n = 0` with every tag
slot aliased to slot zero. The probe's own comment says the shape is degenerate
(`agents/tasks/LJ-1-239/lj-1.239-report.md:79-80`). **The `refl` is real; its
generality is not measured.** INFERRED that `countFo` is independent of the slot
arguments, because a slot is a `var` and `countTm (var i) = 0`
(`src/FOL/Count.lagda.md:594-596`).

**The refused `refl` on `countFo LsetGraph ≡ 0`. NOT RE-DERIVED. INFERRED
TRUE.** I did not run Agda, so I could not reproduce the error type. The
supporting fact is at `src/L/Coding/Model.lagda.md:586`:
`tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ ...)` uses `con`, so the
class-carrier chain carries constants.

**ONE CORRECTION TO THE REPORT'S ARITHMETIC.** `[LJ-1.239]` says the twelve tags
「need `n ≥ 7` before the twelve tags can be distinct」
(`lj-1.239-report.md:78-79`). I get a higher floor. The tag slots index the body
environment of arity `5 + n`. Four of those slots are structural: slot 0 is the
bound witness `w`, slot 1 is `v`, and `src/L/BoundedSubset.lagda.md:105` passes
slots 0, 2 and 3 to `GraphB`. Twelve distinct tags therefore need
`5 + n - 4 ≥ 12`, so **`n ≥ 11` and arity `≥ 15`. INFERRED**, by reading the
slot arguments at `:105` and `:110-111`. Neither figure is typechecked. **The
discrepancy does not change any conclusion**, because both floors are far above
2.

## 2. QUESTION 2: WHOSE DEFECT IS THE TYPE?

**NEITHER HORN. The brief offers a false dichotomy, and the third state is the
true one: the type is fine, the recipe is wrong, and the hypothesis is
UNDISCHARGED rather than UNINHABITABLE.**

**`φ₀` is a MODULE PARAMETER, not a fixed formula. MEASURED.**
`ProbeLJ1237A.agda:127-129` opens `module StageLH (α : S) (ordα : IsOrd α)
(φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)`. `:178-181` opens `module Build (lh : ...)`
inside it. So `lh`'s type is a FAMILY indexed by `φ₀`. 「Uninhabitable」 is not
even well formed for the family. It is well formed only after `φ₀` is fixed.

**The family is not everywhere empty. MEASURED at three clauses.** Take
`φ₀ := ⊤̇`. Then:

1. `embed = mapFo Empty.rec*` (`src/FOL/Manipulation/Relabelling.lagda.md:117-118`).
2. `mapFo f ⊤̇ = ⊤̇` (`src/FOL/Manipulation/Relabelling.lagda.md:62`).
3. `γ ⊨ ⊤̇ = ⊤` (`src/FOL/Semantics.lagda.md:98`).

So `⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed ⊤̇ ⟩` reduces to `⟨ ⊤ ⟩`, and
`lh = λ v b ob e → tt*` inhabits the type. **The three clauses are MEASURED at
the source. The composite reduction is INFERRED**, because I did not run Agda.
**Section 6 names the one-line probe that would make it MEASURED.**

**So C-38's extension does not fire here.** A green build over an uninhabitable
hypothesis is the failure this review exists to catch, and this is not that
failure. `sl` and `sc` prove a real implication: for EVERY `φ₀` and EVERY `lh`
that supplies it at the stage, `sl` and `sc` follow. That is DD4's 「write it
generic」 working as designed, not a false green.

**The danger is real but it sits elsewhere.** `[LJ-1.178]`'s consumer takes
FOUR hypotheses over the same `φ₀`, not one: `ProbeLJ1178A.agda:489-493` lists
`sl`, `sc`, `s₁ : Σ₁ Cr.φP` and `amb : AmbientRead`. `AmbientRead` is the
soundness direction, at `ProbeLJ1178A.agda:190-192`:

```agda
AmbientRead = (v b : S) → IsOrd b
            → ⟨ (v ∷ b ∷ []) Cr.AbsP.⊨ᵛ Cr.φP ⟩ → v ≡ Lset b
```

**MEASURED.** `lh` is the decode-IN direction only
(`agents/tasks/LJ-1-237/lj-1.237-report.md:74-75`). `amb` is the decode-OUT
direction. **A junk `φ₀` satisfies `lh` and kills `amb`.** So the joint
constraint 「some `φ₀` supplies `lh` AND `amb` AND `s₁`」 is what has real
content, and no report in this chain has priced `amb`. **That is the finding the
screen should carry, in place of 「uninhabitable」.**

## 3. QUESTION 3: CAN `lh` BE RESTATED, AND WOULD `sl`/`sc` SURVIVE?

**`lh` DOES NOT NEED RESTATING. Arity 2 is the right arity, and `sl` and `sc`
cost ZERO. MEASURED.**

**Why arity 2 is right.** Devlin states the level-hood at arity 2. His (a) is
`∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]` (`dev/literature/devlin-II5.md:95-96`). `Φ` is
arity 3 and `∃z Φ` is arity 2. `[LJ-1.237]`'s `φ₀ : Formula (⊥*) 2` is the
faithful transcription. **MEASURED** at both lines.

**Why the arity gap does not force a retype.** Two instruments exist and they
behave differently.

- `absFo : Formula K n → Formula (⊥*) (n + countFo φ)`
  (`src/FOL/Manipulation/Parameters.lagda.md:260`). This RAISES arity, and it is
  the instrument the brief's DIFFICULTY names.
- `erase : (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥*) n`
  (`src/FOL/Count.lagda.md:598`). This PRESERVES arity.

**`erase` is the right instrument for `levelHoodB`, because `levelHoodB` has
`countFo ≡ 0`.** The tree says so in its own words:
`src/L/Condensation.lagda.md:1469-1471` reads 「every formula in this chain is
constant-free and `countFo ≡ 0` by refl and the erase route opens at the hull」.
**MEASURED.** So the constant problem costs no arity at all, and `absFo` is a
detour.

**Binding the extra slots is a delivered idiom.** `src/L/BoundedSubset.lagda.md:855-856`
writes `Σ₂ = ∃̇ (∃̇ (∃̇∈ (var (suc (suc zero))) LH.levelHoodB))`, which closes
`levelHoodB` from arity 4 down to arity 1. `:864-869` writes `reverse` the same
way with a `renameFo (padRight ...)`. **So the descent from `4 + n` to 2 is one
binder LESS than a construction the tree already carries. MEASURED.**

**What genuinely remains: the numeral-closure, and it is owed to `amb`, not to
`lh`.** I attacked `[LJ-1.239]` section 3 and my attack FAILED, which is the
result worth recording. My attack was: for `lh` alone, binding the tag slots
without defining them is enough, because `lh` only PROVES a satisfaction and can
supply the real numerals as witnesses. **That attack dies at
`ProbeLJ1178A.agda:190-192`**: `amb` needs the reading to IMPLY `v ≡ Lset b`, so
an unconstrained tag would satisfy the formula at a wrong `v`. **So
`[LJ-1.239]` section 3 stands: each tag must be DEFINED inside the formula.
MEASURED, at the consumer.** The refinement is only about WHERE the cost lands:
on `amb`, not on `lh`.

**The closure is constructible in this syntax. INFERRED.** The finite ordinals
are Δ₀ and constant-free: 「x is empty」 is `∀̇∈ (var x) ⊥̇`, and 「y is the
successor of x」 is a conjunction of two `∀̇∈` and one `∈̇`. All are in the
constructor list at `ProbeLJ1237A.agda:29-31`. So twelve nested definitions plus
twelve `∃̇` give a constant-free arity-2 `φ₀`. **I did not write it and I did not
price it.** The brief forbids pricing the assembly, so I name the probe in
section 6 instead.

**`sl` and `sc` COST NOTHING. MEASURED.** They mention `φ₀` only as the abstract
parameter, at `ProbeLJ1237A.agda:190`, `:204`, `:230`, `:241` and `:251`. Every
construction over it is generic: `wk23` (`:107-109`), `coverForm` (`:113-117`),
`ag` (`:233-235`). **If `φ₀` stays at arity 2, `sl`'s 14 lines and `sc`'s 38
lines are untouched.** The restatement happens INSIDE the definition of `φ₀`,
never in the type of `sl` or `sc`.

**THE FORK, and I surface it with a recommendation.** Two routes reach a
supplied `φ₀`, and they differ exactly on whether `sl`/`sc` survive.

| route | what it does | cost to `sl`/`sc` |
|---|---|---|
| **A. numeral-closure inside `φ₀`** | define the twelve numerals inside the formula, then bind them | **ZERO.** arity stays 2 |
| **B. numerals in the environment** | keep the house style, carry the tags in slots, pay 「the slot holds the numeral」 at the site (`src/L/Condensation.lagda.md:1469-1471`) | **`sl`, `sc`, `coverForm` and `module Whole` all restate at arity `2 + 12`** |

**I recommend ROUTE A.** Three reasons, each at `file:line`. First, `sl`, `sc`,
`coverForm`, `Crossing` and `module Whole` are all written at arity 2 already
(`ProbeLJ1237A.agda:113`, `ProbeLJ1178A.agda:123-124`, `:489-493`). Second, Devlin's
shape is arity 2 (`dev/literature/devlin-II5.md:95-96`). Third, route B does not
avoid the work; it moves the same site fact to every consumer instead of paying
it once. **INFERRED**, from the consumer count.

## 4. THE ARCHIVE: THE SHAPE ALREADY EXISTS (DD18)

**The brief said 「Take SHAPE from the archive, never a claim」. I did, and the
archive settles question 3. I opened every file below myself and read the lines
I cite. MEASURED.**

**THE RETIRED ROUTE WROTE AN ARITY-2 CONSTANT-FREE LEVEL-HOOD.**
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:600-601`:

```agda
levelStory : Formula (⊥* {ℓ}) 2
levelStory = Ap ∧̇ (Cl ∧̇ Rg)
```

**Constant domain `⊥*`. Arity 2. Exactly the type `[LJ-1.237]` gives `φ₀`.**

**IT READ IT AT BOTH CARRIERS BY `embed`, WHICH IS `[LJ-1.237]`'s OWN
ARCHITECTURE. MEASURED.** `:768-769` gives `σᴹ : Formula Sᴹ 2`,
`σᴹ = embed levelStory`, at the SET carrier
`AbsM = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ M) Mtr` (`:127`). `:823-824`
gives `σL : Formula Sʟ 2`, `σL = embed levelStory`, at the CLASS carrier. One
formula, two carriers, no arity change.

**AND IT WROTE BOTH DIRECTIONS AT THE SHAPE OF `lh` AND `amb`. MEASURED.**
`:163-164` and `:167-169`:

```agda
Believes : Formula Sᴹ 2 → Sᴹ → Sᴹ → Type (ℓ-suc ℓ)
Believes φ v b = ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩

CrossOut : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b
           → fst v ≡ Lset (fst b)
```

**`Believes` is `lh`'s conclusion. `CrossOut` is `amb`.** The live probe writes
the same pair at `ProbeLJ1237A.agda:180` and `ProbeLJ1178A.agda:190-192`.
**So the arity-2 statement is not a hopeful abstraction. It is a shape this
project has written before, at a set-sized carrier.**

**THE NUMERAL-CLOSURE'S TWO PRIMITIVES ARE WRITTEN, AND BOTH ARE CONSTANT-FREE.
MEASURED.**

| primitive | file:line | type | constant |
|---|---|---|---|
| the ordinal zero, pinned inside the formula | `archive/.../L/Condensation.lagda.md:529-531` | `zeroForm : Formula (⊥* {ℓ}) 2` | **none** |
| the successor atom 「k = suc a」 | `archive/.../L/LevelKit.lagda.md:567-571` | `sucAt : {n} → Fin n → Fin n → Formula ⟪ u ⟫ n` | **none** |
| 「is an ordinal」 | `archive/.../L/Condensation.lagda.md:441-442` | `isOrdAt : {n} → Fin n → Formula (⊥* {ℓ}) n` | **none** |
| 「is a limit ordinal」 | `archive/.../L/Condensation.lagda.md:449-451` | `isLimitAt : {n} → Fin n → Formula (⊥* {ℓ}) n` | **none** |

`zeroForm` binds a slot and pins it by 「it has no member」,
`¬̇ (∃̇∈ (var f0) ⊤̇)`. `sucAt` pins a slot as the successor of another slot.
**Zero plus eleven successors is the twelve-numeral closure. Both primitives
exist, both are Δ₀, and neither costs a constant.**

**SO `[LJ-1.239]` SECTION 3 IS CORRECT ABOUT `src/` AND WRONG ABOUT THE
CORPUS.** It writes 「No delivered piece does this」
(`agents/tasks/LJ-1-239/lj-1.239-report.md:86-87`). True of `src/`. **FALSE of
`archive/`. MEASURED.** The agent stated the archive as NOT read
(`:170-172`), so this is a gap in coverage and not a false claim.

**WHAT THE ARCHIVE DOES NOT GIVE, and I say so plainly.** Three limits.

1. **`CrossOut σᴹ` is never applied in the file. INFERRED**, from the subagent's
   sweep and from `module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ)`, which
   takes the crossing as a HYPOTHESIS. **So the archive gives the SHAPE and
   leaves the same obligation open.** It is a precedent, never a discharge.
2. **`Cl = ⊤̇`. MEASURED** at `archive/.../L/Condensation.lagda.md:592-593`. The
   closure clause of `levelStory` is EMPTY, so `levelStory` is a frame with one
   clause unwritten.
3. **A slot-role conflict. MEASURED.** `:598-599` reads the two slots as 「the
   witness f at variable zero, the read member x at variable one」. `:166-167`
   reads the same arity-2 type as 「a believed value at an ordinal index」.
   **The two readings are not the same. Nothing in the file reconciles them.**

**THE NET.** The archive does not supply `lh`. It supplies the ANSWER TO
QUESTION 3: an arity-2 constant-free level-hood at a set carrier is a shape this
project has already written, and the numeral-closure's primitives are written
too. **That is what turns 「the type is not instantiable」 from an open worry
into a refuted claim.**

## 5. QUESTION 4: DID THE BRIEF CAUSE IT?

**The brief's object WAS wrong, `[LJ-1.239]` caught it, and the cost to the
agent was small. The cost to the RECORD was larger.**

**The wrong object. MEASURED.** `[LJ-1.237]` section 2 names the difficulty at
`LsetGraph`, the UNBOUNDED class-carrier formula
(`agents/tasks/LJ-1-237/lj-1.237-report.md:100-108`). Step 4 operates on
`graphBndAt` / `levelHoodB`, the BOUNDED matrix. `[LJ-1.239]` measured the
difference and said so (`lj-1.239-report.md:42-46`). **C-44 worked.**

**What it cost the agent: one measurement and one instrument name. INFERRED.**
The probe is 67 lines and ran at 2.42, 2.41 and 2.25 seconds
(`lj-1.239-report.md:117`), so budget was never the limit. The agent spent one
measurement on the refused `refl` for `LsetGraph`, which the conclusion does not
need.

**What it cost the RECORD: the wrong instrument reached section 3.** Following
the brief, `[LJ-1.239]:20-22` names `absFo` as the parameter-free form, and
concludes 「Both readings agree: the stage level-hood formula has arity greater
than 2」. For `levelHoodB` the right instrument is `erase`, which raises no
arity (`src/FOL/Count.lagda.md:598`). **The conclusion survives, as the brief
predicted. The stated REASON does not.** The arity is `4 + n` because the tag
slots are open, never because a constant abstraction raised it. **MEASURED.**

**The brief's own restatement is the larger defect.** `LJ-1.240.md:16` drops
「by the cited pieces」, and `dev/PLAN.md:47` then carries 「REFUTED `lh`'s
TYPE」 and 「uninhabitable hypothesis」. **Neither phrase appears in
`[LJ-1.239]`. MEASURED**, by reading the report whole.

## 6. `lh`'s RIGHT TYPE, AND THE PROBE

**`lh`'s right type is the type `[LJ-1.237]` already wrote.**

```agda
lh : (v b : SL) → IsOrd (fst b) → fst v ≡ Lset (fst b)
   → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩
```

`agents/tasks/LJ-1-237/ProbeLJ1237A.agda:178-180`. **It should stay in the
screen unchanged.** What must change beside it is the RECIPE: four steps become
five, and the fifth is the numeral-closure.

**TWO PROBES, both syntax only, both cheap, neither needing a carrier move.**

**PROBE 1, the decisive one: build a constant-free arity-2 `φ₀`.** Write the
twelve numeral definitions as Δ₀ constant-free formulas, take
`erase levelHoodB _` at a correct `n`, rename `v` and `γ` into slots 0 and 1,
and existentially close everything else. Report GO or NO-GO on
`φ₀ : Formula (⊥*) 2` plus its `Δ₀` or `Σ₁` certificate. **This is the widest
unmeasured term (DD8), and it prices the fifth step.** It touches no carrier and
no stage, so it cannot hit the three walls.

**PROBE 1 SHOULD START FROM THE ARCHIVE, NOT FROM A BLANK FILE.** Section 4
gives the two primitives at `file:line`: `zeroForm`
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:529-531`) and `sucAt`
(`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md:567-571`). **Both are
constant-free and both carry a Δ₀ witness.** The brief for probe 1 must carry an
ARCHIVE section naming them. **Two consecutive reports missed them by declining
the archive; a third must not.**

**PROBE 2, one line, and it closes this review's own gap.** Instantiate
`module Build` with `φ₀ := ⊤̇` and `lh := λ v b ob e → tt*`. If it typechecks,
「the hypothesis is inhabitable」 turns from INFERRED to MEASURED. **Run it
inside probe 1's file, not as a separate process (C-12).**

**PROBE 2b, optional: settle the tag floor.** Measure the least `n` at which
twelve distinct tag slots fit, and close the `n ≥ 7` against `n ≥ 11`
discrepancy of section 1.

## 7. C-42 BOTH DIRECTIONS

**DOES IT REACH FURTHER THAN `lh`? NO for `sl` and `sc`. YES for the total.**

**The floor still describes `sl` and `sc`. MEASURED.** `[LJ-1.228]:16-18` prices
`sl` at about 0.15k and `sc` at about 0.15k, joint 0.25k to 0.35k, on
`[LJ-1.123]`'s bands (`lj-1.228-report.md:110-126`). Section 3 above measures
that `sl` and `sc` do not change under an arity-2 `φ₀`. **So the floor is not
disturbed at the two objects it prices.**

**What the floor never covered is `amb`, and it still does not. MEASURED.**
`[LJ-1.228]` priced `sl`, `sc` and the shared decode. `ProbeLJ1178A.agda:493`
shows `amb` as a fourth, separate hypothesis of `module Whole`. The
numeral-closure is owed to `amb`. **So `[LJ-1.239]`'s last table row is right in
DIRECTION, UP, and wrong in LOCATION: the unpriced layer sits on `amb`, not on
`sl` or `sc`. INFERRED.**

**DOES IT REACH LESS FAR? MUCH LESS FAR, and by more than step 1.**

**Step 1 is untouched. MEASURED.** `ProbeLJ1239A.agda:46-48` reads
`LsetGraphAt zero (suc zero)` at the two-element environment `(v ∷ b ∷ [])`, at
the CLASS carrier `AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`
(`ProbeLJ1239A.agda:37`). That formula is arity 2 and it carries constants, so
the arity finding cannot touch it. The `.agdai` is on disk at
`_build/2.8.0/agda/agents/tasks/LJ-1-239/ProbeLJ1239A.agdai`. **MEASURED.**

**Steps 2 and 3 are untouched. INFERRED.** `graph-in` and
`hasReplacementL-bound` are about placement and bounding. Neither statement
mentions the tag slots (`lj-1.239-report.md:53-67`).

**THE STRONGEST 「LESS FAR」 FINDING, WHICH NO REPORT IN THIS CHAIN STATES:
the `4 + n` object has ZERO consumers in `src/`. MEASURED**, by
`grep -rn "LevelHood" src/`, which returns exactly three lines:
`src/L/BoundedSubset.lagda.md:74` (the module), `:840` (`LevelHood0`) and `:844`
(the one alias inside it). **`LevelHood0` is consumed nowhere in `src/`.**
`[LJ-1.228]:13-14` recorded the same fact for `Σ₂`: 「`LevelHood0.Σ₂` is defined
and unconsumed」. **So the refutation reaches no delivered line of `src/` at
all.** It is about an unconsumed design sketch and about a recipe on a
whiteboard. Nothing green depends on it.

**COROLLARY, and it is uncomfortable.** The tree has never instantiated
`LevelHood` at a correct `n`. The only instance is `LevelHood0` at `n = 0`,
where twelve distinct tags cannot fit (section 1). **So the `4 + n` object is
not a delivered level-hood; it is an unvalidated frame. MEASURED.** Probe 1
would be the first thing to instantiate it correctly.

## 8. DD4

**The `4 + n` finding does NOT change which half `lh` sits in. MEASURED.**

`lh` was already the per-tower instantiation point
(`agents/tasks/LJ-1-237/lj-1.237-report.md:96-98`), and the joining layer above
it costs ZERO to write generic (`:112-117`). Section 3 measures that the layer
still costs zero, because `φ₀` stays at arity 2.

**The numeral tags are Def-tower content and the J tower will not owe them.
MEASURED at the literature.** `dev/literature/devlin-II5.md:375` is row C2:
「Def: satisfaction bound K(u) or its coding analogue; J: the sixteen op-graphs,
**syntax-free**」. The tag numerals index syntactic constructors, so they exist
only on the Def side. **So the numeral-closure lands in the SMALL per-tower
half, and it does not grow the shared half.**

**This agrees with every other DD4 figure in the area, and does not weaken
them.** `[LJ-1.238]` measured `L.Coding.Sequence`'s per-tower residual at ZERO
with 145 of 157 lines verbatim. `[LJ-1.237]` measured the joining layer at ZERO.
**Both stand.** `[LJ-1.239]` section 4 calls the missing closure PER-TOWER and
that is right; row C2 sharpens it to Def-tower-ONLY.

## 9. WHAT SECTION 0.0 SHOULD SAY TONIGHT

**One sentence for the `[LJ-1.7]` row:**

> The type stands, `sl` and `sc` are green over an inhabitable hypothesis, and
> the recipe needs a fifth step: the numeral-closure.

**Three phrases in `dev/PLAN.md:47` are FALSE and should go**: 「REFUTED `lh`'s
TYPE」, 「may be green over an uninhabitable hypothesis」, and 「`[LJ-1.240]`
decides that before anything else is funded」, which is now decided. **The
sentence 「`[LJ-1.228]`'s floor is untested against an arity-`4 + n` object」
should also go**, because `sl` and `sc` never see the `4 + n` object.

**ONE THING SHOULD BE ADDED, and it is not about `[LJ-1.7]`.** The archive holds
an arity-2 constant-free level-hood and both prior reports declined to read it
(section 4). **That is a DD18 coverage failure, not a mathematics failure**, and
it belongs where process rulings live, never in the `[LJ-1.7]` row.

## 10. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| `sl`/`sc` stand on an uninhabitable hypothesis | **MEASURED FALSE** at three clauses; the composite is INFERRED |
| `lh`'s type is the defect | **INFERRED FALSE.** it is Devlin's arity and it is reachable |
| the recipe's four steps produce `φ₀` | **INFERRED TRUE that they do not.** no fifth step exists in `src/` |
| `levelHoodB` has arity `4 + n` | **MEASURED TRUE.** `src/L/BoundedSubset.lagda.md:108` |
| `n ≥ 7` suffices for twelve distinct tags | **INFERRED FALSE.** I get `n ≥ 11` |
| `absFo` is the instrument for `levelHoodB` | **MEASURED FALSE.** `erase` preserves arity and applies |
| restating `lh` costs `sl` and `sc` their lines | **MEASURED FALSE** on route A; **TRUE** on route B |
| the `4 + n` object has a consumer in `src/` | **MEASURED FALSE.** three grep hits, all definitions |
| `LevelHood` was ever instantiated at a correct `n` | **MEASURED FALSE.** only `LevelHood0` at `n = 0` |
| the numeral-closure is owed to `lh` | **MEASURED FALSE.** it is owed to `amb`, `ProbeLJ1178A.agda:190-192` |
| the floor stops describing `sl` and `sc` | **MEASURED FALSE.** neither statement changes |
| I re-derived the refused `refl` on `LsetGraph` | **MEASURED FALSE.** I ran no Agda; INFERRED TRUE from `src/L/Coding/Model.lagda.md:586` |
| no piece anywhere defines a numeral inside a formula | **MEASURED FALSE.** `zeroForm` does, `archive/.../L/Condensation.lagda.md:529-531` |
| an arity-2 constant-free level-hood was never written | **MEASURED FALSE.** `levelStory`, `archive/.../L/Condensation.lagda.md:600-601` |
| the archive discharges the level-hood | **MEASURED FALSE.** `Cl = ⊤̇` at `:592-593`, and `CrossOut σᴹ` is never applied |
| the archive bore on `[LJ-1.237]` and `[LJ-1.239]` | **MEASURED TRUE, and both declined it.** `:191-194` and `:170-172` |

## 11. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-239/lj-1.239-report.md`, read WHOLE. TOOK the lead
  (`:9-24`), the two measurements (`:28-40`), the four steps (`:50-80`), the
  C-36 name (`:84-97`), the DD4 split (`:101-112`) and the negatives table
  (`:125-135`).
- `agents/tasks/LJ-1-239/ProbeLJ1239A.agda`, read WHOLE, not the report's
  account of it. TOOK `step1` (`:46-48`), the `LevelHood0` instantiation
  (`:57-59`) and `check-bounded` (`:66-67`). **The probe's own comment at
  `:11-12` already says 「arity 4 with free tag slots」, so the `4 + n` reading
  is the probe's, not an inference of the report.**
- `agents/tasks/LJ-1-237/ProbeLJ1237A.agda`, read WHOLE. TOOK `StageLH`'s
  header (`:127-129`), `coverForm` (`:113-117`), `wk23` (`:107-109`), `Build`
  and `lh` (`:178-181`), `sl` (`:188-201`), `sc` (`:203-246`) and `At`
  (`:249-255`).
- `agents/tasks/LJ-1-237/lj-1.237-report.md`, read WHOLE. TOOK the lead
  (`:9-32`), the four-step recipe (`:80-93`), the C-36 difficulty (`:100-108`)
  and the DD4 zero (`:112-117`).
- `agents/tasks/LJ-1-233/lj-1.233-report.md`, read `:1-70`. TOOK the three wall
  verdicts (`:12-24`), the false-premise finding (`:26-33`) and the erase-route
  measurement (`:62-70`), which records that no line of `src/` applies `countFo`
  to `Σ₂` or `levelHoodB`.
- `agents/tasks/LJ-1-228/lj-1.228-report.md`, read `:10-25` and `:105-130`.
  TOOK the floor (`:16-18`), the bands (`:110-118`) and the unconsumed `Σ₂`
  (`:13-14`).
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read `:160-245` and `:489-505`.
  TOOK `AmbientRead` (`:187-189`), `crossOut` (`:191-193`) and `module Whole`'s
  four hypotheses (`:489-493`). **This file carried the finding that killed my
  own counter-argument.**
- `src/L/BoundedSubset.lagda.md`, read `:30-210` and `:790-909`. TOOK
  `module LevelHood` (`:74-76`), `levelHoodB` (`:108`), `levelHoodΣ₁` (`:142`),
  `isOrdAt` (`:795`), `erase-Δ₀` (`:825-826`), `LevelHood0` (`:840-869`).
  NOT edited.
- `src/L/Condensation.lagda.md`, read `:1118-1132` and `:1460-1482`. TOOK the
  slot comment (`:1123-1125`) and the erase-route comment (`:1465-1471`).
  NOT edited.
- `src/FOL/Count.lagda.md`, read `:585-626`. TOOK `erase` (`:598`), `eraseTm`
  (`:594-596`) and `erase-inv` (`:617-618`). NOT edited.
- `src/FOL/Manipulation/Parameters.lagda.md`, read `:200-320`. TOOK `placeFo`
  (`:226-246`) and `absFo` (`:260-261`). NOT edited.
- `src/FOL/Manipulation/Relabelling.lagda.md`, read `:60-120`. TOOK
  `mapFo f ⊤̇ = ⊤̇` (`:62`) and `embed` (`:117-118`). NOT edited.
- `src/FOL/Semantics.lagda.md`, read `:88-100`. TOOK `γ ⊨ ⊤̇ = ⊤` (`:98`).
  NOT edited.
- `src/L/Hierarchy.lagda.md`, read `:638-660`. TOOK `Lset-defines` (`:646`).
  NOT edited.
- `src/L/Coding/Model.lagda.md`, read `:370-400` and `:580-590`. TOOK `tagAtL`
  (`:586`), the one `con (numeralL k)` occurrence. NOT edited.
- `src/FOL/Absoluteness.lagda.md`, read the declaration index. TOOK
  `module Single` (`:57`) and the `_⊨ᵐ_` renaming (`:78`). NOT edited.
- `dev/PLAN.md`, read `:1-80`. TOOK section 0.0's `[LJ-1.7]` row (`:47`).
  NOT edited.
- `agents/tasks/LJ-1-240/LJ-1.240.md`, read WHOLE, as the pinned brief.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read `:125-132`,
  `:160-172`, `:438-455`, `:525-532` and `:583-601`. **A read-only search agent
  located these lines. I then opened the file and read every line I cite, so
  every archive claim above rests on the artifact and not on the sweep.** TOOK
  `AbsM` (`:127`), `Believes` (`:163-164`), `CrossOut` (`:167-169`), `isOrdAt`
  (`:441-442`), `isLimitAt` (`:449-451`), `zeroForm` (`:529-531`), `Ap`
  (`:585-586`), `Cl = ⊤̇` (`:592-593`), `levelStory` (`:600-601`), `σᴹ`
  (`:768-769`) and `σL` (`:823-824`). NOT edited.
- `archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md`, read `:565-572`. TOOK
  `sucAt` (`:567-571`), the constant-free successor atom. NOT edited.
- `archive/dev/TASKS-archived.md`, `archive/dev/JOURNAL-archived.md` and
  `archive/dev/DECISIONS-archived.md`: **swept by the search agent, NOT opened
  by me, and NOT used in any claim above.** The sweep returned rows on the D31
  index question and on constant-versus-slot rulings. **I do not repeat them,
  because I did not read them at the artifact.** They are the first thing to
  read if the orchestrator wants the retired route's REASONS as well as its
  shape.

## 12. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:86-120` and `:360-395`.

**TOOK, and it decides question 3.** `:95-96` states Devlin's (a):
`∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`, with `Φ` a Σ₀ formula of arity 3. `∃z Φ` is
therefore arity **2**. `:97-99` states (b), the localized form, at the same two
variables. **So Devlin's statement's shape IS achievable here, and
`[LJ-1.237]`'s `φ₀ : Formula (⊥*) 2` is the faithful transcription.**

**The slot representation does NOT force a different arity. It forces a
different PROOF OBLIGATION.** Devlin's finite ordinals are Σ₀-definable inside
his LST, so his `Φ` needs no tag parameters. Our tree chose slots instead
(`src/L/Condensation.lagda.md:1123-1125`), and the slot choice is reversible
inside a formula by the numeral-closure. **So the answer to the brief's
literature question is: the arity is achievable; what the slot design adds is a
definition layer Devlin does not pay. INFERRED**, from the two presentations.
This agrees with `[LJ-1.239]:178-187` and with `[LJ-1.237]:153-157`, and it
corrects only the inference they both left open, that the arity itself is the
obstruction.

**Row C1** (`:374`) classes the level-hood formula as PER-TOWER content, same
shape. **Row C2** (`:375`) classes the bounded step matrix as PER-TOWER and says
the J side is **syntax-free**. **TOOK row C2 for section 8**, because it is what
places the numeral-closure in the Def-tower half.

**WHY NOT the rest.** `:363-372` (steps A, B) and `:376-382` (steps C3 to G) are
about the collapse, the hull, the counting and the well-order. This review
judges a type and a refutation, so none of them bears.

## 13. PROHIBITIONS, ANSWERED

**No Agda run.** No master, brief or report edited. No file written except this
one. No commit, no push, no `git checkout`, `git stash`, `git reset` or
`git clean`. No `make check`. The three walls not re-litigated. The assembly not
priced.

**ONE READ-ONLY SEARCH AGENT RAN**, to sweep `archive/` for the level-hood
shape. **It ran no Agda and wrote no file.** Its output located line numbers.
**I then opened every archive file and read every line I cite**, so no claim in
this report rests on the sweep. Section 11 marks the archive records I did NOT
open and does not use them.

**My file:** `agents/tasks/LJ-1-240/lj-1.240-report.md`.

## 14. GATES

- `scripts/lint-prose.py --check agents/tasks/LJ-1-240/lj-1.240-report.md`:
  reported in the return.
- `make check` not run, by the brief.
