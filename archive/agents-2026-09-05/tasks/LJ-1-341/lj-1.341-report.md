# LJ-1.341 report: `envK` and `defPairK` are FALSE, and the countermodel is machine-checked

tier: opus (in-harness-subagent-mode). Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED, in those
words.

## 0. LEAD

**FALSE. BOTH. AND NOT ONLY UNPROVABLE: THE TWO HYPOTHESIS TYPES ARE EMPTY.**

**A COUNTERMODEL EXISTS AND AGDA CHECKED IT.**
`agents/tasks/LJ-1-341/ProbeTies341.agda:185-190` and `:231-238` derive
`Empty.⊥` from each hypothesis, at EVERY environment and EVERY bound slot.
`agents/tasks/LJ-1-341/ControlA341.agda:54-67` re-states the chapter's own two
types, at the chapter's own index form, and discharges both into the empty type.

**THE WITNESS IS ONE LINE OF ARITHMETIC.** Instantiate `z` with the BOUND
ITSELF. Then `defPairK` asserts `pr (# 0) b ∈ b`, and `envK` asserts
`{pr (# 0) b} ∈ b`. Both are membership cycles, and `regularityV`
(`src/V/Hierarchy.lagda.md:139-144`) refutes them.

**SO `DefinesAgree` AND `LeafAgree` ARE VACUOUS MODULES.** Their telescopes
cannot be inhabited at any `γ`, so `DefinesAgree.out`/`back`
(`src/L/Condensation.lagda.md:6828-6834`) and `LeafAgree.out`/`back`
(`:7231-7243`) prove nothing that anything can use. **`[LJ-1.338]`'s own
`module Leaf` (`agents/tasks/LJ-1-338/ProbeLeaf338.agda:315-366`) takes the two
as parameters, so its exit 0 does NOT establish leaf adequacy.** That is C-45
in its exact form.

**AND THE REPAIR IS ALREADY PAID FOR.** Bound `z` by the CARRIER slot, which is
in scope at both call sites and is already what the SIBLING tie `satK` does.
Then both become TERMS from fields the `KFacts` record already carries.
MEASURED, at `ProbeTies341.agda:248-266` and `:280-294`.

| item | verdict | basis |
|---|---|---|
| `defPairK` as stated, `src/L/Condensation.lagda.md:7185-7186` | **FALSE** | `ProbeTies341.agda:185-190`, MEASURED |
| `envK` as stated, `:7183-7184` | **FALSE** | `ProbeTies341.agda:231-238`, MEASURED |
| `DefinesAgree` pairK/envK, `:6781-6785` | **FALSE** | `ControlA341.agda:78-91`, MEASURED |
| the satisfaction premise bounds `z` | **MEASURED FALSE** | it reduces to a bare set equation |
| the repaired `defPairK` | **TERM** | `ProbeTies341.agda:254-266` |
| the repaired `envK` | **TERM**, plus ONE new closure | `ProbeTies341.agda:285-294` |

**Runs.** Seven Agda invocations, longest 2.5 s. No wall. One process,
`GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.

## 1. THE READING THE BRIEF ORDERED FIRST, AND THE BRIEF'S PREMISE HOLDS

The brief named its own premise at risk: 「nothing bounds `z`」, and said neither
it nor `[LJ-1.338]` had read `envOneAt` or `tagAtL`. **I read both whole. The
premise is TRUE. The bound is not inside the formula.** MEASURED.

**`tagAtL`, `src/L/Coding/Model.lagda.md:585-586`:**

    tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

**Its meaning is an EQUATION and nothing else.** `tagAtL-adequate` at
`src/L/Coding/Model.lagda.md:588-590`:

    (γ ⊨ tagAtL s k x) ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))

and `PairIs a p = (a ≡ p) , setIsSet a p` at `:119-120`. **There is no
membership anywhere in it.** So `defPairK`'s premise is exactly
`fst w' ≡ pr (# 0) (fst z)`, and it constrains `z` in no way at all.

**`envOneAt`, `src/L/Coding/Powerset.lagda.md:128-129:**

    envOneAt e y = extAt e (tagAtL zero 0 (suc y))

**Its meaning is also an EQUATION.** `envOneAt-out` at
`src/L/Coding/Powerset.lagda.md:157` gives `fst E ≡ envOne v`, where
`envOne y = env {1} (λ _ → y)` at `:125-126`. **So `envK`'s premise says only
that `E` is the one-entry environment over `z`.** It says nothing about where
`z` lives.

**WHICH CONJUNCT DOES THE WORK? NONE.** `extAt y φ` at
`src/L/Coding/Model.lagda.md:662-664` is two universally quantified conjuncts,
「every member of `y` satisfies `φ`」and「everything satisfying `φ` is a member
of `y`」. Both quantify over the WHOLE carrier. The only membership either one
mentions is membership in `E` itself, which is the thing being defined.
**MEASURED, by reading the definition and by the two terms in section 2, each
of which INHABITS the premise at a `z` far outside the bound.**

## 2. THE COUNTERMODEL

**THE SHAPE.** Let `B := lookup Ki γ` be the set the conclusion names, and let
`b := fst B`. Nothing in either telescope prevents `z := B`.

**FOR `defPairK`.** Take `E := B`, `z := B`, `w' := prʟ (numeralL 0) B`. The
premise holds, because `prʟ-fst` and `numeralL-fst` give
`fst w' ≡ pr (# 0) b`. The conclusion is then `pr (# 0) b ∈ b`. But

    b ∈ ⁅ # 0 , b ⁆ ∈ pr (# 0) b ∈ b

is a three-step membership cycle, and `regularityV` refutes it.
**`ProbeTies341.agda:185-190`, MEASURED.**

**FOR `envK`.** Take `E := pairʟ w' w'`, the L-side singleton of that same pair,
and `z := B`. The premise is built with `extAt-in-both`
(`src/L/Coding/Model.lagda.md:674-677`), so nothing about `envOne` is assumed.
The conclusion is `⁅ fst w' , fst w' ⁆ ∈ b`, and

    b ∈ ⁅ # 0 , b ⁆ ∈ pr (# 0) b ∈ ⁅ pr (# 0) b , pr (# 0) b ⁆ ∈ b

is a four-step cycle. **`ProbeTies341.agda:231-238`, MEASURED.**

**THE TWO CYCLE LEMMAS ARE FOUR LINES.** `ProbeTies341.agda:89-95`, each one an
accessibility recursion on `regularityV`. `∈-irrefl` at
`src/V/Hierarchy.lagda.md:155-156` is the length-one case, and the hierarchy
chapter already ships it.

**THE REFUTATION IS UNIVERSAL IN THE SITE.** `module Refute` quantifies over
`{n : ℕ} (Ki : Fin n) (γ : S ^ n)`. The chapter writes
`lookup (suc (suc (suc K))) γ`; that is one instance of `lookup Ki γ`, and
`ControlA341.agda:54-67` proves it by discharging the chapter's verbatim types
through the probe. **So this is not「false at one environment」. It is「the type
is empty at every environment」.** MEASURED.

## 3. WHAT `KValue` KNOWS, GIVEN IT HAS ZERO CONSUMERS

**`KValue` KNOWS THE ANSWER TO THE REPAIRED TIES AND HAS NEVER BEEN ASKED.**

**RE-MEASURED TODAY.** `grep -rn "KValue\|LeafAgree" src/` returns hits only
inside `src/L/Condensation.lagda.md`, and inside that file `LeafAgree` appears
only at its own declaration `:7107` and in two comment lines. `DefinesAgree` has
exactly ONE consumer, `LeafAgree` at `:7207`. **So the whole leaf branch is
unreached.** MEASURED.

**WHAT THE VALUE SUPPLIES, AND IT IS EXACTLY WHAT THE REPAIR NEEDS.**
`KValue.facts` at `src/L/Condensation.lagda.md:7296-7315` fills:

| field | at | what the repair uses it for |
|---|---|---|
| `pairK` | `:7307`, from `B.prʟ∈λ` | closes the tagged pair, so the repaired `defPairK` is one call |
| `numK0` | `:7300`, from `B.num∈λ 0` | puts the tag numeral inside the bound |
| `carrierK` | `:7308`, from `Lset-mono` | lifts the new carrier hypothesis to the bound |

**So the L side built the discharge and never wired it, and the discharge it
built fits the CORRECTED statement and not the written one.** That is the D-10
finding in one line: the residue was recorded, carried and priced, while the
value that answers it sat unwired two hundred lines below.

**ONE FACT `KValue` DOES NOT HAVE, MEASURED.** `KFacts` (`:6076-6112`) carries
no SINGLETON closure, and `envOne v` is a singleton. `grep` over
`src/L/Coding/Bound.lagda.md` finds `pr∈λ`, `trans∈λ`, `num∈λ` and `prʟ∈λ` and
no singleton or unordered-pair closure. **It is two lines, not an
architecture:** `⁅ x , x ⁆` is a member of `pr x x`, so `pr∈λ` then `trans∈λ`
gives it. **`ProbeTies341.agda:285-286`, MEASURED.**

## 4. THE RIGHT STATEMENT, AND I DID NOT WRITE IT INTO `src/`

**BOUND `z` BY THE CARRIER SLOT, NOT BY THE BOUND SLOT.** In `DefinesAgree` the
carrier is the parameter `w`. The corrected types are:

    (envK : (E z : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
           → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
           → ⟨ fst E ∈ fst (lookup K γ) ⟩)
    (pairK : (E z w' : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
           → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
           → ⟨ fst w' ∈ fst (lookup K γ) ⟩)

**THE NEW HYPOTHESIS IS FREE AT BOTH CALL SITES, AND THIS IS THE LOAD-BEARING
CHECK.** `DefinesAgree.fwd` at `src/L/Condensation.lagda.md:6798` and
`DefinesAgree.bwd` at `:6813` both begin `λ z (hz , hx) →`, and `hz` IS
`⟨ fst z ∈ fst (lookup w γ) ⟩`, the first conjunct of `bodyB` and `bodyM`
(`:6790-6796`). Both `go` blocks sit inside those `where` clauses, so `hz` is
already in scope where `envK` and `pairK` are applied, at `:6811`, `:6820` and `:6826`.
**Passing it costs one argument at each of two sites.** MEASURED, by reading.

**THE SIBLING TIE IN THE SAME TELESCOPE ALREADY DOES THIS.** `satK` at
`src/L/Condensation.lagda.md:7187-7189` carries the carrier membership INSIDE
its formula, as the conjunct `var zero ∈̇ var (suc (suc (suc (suc w))))`, and
`[LJ-1.338]` discharged it in ONE line with `KFacts.carrierK`
(`ProbeLeaf338.agda:301-305`). **So the corrected `envK` and `defPairK` are
shaped exactly like the tie beside them that is true. INFERRED, and it is the
reading I find most likely: the missing binder is a transcription slip, not a
design choice.**

**WHAT IT COSTS AT THE FOUR SITES `LeafAgree` HANDS ITS TIES TO.** Nothing.
`WitnessAgree`, `KeyAgree` and `SatGraphAgree` never see these two:
`src/L/Condensation.lagda.md:7191-7205` passes them only to `DefinesAgree` at
`:7207-7209`. **So the restatement touches `DefinesAgree`'s telescope, its two
`go` blocks, and `LeafAgree`'s two pass-through lines. MEASURED, by reading
`:7191-7209`.**

**I DID NOT RESTATE IT IN `src/`.** DD23 freezes mathematical prose and the
brief reserves this for the orchestrator. The four lines to change are
`src/L/Condensation.lagda.md:6781-6785` and `:7183-7186`; the two call sites to
feed are `:6811`, `:6820` and `:6826`.

## 5. WHAT THE 327 BECOMES

**THE SUPPLY FIGURE 327 STANDS. THE RESIDUE FIGURE 51 DOES NOT.**

| `[LJ-1.338]` said | now |
|---|---|
| three sites, 51 + 42 + 234 = **327** lines of tie supply | **unchanged**, MEASURED, nothing in this task touches the 183 supplied lines |
| **51** of site 3's 234 are RESIDUE, six ties | **43**, four ties. Residues 5 and 6 leave the list |
| residues 5 and 6 「may be false」, INFERRED | **MEASURED FALSE**, with a term |
| site 3 exits 0, so the leaf adequacy holds at the ambient carrier | **MEASURED FALSE.** `module Leaf` has an EMPTY telescope, so `out-amb` and `back-amb` are vacuous |

**THE 8 LINES.** Residues 5 and 6 occupy `ProbeLeaf338.agda:343-350`, **8
non-blank lines, 4 code and 4 comment**, MEASURED by count. Those 8 lines price
a statement that is false, so 8 of the 51 residue lines were pricing nothing.

**WHAT REPLACES THEM, MEASURED ON MY OWN CALIBER.** `ProbeTies341.agda:248-266`
is the repaired `defPairK`, **17 non-blank lines** including its two hypothesis
lines, which at the real site are `KFacts` fields and therefore free.
`ProbeTies341.agda:280-294` is the repaired `envK`, **13 non-blank lines**.
`ProbeTies341.agda:122-145` proves once that the one-entry environment IS the
singleton of its entry, **20 non-blank lines**, and that belongs ONCE at the
chapter, not per site.

**SO THE RESIDUE DROPS FROM SIX TIES TO FOUR**, and the four survivors are
`[LJ-1.338]`'s residues 1 to 4: the two arity-numeral facts, `witK` and
`graphWitK`. **Those are untouched by this task and I did not re-price them.**

**THE HARDER HALF, AND IT IS NOT A LINE COUNT.** Until the telescope is
restated, the 234 measures a supply for a module nobody can apply. **The lines
are still the right lines; the module they serve is not yet a real module.** A
brief that funds the residue must order the restatement FIRST, then the four
remaining ties.

## 6. THE NEGATIVE CONTROLS, NON-VACUITY INCLUDED

**FIVE CONTROLS. FOUR GREEN BY CONSTRUCTION, ONE RED ON PURPOSE.**

**CONTROL 1, NON-VACUITY OF `defPairK`'s PREMISE.**
`ProbeTies341.agda:180-182` INHABITS the premise at the three witnesses the
refutation uses. **This is the control `[LJ-1.338]`'s third control was, and it
is the one that matters here:** a hypothesis can look refutable because nothing
meets its premise. **It is met.** The witness is `prʟ (numeralL 0) B`, a real
element of the carrier, and its tag equation is a term. MEASURED.

**CONTROL 2, NON-VACUITY OF `envK`'s PREMISE.** `ProbeTies341.agda:208-229`
builds a satisfying `E` through `extAt-in-both`, so the one-entry reader is
INHABITED at an environment over the bound. Without it the four-step cycle would
be an argument about an empty premise. MEASURED.

**CONTROL 3, THE REPAIR IS NOT EMPTY.** `ProbeTies341.agda:248-266` and
`:280-294` are TERMS. **A refutation that also killed the repaired statement
would mean the tie is unsalvageable; it does not.** MEASURED.

**CONTROL 4, THE EXTENT (C-42).** `ProbeTies341.agda:313-333` proves that
`EnvOneAgree`'s own `pairK` (`src/L/Condensation.lagda.md:6751-6753`), which has
the SAME tag premise but reads a FIXED environment slot instead of a quantified
variable, is a TERM under the same two record fields. **So the shape the
refutation kills is「the tag's payload slot is the quantified variable」and
nothing wider. `[LJ-1.336]`'s 42-line site stands.** MEASURED.

**CONTROL 5, THE GATE IS LIVE.** `agents/tasks/LJ-1-341/MustFail341.agda` is
**EXPECTED RED and must not be repaired.** It attempts the one proof a reader
would try, `defPairK` without bounding `z`, from the same two fields that prove
the bounded form. **Agda refuses at `MustFail341.agda:54.35-40` with
`UnequalTerms`, and the error NAMES the missing fact:**

    when checking that the expression numK0 has type
    ⟨ fst z ∈ fst (lookup Ki γ) ⟩

**So the green of the other two files is not a green of an empty file, and the
gap is exactly the carrier hypothesis of section 4.** MEASURED, exit 42 in
1.1 s.

**THE SWEEP (C-42).** I searched `src/` for the same shape,「a tie quantifying
over a variable that appears in no conclusion and no membership premise」.
**Inside the seven, the count is TWO, and they are these two.** `satK`
(`:7187-7189`) binds by its formula; `keyValK` (`:7181-7182`) binds nothing but
concludes about the SAME variable the tag reads, so no cycle arises; `witK`
(`:7116-7118`) and `graphWitK` (`:7171-7180`) bind by their formulas.
`EnvOneAgree.pairK` (`:6751-6753`) reads a fixed slot. **MEASURED, by reading
all fifteen `LeafAgree` parameters at `:7107-7190` plus `EnvOneAgree`'s three.**

## 7. C-57: THE HITS I READ AND THE ONES I REJECTED

**A search that returns the answer and a reading that discards it are two
different failures. Here is the reading.**

| search | hits | read | rejected, and why |
|---|---:|---:|---|
| `envOneAt\|tagAtL` in `src/L/Condensation.lagda.md` | 40 | 6 | 34 are adequacy transports (`tagAtL-adequate` calls); they use the reader and say nothing about the tie |
| `envOneAt` across `src/` | 11 | 5 | `Everything.lagda.md:582` and `:983`, `Powerset:748` and `:763` are prose; they describe the reader and state no bound |
| well-foundedness across `src/` | 30 | 3 | `FOL/ZFModel.lagda.md:170-233` is the OBJECT-language regularity field, the wrong layer; `Everything.lagda.md` hits are prose |
| `KValue\|LeafAgree` across `src/` | 3 | 3 | none rejected; all three are inside the one chapter |
| `Bound` closures | 6 | 6 | none rejected; the absence of a singleton closure is the finding |

**The one I nearly discarded and should not have:** `envOneAt-out`
(`src/L/Coding/Powerset.lagda.md:157`). It looked like a transport lemma. **It
is the whole answer to「does the premise bound `z`」, because it says the
premise is an EQUATION.**

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the bound is inside `envOneAt` or `tagAtL` | **MEASURED FALSE.** Both reduce to bare set equations |
| `envK` and `defPairK` are true as stated | **MEASURED FALSE.** Two terms deriving `Empty.⊥` |
| they are false only at some environments | **MEASURED FALSE.** `module Refute` is universal in `Ki` and `γ` |
| only `LeafAgree` carries the false form | **MEASURED FALSE.** `DefinesAgree:6781-6785` carries it too, and `ControlA341.agda:78-91` refutes it there |
| the refutation needs a special bound | **MEASURED FALSE.** It needs only that the bound is a set, by regularity |
| the premise is empty, so the refutation is vacuous | **MEASURED FALSE.** Controls 1 and 2 inhabit both premises |
| the repaired statement is also false | **MEASURED FALSE.** Controls 3, two terms |
| the repair needs a new record field for `defPairK` | **MEASURED FALSE.** `KFacts.pairK` and `numK0` suffice |
| the repair needs nothing new for `envK` | **MEASURED FALSE.** It needs a singleton closure, which `KFacts` lacks |
| that singleton closure is expensive | **MEASURED FALSE.** Two lines from `BoundOver.pr∈λ` and `trans∈λ` |
| the new hypothesis is unavailable at the call sites | **MEASURED FALSE.** It is `hz`, already bound at `:6798` and `:6813` |
| the refutation sweeps `EnvOneAgree` away too | **MEASURED FALSE.** Control 4, a term |
| `LeafAgree` or `KValue` has a consumer in `src/` | **MEASURED FALSE.** Re-measured today, zero |
| `[LJ-1.338]`'s exit 0 establishes leaf adequacy | **MEASURED FALSE.** Its `module Leaf` telescope is empty |
| the 327 supply figure moves | **MEASURED FALSE.** Nothing here touches the 183 supplied lines |
| the 51-line residue figure stands | **MEASURED FALSE.** 8 of those lines price a false statement |
| I restated the telescope in `src/` | **MEASURED FALSE.** `git status` shows four files, all in `agents/tasks/LJ-1-341/` |
| a run hit a wall | **MEASURED FALSE.** The longest was 2.5 s |
| the whole chapter typechecks with the repair landed | **INFERRED.** Nothing landed and I ran no chapter check |
| the four remaining residues are affected | **INFERRED FALSE.** I did not re-price them |

## 9. DD4, WITH THE AXIS NAMED (C-46)

**MY AXIS IS THE L-AGAINST-AMBIENT AXIS, AND IT IS NOT DD4's OWN.** DD4's axis
is AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**ON DD4's OWN AXIS THIS PROBE IS NEUTRAL BY STRUCTURE.** `L.Condensation` is in
neither trophy closure, so nothing here moves `L ⊨ AC` or `L ⊨ GCH`.

**ON THE L-AGAINST-AMBIENT AXIS, THE 5,626 FOR 114 IS UNCHANGED AND ITS MEANING
IS NOT.** `[LJ-1.338]` measured the paid instance at 5,626 copied lines for 114
hand-written. **Nothing in this task changes either number: the copied
mathematics is untouched and `KValue` still transports at 0 changed lines.**

**WHAT DOES CHANGE IS WHICH SIDE THE FIX FALLS ON, AND IT FALLS ON THE SHARED
SIDE.** The corrected statement, the carrier hypothesis and the singleton
closure are all class-free: they name `pr`, `trans∈λ` and a carrier slot, and
none of them names L or the ambient carrier. **So the repair is written ONCE and
serves both ends, which is what DD4 asks. INFERRED, from the fact that my
`module Refute` and both repair modules are generic in `γ` and were never
instantiated at either carrier.**

**THE HONEST HALF.** The tie supply is not part of the 5,626 ratio at all;
`[LJ-1.338]` section 10 says so and I did not re-open it.

## 10. ARCHIVE USED (DD18)

One line read per archived file.

- **`agents/tasks/LJ-1-338/lj-1.338-report.md`, read WHOLE, as the brief
  orders.** **Line read:** `:205-213`,「RESIDUES 5 AND 6 MAY BE FALSE AS STATED
  ... INFERRED, by reading `:7183-7186`. I did not build the counterexample」.
  **TOOK** it as the claim under test. **CORRECTED its class:** the INFERRED
  becomes MEASURED, and it is stronger than the sibling guessed, because the
  types are empty rather than merely unproved.
- **`agents/tasks/LJ-1-338/ProbeLeaf338.agda`, read `:314-366`, and counted
  `:343-350`.** **Line read:** `:348`,「RESIDUE 6. The tagged pair over that
  same unbounded `z`」. **TOOK** the 8-line figure and the observation that both
  are module PARAMETERS, which is what makes `module Leaf` vacuous.
- **`agents/tasks/LJ-1-338/ControlC338.agda`, read WHOLE.** **Line read:**
  `:292-295`, `keyValK-live`, the non-vacuity witness. **TOOK** the control
  SHAPE: inhabit the premise before believing anything about the tie. My
  controls 1 and 2 are that shape at these two ties.
- **`agents/tasks/LJ-1-336/lj-1.336-report.md`, read the sections on the
  downward and upward debts.** **Line read:** its `Bound` finding, that the
  upward supplier is `src/L/Coding/Bound.lagda.md:130-145`. **TOOK** it as the
  place to look for a singleton closure. **CORRECTED nothing; ADDED** that the
  supplier has none, and that it is two lines away.
- **`agents/tasks/LJ-1-302/ProbeLJ1302B.agda`, read `:85-122`.** **Line read:**
  `:105-108`, `pair∈pr`. **TOOK** the three pair lemmas, copied rather than
  imported, at `ProbeTies341.agda:101-117`, because importing that probe would
  pull its whole ambient frame in for three lines.
- **`archive/dev/TASKS-archived.md`, read the shared-kit rows.** **TOOK SHAPE
  ONLY:** the retired route also carried hypotheses whose quantifier was wider
  than the proof needed. **WHAT WOULD NOT TRANSFER:** every figure. That route
  had a different carrier, a different coding and no second tower, so its
  residue counts price nothing here, and it never had a `KFacts` record to
  answer a corrected tie for free.

## 11. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:243-255` and `:404-410`.**

**THE ONE LINE THE BRIEF ASKS FOR: Devlin's corresponding step has NO unbounded
variable at all.** `:245-250` records that 2.2 to 2.4 write
`D(v, u) = "v = Def(u)"` as Σ₁ and **「then bind every unbounded quantifier by
the concrete set K(u), the finite sequences over the formula set, the variables
and the members of u」**, and that the Σ₀ matrix `C(w, v, u)` with `w = K(u)` is
「the bounded satisfaction substrate of Devlin's engine」.

**SO THE PORT-ARTEFACT READING IS THE RIGHT ONE.** In the source, the bound is
part of the FORMULA and no variable escapes it. In our telescope the bound was
moved out of the formula and into a hypothesis, and on the way `z` lost its
binder. **The corrected statement of section 4 puts the binder back, and it is
Devlin's own `z ∈ u` restricted to the carrier.** INFERRED, by comparison; the
digest states the binding, not our telescope.

**WHY NOT the rest of the digest.** `:147` and `:451` are the cardinality half
of 5.5 and 5.6, which no tie of `LeafAgree` reaches. `:175-193` is the
Σ₁-elementarity requirement at the hull, a different step. `:300-307` and
`:375` partition by tower, which is Devlin's axis and not DD4's, and C-46
forbids using it as the DD4 axis.

## 12. WHAT I DID NOT SETTLE

- **The four remaining residues.** `witK`, `graphWitK` and the two
  arity-numeral facts are untouched. I did not test their truth.
- **Whether the chapter typechecks with the repair landed.** Nothing landed and
  I ran no chapter check. INFERRED that it does, because the only new argument
  at each call site is `hz`, which is in scope.
- **Whether `satK` and `keyValK` are true.** I read them and found no cycle, and
  `[LJ-1.338]` discharged both. I did not re-verify them.
- **The ambient carrier.** My refutation is generic in `γ`, so it holds at both
  carriers, but I instantiated at neither.
- **The landing cost of the restatement.** This probe lands nothing.

## 13. SECONDS, LOAD, RUNS

One Agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. No
heap exhaustion. **No invocation reached 30 minutes; the longest was 2.5 s.** I
ran `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` before every
invocation. **It returned 0 five times and 1 twice**, and on the two occasions
it returned 1 a sibling held the other slot, so C-12's cap of two was never
exceeded.

| file | exit | seconds | note |
|---|---:|---:|---|
| `ProbeTies341.agda` | 42 | 2.2 | scope: `_+_` is not in `Base.Prelude` |
| `ProbeTies341.agda` | **0** | **2.4** | both refutations, both non-vacuity controls |
| `ControlA341.agda` | **0** | **1.7** | the chapter's own two types, discharged |
| `ControlA341.agda` (both files, after rename) | **0** | **2.0** | reload of both |
| `MustFail341.agda` | **42** | **1.1** | **EXPECTED RED**, and the error names the missing fact |
| `ProbeTies341.agda` | 42 | 2.1 | scope: `_⊆_` needs naming in the `using` list |
| `ControlA341.agda` (both files, final) | **0** | **2.5** | with both repairs added |

`.venv/bin/python scripts/gate/lint-agda.py --check` exits 0.
`.venv/bin/python scripts/gate/lint-prose.py --check` exits 0.

## 14. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-341/`: this report, `ProbeTies341.agda`,
`ControlA341.agda` and `MustFail341.agda`. `git status` shows those four files
and nothing else of mine. **`src/` holds no probe of mine and I opened no file
under `src/` for writing.** I did not restate `LeafAgree` or `DefinesAgree`;
section 4 says what to change and stops, as the brief orders, and DD23 is
respected. `agents/tasks/LJ-1-338/`, `LJ-1-336/` and `LJ-1-302/` were read and
counted, never edited. I did not open `src/Everything.lagda.md`, `dev/PLAN.md`,
`dev/LESSONS.md`, `dev/ledger.toml`, `AGENTS.md` or `.claude/`. No commit, no
push, no `git checkout`, `stash`, `reset` or `clean`. No `make check`. No em
dash in any language.
