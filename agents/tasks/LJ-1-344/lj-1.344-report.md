# LJ-1.344 report: both repaired ties are SUPPLIED, and `KValue` is wired

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**BOTH TIES ARE SUPPLIED, AS TERMS, AT THE DELIVERED TYPES.**
`agents/tasks/LJ-1-344/Supply344.agda`, **exit 0 in 3.09 s**. The two ties cost
**25 code lines** of new proof. They add **NO field to `KFacts`** and **NO lemma
to `BoundOver`**.

**THE BRIEF'S PREMISE AT RISK IS MEASURED FALSE, in the cheap direction.** The
singleton closure is **not two lines from `BoundOver.pr∈λ` and `trans∈λ`**. It
is **8 lines from `KFacts.pairK` and `KFacts.arityK`**, which the delivered
record already carries. The two-line reading named the right shape at the wrong
SORT. Section 2.

**AND `KValue` HAS ITS FIRST CONSUMER.** `[LJ-1.338]` measured that
`src/L/Condensation.lagda.md:7277-7330` has zero consumers anywhere in `src/`.
`Supply344.KWire` feeds its `facts` record to the supply and **both ties FIRE,
with every premise discharged** except `KValue`'s own ordinal frame and one
named hypothesis that the carrier stage is at least 1. MEASURED, exit 0.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| `envK` supplied at the delivered type | **YES, MEASURED** | `Supply344.agda:179-187`, exit 0 |
| `defPairK` supplied at the delivered type | **YES, MEASURED** | `Supply344.agda:190-198`, exit 0 |
| the singleton closure is two lines from `BoundOver` | **MEASURED FALSE** | section 2 |
| the closure needs a new `KFacts` field | **MEASURED FALSE** | `sgltK` uses only delivered fields |
| `DefinesAgree` accepts the supply positionally | **YES, MEASURED** | `Supply344.agda:281-312` |
| the `LeafAgree` index form accepts it | **YES, MEASURED** | `Supply344.agda:314-341` |
| `KValue` transports as `[LJ-1.338]` measured | **YES, MEASURED** | `ProbeKValue338.agda` re-run, exit 0 in 9.37 s |
| the supply proves the PRE-repair tie too | **MEASURED FALSE** | Control A, exit 42 at the missing hypothesis |
| the tie is met by any environment | **MEASURED FALSE** | Control B, exit 42 at one changed numeral |
| the premises are inhabited | **YES, MEASURED** | `live-envK-premise`, `live-defPairK-premise`, `KWire.envK-fires` |
| `witK` and `graphWitK` are supplied | **NO.** Priced, section 6.1 |
| `wCodesK`'s arity conjunct is true | **INFERRED FALSE**, countermodel built, one clause walls, section 6.3 |

**ONE FILE IN MY DIRECTORY DOES NOT TYPECHECK, AND I SAY SO HERE RATHER THAN
LET A READER FIND IT.** `agents/tasks/LJ-1-344/Residue344.agda` and
`agents/tasks/LJ-1-344/Bisect344A.agda` and `Bisect344D.agda` do not return
inside my budget. They are kept because a probe is never deleted and because
the bisection is the evidence for section 6.3. **`Supply344.agda`,
`ControlA344.agda`, `ControlB344.agda`, `Bisect344B.agda`, `Floor344.agda` and
`Floor344B.agda` all return, at the exits the table gives.**

## 2. THE SINGLETON CLOSURE. The two-line reading is FALSE, and cheaply

**WHAT THE BRIEF SAID.** 「`KFacts` carries no SINGLETON closure, and `envOne v`
is a singleton. It is TWO lines from `BoundOver.pr∈λ` at
`src/L/Coding/Bound.lagda.md:69` and `trans∈λ` at `:93`.」

**THE FIRST HALF IS TRUE AND I RE-CONFIRMED IT.** `KFacts`
(`src/L/Condensation.lagda.md:6076-6112`) has no field of singleton shape.
MEASURED, by reading all 29 fields.

**THE SECOND HALF IS FALSE, AND THE REASON IS THE SORT.** `BoundOver` states
every fact over the AMBIENT sort: `pr∈λ` and `trans∈λ` are
`(x y : S) → ⟨ … ∈ˢ T lam ⟩` where `S` is `hPropStructure 𝒮ᵥ`'s carrier, that
is `V ℓ` (`src/L/Coding/Bound.lagda.md:34`, `open hPropStructure 𝒮ᵥ`). Composed
there, they give

```
sglt∈λ : (x : V ℓ) → ⟨ x ∈ b ⟩ → ⟨ ⁅ x , x ⁆ ∈ b ⟩
```

**and the tie cannot use it.** The tie's conclusion is `⟨ fst E ∈ … ⟩` for an
`E : S` at the **L sort**, which the tie itself quantifies over, and every
`KFacts` closure is stated at `fst` of an L element. A closure over bare `V ℓ`
sets never reaches `fst E`.

**WRITTEN AT THE SORT THE TIE USES, THE CLOSURE COSTS 8 LINES AND NO NEW FACT**
(`Supply344.agda:169-176`):

```agda
sgltK : (a E : S) → fst E ≡ ⁅ fst a , fst a ⁆
      → ⟨ fst a ∈ bnd ⟩ → ⟨ fst E ∈ bnd ⟩
sgltK a E q ha = arityK (prʟ a a) E mem (pairK a a ha ha)
```

**`pairK` puts `pr a a` in the bound and `arityK` brings `fst E` down out of
it**, because `⁅ x , x ⁆` is a member of `pr x x`. Both are delivered fields, at
`src/L/Condensation.lagda.md:6107-6108` and `:6111-6112`. **So the third kind of
debt did not need a new closure fact at all. It needed the closure stated one
sort up.**

**THE ONE THING THE TREE REALLY LACKS is not a closure but an ACCESS.**
`⁅ x , y ⁆ ∈ pr x y` is `inr∈⁅,⁆` at `src/V/Coding.lagda.md:149-150`, inside
that chapter's `private` block. `[LJ-1.302]`, `[LJ-1.338]`, `[LJ-1.341]` and now
this task each re-wrote it because no consumer can name it. **That is 4 lines
paid four times, MEASURED.**

## 3. WHAT THE SUPPLY COSTS

Caliber: non-blank lines, comments separated, the caliber `[LJ-1.338]` used.

| block | `Supply344.agda` | non-blank | code |
|---|---|---:|---:|
| **`sgltK`, the singleton closure** | `:169-176` | 8 | **8** |
| **`envK`** | `:179-187` | 9 | **9** |
| **`defPairK`** | `:190-198` | 8 | **8** |
| the four `KFacts` fields, as parameters | `:137-145` | 9 | 9 |
| private helpers (`tagged`, its `fst`, its closure) | `:147-159` | 10 | 10 |
| **THE SUPPLY PROPER** | | **44** | **44** |
| ambient pair facts, re-written because `private` | `:73-126` | 45 | 36 |
| non-vacuity witnesses | `:200-256` | 47 | 31 |
| `FromRecord`, the record hands the four over | `:264-279` | 13 | 5 |
| `Fit`, `DefinesAgree` instantiated | `:281-312` | 27 | 14 |
| `LeafFit`, the second index form | `:314-341` | 25 | 25 |
| `KWire`, `KValue` end to end | `:359-386` | 22 | 19 |

**THE HEADLINE FIGURE IS 25 CODE LINES**, the three terms. **44 with the
telescope and the helpers.** The rest is evidence, not supply: the fit tests,
the witnesses and the wiring.

**BASIS (DD8): a delivered comparable is not used here.** These are counted
lines of a green file, not an estimate.

## 4. `KValue`: IT TRANSPORTS, AND IT NOW HAS A CONSUMER

**THE TRANSPORT REPRODUCES.** `agents/tasks/LJ-1-338/ProbeKValue338.agda`
re-runs **exit 0 in 9.37 s**, against `[LJ-1.338]`'s 9 s. MEASURED. I did not
re-run the `difflib` alignment; **INFERRED** that its 50-lines-0-changed figure
still holds, because neither `KValue` nor the probe changed since.

**THE STRONGER RESULT: `KValue` IS NOW WIRED.** `Supply344.KWire`
(`:359-386`) opens `KValue` at its own six frame parameters, takes its `facts`
record, and produces both ties at the concrete 14-slot `Kenv`. **`KValue` had
zero consumers in `src/` and this is its first anywhere.** MEASURED, exit 0.

**AND THE CARRIER IS INHABITED, so the ties fire on real arguments.**
`KWire.zero∈carrier` proves `fst (numeralL 0) ∈ Lset gam` from `ord∈Lset-suc`
and `Lset-mono`, under ONE added hypothesis `⟨ # 1 ∈ gam ⟩`, which says the
carrier stage is at least 1. **Then `envK-fires` and `defPairK-fires` are closed
terms of the two conclusions.** This is what a supply looks like when it is not
a parameters-green.

## 5. THE NEGATIVE CONTROLS, BOTH MEASURING

**CONTROL A: the gate is live.** `ControlA344.agda` asks the same supply for the
PRE-repair `envK`, the unbounded one `[LJ-1.341]` refuted. **Exit 42 in 2.62 s**,
refused at `ControlA344.agda:56` with the satisfaction premise offered where
`⟨ fst z ∈ fst (lookup A γ) ⟩` is wanted. **So the supply does not accidentally
prove the false statement**, and the repair is load-bearing in the proof and not
only in the type. MEASURED.

**CONTROL B: NON-VACUITY, and it discriminates.** `Supply344.agda` exhibits a
real inhabitant of the `envK` premise, the one-entry environment over tag
NUMERAL ZERO. `ControlB344.agda` changes that tag to ONE and changes nothing
else. **Exit 42 in 1.68 s**, refused at `ControlB344.agda:59.46-71`, inside the
equation that feeds the tie, with `# 1` against `# 0`. **The tie is unchanged
and still true; only the WITNESS dies.** So the premise is a real constraint
that some environments meet and others fail, which is exactly what a hypothesis
that typechecks cannot tell you (C-45). MEASURED.

**NON-VACUITY, POSITIVE HALF, THREE LAYERS.**

1. `envK-live` (`:203-206`) reaches the satisfaction premise from a bare set
   equation, through the chapter's own `envOneAt-in`.
2. `live-envK-premise` (`:238-241`) BUILDS the inhabitant: `sglS (tagged z)` is
   the one-entry environment as an element of the L sort, its `isL` component
   from the transitivity of L applied to `pr a₀ a₀`. Nothing is assumed to
   exist.
3. `KWire.envK-fires` closes the last premise, so the tie fires with no free
   hypothesis but `KValue`'s own frame.

## 6. THE FOUR REMAINING CONSTRUCTION TIES

**`[LJ-1.338]` counted six. Two are now supplied. The other four split into two
very different kinds, and I read every telescope.**

### 6.1 `witK` and `graphWitK`: repairable the same way, one line each

**`witK` (`src/L/Condensation.lagda.md:7124-7126`) HAS THE SAME SHAPE DEFECT AS
THE TWO REFUTED TIES.** Its premise is
`(lookup (suc zero) γ) ∈ fst w'` together with `closedAt w'` and
`shapedAt w' (carrier)`, and its conclusion is `fst w' ∈ K`. **Neither formula
bounds `w'` above.** MEASURED, by reading both:
`closedAt C` (`src/L/Coding/Model.lagda.md:2191-2195`) is a conjunction of shape
clauses about MEMBERS of `C`; `shapedAt C A` (`src/L/Coding/Shape.lagda.md:189`)
is `∀̇∈ (var C) (shapes A)`, a bounded universal over MEMBERS of `C`.

**I did NOT refute it, and I say why.** The easy countermodel is closed off:
`shapedAt` forces every member of `w'` to be a shape, so `w'` cannot be the set
that produces a membership cycle. **INFERRED that `witK` is true at the intended
instance and unprovable from closure**, exactly as `[LJ-1.338]` classified it.

**THE CURE IS `[LJ-1.343]`'s, and then the supply is ONE line.** Add
`⟨ fst w' ∈ fst (lookup A γ) ⟩` to the telescope and `KFacts.carrierK` closes
it. **This is the shape `satK` already has**: `satK` carries its carrier
membership inside its formula and `[LJ-1.338]` measured its supply at one call
of `carrierK`.

**`graphWitK` (`:7179-7188`) IS TWO THIRDS THE SAME AND ONE THIRD DIFFERENT.**
Its first conjunct is `var zero ≐ var (suc (suc (suc (suc (suc (suc w))))))`,
which at the environment `(f ∷ e ∷ d ∷ γ)` says **`fst f` IS the carrier
itself**. So its third conclusion, `fst f ∈ K`, is not a `carrierK` call: it
needs **the carrier as a MEMBER of the bound**, and `KFacts` has no such field.
MEASURED, by reading all 29 fields. **That is a genuine missing field**,
`boundK : ⟨ fst (lookup A γ) ∈ fst (lookup K γ) ⟩`, and at `KValue` it is
`Lset gam ∈ Lset lam`, true whenever `gam ∈ lam`, which `KValue` already
assumes as `γ∈λ`. **INFERRED that one field and one supplier line close it. I
did not build either.**

### 6.2 The two arity-numeral conjuncts: a D-10 case, and I priced its TRUTH

**THE CONJUNCT.** `wCodesK` (`:7130-7136`) and `wUnCodesK` (`:7137-7142`), and
their graph twins `gCodesK` (`:7153-7160`) and `gUnCodesK` (`:7161-7167`), each
end in `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`: **the arity component of a code is a
numeral.**

**THE PREMISE NEVER SAYS `w'` IS A CODE SET. MEASURED, by reading the
telescope.** It says only `⟨ fst w' ∈ fst (lookup K γ) ⟩`, `⟨ fst c ∈ fst w' ⟩`
and the pair equation. **`closedAt` and `shapedAt` appear in `witK`'s premise
and NOT in `wCodesK`'s.** So any set in the bound with any member of the pair
shape is a legal instantiation.

**AND THE SAME CONJUNCT SITS AT TWO MORE SITES THE PRIOR SWEEPS DID NOT COUNT.**
`module ShapesAgree` (`src/L/Condensation.lagda.md:6157-6175`) takes `compK` and
`unCompK`, whose last conjunct is the same `∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁` and
whose subject `C : S` is a bare module parameter with **no hypothesis at all**.
MEASURED, by reading the telescope. **So the arity-numeral family has SIX
occurrences, not four**, and `[LJ-1.338]`'s residue count of six ties is a count
of `LeafAgree`'s ties, not of this family.

**SO THE CONJUNCT IS A REFUTATION CANDIDATE, and I built the countermodel**:
`agents/tasks/LJ-1-344/Residue344.agda`. Section 6.3 says how far it got.

### 6.3 The countermodel: built, and HALF proved. A WALL, bisected

**THE COUNTERMODEL, in full, at `Residue344.agda:107-184`.** Take the carrier to
have a member `u`. Put

- `ar := sglS (numeralL 1)`, whose set is `⁅ # 1 , # 1 ⁆`;
- `c := prʟ ar (prʟ (numeralL 0) (prʟ u u))`, of exactly the tie's pair shape at
  `k := 0` and `a := b := u`;
- `w' := sglS c`, the singleton of the code.

**Every membership the tie needs is built from the SAME `KFacts` fields the
supply uses**, `sglK` included, so no new closure enters. The tie then forces
`∥ Σ m. ⁅ # 1 , # 1 ⁆ ≡ # m ∥₁`.

**THE MATHEMATICS IS RIGHT AND HALF OF IT IS MACHINE-CHECKED.**
`agents/tasks/LJ-1-344/Bisect344B.agda`, **exit 0 in 2.01 s**, proves

```agda
sgl1-not-suc : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # (suc m) → Empty.⊥
```

by `#mono`, `pair-only` and `#-inj`. **MEASURED. So the singleton of one is not
a POSITIVE numeral.**

**THE `m = 0` CASE IS A WALL, BY TWO INDEPENDENT ROUTES, BISECTED.**

| file | content | result |
|---|---|---|
| `Bisect344B.agda` | the `suc m` clause alone | **exit 0, 2.01 s** |
| `Bisect344A.agda` | the same plus `m = 0` through `V.Model.empty-spec` | **INTERRUPTED past 400 s** |
| `Bisect344D.agda` | the same plus `m = 0` through `regularityV (# 1)` | **INTERRUPTED past 160 s** |
| `Residue344.agda` | the whole file, regularity route | **INTERRUPTED at 330 s** |

**MEASURED: the cost is in refusing `# 1 ∈ # 0` at CONCRETE numerals, and it is
not the route.** One route transports along an hProp path out of the hierarchy
(`empty-spec`); the other forces the accessibility of `# 1`. **Both fail; the
clause that avoids both exits in 2 s.** This is R-40's class: a membership stated
against a concrete successor chain normalizes against the level's union
representation.

**SO THE VERDICT ON THE ARITY CONJUNCT IS: INFERRED FALSE, not MEASURED FALSE.**
The countermodel is built and typechecks up to one clause. **I did NOT prove the
tie false and I do not claim it.** What is MEASURED is the premise reading of
section 6.2: `wCodesK`'s telescope carries no shapedness, which is what makes
the countermodel legal.

**THE PRICE OF FINISHING IT.** One lemma, `# 1 ∉ # 0`, written so that it never
normalizes a concrete numeral against the union representation. R-40's own cure
says to state the membership at a SHALLOW index and climb; here the honest next
step is to pick a non-numeral whose refutation needs no `m = 0` case at all.
**INFERRED at about 15 lines and one run. I did not build it.**

## 7. WHERE THE SUPPLY BELONGS IN THE CHAPTER

**ONE new module, immediately after `KFactsCons`, which ends at
`src/L/Condensation.lagda.md:6155`, and before `module ShapesAgree` at
`:6157`.** MEASURED, by reading both boundaries. It must sit after `KFacts` and
before the first consumer, and the first consumer of the family is `EnvOneAgree`
at `:6748`.

**ITS SHAPE, exactly as `Supply344.agda:137-198` has it:**

1. `pair∈pr`, 4 lines, at the top of the chapter's ambient block. **Better: make
   `inr∈⁅,⁆` public in `src/V/Coding.lagda.md` and delete four copies.** That is
   a one-word edit to a `private` keyword and I did not make it.
2. `sglS`, 7 lines: the singleton as a carrier element.
3. `module KTies (f : KFacts …)`, holding `sgltK`, `envK`, `defPairK`, 25 code
   lines, taking the four fields off the record.
4. At `LeafAgree`'s call of `DefinesAgree` (`:7207-7209`), pass
   `KTies.envK` and `KTies.defPairK` instead of the two parameters, and delete
   them from both telescopes.

**I LANDED NONE OF THIS.** `src/` is untouched.

**A WARNING FOR WHOEVER LANDS IT.** `Supply344.agda` imports `L.Condensation`
and reads its `KFacts` from the interface. **A supply written INSIDE the chapter
sits before `KValue` and after `KFacts`, so it cannot use `KValue`; the wiring
of section 4 must stay at `KValue`'s own site or below it.**

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**THE SUPPLY IS CLASS-FREE, so it keeps the property `[LJ-1.341]` measured for
the repair.** MEASURED, by reading the three terms: `sgltK`, `envK` and
`defPairK` name `fst`, `∈`, `lookup`, `pr`, `prʟ`, `numeralL`, `⁅_,_⁆` and four
`KFacts` fields. **Not one of them mentions AC, GCH, a well-ordering or a
cardinal.** So the 25 lines are written once and serve both ends.

**AND THE SUPPLY MAKES THE SHARING BIGGER, not smaller.** `[LJ-1.338]` measured
the ambient tie supply at 327 lines, of which 51 are residue statements. **This
task removes two of the six residues at 25 lines, and those 25 lines are the
SAME 25 at both carriers**, because `KFacts` is already generic
(`[LJ-1.338]`:410-413, `GenAgree.agda:4886`). One rule, two ends.

**`dev/ledger.toml:204` UNDERSTATES, as the brief notes.** The GCH closure is
read from a statement whose proof is not wired. `L.Condensation` is `gch_only`
at **6,731** lines, `[LJ-1.345]`'s corrected figure, and I did not re-measure it.

## 9. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the singleton closure is two lines from `BoundOver` | **MEASURED FALSE.** Wrong sort; it is 8 lines from two `KFacts` fields |
| `KFacts` needs a new field for the two ties | **MEASURED FALSE.** `Supply344.agda` adds none |
| `BoundOver` needs a new lemma | **MEASURED FALSE.** `Supply344.agda` does not import it |
| the supply has the right type but the consumer refuses it | **MEASURED FALSE.** `DefinesAgree` instantiated, both directions forced |
| the supply also proves the pre-repair tie | **MEASURED FALSE.** Control A, exit 42 |
| the tie's premise is met by any environment | **MEASURED FALSE.** Control B, exit 42 at one numeral |
| the premises are empty, so the supply discharges nothing | **MEASURED FALSE.** Three layers of witness, section 5 |
| `KValue` still has zero consumers | **MEASURED FALSE.** `KWire` is one, exit 0 |
| `KValue` needs changed lines to transport | **INFERRED FALSE.** Re-run green; alignment not re-counted |
| `witK` is refutable by the `[LJ-1.341]` countermodel | **MEASURED FALSE.** `shapedAt` blocks it |
| `witK` or `graphWitK` is supplied here | **MEASURED FALSE.** Neither is built; both are priced |
| `graphWitK` needs only existing fields | **MEASURED FALSE.** Its `f` conclusion needs the carrier IN the bound, and no field says that |
| `wCodesK`'s premise constrains `w'` to be a code set | **MEASURED FALSE.** No `closedAt`, no `shapedAt` in its telescope |
| `wCodesK`'s arity conjunct is refuted here | **MEASURED FALSE.** The countermodel is built; one clause walls, section 6.3 |
| the singleton of one is a positive numeral | **MEASURED FALSE.** `Bisect344B.agda`, exit 0 |
| the `m = 0` wall is an artefact of one route | **MEASURED FALSE.** Two independent routes both fail |
| the chapter is re-checked by this task | **MEASURED FALSE.** I ran no whole-chapter check; the interface was cached and I did not touch it |
| anything landed in `src/` | **MEASURED FALSE.** `git status` shows `agents/tasks/LJ-1-344/` only |
| a run hit a wall | see section 10 |

## 10. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before every
invocation: **0 every time**.

**FLOORS, BOTH REPORTED (C-53).** Empty-file floor `Floor344.agda`: **0.92 s**.
Import-block floor `Floor344B.agda`, the same imports and no definition:
**2.62 s**.

**THE SUPPLY'S OWN DELTA IS 3.09 minus 2.62 = 0.47 s, WHICH IS UNDER THE
EMPTY-FILE FLOOR. It is UNMEASURABLE, not small.** I do not claim the supply is
cheap in seconds; I claim its cost cannot be separated from the noise at this
size.

**A CACHE WARNING, inherited from `[LJ-1.345]` and re-confirmed.** My files load
`L.Condensation` from its committed interface. **No figure here is a cold check
of the chapter**, and none is offered as one.

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-344/Floor344.agda` | 0 | 0.92 |
| `agents/tasks/LJ-1-344/Floor344B.agda` | 0 | 2.62 |
| `agents/tasks/LJ-1-344/Supply344.agda` (first green) | 0 | 2.87 |
| `agents/tasks/LJ-1-344/Supply344.agda` (`+ KWire`) | 0 | 3.27 |
| `agents/tasks/LJ-1-344/Supply344.agda` (final) | 0 | 3.09 |
| `agents/tasks/LJ-1-344/ControlA344.agda` (EXPECTED RED) | 42 | 2.62 |
| `agents/tasks/LJ-1-344/ControlB344.agda` (EXPECTED RED) | 42 | 1.68 |
| `agents/tasks/LJ-1-338/ProbeKValue338.agda` (re-run) | 0 | 9.37 |
| `agents/tasks/LJ-1-341/ProbeTies341.agda` (re-run) | 0 | 1.32 |
| `agents/tasks/LJ-1-344/Bisect344B.agda` (first, orientation slip) | 42 | 1.94 |
| `agents/tasks/LJ-1-344/Bisect344B.agda` | 0 | 2.01 |
| `agents/tasks/LJ-1-344/Residue344.agda` (`empty-spec` route) | INTERRUPTED | 330 |
| `agents/tasks/LJ-1-344/Bisect344A.agda` | INTERRUPTED | 400+ |
| `agents/tasks/LJ-1-344/Bisect344D.agda` | INTERRUPTED | 160+ |
| `agents/tasks/LJ-1-344/Residue344.agda` (regularity route) | INTERRUPTED | 300+ |

**NO INVOCATION REACHED THE 30-MINUTE WALL.** I interrupted four runs EARLY, at
330 s, 400 s, 160 s and 300 s, because a bisection was cheaper than the wait.
The brief's protocol is interrupt, report elapsed seconds, bisect; I report the
elapsed seconds above and the bisection in section 6.3. **NO heap exhaustion.
The cap was never raised.**

## 11. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-345/lj-1.345-report.md`, read WHOLE.** **Line read:**
  its section 3, 「`src/L/Coding/Bound.lagda.md` carries `pr∈λ` (`:69`),
  `trans∈λ` (`:93`) … and NO singleton closure … The next task's first line
  stands as written」. **TOOK** it as the claim under test. **CORRECTED it:**
  the gap is real, the SUPPLIERS it names are the wrong ones, and the closure
  costs 8 lines from `KFacts` and not two from `BoundOver`.
- **`agents/tasks/LJ-1-341/lj-1.341-report.md` and `ProbeTies341.agda`, read
  WHOLE and re-run.** **Line read:** `ProbeTies341.agda:285-286`, `sgltIn x hx
  = transIn (pr x x) ⁅ x , x ⁆ (pair∈pr x x) (prIn x x hx hx)`. **TOOK** the
  mathematical shape, which is right. **REJECTED its sort:** its `prIn` and
  `transIn` are over `V ℓ`, and the tie needs the closure at `fst` of an L
  element, which is why `arityK` and not `trans∈λ` is the supplier.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`, read WHOLE.** **Line read:**
  `:194-196`, residues 5 and 6, 「its entry `z` carries NO hypothesis, so the
  tie climbs from an unbounded set」. **TOOK** its residue table as the map of
  the remaining four. **EXTENDED it:** its residues 1 and 2 are worse than it
  said, and section 6.2 gives the reason.
- **`archive/dev/TASKS-archived.md`, read the header and the index shape.**
  **TOOK SHAPE ONLY:** a retired route's dispatch history. **REJECTED every
  figure:** that route has a different carrier and no `KFacts` record, so no
  count and no seconds figure from it prices anything here.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:238-256`.**

**THE ONE LINE THE BRIEF ASKS FOR: my supply is the port of something Devlin
PROVES, not of something he assumes.** `:246-249` says the argument builds `K(u)`
as the finite sequences over the formula set, the variables and the members of
`u`, and then binds every unbounded quantifier by it. **Closure of `K(u)` under
pairing and its transitivity are properties Devlin establishes of that
construction**, and `sgltK` is one composition of exactly those two. `[LJ-1.345]`
confirmed the same reading against the primary source at
`_build/literature/dev2.txt:593-630`.

**The repair's HYPOTHESIS is the port of his 「x ∈ u」, as `[LJ-1.345]`
established. My SUPPLY is the port of his closure lemma.** The two halves meet:
his premise becomes our hypothesis, his closure becomes our term.

**WHY NOT the rest of the digest.** `:243-244` is the `[LJ-1.12]` Δ₀ question,
settled. `:258` onward is Step D, which no tie of `LeafAgree` reaches. The
cardinality halves of 5.5 and 5.6 are another step, and C-46 forbids using
Devlin's tower axis as DD4's.

## 13. WHAT I DID NOT SETTLE

- **`witK` and `graphWitK`.** Priced, not built, and `graphWitK` needs one new
  `KFacts` field.
- **The `wUnCodesK`, `gCodesK`, `gUnCodesK` twins** of section 6.2. The same
  reading applies to all four by their telescopes, but I ran the countermodel
  against `wCodesK` only.
- **The chapter's own green with the supply landed.** Nothing landed and I ran
  no whole-chapter check.
- **`KValue`'s alignment count.** Re-run green, not re-aligned.
- **Whether the carrier stage is always at least 1 at the real call sites.** I
  added it as a named hypothesis and did not chase its supplier.

## 14. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-344/`: this report, `Supply344.agda`,
`ControlA344.agda`, `ControlB344.agda`, `Residue344.agda`, `Floor344.agda`,
`Floor344B.agda`, and the three bisection files `Bisect344A.agda`,
`Bisect344B.agda` and `Bisect344D.agda`. `git status --short` shows that
directory and nothing else. **`src/` holds no probe of mine and I opened no file under `src/` for
writing.** I read `src/L/Condensation.lagda.md`, `src/L/Coding/Bound.lagda.md`,
`src/L/Coding/Powerset.lagda.md`, `src/L/Coding/Model.lagda.md`,
`src/L/Coding/Shape.lagda.md` and `src/V/Coding.lagda.md`. I read and re-ran
probes in `agents/tasks/LJ-1-338/` and `agents/tasks/LJ-1-341/` and edited
neither directory. I did not open `src/Everything.lagda.md`, `dev/PLAN.md`,
`dev/LESSONS.md`, `AGENTS.md` or `.claude/` for writing. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`. No em dash in any
language. `.venv/bin/python scripts/gate/lint-prose.py --check` and
`.venv/bin/python scripts/gate/lint-agda.py --check` both exit 0 on everything I
wrote.
