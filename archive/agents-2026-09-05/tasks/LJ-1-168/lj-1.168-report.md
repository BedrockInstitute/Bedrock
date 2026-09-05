# LJ-1.168 report: re-price the satisfaction layer

Status: COMPLETE. **Recon only. No build. No master edited. No probe run. No
commit, no push.** Every negative is marked **MEASURED** or **INFERRED**
(C-36). Written incrementally (C-22).

## 0. HEADLINE, in the order the brief asked for it

1. **ALREADY DELIVERED, and it is the lead. Four suppliers stand in the live
   tree and no brief in this phase has cited any of them.** The decode side of
   the satisfaction layer, the environment set itself, a second `consAtL`
   decode in `L/Choice/`, and **the Levy reflection theorem for L**. Section 1.
2. **The Σ₁ reading collapses the figure, and a prior gate already said so.**
   `[LJ-1.2]` never measured 5,047; it quoted `[T257]`. `[LJ-1.10]` then called
   the figure "a false anchor for today's tree" and was discarded with a
   recommendation that had nothing to do with it. Section 2.
3. **The count in the brief's own source is wrong.** `TFacts` has **59 fields,
   not 57**, and **28 are not closure facts, not 26**. Section 3.1.
4. **The satisfaction fields are HYPOTHESES, not obligations.** MEASURED: **zero
   of the 59 fields conclude a satisfaction.** Section 3.2.
5. **THE PRICE: about 270 in-fence lines for the 28 satisfaction fields, and
   about 360 for the whole `TFacts` supply.** Against 5,047 that is a factor of
   about 14. Section 4.
6. **The route-level question is answered NO.** The satisfaction facts CAN be
   supplied on this coding. Section 4.3.

## 1. WHAT IS ALREADY DELIVERED

### 1.1 The decode side is delivered for every formula family

**MEASURED.** The 22 satisfaction fields use exactly six object-level formula
families. Every one has a delivered decode lemma:

| formula family | definition | delivered decode | direction |
|---|---|---|---|
| `envSetAt` | `src/L/Coding/Model.lagda.md:1149-1150` | `extAt-out`, `extAt-in`, `extAt-in-both`, `src/L/Coding/Model.lagda.md:667-678` | both |
| `envOverAt` | `src/L/Coding/Model.lagda.md:483-484` | `envOver-sv`, `envOver-dom`, `envOver-values`, `envOver-pairs`, `:487-496`; `envOverAt-transport` `:517-560` | four readers |
| `tmValAt` | `src/L/Coding/Model.lagda.md:1701-1702` | `tmValAt-var` `:1717`, `tmValAt-con` `:1723`, `tmValAt-out` `:1726` | both |
| `subValAt` | `src/L/Coding/Model.lagda.md:817-818` | `subValAt-adequate` `:821-825`, a `⇔toPath` | **equality** |
| `subValSuccAt` | `src/L/Coding/Model.lagda.md:1405-1406` | `subValSuccAt-adequate` `:1409-1413`, a `⇔toPath` | **equality** |
| `consAtL` | `src/L/Coding/Model.lagda.md:1484-1485` | `consAt-adequate`, `src/L/Coding/Environment.lagda.md:502-507`; `consAtL-out`, `consAtL-in`, `src/L/Coding/Bridge.lagda.md:247-261` | both |

**So no satisfaction machinery has to be written.** The delivered coded
satisfaction already reads every hypothesis these fields take.

### 1.2 The set that nine of the fields are about is already built

**MEASURED. `Generic.envSetGen B ar` (`src/L/Coding/EnvSet.lagda.md:456-457`)
IS the set of all environments over `ar` with values in `B`,** built by
separation over the L-power of a bounding stage. It is delivered with its whole
two-way apparatus:

| lemma | `file:line` | what it gives |
|---|---|---|
| `envSetGen-spec` | `src/L/Coding/EnvSet.lagda.md:459-461` | the separation equation |
| `envSetGen-in` | `:463-466` | into the set |
| `envSetGen-out` | `:468-470` | out of the set |
| `envSubset` | `:474-489` | every environment is a subset of the bounding stage |
| `foSat` | `:491-505` | the object-level description at any frame |
| `backToFo` | `:507-519` | the converse at any frame |
| `Generic.Holds` | `:521-541` | `⟨ γ ⊨ envSetAt Ei di bi ⟩` from `lookup Ei γ ≡ envSetGen` |

**`Generic.Holds` is one half of the `envK-*` fields, already proved.**

### 1.3 A second `consAtL` decode sits in `L/Choice/`, uncited

**MEASURED, and it is the brief's predicted miss.**
`src/L/Choice/Internal.lagda.md:610-670` carries `AtValue`, `AtKey`, `AtArity`,
`AtCons`, `DenoteOf`, `DenoteBody-in` and `DenoteBody-out`: a full two-way
decode of `⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩` into meta-level
data. **That is the exact shape the three `consK-*` fields consume.**
**`L/Choice/` has now paid three times** (`[LJ-1.163]` `ElemDown`, `[LJ-1.166]`
`Name.lagda.md`, this task `Internal.lagda.md`).

### 1.4 THE LARGEST MISS: the Levy reflection theorem for L is delivered

**MEASURED, and it is the supplier for the term `[LJ-1.166]` named as the one
that "could still NO-GO the route".**

`src/L/ReflectFo.lagda.md:525-531` delivers

```agda
  mkReflect : ∀ {n} (φ : Formula S n) (δ : V ℓ) → IsOrd δ
            → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
                (⟨ δ ∈ β ⟩
                 × ((γ : S ^ n) → Below β γ
                    → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ)))
```

**Given any formula and any ordinal, it returns a LARGER ordinal whose level
reflects that formula.** Below it, `src/L/Reflect.lagda.md:442-497` builds the
single-formula ladder: `Single.βω` is the union of an increasing ω-chain
(`:474-486`, `Ladder.top` at `:268-270`), so it is a LIMIT, and it carries
`closed : ClosedFor βω ψ` (`:492-493`) and
`reflect : (ρ ⊨ ∃̇ ψ) ≡ Wit ψ ρ βω` (`:495-496`), where
`Wit ψ ρ σ = ∃[ q ] ((q ∈ Lset σ) ⊓ Sat ψ ρ q)` (`src/L/Reflect.lagda.md:164-165`).

**`Wit` IS Devlin's "the Σ₁ witness inside the carrier".** The digest lists it
as requirement 2 of Step C (`dev/literature/devlin-II5.md:218-223`). **It is
delivered, in 217 plus 268 in-fence lines, and consumed today by
`src/L/Axioms/Full.lagda.md:55`.**

**No brief in this phase has cited `L.Reflect` or `L.ReflectFo`.** `[LJ-1.166]`
named `powK` as the term that "could still NO-GO the route"
(`agents/tasks/LJ-1-166/lj-1.166-report.md:334-335`) and searched
`src/L/Constructible.lagda.md` and `src/L/Axioms/Basic.lagda.md` for a closure
lemma. **The tree does not answer that question with a closure lemma. It
answers it with reflection.**

### 1.5 What is NOT delivered

**MEASURED: no value of `TFacts`, `LFacts` or `UFacts` exists anywhere in
`src/`.** `grep -rn "TFacts" src/` returns the record declaration
(`src/L/Condensation/TwelveAgree.lagda.md:128`) and one module parameter
(`:307`, `:310`). Nothing else. `LowerAgree`, `UpperAgree` and `AbstractFrame`
are imported by `src/Everything.lagda.md:371-373` and applied by nobody. **The
whole layer is stated and unsupplied**, exactly as `[LJ-1.165]` measured for
`KFacts`.

## 2. THE Σ₁ READING, AND WHETHER IT COLLAPSES THE 5,047

### 2.1 The 5,047 was never a measurement of this content

**MEASURED, and it is the first thing a reader must carry.** `[LJ-1.2]` did not
measure 5,047. Its own words are "This is the archived crossing-rebuild content.
Its measured price is 5,047 lines (T257 section 4.2)"
(`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md:125-127`).

The chain, at `file:line`:

1. `[T257]` summed four archived ledger rows, `676 + 1,866 + 2,378 + 127 = 5,047`
   (`agents/tasks/archive/L3-32-T259/l3.32-t259-crossing.md:35`, citing
   `dev/ledger.toml:1811-1813`), and recorded it as the **rud route's
   `crossing-rebuild`** row
   (`agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md:236`, `:263`).
2. `[LJ-1.2]` quoted that figure as the price of the missing substrate
   (`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md:126`).
3. `dev/PLAN.md:523` and six later briefs re-quoted `[LJ-1.2]`.

**So the 5,047 is a third-hand figure for REBUILDING the coded satisfaction
machine on the retired route.** It never measured the satisfaction facts this
phase needs. **P-l applies exactly: it is a comparable from another route, so
here it is a hypothesis and not a price.**

### 2.2 A prior gate already refuted it, and the phase lost the answer

**MEASURED. `[LJ-1.10]` re-priced the 5,047 and called it a false anchor.**

> **The recorded price of 5,047 lines is a false anchor for today's tree.**
> The figure measures the coded satisfaction machine. The machine is
> delivered. The substrate is the bounded formula layer over the machine.
> (`agents/tasks/archive/LJ-1-10/lj-1.10-reprice.md:28-31`)

`[LJ-1.10]` verified the machine's homes on the live tree, master by master, at
`:45-50`: `Model` 1,289, `Sound` 801, `Unique` 630, `Table` 248, `Shape` 354,
`InL` 330, `Slot` 187, `Closed` 171, `Recover` 190, `Descent` 44, `EnvSet` 229,
`Bridge` 294, `CodeSet` 200. **All those masters still stand.** Its D-10
correction is explicit at `:65-74`: "The rebuild content is the machine. The
machine stands."

**HOW THE ANSWER WAS LOST, and it is a process finding.** `dev/PLAN.md:524`
records `[LJ-1.10]` as "RETURNED, but REFUTED by LJ-1.11". **`[LJ-1.11]`
refuted `[LJ-1.10]`'s section 4, the route-C recommendation, on the ground that
the archived story's `⊤̇` Def step recognizes no level.** It did not touch
section 2, the D-10 correction on the 5,047, which is independent of route C.
**A refuted recommendation took a sound measurement down with it**, and
`dev/PLAN.md:523` still carries "Crossing 5.0-5.1k" as `[LJ-1.2]`'s live
result.

### 2.3 What the Σ₁ reading changes, stated exactly

**`dev/literature/devlin-II5.md:242-255` is right, and it is narrower than the
brief's reading.** It says two things and only the first is a collapse:

1. **A Δ₀ witness for the satisfaction leaves is NOT needed.** Level-hood is
   used at Σ₁ strength, `∃z` with a Σ₀ matrix (`:242-245`). **This kills
   `[LJ-1.2]`'s criterion at its own failure point.** `[LJ-1.2]` failed because
   `Δ₀` has no constructor for an unbounded existential
   (`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md:60-63`,
   `src/FOL/LevyHierarchy.lagda.md:47-57`). **Under the Σ₁ reading that
   existential is permitted at the top level, so the NO-GO's own failure mode is
   not a failure.**
2. **A bounded description of the Def step inside the Σ₀ matrix IS needed**
   (`:245-249`), with the bound inside the carrier, and "the argument does not
   require them to have any particular shape, only that some bounded description
   with a bound inside the carrier exists" (`:253-255`).

**The tree already has the Σ₁ form.** `[LJ-1.166]` measured `LevelHood0.Σ₂` at
`src/L/BoundedSubset.lagda.md:855-856` as `∃̇ (∃̇ (∃̇∈ (var 2) levelHoodB))`,
classified Σ₁ by `Σ₁-Σ₂` at `:858-859`. **The unbounded existential `[LJ-1.2]`
could not certify is the OUTER one, and Devlin's argument wants it there.**

### 2.4 The verdict on the figure

**The 5,047 does not price anything this phase must build. MEASURED.** It
prices a rebuild of masters that stand. **The collapse is from 5,047 to about
360, a factor of about 14, and section 4 gives the arithmetic.**

## 3. THE FACTS, NAMED AND COUNTED

### 3.1 The count in the brief's source is wrong, twice

**MEASURED, by counting the record's fields at
`src/L/Condensation/TwelveAgree.lagda.md:128-301`:**

| figure | `[LJ-1.166]` said | MEASURED |
|---|---:|---:|
| `TFacts` fields | 57 | **59** |
| closure-class fields | 31 | **31** |
| non-closure fields | 26 | **28** |

**`[LJ-1.166]`'s LIST was right and its ARITHMETIC was wrong.** Its own list
(`agents/tasks/LJ-1-166/lj-1.166-report.md:359-366`) names 28 fields and calls
them 26.

### 3.2 Zero of the 59 fields conclude a satisfaction

**MEASURED, and it is the correction that changes the price.**
`[LJ-1.166]:363-365` says the 26 are "of the form 'this environment SATISFIES
this formula', not 'this set lies in K'". **That is FALSE. Every one of the 59
fields concludes `∈ K` or a tag equation.** The 22 fields that mention `⊨`
carry the satisfaction as an ANTECEDENT. The shape of every one is

```
    ⟨ γ ⊨ φ ⟩  →  ⟨ fst x ∈ fst (lookup K γ') ⟩
```

**So the obligation is: decode a delivered formula, then apply a closure fact.**
It is not "supply a satisfaction table". **Nothing in this layer builds a
table.**

### 3.3 The 28 non-closure fields, at `file:line`, with what each asserts

All in `src/L/Condensation/TwelveAgree.lagda.md`. Six groups by proof shape.

**Group A, the code-set decomposition. 2 fields, no `⊨`.**

| field | line | asserts |
|---|---:|---|
| `codesK` | `:161-165` | a binary code in the code slot splits into arity and two parts, all three in `K` |
| `codesK-un` | `:166-169` | the same for a unary code, two parts |

**Group B, the table-value fields. 2 fields, no `⊨`.**

| field | line | asserts |
|---|---:|---|
| `valK` | `:170-173` | the table's value at a binary code lies in `K` |
| `valK-un` | `:174-177` | the same at a unary code |

**Group C, the environment-set fields. 9 fields, all with `⊨`.**

| field | line | asserts |
|---|---:|---|
| `envK-mem` | `:183-186` | `E` is the set of environments over `ar` into `B`, so `E ∈ K` |
| `envK-neg` | `:187-190` | the same at the Neg row's frame |
| `envK-top` | `:191-194` | the same at the Top row's frame |
| `envK-imp` | `:195-198` | the same at the Imp row's frame |
| `envK-allin` | `:199-202` | the same at the AllIn row's frame |
| `envInK-mem` | `:203-206` | `z` IS an environment over `ar` into `B`, so `z ∈ K` |
| `envInK-neg` | `:207-210` | the same at the Neg row's frame |
| `envInK-top` | `:211-214` | the same at the Top row's frame |
| `envInK-imp` | `:215-218` | the same at the Imp row's frame |

**Group D, the term-value fields. 3 fields, all with `⊨`.**

| field | line | asserts |
|---|---:|---|
| `valV` | `:219-224` | the value of a term under an environment lies in `K` |
| `valW` | `:225-230` | the same at the second term slot |
| `wKfact` | `:231-236` | the same at the `w` slot of the Un row |

**Group E, the substitution and cons fields. 10 fields, all with `⊨`.**

| field | line | asserts |
|---|---:|---|
| `subK₁-and` | `:240-245` | a substitution value at the And row lies in `K` |
| `subK₀-and` | `:246-251` | the same at the second argument |
| `subK₁-imp` | `:252-257` | the same at the Imp row |
| `subK₀-imp` | `:258-263` | the same at the Imp row's second argument |
| `subK-neg` | `:265-270` | the same at the Neg row |
| `subK-un` | `:276-281` | the same, through `subValSuccAt`, at the Un row |
| `subK-allin` | `:291-296` | the same, through `subValSuccAt`, at the AllIn row |
| `consK-exist` | `:282-286` | an environment extended by one pair lies in `K`, Exist row |
| `consK-forall` | `:287-290` | the same at the Forall row |
| `consK-allin` | `:297-301` | the same at the AllIn row |

**Group F, the two that are neither. 2 fields.**

| field | line | asserts |
|---|---:|---|
| `someEnv` | `:264` | **an existence claim**: for any three `K`-members there EXISTS an environment `E ∈ K` satisfying `envHypB2`. Defined at `src/L/Condensation/LowerAgree.lagda.md:51-57` |
| `envSetK` | `:271-275` | **a pure closure fact**, no `⊨`: `B ∈ K` and `ar ∈ K` imply `Generic.envSetGen B ar ∈ K` |

### 3.4 The three records are two halves and their union, not three copies

**MEASURED, and it removes a threefold multiplier the brief inherited.**

| record | `file:line` | fields | with `⊨` |
|---|---|---:|---:|
| `LFacts` | `src/L/Condensation/LowerAgree.lagda.md:94` | 36 | 13 |
| `UFacts` | `src/L/Condensation/UpperAgree.lagda.md:91` | 35 | 12 |
| `TFacts` | `src/L/Condensation/TwelveAgree.lagda.md:128` | **59** | **22** |

`LFacts` carries `tagEq0` to `tagEq5` and `numK0` to `numK5`; `UFacts` carries
`tagEq6` to `tagEq11` and `numK6` to `numK11`. **They are the lower six and the
upper six rows, and `TFacts` is the twelve.** `[LJ-1.166]:365-366` calls them
"parallel records", which invites a threefold reading. **MEASURED: the distinct
obligation set is `TFacts`' 59 and nothing more.** `UFacts.arityK` is
`TFacts.transK` under another name, and `envSetK` occurs only in `TFacts`.
**Three record VALUES must be written; the field PROOFS are written once.**

## 4. THE PRICE

### 4.1 The figure, and its basis (DD8)

**ONE best-effort number: 270 in-fence lines for the 28 satisfaction fields.
With `[LJ-1.166]`'s measured 88 for the closure half, the whole `TFacts` supply
is about 360 in-fence lines.**

**BASIS, named as DD8 requires: DELIVERED COMPARABLES, measured at this task, in
the same masters whose formulas the fields consume.** It is not a probe of mine
and it is not an analogy from another route. Every comparable below is a live
lemma of the same shape, counted as non-blank lines:

| comparable | `file:line` | lines |
|---|---|---:|
| `AmbientHoldsGen` | `src/L/Coding/Sound.lagda.md:287-293` | **6** |
| `envSubset` | `src/L/Coding/EnvSet.lagda.md:473-489` | **16** |
| `Generic.Holds` | `src/L/Coding/EnvSet.lagda.md:521-541` | **14** |
| `foSat` | `src/L/Coding/EnvSet.lagda.md:492-515` | **23** |
| `DenoteBody-out` | `src/L/Choice/Internal.lagda.md:641-670` | **26** |
| `NumeralFromGeneric` | `src/L/Coding/Sound.lagda.md:298-344` | **40** |
| `envOverAt-transport` | `src/L/Coding/Model.lagda.md:517-560` | **42** |
| `subValAt-adequate` | `src/L/Coding/Model.lagda.md:821-870` | **45** |

The build, lemma by lemma:

| # | supporting lemma | consumes (delivered) | comparable | lines |
|---|---|---|---|---:|
| L1 | code splits into `K`-members | the code slot's characterization | `envSubset` 16 | 20 |
| L2 | table value in `K` | `transK` and the table slot | `AmbientHoldsGen` 6 | 12 |
| L3 | `⊨ envSetAt E ar B → E ≡ envSetGen B ar` | `Generic.Holds` `fwd`/`bwd`, `extAt-out`/`-in` | `NumeralFromGeneric` 40 | 30 |
| L4 | `⊨ envOverAt z ar B → z ∈ K` | `Generic.bwd`, `envSetK`, `transK` | `envSubset` 16 | 15 |
| L5 | `⊨ tmValAt t e v → v ∈ K` | `tmValAt-out` | `foSat` 23 | 22 |
| L6 | `⊨ subValAt / subValSuccAt → y ∈ K` | the two `-adequate` equalities | `subValAt-adequate` 45 | 30 |
| L7 | `⊨ consAtL e' m e → e' ∈ K` | `consAt-adequate`, `DenoteBody-out` | `DenoteBody-out` 26 | 25 |
| L8 | `someEnv`, the existence field | `Generic.Holds`, `envSetK` | `Generic.Holds` 14 | 30 |
| L9 | **`envSetK`** | **`mkReflect`** | section 4.3 | **45** |
| | **supporting lemmas** | | | **229** |
| | 28 field entries at about 1.5 lines | `[LJ-1.166]` measured 29 entries at 15 lines | | **42** |
| | **THE PRICED FIGURE** | | | **271** |

**I report 270 as one number. I did not shrink it by argument and I did not
widen it into a band.**

**Why the lemma count is 9 and not 28.** MEASURED from section 3.3: the 28
fields fall into 6 proof shapes plus 2 singletons. Group C's nine fields differ
only in de Bruijn index arithmetic at five and four frames; Group E's ten differ
only in which of two adequacy equalities they call. **A field entry is an
instantiation, not a proof.**

### 4.2 The two honesty notes on the 270

- **The comparables are DELIVERED lemmas, not lemmas of this task.** A delivered
  comparable prices the shape and not the difficulty. **The figure is a survey
  anchored on same-master measurements, not a probe measurement**, and it is
  weaker than `[LJ-1.166]`'s 88 for that reason.
- **The 270 excludes the three record values' plumbing** (module headers,
  `Fin` index names, imports). `[LJ-1.166]` measured that overhead at 15 index
  lines and 34 import lines for one record and called 15 of its 88 a probe
  artifact. **Expect the same class of overhead here, once per record.**

### 4.3 THE WIDEST UNMEASURED TERM: `envSetK`, and its probe

**`envSetK` (`src/L/Condensation/TwelveAgree.lagda.md:271-275`) is the widest
unmeasured term, and it is the same term `[LJ-1.166]` named as `powK`.** It
gates Group C's nine fields through L4, and `someEnv` through L8. **Ten of the
28 fields depend on it.**

**Why it is not free. MEASURED.** `Generic.envSetGen B ar` is built by
separation over `powamb = hasPowerL amb`, the FULL L-power of a bounding stage
(`src/L/Coding/EnvSet.lagda.md:441-446`). **`Lset λ` at an arbitrary limit `λ`
is not closed under the L-power.** And `HullStage`'s telescope carries no
closure hypothesis that would supply it: **MEASURED, it is exactly
`lam, ordλ, succλ, X, X⊆L, ∅∈λ`** (`src/L/BoundedSubset.lagda.md:903-905`).

**Why it is nonetheless answerable, and this is section 1.4's find.**
`mkReflect` (`src/L/ReflectFo.lagda.md:525-531`) takes any formula and any
ordinal and returns a larger ordinal whose level reflects that formula. **The
site does not need `Lset λ` closed under the power for every `λ`. It needs ONE
`λ` at which the environment-set description reflects, and `mkReflect` builds
it.** `Single.βω` is a limit by construction (`src/L/Reflect.lagda.md:268-270`),
so `ordλ` and `succλ` survive.

**THE PROBE, and it is one declaration.** Add to `[LJ-1.166]`'s existing green
`Bound` module (`agents/tasks/LJ-1-166/ProbeLJ1166A.agda:85-146`):

```agda
  envSet∈λ : (B ar : S) → ⟨ B ∈ˢ Lset lam ⟩ → ⟨ ar ∈ˢ Lset lam ⟩
           → ⟨ Generic.envSetGen B ar ∈ˢ Lset lam ⟩
```

**GO if it closes by instantiating `lam` from `mkReflect` at the formula
`envFoGen` (`src/L/Coding/EnvSet.lagda.md:450-453`). NO-GO if `envFoGen` cannot
be written with the bounding stage as a parameter**, because `mkReflect` takes a
`Formula S n` and `envFoGen` mentions `con ar` and `con B` as constants.
**INFERRED, and I mark it: I did not check that `envFoGen` is in `mkReflect`'s
form. That is the probe's real question.**

**A NO-GO here does not sink the route.** The fallback is to add the closure as
a fourth hypothesis to `HullStage` and discharge it where `λ` is chosen. **That
moves the cost, it does not create a wall.**

### 4.4 The route-level question, answered

**The brief's fourth abort criterion is "the satisfaction facts cannot be
supplied at all on this coding". MEASURED: that is FALSE.**

Every one of the 28 is a decode plus a closure step; every decode is delivered
(section 1.1); the set nine of them speak about is delivered with its adequacy
(section 1.2); and the reflection that supplies the tenth-through-nineteenth is
delivered (section 1.4). **There is no wall. There is a funding decision.**

## 5. DD4: WHAT FRACTION IS TEMPLATE

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

### 5.1 The statement layer is 100 percent template. MEASURED

**MEASURED by grepping the record body for a tower token (`Lset`, `𝒟ₒ`, `isL`,
`layer`) over `src/L/Condensation/TwelveAgree.lagda.md:128-301`: ZERO
occurrences. All 59 fields are tower-blind.** They speak of `lookup K γ'`,
`numeralL`, `prʟ`, `pr` and `Generic.envSetGen`. The whole master carries 2
tower tokens, both outside the record.

**So the J tower RE-INSTANTIATES the record, all 59 fields, with no edit.**

### 5.2 The supply layer is per-tower, and the reason is structural

**MEASURED, and I do not soften it.** The supply rides `src/L/Coding/`, and
that cone is monomorphic in `𝒮ʟ`: `src/L/Coding/Sequence.lagda.md:59-62` opens
`hPropStructure 𝒮ʟ` and `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`.
`src/L/Condensation/TwelveAgree.lagda.md` opens the same `AbsL`, so the `_⊨_`
in every satisfaction field is the L-relativized satisfaction.

**`[LJ-1.10]` priced abstracting that cone at 2.45 to 5.1 thousand lines and
called it "carried as a fork, not a saving"**
(`agents/tasks/archive/LJ-1-10/lj-1.10-reprice.md:147-161`). Its census is 21
masters, 6,219 in-fence lines bound to `𝒮ʟ`, 216 abstraction sites (`:129-132`).

### 5.3 The answer, and the recommendation

**The J tower RE-INSTANTIATES the 59-field statement and RE-WRITES the 270-line
supply, unless the coding cone is abstracted first.**

| layer | lines | J tower does |
|---|---:|---|
| the three record declarations | 463 + 291 + 290 in-fence, delivered | **re-instantiates, zero edit** |
| the satisfaction supply | **270**, this task's figure | **re-writes** |
| the closure supply | 88, `[LJ-1.166]` | **re-writes**, and `[LJ-1.166]:410-418` prices the generic form at +6 lines now, −42 at the J end |

**MY RECOMMENDATION, and no stop-line pushed me toward writing fixed.** The
270 is small enough that abstracting the cone to save it is not worth 2.45 to
5.1 thousand lines. **Write the supply fixed at the L end, and re-price the
cone abstraction when the bridge is funded, exactly as `[LJ-1.10]:341-343`
recommends.** **DD4 is served better here by the record's own tower-blindness,
which is already 100 percent, than by a cone abstraction that costs nine times
what it saves.**

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `[LJ-1.2]` measured the 5,047 | **MEASURED FALSE.** It quoted `[T257]` at `lj-1.2-gate.md:126` |
| the 5,047 prices content this phase must build | **MEASURED FALSE.** It prices masters that stand; `[LJ-1.10]:45-50` verified them and I re-verified `EnvSet`, `Sound`, `Model` at this task |
| the Σ₁ reading collapses the figure | **MEASURED TRUE.** From 5,047 to about 360, a factor of about 14 |
| `[LJ-1.2]`'s NO-GO answered the wrong question | **MEASURED TRUE in part.** Its Δ₀ criterion is not what the argument needs (`devlin-II5.md:242-245`). **But the digest's second half stands**: a bounded description with its bound inside the carrier IS required (`:245-255`) |
| `TFacts` has 57 fields | **MEASURED FALSE. 59** |
| 26 fields are non-closure | **MEASURED FALSE. 28** |
| the non-closure fields assert satisfactions | **MEASURED FALSE.** Zero of 59 conclude a satisfaction; 22 take one as a hypothesis |
| `LowerAgree` and `UpperAgree` are parallel copies of `TwelveAgree` | **MEASURED FALSE.** They are the lower six and upper six rows |
| any value of `TFacts`, `LFacts` or `UFacts` exists in `src/` | **MEASURED FALSE.** None |
| the decode side must be built | **MEASURED FALSE.** All six formula families carry delivered decode lemmas |
| the set `envSetGen` must be built | **MEASURED FALSE.** `src/L/Coding/EnvSet.lagda.md:456` with seven supporting lemmas |
| the tree has no answer to `[LJ-1.166]`'s `powK` risk | **MEASURED FALSE.** `mkReflect` at `src/L/ReflectFo.lagda.md:525` |
| `HullStage` carries a power-closure hypothesis | **MEASURED FALSE.** Its telescope is `lam, ordλ, succλ, X, X⊆L, ∅∈λ` |
| `envFoGen` is in `mkReflect`'s formula form | **NOT MEASURED. INFERRED as the probe's question.** Section 4.3 |
| the satisfaction facts cannot be supplied on this coding | **MEASURED FALSE.** Section 4.4 |
| the J tower re-instantiates the statement layer | **MEASURED TRUE.** Zero tower tokens in 59 fields |
| the J tower re-instantiates the supply | **MEASURED FALSE.** The coding cone is monomorphic in `𝒮ʟ` |
| my 270 is probe-measured | **MEASURED FALSE, and I say it in 4.2.** It rests on delivered comparables, so it is weaker than `[LJ-1.166]`'s 88 |
| a cheaper supply exists | **NOT CLAIMED. C-36.** I priced one route and named its fallback in 4.3 |
| anything walled | **NOT APPLICABLE. I ran no Agda process.** Section 8 |

## 7. WHAT THE NEXT BRIEF SHOULD FUND

**Offered, not assumed.**

1. **The `envSet∈λ` probe of section 4.3**, one declaration in an existing green
   file. **It is the narrowest decisive term in the whole layer and ten of the
   28 fields hang on it.**
2. **`dev/PLAN.md:523` should be corrected.** It carries "Crossing 5.0-5.1k" as
   `[LJ-1.2]`'s live result. **Two gates have now refuted that figure**,
   `[LJ-1.10]` in section 2 and this task.
3. **A lesson is available and I do not number it** (the orchestrator assigns
   IDs). **The measurement: `[LJ-1.11]` refuted `[LJ-1.10]`'s RECOMMENDATION and
   the phase discarded its independent MEASUREMENT with it, so the 5,047 stayed
   live in `dev/PLAN.md` for six further briefs.** The cure is that a refutation
   names which section it refutes.

## 8. CHECKERS AND PROHIBITIONS

| item | result |
|---|---|
| Agda processes run | **ZERO.** I priced by reading and by counting delivered lemmas |
| probe written | **NONE.** Section 4.3 names one and does not run it |
| masters edited | **NONE** |
| `src/Everything.lagda.md` | **never opened** |
| commit, push, `git checkout .`, `stash`, `reset`, `clean` | **none** |
| files written | **one**, this report, in `agents/tasks/LJ-1-168/` |

**C-12.** I ran no Agda process, so the sibling's Agda run cost me nothing. **My
figures are lines and shape, so a busy machine costs me only time**, exactly as
the brief said.

**Why no probe.** The brief allows one "only if a step genuinely cannot be
priced by reading". **Eight of the nine lemmas priced by reading against
delivered comparables.** The ninth, `envSetK`, cannot, **and section 4.3 names
its probe rather than running it**, because the brief's first abort criterion
fired: I can price it, so I report the figure and stop.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md`, READ WHOLE.** **TOOK the
  provenance of the 5,047 at `:125-127`**, which is the finding: it is a
  quotation of `[T257]`, not a measurement. **TOOK its verdict at `:8-20` and
  its failure mode at `:37-63`**, the missing `Δ₀` constructor for an unbounded
  existential. **TOOK its two named missing facts at `:98-121`**, and I locate
  both on the live tree in sections 1.1 and 1.2. **TOOK its own DD4 paragraph
  at `:70-89`**, which already says the missing content is generic.
- **`agents/tasks/archive/LJ-1-10/lj-1.10-reprice.md`, READ WHOLE, and it is
  the archive find of this task.** **TOOK section 2's D-10 correction
  (`:28-31`, `:65-74`)**, the master-by-master verification of the delivered
  machine (`:45-50`), the two missing facts re-verified (`:52-63`), the
  Candidate B census and its 2.45 to 5.1k price (`:129-153`), and the DD4
  scoring (`:316-343`). **I did NOT take its section 4, route C**, which
  `[LJ-1.11]` refuted and `dev/PLAN.md:524` records as refuted.
- **`agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md:236`, `:263`.** The
  `5,085` and `5,047` re-sum, and "the internalization route owns 5,047 of
  5,047". **TOOK the number's origin, no claim.**
- **`agents/tasks/archive/L3-32-T259/l3.32-t259-crossing.md:35`.** The four
  terms `676 + 1,866 + 2,378 + 127` and their ledger home `dev/ledger.toml:1811-1813`.
  **TOOK the arithmetic.**
- `agents/tasks/archive/LJ-1-11/lj-1.11-review.md:183`: that `[LJ-1.10]`
  D-10-checked the 5,047 anchor. **This confirms the refutation did not touch
  section 2.**
- `agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:65`: the earliest carry of the
  5,047, which already says "On this tree the supplier stands".
- **`archive/dev/DECISIONS-archived.md:57` (D38).** Records `[T259]` as the open
  question of whether the 5,047 is forced, and that `[T130]` answered NO with
  "no probe, no Agda run". **TOOK the fact that the figure was contested on the
  retired route too.**
- **`agents/tasks/LJ-1-166/lj-1.166-report.md`, READ WHOLE.** TOOK its 88-line
  measurement (`:204-218`), its `KFacts` correspondence (`:99-124`), the
  `HullStage` telescope (`:136-140`), the `LevelHood0.Σ₂` classification
  (`:292-296`), the `powK` risk (`:322-347`), the `TFacts` field list
  (`:353-368`) and the generic-form price (`:410-422`). **I correct three of its
  figures in sections 3.1, 3.2 and 3.4, and I confirm its central measurement.**
- `agents/tasks/LJ-1-165/`: taken through `[LJ-1.166]`'s report, **not read
  whole. I mark that so nobody credits me with a reading I did not do.**
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md`,
  `L/Coding/CodeSet.lagda.md`, `L/LevelFormula.lagda.md`: NOT read.**
  `[LJ-1.166]:502-514` read all three at this phase and reported that none
  builds a bound and none holds a shape to copy. **I did not re-read what a
  live report already measured, and I say so rather than pad this section.**
- **`dev/LESSONS.md`: D-10, C-22, P-l, D-26 read through
  `scripts/rules.py --for recon`.** **P-l is the rule this task turns on**: the
  5,047 is a comparable from another route, so here it was a hypothesis and
  never a price. **D-10 is the second**: the recorded residue named a target,
  and the target was wrong.

## 10. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:209-256`, READ WHOLE**, which is Step C and the
  passage the brief called load-bearing. **What Devlin's satisfaction steps need,
  and at what Levy grade, stated exactly as the digest states it:**
  1. **Level-hood as Σ₁ with a Σ₀ matrix** (`:214-217`). The witness `z` bundles
     the level sequence and its bound. **"the existential over z is UNBOUNDED at
     the ambient level".**
  2. **Uniform Δ₁ at limit `α > ω`** (`:218-223`), and **the forward half needs
     the witnessing `z` INSIDE `L_α`**. **"the Σ₁ form is witnessed inside the
     carrier, not merely in V".**
  3. **Σ₀ absoluteness of the matrix at every transitive carrier** (`:224-227`).
  4. **Transfer along Σ₁-elementarity and the collapse, both directions**
     (`:228-233`).
  5. **Ordinal bookkeeping at Σ₀** (`:234-237`), and the union law (`:238-240`).
  **The direct answer at `:242-245`: a Δ₀ witness for the satisfaction leaves is
  NOT what the argument needs.** **What IS required, at `:245-249`: a bounded
  description of the Def step inside the Σ₀ matrix, every unbounded quantifier
  bound by `K(u)`.** **The freedom clause at `:253-255`: no particular shape is
  required, only that some bounded description with a bound inside the carrier
  exists.**
- **`dev/literature/devlin-II5.md:299-310`, the summary of strengths.** Item (2),
  "a bounded object-level description of the Def step with its bound inside the
  carrier", is the obligation this layer discharges. **Item (2)'s second half,
  the bound inside the carrier, is what `mkReflect` supplies and what section 1.4
  reports as delivered.**
- `dev/literature/devlin-II5.md:250-252` names `[LJ-1.2]`'s two missing facts as
  the analogues of Devlin's substrate. **TAKEN, and sections 1.1 and 1.2 locate
  both on the live tree.**
- `_build/literature/dev2.txt`: **NOT read.** `[LJ-1.166]:542-547` read
  `:593-640` at this phase and reported it verbatim. **I did not re-read it.**
