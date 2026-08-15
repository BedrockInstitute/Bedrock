# LJ-1.315 report: literature for the `φ₀` slot-role ruling

## 0. LEAD

**The literature favours FORM 1, and the agreement is unanimous across four
authors.** Every source that writes level-hood as a formula leaves exactly two
slots free, the VALUE and the ORDINAL, and closes every bound with it. **No
source leaves a bound free, and no source uses two independent bounds.** Devlin
states the single-bound rule as a sentence in the text: all unbounded
quantifiers of the matrix "can (without loss of meaning) be bound by the set
`K(u)`", one set (`_build/literature/dev2.txt:600-601`, READ). **Form 2 keeps
two independent bounds. That shape has NO precedent in any source I read.**

**A second finding the owner must hear.** No formalization closes the value
slot the way Bedrock does, because **no formalization writes an object-level
level-hood formula at all**. Isabelle/ZF, the most complete development, builds
`L` from a recursion over a definable powerset function and proves absoluteness
by relativization. **So Bedrock's `closeN 14` is a local design choice with no
precedent, and the slot-role problem is created by Bedrock's own closure
choice.** That is the brief's third abort criterion, and it fires.

**One caution, and it belongs beside the ruling.** Devlin's bound is DETERMINED,
not chosen: his `∃w` carries the conjunct `K(w, u)` which says `w = K(u)`
(`dev2.txt:619-620`, READ). **Neither cure supplies a determining conjunct.** Both
cures close the bound with a bare existential. That difference is real, it is
independent of the slot-role question, and it is a mathematics question that
this survey does not settle. **INFERRED** from reading the two texts side by
side.

## 1. THE COMPARISON TABLE

Every row was READ in a primary text or a fetched scan. The locator column
names the file and the line.

| # | Source, status | The statement | Arity | What it BINDS | What stays FREE | Roles of the free slots | Locator |
|---:|---|---|---:|---|---|---|---|
| 1 | Devlin 2.4, **READ** | `D(v,u) = ∃w[K(w,u) ∧ C(w,v,u)]`, and `D(v,u) ↔ v = Def(u)` | 2 | `w`, ONE bound, DETERMINED by `K(w,u)` | `v`, `u` | VALUE, ARGUMENT | `_build/literature/dev2.txt:619-623` |
| 2 | Devlin 2.6, **READ** | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`, and `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |
| 3 | Devlin 2.7, **READ** | `H(x,α) = ∃f[G(f,α) ∧ (x = f(α))]`, and `H` says `x = L_α` | 2 | `f`, and `w` inside `G` | `x`, `α` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:679-680` |
| 4 | Devlin 5.2 clause (a), **READ, restored** | `Φ(z, v, γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |
| 5 | Devlin 5.2 clause (b), **READ** | `(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]` | same | `z` | `v`, `γ` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1193-1198` |
| 6 | Jech 13.14, **READ** | "The function `α → L_α` is Δ₁", proved from a Σ₁ step `∃W[W is a function ∧ ... ∧ Y = ran(W)]` | 2 | `W`, the approximating function | value, ordinal | **VALUE, ORDINAL** | `_build/literature/jech13.txt:561-572` |
| 7 | Jech 13.13, **READ** | A Π₂ SENTENCE `σ` with `(M,∈) ⊨ σ` iff `M = L_δ` for a limit `δ` | **0** | everything | nothing | level-hood is a property of the CARRIER | `_build/literature/jech13.txt:605-614` |
| 8 | Kunen VI 3.2, **READ** | "The function `L(α)` is absolute for transitive models of ZF - P" | 2, IMPLICIT | **not exhibited** | value, ordinal | **VALUE, ORDINAL** | scratch extract of `Kunen-1980-Set_Theory.pdf`, printed Ch. VI section 3 |
| 9 | Schindler-Zeman 1.10(2), **READ** | "`x = S_γ^A` is Σ₁ over `J_α^A` as witnessed by a formula which does not depend on `α`" | 2 | not exhibited | `x`, `γ` | **VALUE, ORDINAL** | `_build/literature/sz-full.txt:322-323` |

### 1.1 What the table says, in three sentences

**THE SOURCES AGREE.** Rows 3, 4, 5, 6, 8 and 9 all leave the same pair free,
the VALUE and the ORDINAL, in that role. **Rows 1, 2 and 3 show that Devlin
closes every bound and every approximation object he introduces.** Row 7 is the
one different convention, and section 1.3 says what it means.

### 1.2 The single-bound rule, quoted

Devlin writes the rule twice, once for the step and once for the sequence. Both
sentences are legible in the scan.

> We now seek a bound for all the unbounded quantifiers in `B(v,u)`.
> (`_build/literature/dev2.txt:590-591`, **READ**)

> Hence, all unbounded quantifiers in `B(v,u)` can (without loss of meaning) be
> bound by the set `K(u) = ...`
> (`_build/literature/dev2.txt:600-601`, **READ**)

> ... all the unbounded quantifiers which figure in `E(f,α)` ... can be bound by
> the set `K(⋃ran(f))`.
> (`_build/literature/dev2.txt:655-656`, **READ**)

**ONE bound set binds ALL the unbounded quantifiers.** Devlin says so in the
text, at both levels of his construction. He never introduces a second bound
variable, and he never leaves a bound free.

### 1.3 The one convention that differs, and it does not split the ruling

Jech row 7 is a SENTENCE with zero free slots. Jech makes level-hood a property
of the CARRIER: `M ⊨ σ` holds exactly when `M` is a level. **That is a different
presentation, and it is not a different answer.** Jech also gives row 6, the
Δ₁ function `α → L_α`, whose relation has the same free pair as Devlin's. So
Jech carries BOTH shapes and neither shape leaves a bound free.

**The digest already recorded this divergence** at
`dev/literature/devlin-II5.md:296-310` and `:506-510`, and it called it D-26's
dichotomy. That reading survives and I take it.

**So the second abort criterion does NOT fire.** The sources do not disagree
with each other about the free pair. The owner is choosing between right and
wrong here, and not between conventions.

### 1.4 Kunen never writes the formula, and that is a finding

**Kunen exhibits no level formula.** His Definition VI 1.1 gives the definable
powerset as a SET, not as a formula:

> `D(A) = { X ⊆ A : ∃n ∈ ω ∃s ∈ Aⁿ ∃R ∈ Df(A, n+1) (X = {x ∈ A : s⌢⟨x⟩ ∈ R}) }`
> (Kunen 1980, printed page 165, Definition VI 1.1, **READ** in the scratch
> extract)

His absoluteness proof appeals to a general theorem about recursion, and it
never displays a syntactic witness:

> The function `L(α)` is absolute for transitive models of ZF - P. PROOF. We saw
> in V 1.7 that `Df` was absolute. It then follows easily from the methods of
> IV section 5 that `D` is absolute. Since `L(α)` was defined by transfinite
> recursion from `D`, it is absolute as well (see IV 5.6).
> (Kunen 1980, Lemma VI 3.2, **READ**)

I opened IV 5.6 to check whether a Σ₁ witness hides there. **It does not.** IV
5.6 argues by transfinite induction INSIDE the model `M`, and it exhibits no
formula (**READ**, same extract). **So Kunen agrees on the free pair and is
silent on what a level formula binds.** That is a weaker agreement than
Devlin's, and I mark it as such.

## 2. VERIFYING THE `[LJ-1.312]` READING OF DEVLIN (C-44)

The brief orders me to check the reading and to say whether the digest can
carry a ruling.

**THE READING IS CORRECT.** `[LJ-1.312]` section 7 says `Φ` has three slots,
that clause (a) closes `z` at position 0, and that `v` at 1 and `γ` at 2 stay
free as VALUE and ORDINAL. Every part of that is true of the primary text.

**THE DIGEST IS FAITHFUL ENOUGH TO CARRY THE RULING, but not for the reason it
gives.** Here is the defect, and here is why it does not matter.

| item | what the scan actually holds | verdict |
|---|---|---|
| the slot ORDER `Φ(z, v, γ)` | LEGIBLE. `dev2.txt:1186` prints "By 2.7 there is a Σ o formula Φ (z, ι;, γ) of LST such that" | the load-bearing fact is in the scan |
| clause (a)'s displayed body | **DEGRADED, almost entirely lost.** `dev2.txt:1187-1191` prints only "(a)", then "V", then "y" | the digest's clause (a) is a RESTORATION |
| clause (b) | LEGIBLE. `dev2.txt:1196-1198` prints "(Vy < α)(Vϋ)[t; = Lγ^veLa" and "A N L α 3zφ(z, ι;, y)]" | independent confirmation of the same free pair |
| Devlin 2.7's `H(x,α)` | LEGIBLE. `dev2.txt:679-680` prints "Let H(x, α) be the LST formula which says that "x = Lα", namely: 3/[G(/,α)Λ(x=/(α))]" | independent confirmation, arity 2 |

**The gap:** `dev/literature/devlin-II5.md:95-100` presents clause (a) as a
quotation and does not flag that the scan lost its display. The digest's
section 6 lists other restorations and does not list this one. **MEASURED**, by
reading `_build/literature/dev2.txt:1186-1198` line by line.

**Why the ruling still stands.** The restoration is CORRECT, and three legible
facts prove it without clause (a): the slot order at `:1186`, clause (b) at
`:1196-1198`, and 2.7's own `H(x,α)` at `:679-680`. **So no primary text needs
fetching. The fourth abort criterion does NOT fire.**

**One repair the digest should get.** Its section 6 should record clause (a) as
a restoration with its three confirming sources. I propose that text in section
5 of this report.

## 3. THE FORMALIZATIONS, ISABELLE FIRST

**READ FIRST**, as ordered: `dev/literature/formalizations.md` (243 lines,
**READ** whole) and `dev/literature/formalizations-landscape.md` (421 lines,
**READ** whole). I re-derived nothing they hold. I did no web search for this
section, because the landscape file already searched six systems through their
own indexes on 2026-08-02.

### 3.1 Isabelle/ZF, Paulson

**It faces NO slot-role question, because it writes no object-level level
formula.** Paulson builds `L` from a definable powerset function:

> `DPow(A) = {X ∈ Pow(A) ; ∃ env ∈ list(A). ∃ p ∈ formula. arity(p) ≤
> succ(length(env)) & X = {x∈A. sats(A, p, Cons(x,env))}}`
> (`dev/literature/formalizations.md:41-45`, **READ**; the file records this as
> fetched from Paulson sections 6.1 to 6.7, pages 25 to 32)

Read the shape. `DPow` is a FUNCTION of one argument. Level-hood is `Lset(α)`,
a recursion, and it is a term and never a formula. **The existentials over
`env` and `p` are set-theoretic and they sit inside a set comprehension.** They
are not slots in a de Bruijn environment, so nothing can be off by one.

**Paulson DOES internalize formulas**, in the theories `Internalize`,
`Satisfies_absolute` and `DPow_absolute`
(`dev/literature/formalizations-landscape.md:204-211`, **READ**). That
internalization exists to prove `(V = L)^L`, and Paulson calls it the largest
and hardest part of the work
(`dev/literature/formalizations.md:71-73`, **READ**). **But the internalized
objects are the ZF axioms and the separation instances, not a level-hood
formula whose free slots a later theorem re-uses.** So the question does not
arise there either. **INFERRED** from the theory list and the document text
that the landscape file quotes; I did not open the Isabelle sources myself.

**Paulson's own verdict on the metatheory bears on this ruling.** He reports
that his two `V = L` proofs do not fit together, "because the two instances of
`V = L` are formalized differently: one is relativized and the other is not"
(`dev/literature/formalizations.md:83-87`, **READ**). **That is the same class
of defect Bedrock is looking at now: two statements of one object that do not
line up.** Paulson could not repair it and left it as a challenge.

### 3.2 Lean: mathlib4 and Flypitch

**Neither builds `L` at all.** mathlib4 has no `Lset`, no `DPow` and no
set-theoretic `L` declaration, per a search of the full declaration index on
2026-08-02 (`dev/literature/formalizations-landscape.md:245-260`, **READ**).
Flypitch proves the independence of CH by Boolean-valued models and names "the
consistency of CH via construction of the constructible universe" as future
work (`dev/literature/formalizations.md:188-199`, **READ**). **So no slot-role
question exists in either.**

### 3.3 Mizar, Metamath, Coq and Naproche

**None builds `L`.** The landscape file's table is at
`dev/literature/formalizations-landscape.md:25-32` (**READ**). Mizar has the
Mostowski operations `A1` to `A7` but never defines `L(α)` or `V = L`
(`:118-141`). Metamath has no class constant `L` (`:75-83`). Coq's opam archive
has no constructible package (`:294-306`). Naproche has a `GCH` file, but `GCH`
there is an assumed axiom of the ambient theory (`:344-355`).

### 3.4 The direct answer to the brief's third question

**DOES ANY FORMALIZATION CLOSE THE VALUE SLOT THE WAY BEDROCK DOES? NO.**

**MEASURED, within the corpus I read**: no formalization in the six systems the
landscape file searched writes an object-level level-hood formula with numbered
free slots. The one system with `L` is Isabelle/ZF, and it uses a recursion over
a function.

**INFERRED, for the wider claim**: I did not open the Isabelle/ZF sources, the
mathlib4 sources or the Mizar articles myself. My claim rests on the landscape
file's index searches of 2026-08-02 and on the quotations it carries. **A later
version of any library could add this material**, and the landscape file states
that caveat itself at `:14-16`.

**SO THE BRIEF'S THIRD ABORT CRITERION FIRES.** No formalization faces this
question. **The slot-role problem is created by Bedrock's own closure choice**,
and the owner should know that before choosing a cure. The choice is not wrong
because it is unprecedented; Bedrock's port has a constraint no other project
has, and section 4 names it.

## 4. WHY BEDROCK CLOSES FOURTEEN, TRACED TO ITS ORIGIN

**THE FOURTEEN DECOMPOSE INTO TWELVE PLUS TWO, and the two halves have
different origins.** Here is the trace, all of it inside this repository.

### 4.1 The arithmetic, from the probe that builds `φ₀`

`agents/tasks/LJ-1-241/ProbeLJ1241A.agda` (**READ**, `:55-146`) builds `φ₀`:

- `base = Cnt.erase LH.levelHoodB refl`, arity **16**, at `:113-114`. The
  comment at `:112` names it "the constant-free matrix, arity 4 + 12 = 16".
- `LevelHood` is instantiated at `n = 12` (`:85`). **The twelve extra slots hold
  the twelve tag numerals.**
- `ρ` maps base slot 0 to 0, slot 1 to **14**, slot 2 to **15**, slot 3 to 1,
  and slot `4+i` to `2+i` (`:106-111`).
- `pins` pins the twelve renamed slots 2 to 13 to the numerals 0 to 11
  (`:118-133`).
- `φ₀ = closeN 14 (pins ∧̇ renamed)`, arity 2 (`:145-146`).

**So the fourteen closed slots are: twelve tag numerals, plus base slot 0, plus
base slot 3.** The probe's own comment says so at `:120-122`: "the head 14 slots
(w, K, and the twelve δ's) are existentially closed, leaving v and γ free".

### 4.2 The origin of the TWELVE: the constant-free requirement, and it is owed
to `amb`

`dev/JOURNAL.md:934-1000` (**READ** whole) records `[LJ-1.240]`. The decisive
line is `dev/JOURNAL.md:995-997`:

> It argued that binding the tag slots without defining them would suffice for
> `lh` alone, and that dies at `amb`
> (`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`): an unconstrained tag
> satisfies the formula at a wrong `v`. **So the numeral-closure is real, and it
> is owed to `amb` rather than to `lh`.**

**READ THAT CAREFULLY.** The twelve closures are NOT free. Each tag slot must
be closed AND pinned, because an unclosed or unpinned tag makes the formula
true at a wrong value. **So the twelve follow from the constant-free
requirement, and a measurement backs them.**

`dev/PLAN.md:1148` (**READ**) records the ruling row: "LJ-1.240 | DD25 review of
LJ-1.239's refutation | RECIPE UPHELD, MY ESCALATION REFUTED | The type stands
and costs `sl` and `sc` zero." And `dev/JOURNAL.md:948-953` records why the
arity-2 type is right: "the arity-2 type is RIGHT: Devlin's `∃z Φ(z,v,γ)` is
arity 2 and `erase` PRESERVES arity".

**So `[LJ-1.240]` chose the constant-free `φ₀` for a reason, it named Devlin as
the authority for the arity, and a probe measured that the tags must be closed.**

### 4.3 The origin of the TWO: the level formula's own witness and bound

Base slot 0 and base slot 3 are `levelHoodB`'s own slots. `src/L/BoundedSubset.
lagda.md:105-112` (**READ**) gives:

```
levelHoodB = ∃̇∈ (var (suc (suc (suc zero))))
               (G.graphBndAt ∧̇ (var (suc zero) ≐ var zero))
```

Under the file's own comment at `:70-73`, slot 0 is the witness `w` and slot 3
is the bound `K`. **These two are the direct analogue of Devlin's `∃z`**, and
`[LJ-1.310]:459-462` reads them the same way.

### 4.4 THE ANSWER TO THE BRIEF'S QUESTION

**DO THE FOURTEEN CLOSURES FOLLOW FROM THE CONSTANT-FREE REQUIREMENT, OR WERE
THEY AN INDEPENDENT CHOICE? BOTH, and the split is twelve to two.**

| the closures | count | origin | is it forced? |
|---|---:|---|---|
| the tag numerals `δ₀` to `δ₁₁` | **12** | `[LJ-1.240]`'s constant-free `φ₀`, so `embed` can carry the formula between carriers | **FORCED**, and measured at `ProbeLJ1178A.agda:190-192` through `amb` |
| the witness `w` and the bound `K` | **2** | `levelHoodB`'s own shape | **NOT forced by constant-freeness.** It is the port's rendering of Devlin's `∃z` |

**So `[LJ-1.310]`'s phrase "the SHAPE OF THE CLOSURE" is right about the TWO and
wrong about the TWELVE.** The twelve are not a shape choice. They are the price
of a constant-free formula, and Devlin pays none of it because he never moves a
formula between constant domains. `[LJ-1.310]:466-472` says exactly this itself,
so I extend that report rather than correct it.

**THE PART THAT IS A GENUINE CHOICE IS THE TWO**, and it is the only part the
ruling touches. Both cures leave the twelve alone.

### 4.5 Why Devlin's count is not two either, and what that means

**Devlin closes MORE than one object, and the digest's "ONE slot" reading is
about the DISPLAY and not about the content.** Clause (a) writes `∃z`, one
variable. But `z` bundles Devlin's own two objects:

- `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]` closes the bound `w`
  (`dev2.txt:659`, **READ**).
- `H(x,α) = ∃f[G(f,α) ∧ x = f(α)]` closes the sequence `f`
  (`dev2.txt:679-680`, **READ**).

Unfolded, Devlin's level-hood is `∃f ∃w [K(w,⋃ran f) ∧ F(w,f,α) ∧ x = f(α)]`.
**Two closures, one of them a bound, one of them an approximation.** Bedrock's
two are a value witness and a bound; Bedrock's approximation sequence sits
inside `GraphB`'s own bounded existential.

**So the counts line up better than "one against fourteen" suggests: Devlin
closes two objects at the top, Bedrock closes two plus the twelve tags.** The
divergence that matters is not the count. **It is WHICH slots stay free**, and
that is exactly what `[LJ-1.312]` refuted.

## 5. DOES FORM 2's MEANING HAVE ANY PRECEDENT?

**NO. MEASURED against the four sources I read, and the negative is a reading of
their text and not an absence of search.**

### 5.1 What the two forms mean, restated from the syntax

I read `src/L/BoundedSubset.lagda.md:105-112` and
`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-146` to state these. I ran no Agda.
The slot roles are `[LJ-1.312]`'s measurement and not mine.

| form | what `φ₀(v, γ)` says | how many bounds |
|---|---|---:|
| delivered | broken; the free pair is (ORDINAL, machinery bound) | 2, independent |
| **Form 1** | `∃K ∃x∈K [ x is the level at γ inside K ∧ v = x ]` | **1**, shared by the witness and the machinery |
| **Form 2** | `∃K₁ ∃K₂ ∃x∈K₂ [ x is the level at γ inside K₁ ∧ v = x ]` | **2**, independent |

### 5.2 What each source has

| source | how many bounds in the level formula | free slot for a bound? | locator |
|---|---:|---|---|
| Devlin 2.4 | **1**, `w`, and `K(w,u)` DETERMINES it | no | `dev2.txt:600-601`, `:619-620` |
| Devlin 2.6 | **1**, `w`, determined by `K(w, ⋃ran f)` | no | `dev2.txt:655-659` |
| Devlin 2.7 and 5.2 | **1**, inherited from 2.6 | no | `dev2.txt:679-680`, `:1186` |
| Jech 13.14 | **0** explicit bounds; one approximating function `W` | no | `jech13.txt:561-572` |
| Jech 13.13 | **0**; the carrier is the bound | no | `jech13.txt:605-614` |
| Kunen VI 3.2 | no formula written | no | Kunen Ch. VI section 3 |
| Schindler-Zeman 1.10(2) | not exhibited | no | `sz-full.txt:322-323` |

**No source uses two independent bounds. Devlin's text says the opposite in
words: ONE set binds ALL the unbounded quantifiers.** Section 1.2 quotes that
sentence twice, once per level of his construction.

### 5.3 The consequence for the ruling

**Form 1 matches the sources. Form 2 does not.** `[LJ-1.312]:222-224` already
warned that the two forms differ in meaning and that its own Form 2 is
**INFERRED** and unbuilt. **The literature now says which meaning is the
orthodox one, and it is Form 1's.**

**And there is a second reason, which is about strength.** `∃K φ(K,K)` implies
`∃K₁∃K₂ φ(K₁,K₂)`, and the converse needs an amalgamation lemma that nobody has
built. **So Form 2 states a formally WEAKER property than Form 1.** A weaker
level-hood is easier to satisfy and therefore easier to satisfy at a WRONG
value, which is the exact failure mode `amb` measured for the tags
(`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`, cited through
`dev/JOURNAL.md:995-997`, **POINTER-ONLY**; I did not open the probe). **INFERRED**,
and it is a hypothesis about `q'` and not a measurement of it.

**MY RECOMMENDATION, and it is the literature's and not mine.** `[LJ-1.312]`
recommended pricing Form 2 first because it is cheaper to try. **The outside
view reverses the order of preference and not the order of pricing.** If the
owner wants the cheap experiment first, Form 2 is still the cheap experiment.
**But Form 1 is the one to LAND**, and `[LJ-1.312]:229` said the same thing.
**The literature now makes that a finding rather than a preference.**

### 5.4 What NEITHER cure has, and the owner should hear it

**Devlin's bound is DETERMINED and Bedrock's is CHOSEN.** Devlin writes
`∃w[K(w,u) ∧ C(w,v,u)]`: the conjunct `K(w,u)` says `w = K(u)`, so the witness
is unique (`dev2.txt:611-620`, **READ**). Bedrock's `closeN 14` closes the bound
slot with a bare existential and adds no determining conjunct
(`ProbeLJ1241A.agda:140-146`, **READ**).

**Is that a defect?** I do not know, and I say so. "There is SOME bound that
works" and "THE canonical bound works" are different statements, and only the
second is Devlin's. **INFERRED, not MEASURED.** It bears on whether `q'` is
provable, and not on which cure has the right slot roles. **It is a separate
question and it deserves its own gate.**

## 6. DD4, IN ONE LINE

**YES, the literature suggests a shape that serves BOTH trophies: the two-slot
shape (VALUE, ORDINAL) with every bound closed.** Devlin states it for the Def
tower (`dev2.txt:679-680`) and Schindler-Zeman state the SAME two-slot shape for
the S and J tower, "`x = S_γ^A` is Σ₁ ... witnessed by a formula which does not
depend on `α`" (`sz-full.txt:322-323`). **One shape, two towers, and `φ₀` sits
in the carrier-free layer where a shape chosen once is inherited by everything
above it.** Form 1 gives that shape; Form 2 does not.

## 7. C-41: WHAT DOES NOT TRANSFER FROM THE RETIRED ROUTE

The brief's C-41 warning applies to `dev/literature/`. Here is my split.

| item | transfers? |
|---|---|
| Devlin 2.4 to 2.7, the level formula's arity and free pair | **TRANSFERS.** It is mathematics about `L`, and the route change does not touch it |
| Devlin's single-bound rule | **TRANSFERS.** Same reason |
| Jech 13.13 and 13.14 | **TRANSFERS** |
| Schindler-Zeman 1.10 | **TRANSFERS as the J-tower analogue**, and DD2's two-tower route is where it now sits |
| `devlin-II5.md` section 8, the retired route's verdicts | **DOES NOT TRANSFER.** It prices the rud route's crossing, and its 700 to 1,720 band is dead |
| `formalizations.md` section 4's "virgin territory" verdict | **TRANSFERS as a fact about the outside world**, and its route advice does not apply |
| `rudimentary-functions.md`, `j-hierarchy.md`, `fine-structure.md` | **NOT READ.** See section 10 for WHY NOT |

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| No source I read leaves a bound slot free | **MEASURED**, section 5.2, by reading each text |
| No source I read uses two independent bounds | **MEASURED**, section 5.2 |
| Devlin's clause (a) is not legible in the scan | **MEASURED**, `dev2.txt:1187-1191` |
| The digest does not flag clause (a) as restored | **MEASURED**, `dev/literature/devlin-II5.md:95-100` and its section 6 |
| Kunen exhibits no level formula | **MEASURED**, Kunen VI 1.1, VI 3.2 and IV 5.6 in the scratch extract |
| No formalization in the six searched systems writes an object-level level formula | **INFERRED.** I read the landscape file's index searches and its quotations; I did not open the Isabelle, Lean or Mizar sources |
| Isabelle/ZF faces no slot-role question | **INFERRED** from `DPow`'s shape and the theory list, not from the sources |
| Form 2 is formally weaker than Form 1 | **INFERRED.** It is an implication between two closed formulas and I ran no Agda |
| Neither cure determines its bound | **INFERRED**, by reading `ProbeLJ1241A.agda:140-146` beside `dev2.txt:619-620` |
| The twelve tag closures are forced | **MEASURED by `[LJ-1.240]`**, through `amb` at `ProbeLJ1178A.agda:190-192`. I did not re-run it, so it is that task's measurement and not mine |

## 9. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- `dev/literature/devlin-II5.md`, **READ** whole. **Line read:** `:95-96`, "By
  2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that (a) ∀v∀γ [v = L_γ ↔ ∃z
  Φ(z, v, γ)]". **TOOK** the level-hood chain and the requirement list of its
  section 2. **CORRECTED:** clause (a) is a restoration and the digest does not
  say so (section 2 here). **EXTENDED:** with Devlin 2.4 and 2.6's
  single-bound rule, which the digest names but does not quote.
- `dev/literature/formalizations.md`, **READ** whole. **Line read:** `:43-45`,
  the `DPow(A)` definition. **TOOK** the finding that Isabelle/ZF's route is a
  recursion over a function and not an object-level formula.
- `dev/literature/formalizations-landscape.md`, **READ** whole. **Line read:**
  `:25-32`, the per-system table. **TOOK** the six-system negative, with its
  own "not found via the index cited" wording preserved.
- `dev/literature/BIBLIOGRAPHY.md`, **READ** whole. **Line read:** `:190-195`,
  entry 21, "Jech ... fetched as the typed PDF extraction
  `_build/literature/jech13.txt`". **TOOK** the fetch map, and it saved a fetch:
  Devlin, Jech and Schindler-Zeman are all on disk. **Kunen was cite-only at
  `:166-167`, so I fetched it.**
- `agents/tasks/LJ-1-312/lj-1.312-report.md`, **READ** whole. **Line read:**
  `:240-241`, "Φ carries THREE slots. Clause (a) closes ONE of them, `z`, at
  position 0." **VERIFIED** it against the primary text. **TOOK** the two cure
  forms and the measured slot roles.
- `agents/tasks/LJ-1-310/lj-1.310-report.md`, section 7 and section 12
  **READ**. **Line read:** `:459-462`, "Bedrock's `closeN 14` closes fourteen
  ... It is the SHAPE OF THE CLOSURE". **CORRECTED in part:** the twelve are
  not a shape choice (section 4.4 here). **The same report says so itself at
  `:466-472`**, so this is an extension of its own reading.
- `archive/dev/TASKS-archived.md`, **NOT READ.** **WHY NOT:** it holds the
  retired route's dispatch verdicts. This task asks what the SOURCES say about
  a formula's slots. The archive holds no source. `dev/literature/devlin-II5.md`
  section 8 already digests the archived condensation verdicts, and I read that
  section. **SHAPE taken:** none, because none bears on slot roles.

## 10. LITERATURE USED (DD18), WITH WHY NOT

### 10.1 READ

| source | status | locator | what I took |
|---|---|---|---|
| Devlin, "Constructibility", Ch. II, sections 2.2 to 2.7 | **READ** | `_build/literature/dev2.txt:585-693` | `D`, `G`, `H`, the `K(u)` bound, the single-bound rule |
| Devlin, Ch. II section 5.2 | **READ** | `_build/literature/dev2.txt:1180-1200` | clauses (a) and (b), and the OCR verdict |
| Jech, "Set Theory" 3rd ed., Ch. 13 | **READ**, the level-formula parts | `_build/literature/jech13.txt:555-625` | Lemma 13.14, the adequacy sentence (13.12) and (13.13), Lemma 13.17 |
| Kunen, "Set Theory: An Introduction to Independence Proofs", 1980 | **READ**, Ch. VI section 1 and section 3, and Ch. IV Theorem 5.6 | fetched from `https://fa.ewi.tudelft.nl/~hart/onderwijs/set_theory/Jech/Kunen-1980-Set_Theory.pdf`, printed page 165 for Definition VI 1.1; the printed pages for VI 3.2 and IV 5.6 are not recoverable from the extraction | Definition VI 1.1, Lemma VI 3.2, and the finding that no level formula is written |
| Schindler and Zeman, "Fine structure" | **SKIMMED**, Lemma 1.10 read in full | `_build/literature/sz-full.txt:310-330` | "`x = S_γ^A` is Σ₁ ... by a formula which does not depend on `α`" |
| `dev/literature/devlin-II5.md` | **READ** whole | in repo | section 9 above |
| `dev/literature/formalizations.md` | **READ** whole | in repo | section 3.1, 3.2 |
| `dev/literature/formalizations-landscape.md` | **READ** whole | in repo | section 3.3 |
| `dev/literature/BIBLIOGRAPHY.md` | **READ** whole | in repo | the fetch map |

**On the Kunen fetch.** The PDF is 6.6 MB and it opened without a paywall on
2026-08-15. I extracted the text with `pdftotext` into my scratch directory and
read the two chapters named above. **The extraction is degraded in the same way
Devlin's scan is**: `Def` prints as `~` or `D`, and subscripts are lost. **Every
Kunen quotation above was checked for sense against the surrounding prose**, and
I marked the one place where the glyph matters. **The load-bearing Kunen fact is
a NEGATIVE, that no formula is written, and a degraded glyph cannot manufacture
that.**

### 10.2 POINTER-ONLY

| source | why it is a pointer | what it would settle |
|---|---|---|
| `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`, the `amb` measurement | I did not open it. I read it through `dev/JOURNAL.md:995-997` | whether an unpinned tag really satisfies the formula at a wrong `v`. It bears on section 5.3's strength argument |
| Jensen 1972, "The fine structure of the constructible hierarchy" | cite-only in `BIBLIOGRAPHY.md:141-144`, never fetched | the original J-hierarchy level formula. Schindler-Zeman 1.10 already carries the modern statement |
| Zeman, "Inner Models and Large Cardinals", Ch. 1 | cite-only in `BIBLIOGRAPHY.md:151-153` | a fourth author's `rud` exposition. It would add a fifth row and not change the table |

### 10.3 NOT READ, and WHY NOT

| source | WHY NOT |
|---|---|
| `dev/literature/rudimentary-functions.md` | It digests the `rud` basis `R0` to `R8`. **The question is a formula's free slots, and the `rud` basis states no level formula.** C-41: it is route-specific to the retired route |
| `dev/literature/j-hierarchy.md` | Its section 2 carries the J-side engine. **I took the same content from the primary text, `sz-full.txt:310-330`, which is one step closer to the source.** Reading the digest too would have added a row of the same author |
| `dev/literature/fine-structure.md` | It carries SZ projecta and reducibility, sections 5.2 to 5.4. **`devlin-II5.md:26-29` records that those are NOT Devlin II.5's items and that the numbering is a coincidence.** So it bears on nothing here |
| `dev/literature/devlin-errata.md` | The known-error list stops before II.5, per `devlin-II5.md:514-518`. **A slot order is not an erratum territory question** |
| `dev/literature/geology.md`, `owner-notes-rud.md`, `terms-2026-08.md`, `glossary-review-2026-08.md`, `primary-sources.md`, `digest.md` | None states a level-hood formula. `primary-sources.md` holds the fetch map, and `BIBLIOGRAPHY.md` already gave me that |
| Mathias-Bowler, Mathias "Weak systems", Welch draft | They correct Devlin's Chapter VI, the `rud` chapter. **Chapter II's level formula is not in their inventory** (`devlin-II5.md:514-518`) |
| Paulson arXiv:2104.12674, the Isabelle outline PDF, the Flypitch papers | **Already digested in full** by `formalizations.md`, with verbatim quotations. Re-fetching them would re-derive what the corpus holds, and the brief forbids that |
| Any new web search for a formalization | `formalizations-landscape.md` searched six systems through their own indexes on 2026-08-02, **thirteen days before this task**. A fresh sweep would cost hours and would move nothing |

## 11. WHAT I DID NOT SETTLE

1. **Whether `q'` is provable after Form 1.** The cure fixes the slot roles. The
   literature says the roles are right. Neither supplies the proof.
2. **Whether the undetermined bound matters** (section 5.4). It is a real
   difference from Devlin and it needs its own gate.
3. **Whether Bedrock's outer `∃̇` becomes vacuous under Form 1.**
   `[LJ-1.312]:180-184` measured slot 0 as UNUSED after the cure. Devlin's `∃z`
   is never vacuous. **I did not check what a vacuous closure costs**, and it is
   a probe question for `[LJ-1.313]` and not a literature question.
4. **Whether any formalization outside the six searched systems writes such a
   formula.** The sweep is bounded by its indexes and its date.

## 12. PROHIBITIONS, ANSWERED

- I ran **NO AGDA**.
- I wrote only inside `agents/tasks/LJ-1-315/`. The Kunen PDF and its text
  extraction live in the session scratch directory, outside the repository.
- I landed **nothing** in `dev/literature/`. The proposed digest is
  `agents/tasks/LJ-1-315/proposed-devlin-slot-roles.md`, for the orchestrator to
  land.
- I did not edit `src/`, `dev/`, `AGENTS.md` or another task directory.
- I did not commit, push, `git checkout .`, `git stash`, `git reset --hard` or
  `git clean`. I did not run `make check`.
- `lint-prose.py --check` exits 0 on both files.
