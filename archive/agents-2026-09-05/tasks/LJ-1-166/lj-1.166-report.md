# LJ-1.166 report: gate `K(u)`, the SUPPLY that six gates never priced

tier: opus (version `override`). **No master is edited. `git status` shows two
new files, both mine, both in `agents/tasks/LJ-1-166/`. No commit, no push.**
Every negative is marked **MEASURED** or **INFERRED**. Written incrementally
(C-22).

## 0. THE CRITERIA, FIXED BEFORE ANY RUN (D-1, DD8)

### 0.1 The wall-clock criterion, written before the first `agda` invocation

**20 minutes of wall time per `agda` invocation.** `GHCRTS="-A64m -I0 -M8g"`,
**ONE** agda process, **cap NEVER raised**. Past 20 minutes I record a WALL with
its wall clock and its resident set, and I report the price without that term.
I do not move the criterion after I see a clock.

**No run came near it. Three runs, 2.80 s, 2.57 s, 2.69 s.** Section 5.3.

### 0.2 The line criterion, fixed before the probe

**There is no standing figure to beat, because no gate in this phase has ever
priced a supply.** I fixed an ABORT instead: **if the `KFacts` value needs more
than 150 in-fence lines, stop and report the shape rather than finish it.**
**It needed 88. I did not move the figure.**

### 0.3 The brief's four criteria, and which fired

| criterion | fired |
|---|---|
| I can price it | **YES.** Section 5 |
| The bound cannot sit inside the carrier | **NO.** It can, MEASURED. Section 6 |
| `K(u)` is already built under another name | **YES, and I say it first.** Section 4.1 |
| Anything walls | **NO.** Section 5.3 |

## 1. VERDICT

### 1.1 The three sentences a reader must carry

1. **`K(u)` CAN be built on this coding, the bound DOES sit inside the carrier,
   and I built one. GO.** `KFacts` is no longer a record with no value:
   `agents/tasks/LJ-1-166/ProbeLJ1166A.agda` constructs one and feeds it to the
   tree's own `KFactsCons`. **Exit 0, 2.69 s, RSS 611 MB, 88 in-fence lines.**
2. **Most of it was already built, three chapters away, and nobody cited it.**
   `src/L/Choice/Name.lagda.md:120-135` proves three of the four closure classes
   at `Lset ω`, and its own prose describes Devlin's argument. **Six gates spent
   themselves on a term the tree half-held.** Section 4.1.
3. **My figure covers the CLOSURE layer and NOT the satisfaction layer, and I say
   so rather than let it read as the whole supply.** `KFacts` is 29 fields and I
   supply 29. `TFacts` (`src/L/Condensation/TwelveAgree.lagda.md:128`) is 57, of
   which **31 are the same closure class and 26 are satisfaction facts my
   construction does not touch.** Section 7. **C-38 as extended, obeyed.**

### 1.2 The finding that would have re-planned the route, and it is NEGATIVE

**The brief named "the bound cannot sit inside the carrier" as the deepest
finding available. MEASURED: it is FALSE.** The bound is `Lset λ` as an
L-element, and `CS.S`, the type my `env` slot holds, **is** the carrier of the
model that `LevelHood0.Σ₂`'s outer `∃̇` ranges over. **Devlin's engine transfers
to this coding. The route needs funding, not re-planning.**

## 2. WHAT DEVLIN'S `K(u)` IS, and what makes its bound work

**`_build/literature/dev2.txt:600-612`, read verbatim.** Devlin's `K(u)` is a
union of THREE pieces, and each piece is a set of finite sequences:

1. the finite sequences of members of `𝓕 ∪ {vᵢ | i ∈ ω} ∪ {x | x ∈ u}`;
2. the finite sequences of finite sequences of members of the same set;
3. the finite sequences of finite subsets of `{vᵢ | i ∈ ω}`.

`𝓕` is the formula set and `{vᵢ}` the variables.

**Why THOSE three pieces, and this is the criterion, not decoration**
(`dev2.txt:596-600`). The unbounded quantifiers of `B(v, u)` fall into exactly
three types: those over formulas, those over finite sequences of formulas, and
those over finite sequences of finite sets of variables. **The three pieces are
the three types, one each.** `K(u)` is not canonical. It is whatever set catches
every unbounded quantifier of the matrix.

**What makes the bound WORK is two facts, and they are separate**
(`dev2.txt:612-625`):

- **`K(u)` is a SET, built from `u` by closure operations** (`Seq`, `Pow`,
  union). So `C(w, v, u)` with `w = K(u)` is Σ₀.
- **`K(w, u)`, the formula saying `w = K(u)`, is Σ₁.** So
  `D(v, u) = ∃w[K(w, u) ∧ C(w, v, u)]` is Σ₁.

**And there is a third, unwritten, and it is the one this task turns on.** For
`D` to be absolute at a level, `K(u)` must BE at that level when `u` is. Devlin
records it as the parenthetical at `dev2.txt:640`: `L_α` is closed under `Def` at
limit `α > ω`. **The bound must sit inside the carrier.**

**The digest's clause is my freedom and my criterion**
(`dev/literature/devlin-II5.md:253-256`): the argument "does not require them to
have any particular shape, only that some bounded description with a bound inside
the carrier exists."

## 3. WHAT `K(u)` IS ON THIS CODING

### 3.1 The tree already STATES `K(u)`. Its name is `KFacts`

**MEASURED. `KFacts` (`src/L/Condensation.lagda.md:5996-6032`) IS this coding's
"`w = K(u)`", field for field.** Nobody wrote that down, so I do.

`KFacts {n} (A K N0 .. N11 : Fin n) (γ : S ^ n)` has **29 fields in five
classes**, and the bound is the set at the environment slot `K`:

| class | fields | count | Devlin's piece |
|---|---|---:|---|
| `tagEq0-11` | the twelve arity tags ARE the numerals | 12 | the alphabet, not a bound |
| `numK0-11` | the twelve numerals lie in `K` | 12 | **`𝓕 ∪ {vᵢ}`**, formulas and variables |
| `innerK`, `innerPairK`, `pairK` | `K` closed under the Kuratowski pair | 3 | **the finite sequences** |
| `carrierK` | `K` holds the carrier `A` | 1 | **`{x | x ∈ u}`** |
| `arityK` | `K` is **TRANSITIVE** | 1 | what makes the three pieces one set |

**The correspondence is exact and it is not an analogy I chose.** On this coding
every code is a Kuratowski pair of numerals and carrier members
(`src/L/Coding/Model.lagda.md:326`: `prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)`),
so "sequences over `𝓕 ∪ {vᵢ} ∪ u`" collapses to "closed under `prʟ`, holds the
numerals, holds the carrier". **The three pieces become three fields.**

**And `arityK` is not plumbing.** It is `(N v : S) → v ∈ N → N ∈ K → v ∈ K`:
transitivity of the bound, unrestricted. Devlin gets it free because his `K(u)`
is a union of sequence sets over a transitive base.

### 3.2 The analogue, named at `file:line`

**`K(u) := Lset λ`, a LATER LEVEL of the tower, for a limit `λ` above the
carrier's ordinal.** As an L-element it is `LsetS lam ordλ`
(`src/L/Axioms/Basic.lagda.md:160-161`, PROVED).

**Why a level and not a bespoke set, MEASURED.** Devlin builds `K(u)` from `u` by
`Seq` and `Pow` because his `L_α` is not handed to him closed. Here the tower IS
the object under study, and a limit level is transitive, holds every numeral and
is pair-closed. **The literature's clause permits exactly this.**

**And the site already carries the three hypotheses this needs.**
`HullStage` (`src/L/BoundedSubset.lagda.md:903-905`) is parameterised by
`ordλ : IsOrd lam`, `succλ : d ∈ lam → sucV d ∈ lam` and `∅∈λ : ∅ ∈ lam`.
**My construction assumes nothing beyond those three.** MEASURED: they are the
`Bound` module's whole telescope, `ProbeLJ1166A.agda:85-87`.

## 4. WHAT ALREADY EXISTS, and criterion 3 FIRES

### 4.1 The lead finding: `K(u)` is ALREADY BUILT at `Lset ω`

**MEASURED. `src/L/Choice/Name.lagda.md:120-135` proves three of the four closure
classes at the single set `Lset ω`, and its own prose says it is doing this.**

| `KFacts` class | delivered supplier | `file:line` | state |
|---|---|---|---|
| `numK0-11` | `numeral∈limit : (k : ℕ) → ⟨ (# k) ∈ˢ Lset ω ⟩` | `src/L/Choice/Name.lagda.md:120-121` | **PROVED** |
| `pairK` | `pr∈limit : (x y : S) → x ∈ˢ Lset ω → y ∈ˢ Lset ω → pr x y ∈ˢ Lset ω` | `src/L/Choice/Name.lagda.md:123-132` | **PROVED** |
| `innerK` | `tag∈limit : (k : ℕ) (x : S) → x ∈ˢ Lset ω → mkTag k x ∈ˢ Lset ω` | `src/L/Choice/Name.lagda.md:134-135` | **PROVED** |
| `arityK` | `layer-trans (Lset-layer ω)` | `src/L/Constructible.lagda.md:183`, `:246` | **PROVED** |
| `carrierK` | `Lset-mono` | `src/L/Constructible.lagda.md:355-356` | **PROVED** |

**`src/L/Choice/Name.lagda.md:99-104` states the method in its own words**: "two
closure facts suffice, and both are lifted rather than re-derived". **That is
Devlin's `K(u)` argument, written for one level, for a different consumer, three
chapters away from `Condensation`.**

**This is `[LJ-1.163]`'s pattern for the second time in this phase, and the brief
predicted it.** Not one of the six gates cited `Name.lagda.md`.

### 4.2 What is NOT already built, and it is the whole gap

**MEASURED: `pr∈limit` is hard-coded to `ω` and does not generalise by
re-instantiation.** Its recursion runs along `ℕ`: `inSome`
(`src/L/Choice/Finite.lagda.md:987`) decomposes `Lset ω` into `finiteStage n`,
and `raiseTo` (`src/L/Choice/Name.lagda.md:116-118`) climbs by numeral
successors. **`ω` is not a parameter of that argument. It is the recursion's
index.**

**And the site needs an arbitrary limit.** `carrierK` asks the bound to hold the
carrier, and the carrier at the Def step is the stage `Lset γ` whose definable
power is being taken. **`Lset ω` bounds only `γ ∈ ω`.**

**MEASURED, from the archive: the general-limit form WAS built on the retired
route.** `archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:291`,
`Lpr-limit : (γ : S) → ⟨ isLimit γ ⟩ → ... → ⟨ pr p q ∈ˢ Lset γ ⟩`, PROVED, with
`Lpair-limit` at `:280`. **The shape was known and paid for once.**

### 4.3 The one proved `κ → κ` pairing closure in the whole live tree

**MEASURED: there is exactly ONE**, `pr∈limit` at `Lset ω`. Every other proved
pairing lemma **shifts the set**: `pr∈Lset-suc`
(`src/L/Axioms/Basic.lagda.md:596-599`) goes from `Lset σ` to
`Lset (sucV (sucV σ))`, and the `smallDom` family
(`src/L/Recursion.lagda.md:133-134`, `src/L/Coding/EnvSet.lagda.md:91-99`,
`:425-436`, `src/L/Choice/Limit.lagda.md:418-436`,
`src/L/Choice/Table.lagda.md:656-682`) produces a NEW bounding set rather than
closing an old one.

**A shifted lemma cannot fill `pairK`, which is `κ → κ`.** That single structural
fact is what makes this a construction rather than a lookup, and it is what my
48-line block 1 buys.

## 5. THE PRICE OF ONE `KFacts` VALUE

**Basis, named as DD8 requires: a PROBE, built and run at this task.**
`agents/tasks/LJ-1-166/ProbeLJ1166A.agda`, tracked, beside this report, run
while the task was live.

### 5.1 Lines: ONE best-effort figure, 88

| part | `ProbeLJ1166A.agda` | in-fence lines |
|---|---|---:|
| **BLOCK 1**, the bound at an ARBITRARY limit | `:85-146` | **48** |
| **BLOCK 2**, the `KFacts` value: module header and the 14-slot environment | `:157-169` | 10 |
| the twelve `Fin 14` index names | `:170-184` | 15 |
| the `record { .. }` itself, 29 fields | `:186-201` | 15 |
| **BLOCK 2 total** | | **40** |
| **THE PRICED FIGURE** | | **88** |
| BLOCK 3, the consumer test (section 5.4) | `:202-217` | 6 |
| imports and structure header | `:38-76` | 34 |

**ONE number: 88 in-fence lines for one `KFacts` value at an arbitrary limit,
carrier included.** Basis: this probe.

**Two honesty notes on the 88.**

- **15 of the 88 are the `Fin 14` index names, and they are a probe artifact.**
  At the real site the indices arrive from the consumer, as they do in
  `LevelHood` (`src/L/BoundedSubset.lagda.md:74-77`). **The content figure is 73.**
  I report 88 because I measured 88 and I do not shrink a figure by argument.
- **The 34 import lines are not in the figure** and mostly exist already in
  `Condensation`, which imports `Lset`, `Lset-mono`, `layer-trans` and
  `numeralL` today.

### 5.2 Cold seconds: ONE best-effort figure, 2.69 s

| figure | value |
|---|---|
| **wall** | **2.69 s** |
| exit | **0** |
| resident set | **611 MB** |
| heap cap | `-M8g`. **No heap exhaustion. Cap never raised** |
| process count | **ONE** |

**Basis: measurement, `/usr/bin/time -l`, warm dependencies, the whole probe
including block 3.** The figure is dominated by interface loading:
`L.Condensation` alone is a 7,000-line master, and `[LJ-1.165]` measured its own
probes against the same imports at 4 s and 6 s. **The marginal cost of the 88
lines is below the resolution of one process start.**

**DD24, cold seconds over in-fence lines: 2.69 / 88 = 0.031 s per line.** For
comparison `[LJ-1.48]` measured the condensation skeleton at 0.0097 s per line.
**I mark the comparison as weak: my numerator is a fixed load cost, not a
per-line cost, so the ratio flatters nothing and means little at this size.**

### 5.3 Three runs, no wall

| run | change | exit | wall | RSS |
|---|---|---|---|---|
| 1 | blocks 1 and 2 | **error, 2 unsolved implicits** | 2.80 s | 602 MB |
| 2 | the two implicits given explicitly | **0** | 2.57 s | 611 MB |
| 3 | block 3 added | **0** | 2.69 s | 611 MB |

**Run 1's failure is P-i class [F] again, and the cure is the brief's own
handed-down wall lesson**: `mem-ord` and `suc-ord` carry an implicit set index,
and the elaborator blocked on `_A_167` and `_A_192`. **Giving `{A = lam}`,
`{A = δ}` and `{A = ε}` cleared it.** That is the SAME repair `[LJ-1.165]`
measured at `mapΣ₁`, at a different lemma. **P-i [F] fired twice in two
consecutive tasks, so it is not a coincidence of one term.**

**No run approached the 20-minute criterion. No heap exhaustion. Cap never
raised.**

### 5.4 The value is a VALUE, and this is the C-38 test

**MEASURED. `KFactsCons` accepts it.** `[LJ-1.165]` measured that `KFactsCons`
(`src/L/Condensation.lagda.md:6039-6046`) is "the only thing shaped like a
constructor" and that it "builds a `KFacts` FROM another `KFacts`, so there is no
base case and no value is ever made". **Block 3 gives it that base case**
(`ProbeLJ1166A.agda:212-217`): `consed c = KFactsCons iA iK i0 .. i11 env c facts`,
typechecked at exit 0.

**So the figure covers a VALUE and not an interface.** I did not state a
telescope and price the statement. `[LJ-1.146]` made that mistake and caught
itself; **section 7 says exactly where my value stops.**

## 6. DOES THE BOUND SIT INSIDE THE CARRIER

### 6.1 At the class carrier: YES, MEASURED

**The proof is the probe's own type-checking, and it is not an argument.**
`env : CS.S ^ 14` (`ProbeLJ1166A.agda:164`) holds `LsetS lam ordλ` in the `K`
slot, and **`CS.S` is `hPropStructure 𝒮ʟ`'s carrier: the elements of the class
L.** For the slot to typecheck at all, the bound must BE an element of the model.
**It is. Exit 0.**

**And that is the model the statement quantifies over.**
`LevelHood0.Σ₂` (`src/L/BoundedSubset.lagda.md:855-856`) is
`∃̇ (∃̇ (∃̇∈ (var 2) levelHoodB))`, with the master's own comment at `:854`
reading "exists K, v, w in K". **The outer `∃̇` binds the bound itself and ranges
over the carrier.** `Σ₁-Σ₂` at `:858-859` classifies it as Σ₁.

**This is structurally Devlin's `D(v, u) = ∃w[K(w, u) ∧ C(w, v, u)]` with the
`K(w, u)` conjunct MISSING**. The tree says "there exists some K", never "and it
is the right K". **`KFacts` is that missing conjunct, stated at the meta level
instead of the object level, and section 5 prices its value.**

### 6.2 At the hull: NOT MEASURED, and I mark it

**INFERRED, and I did not build it.** `HullStage` carries
`X⊆L : x ∈ˢ X → x ∈ˢ Lset lam` (`src/L/BoundedSubset.lagda.md:905`). If
`Lset lam ∈ X` then `Lset lam ∈ Lset lam`, which foundation refutes. **So at the
hull the bound must be a level BELOW `λ`, not `Lset lam` itself.** My
construction takes the limit as a parameter, so it supplies any such level the
hull contains. **But that the hull CONTAINS one is an elementarity fact I did
not measure.**

**C-36 binds. I do not claim the hull instantiation is blocked. I claim I
measured the class-carrier half and not the hull half**, and section 7 names it.

## 7. THE WIDEST UNMEASURED TERM, and its probe

**My 88 lines buy the CLOSURE layer. They buy no satisfaction fact.** Two terms
remain and I rank them, because DD8 asks for the widest and the two are widest in
different senses.

### 7.1 Widest by RISK: `powK`, the definable power in `K`

**`[LJ-1.162]` named it, `[LJ-1.165]` measured `𝒟ₒ` at zero occurrences across
`Condensation` and the three `*Agree` masters, and I re-measure the reason.**

**MEASURED: the tree has NO lemma about `𝒟ₒ x` for a general `x`.** Every
delivered `𝒟ₒ` fact is at `𝒟ₒ (Lset δ)`: `Lset-in`
(`src/L/Constructible.lagda.md:319`), `Lset⊆𝒟ₒ` (`:310-311`), `𝒟ₒ∋⊆` (`:313`),
`Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), `𝒟ₒS` (`:234`). **`powK` needs
`x ∈ Lset λ → 𝒟ₒ x ∈ Lset λ` at a limit, and no lemma in `src/` is within one
step of it.**

**This is the term that could still NO-GO the route**, because it is a closure
`Lset λ` may not have on this tower's own definition of `𝒟ₒ`.

**Its probe, and it is cheap: ONE declaration added to
`agents/tasks/LJ-1-166/ProbeLJ1166A.agda`'s `Bound` module.**

```agda
  pow∈λ : (x : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ 𝒟ₒ x ∈ˢ Lset lam ⟩
```

**GO if it closes with `Lset-out`, `Lset-suc` and `Lset-mono` alone, the way
`pr∈λ` did. NO-GO if it needs a rank fact the tower does not give.** The file is
already green and already carries every import, **so the probe costs one
declaration and one run.**

### 7.2 Widest by VOLUME: the satisfaction-class fields

**MEASURED, and it is the C-38 boundary of my figure.**

| record | `file:line` | fields | of which my construction supplies |
|---|---|---:|---:|
| `KFacts` | `src/L/Condensation.lagda.md:5996` | **29** | **29** |
| `TFacts` | `src/L/Condensation/TwelveAgree.lagda.md:128` | **57** | **31** |

**`TFacts`' other 26 are NOT closure facts.** They are `codesK`, `codesK-un`,
`valK`, `valK-un`, `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin`,
`envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp`, `valV`, `valW`,
`wKfact`, `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `someEnv`,
`subK-neg`, `envSetK`, `subK-un`, `consK-exist`, `consK-forall`, `subK-allin`,
`consK-allin`. **Most are of the form "this environment SATISFIES this
formula", not "this set lies in `K`".** `LowerAgree` and `UpperAgree` carry
parallel records.

**A bound does not supply a satisfaction. I priced the bound. Nobody has priced
the satisfaction layer and I do not price it here.**

### 7.3 The third, and it is small: generalising `pr∈limit` in place

**Not a residue, an option.** Block 1's 48 lines could instead REPLACE
`src/L/Choice/Name.lagda.md:123-132`, generalising `pr∈limit` from `ω` to any
successor-closed ordinal and leaving `ω` as an instance. **MEASURED: `pr∈limit`
has consumers** (`code∈limit` at `:153-165`), so this is a rewrite with a
regression surface, and I did not measure it. **I name it because DD13 says price
the ideal form, and the ideal form here is one lemma, not two.**

## 8. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

### 8.1 The measurement

**MEASURED by counting lines that name a tower token (`Lset`, `𝒟ₒ`, `layer`):
27 of the 88. Sixty-one are TEMPLATE.**

| part | lines | naming a tower | class |
|---|---:|---:|---|
| BLOCK 1, the bound at a limit | 48 | **25** | the argument is generic, the NAMES are not |
| BLOCK 2, the value | 40 | **2** | **TEMPLATE.** The record is 29 fields of closure, tower-blind |

**Of BLOCK 1's five declarations, four carry `Lset` in their TYPE**: `num∈λ`,
`pr∈λ`, `prʟ∈λ`, `trans∈λ`. The fifth, `#∈λ`, is about the ordinal alone and is
fully generic.

### 8.2 Would the J tower re-instantiate or rewrite? REWRITE as written

**MEASURED, and I do not soften it.** BLOCK 1 calls `Lset-out`, `Lset-mono`,
`pr∈Lset-suc`, `layer-trans`, `Lset-layer` and `ord∈Lset-suc`. **Every one is an
L-tower lemma.** The J tower's `Sset` must supply its own six. **As written, the
J side re-writes 48 lines and re-instantiates 40.**

### 8.3 The generic form, and it is CHEAPER, so I recommend it

**The argument uses only four properties of the tower, and none of them is
L-specific**: a limit decomposes into stages, stages are monotone in the ordinal,
a pair of two stage members appears a bounded number of stages later, and every
stage is transitive.

**Parameterise `Bound` over `(T : S → S)` with those four hypotheses. Cost: about
six added lines in the module header. Saving: BLOCK 1's 48 lines are then written
ONCE for both towers.** MEASURED against my own file: the 25 tower-naming lines
become tower-blind, and the four L lemmas move to a six-line instantiation at the
L end and a six-line one at the J end.

**Net: +6 lines now, −42 lines at the J end. I did not write it that way in the
probe because the probe's job was to gate the CONSTRUCTION, and a generic
wrapper would have added an unmeasured elaboration cost to the thing under
measurement.** **No stop-line pushed me toward writing fixed, and I say so as
the rule requires.**

### 8.4 The limit, so nobody over-reads it

**`KFacts` itself is already tower-blind and that is not my doing.** Its 29
fields mention no tower name: they speak of `lookup K γ`, `numeralL` and `prʟ`.
**What is per-tower is the SUPPLY, and section 8.2 measures it at 25 lines.**
`[LJ-1.165]` measured the assembly at 26 of 28 template; **the supply is the
opposite balance, and that is the honest shape of this layer.**

## 9. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `K(u)` can be built on this coding | **MEASURED TRUE.** Exit 0, 88 lines, 2.69 s |
| the bound sits inside the carrier, at the class carrier | **MEASURED TRUE.** `env`'s `K` slot has type `CS.S`, the model's carrier |
| the bound sits inside the HULL | **NOT MEASURED.** `Lset lam ∉ X` is INFERRED from foundation; that the hull holds a smaller level is an elementarity fact I did not build. C-36 |
| Devlin's engine fails to transfer to this coding | **MEASURED FALSE.** This was the brief's deepest available finding and it does not hold |
| `KFacts` is constructed anywhere in `src/` | **MEASURED TRUE, STILL.** My value is in `agents/tasks/`, not `src/`. `[LJ-1.165]`'s measurement is unchanged in the tree |
| `KFactsCons` accepts a base case | **MEASURED TRUE.** Block 3, exit 0 |
| `K(u)` is already built under another name | **MEASURED TRUE, in part.** Three of four closure classes at `Lset ω`, `src/L/Choice/Name.lagda.md:120-135` |
| `pr∈limit` generalises to an arbitrary limit by re-instantiation | **MEASURED FALSE.** Its recursion is indexed by `ℕ` through `inSome` and `raiseTo` |
| more than one proved `κ → κ` pairing closure exists in `src/` | **MEASURED FALSE.** Exactly one, at `Lset ω`. Every other shifts the set |
| the tree holds a lemma about `𝒟ₒ x` for general `x` | **MEASURED FALSE.** Every `𝒟ₒ` fact is at `𝒟ₒ (Lset δ)` |
| `powK` is supplied by my construction | **MEASURED FALSE.** `KFacts` has no `powK` field, and section 7.1 gives its probe |
| my figure covers the whole supply | **MEASURED FALSE, and I say it in section 1.1.** 29 of 29 `KFacts` fields, 31 of 57 `TFacts` fields, 0 satisfaction facts |
| the satisfaction-class fields are priced | **MEASURED FALSE. NOT PRICED, by me or by anyone** |
| the six gates were wrong | **NOT CLAIMED.** They priced derivations correctly. `[LJ-1.165]` found what they missed and this task fills it |
| anything walled | **MEASURED FALSE.** Three runs, 2.80 s, 2.57 s, 2.69 s, against a 20-minute criterion |
| P-i repair [F] was needed again | **MEASURED TRUE.** Run 1 blocked on two implicit set indices; `{A = ..}` cleared it |
| the J tower re-instantiates block 1 as written | **MEASURED FALSE.** Six L-tower lemmas; section 8.3 prices the generic form at +6 lines |
| a cheaper supply exists | **NOT CLAIMED. C-36.** I measured one route and named one alternative in section 7.3 |

## 10. CHECKERS AND PROHIBITIONS

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,779 tracked files** |
| `scripts/lint-prose.py --check` on this report | see section 10.1 |
| `make check` | **NOT RUN.** The orchestrator runs it |

**Prohibitions, answered one by one.** **No master edited**; `git status` shows
exactly two untracked files, `agents/tasks/LJ-1-166/ProbeLJ1166A.agda` and this
report. `src/Everything.lagda.md` never opened. The three `*Agree` masters and
`src/L/Coding/Graph.lagda.md` **read by `grep` and `sed` only, never edited**.
`[LJ-1.164]`'s move untouched. **No commit, no push, no `git checkout .`, no
`stash`, no `reset`, no `clean`.** No probe under `src/`. **No `postulate`, no
hole, no unsolved meta**, and `--safe` is on.

**C-12.** ONE agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised.** My line figures are lines; my three second-figures are all under 3 s
against a 20-minute criterion, so machine load cannot explain them.

**I did not build `K(u)` into the tree.** The probe is a gate: it measures that
the construction exists and what it costs. **`src/` is byte-identical to HEAD.**

### 10.1 One note on the prose linter

This report is an agent report under `agents/`, which `AGENTS.md` exempts from
the prose linter as a record that is never rewritten. I wrote it in ASD-STE100
regardless, and it contains no em dash.

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md`, section 5 (`:98-128`), READ.**
  **TOOK its two named missing facts.** Fact 1 (`:103-111`) names `Codes` and
  `AllCodes` (`src/L/Coding/CodeSet.lagda.md:440-441`, `:458`) as the delivered
  code set and says "no bounded object-level description of the code set
  exists". **USED, and I correct a reading it invites**: `KFacts` needs a SET
  with closure properties, not an object-level DESCRIPTION. **The two are
  different obligations and only the second is what `[LJ-1.2]` measured.** My
  gate answers the first; the second is still open and is Devlin's Σ₁ `K(w, u)`.
  Fact 2 (`:112-121`) names the table and the twelve clauses: **that is section
  7.2's satisfaction layer, and `[LJ-1.2]` priced it at 5,047 lines (`:126`).**
- **`archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:280`, `:291`.**
  `Lpair-limit` and `Lpr-limit`, the pairing closure at a GENERAL limit, PROVED.
  **TOOK the SHAPE: this is block 1's `pr∈λ` on the retired route. I took no
  claim** (`[LJ-1.11]` ruled that route's condensation target classically FALSE);
  I took the fact that the argument closes.
- **`archive/src/2026-08-09-rud-route/L/Coding/CodeSet.lagda.md:322-333`, 200
  in-fence lines.** **READ, and the answer to the brief's question is NO**: the
  retired route's bounded code set is built by `smallDom` plus separation and
  carries a membership characterization with **zero closure lemmas**. **So it is
  not a `K(u)` and the archive holds no shape to copy for one.**
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md:77-114`, 118
  in-fence lines.** **READ. It builds NO bound.** It makes the MODEL small
  (`InnerSmall`, `:91`) so no bounding set is ever named. **A genuinely different
  technique, and it does not transfer to a statement that must quantify over the
  bound.**
- **`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`, 258 in-fence
  lines. READ structurally.** It bounds its quantifiers by the carrier stage
  itself through the alphabet `⟪ Lset α ⟫`, and builds no auxiliary set.
- **`archive/src/2026-08-09-rud-route/L/Rud/StepGraph.lagda.md:2218-2231` and
  `:2618-2666`.** The closest comparable in either tree: a telescope of closure
  facts as parameters (~14 lines) DISCHARGED at a concrete tower (~48 lines).
  **My 88 against that 62 is the only external check my figure has, and the two
  agree in order of magnitude.** `:2605-2606` carries a `-- perf: P-i layer cap`
  comment, so that route met the same elaboration cost at the same place.
- **`archive/src/2026-08-09-rud-route/L/Choice/Name.lagda.md:124`, `:127`** and
  **`L/Ordinal/Stages.lagda.md:471`.** The `Lset ω` trio existed on the retired
  route too and survived the route change into `src/`. **So it has been in the
  tree, unused for this purpose, across two routes.**
- **`agents/tasks/LJ-1-165/lj-1.165-report.md`, READ WHOLE.** TOOK the stop
  (`:43-50`), the seven site facts (`:186-199`), the `KFacts`-never-constructed
  measurement (`:200-205`), the `HasLevels` correction (`:213-233`), the two
  walls (`:288-324`) and the offered next gate (`:486-505`). **Section 5.4 gives
  its "no base case" the base case it named.**
- `agents/tasks/LJ-1-162/` and `LJ-1-161/`: taken through `[LJ-1.165]`'s report,
  **not read whole. I mark that so nobody credits me with a reading I did not
  do.**
- **`dev/LESSONS.md`: C-38, C-35, D-1, P-l, P-i, C-12, C-22, C-36, C-39, C-40
  read whole**; D-10, D-26, D-29, D-30, C-31 to C-34, C-37, R-40, I-5 loaded
  through `scripts/rules.py --for recon` and `--for probe`. **P-i produced this
  task's one repair, at run 1.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a line count or a
  closure lemma.

## 12. LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:593-640`, READ VERBATIM, and it is the passage
  the brief asked me to report exactly.** Section 2 gives `K(u)`'s three pieces
  (`:600-612`), the three quantifier types they answer (`:596-600`), the Σ₁
  formula `K(w, u)` with its `Vbl`, `Const`, `Seq` and `Pow` conjuncts
  (`:614-625`), and `D(v, u) ↔ v = Def(u)` (`:627-632`). **The closure remark
  that the bound must lie at the level is at `:640`.**
- **`dev/literature/devlin-II5.md:240-260`, READ.** `:245-252` is the digest's
  statement of the substrate; **`:253-256` is the clause that gave me both my
  freedom and my criterion**, and section 3.2 rests on it.
- `dev/literature/devlin-II5.md:374-382`, the per-step DD4 table: **row C1 is
  PER-TOWER, which agrees with section 8.2's measurement rather than with a hope
  that the supply is shared.**
- `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s measurement
  that the errata touch no part of II.5.

## 13. WHAT THE NEXT BRIEF SHOULD FUND, WITH ITS GATE

**Offered, not assumed. Two items, and the first is one declaration.**

1. **`powK`.** Add `pow∈λ` to `ProbeLJ1166A.agda`'s `Bound` module, exactly as
   section 7.1 writes it. **GO if it closes with the same three lemmas `pr∈λ`
   used; NO-GO if it needs a rank fact the tower does not give.** **This is the
   narrowest decisive term left in the closure layer and it costs one run.**
2. **The satisfaction layer, and it should be GATED before it is funded.**
   Section 7.2 measures 26 unpriced fields in `TFacts` alone, with parallel
   records in `LowerAgree` and `UpperAgree`. **`[LJ-1.2]` priced the same content
   at 5,047 lines** (`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md:126`). **No gate
   in this phase has re-measured that number against the current coding, and it
   is by far the largest figure anywhere in this wing.**

**And one line for the brief writer, in the spirit of `[LJ-1.165]`'s.** This task
found its answer half-built in `src/L/Choice/Name.lagda.md`, a file no gate in
this phase had cited. **`[LJ-1.163]` found the same class of miss for `ElemDown`.
Two misses in four dispatches is a pattern in the SEARCH, not in the
mathematics.** A brief that names a term should name the greps that would find it
already supplied, and `L/Choice/` has now paid twice.
