# LJ-1.156 report: does A5 need `CSB` at all?

## 0. VERDICT: **DISSOLVED**

**`[LJ-1.136]`'s dissolution claim is CONVERTED from INFERRED to MEASURED.**
Leastness over injections closes all three `CSB` sites. The chain elaborates
with `--safe`, exit 0, and it contains no `CSB`, no `≃`, and no
`Cubical.Foundations.Equiv` import.

**`agents/tasks/LJ-1-156/ProbeLJ1156A.agda`, 608 lines, 393 non-blank
non-comment, `agda --safe`, exit 0, first attempt, no wall.**

**A5 CARRIES NO `hasReplacementL`. MEASURED at the chain level.** `CSB` was
the only object that could put one back (`[LJ-1.152]` and `[LJ-1.154]` both).
It is not in the chain, so nothing puts one back.

**A5's price, and the surprise is where it now sits.** The seconds do not go
to `CSB`, and they never did: `[LJ-1.107]` measured `CSB` at 2.03 s of its
117 s (`agents/tasks/LJ-1-107/lj-1.107-report.md:51`). **The whole cost is the
least-of over `⟪ sucV α ⟫`, MEASURED here at 100.64 s of the file's 133.00 s,
and the design change moves it by 4.7 percent, which is inside the noise
band.** Sections 4.1 and 5.3 give the numbers; section 14 names the next
gate.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

**Written at 22:30, before the probe file existed and before Agda started.**

The claim under test is `[LJ-1.136]` section 9.1
(`agents/tasks/LJ-1-136/lj-1.136-report.md:504-526`), classified there as
**INFERRED**: `[LJ-1.107]` states leastness over BIJECTIONS, that is the only
reason `CSB` is in the chain, and leastness over INJECTIONS refutes all three
sites directly.

**The test.** Restate `[LJ-1.107]`'s chain with leastness over injections,
delete the `CSB` module, and typecheck the whole chain at the real sites.

- **DISSOLVED.** The file elaborates with `--safe`, exit 0, it contains no
  `CSB` and no manufactured equivalence, and all three sites close. **Then A5
  loses its last unknown.**
- **NEEDED, AND CHEAP.** A site still wants an object that only `CSB` gives,
  but that object carves or composes with `hasSeparationL` alone, under 30 s.
- **NEEDED, AND EXPENSIVE.** A site forces a bijection built by the
  back-and-forth recursion. That graph needs a `hasReplacementL`, and A5
  carries one at 259 to 269 s.
- **WALL.** A heap exhaustion under `GHCRTS="-A64m -I0 -M8g"` is reported as a
  wall. The cap is never raised.
- **C-36 guard.** A type error says the types differ. It never says that no
  term connects them. Each refusal gets its exact text and one named
  alternative before it is written down.

**The DISSOLVED branch fired. No other branch was reached, and no refusal text
was produced by any run.**

## 2. THE DESIGN, AND WHY IT IS THE CHEAPEST DECISIVE ONE

**One line changes.** `[LJ-1.107]`'s `LeastCard`
(`agents/tasks/LJ-1-107/ProbeLJ1107A.agda:219-220`) reads

```
  Eq : S → Type ℓ
  Eq γ = ⟪ γ ⟫ ≃ ⟪ α ⟫
```

and `ProbeLJ1156A.agda:178-179` reads

```
  Inj : S → Type ℓ
  Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫
```

**Everything else in `LeastCardInj` is `[LJ-1.107]`'s module with the
predicate swapped**, including the well-order, the `leastOf`, and the
three-line transport in `κ-min-at`. Non-emptiness moves from `idEquiv` to the
identity injection (`ProbeLJ1156A.agda:197-201`).

**The direction is not free and I state it.** `⟪ α ⟫ ↪ ⟪ γ ⟫` reads "α is no
bigger than γ", so its LEAST solution is the cardinal. The opposite direction,
`⟪ γ ⟫ ↪ ⟪ α ⟫`, holds at every member of α and its least solution is 0.
`ProbeLJ1156A.agda:170-175` records this in the file.

**The theorem's statement does not change.** `Chain.theorem` proves
`(α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α`, which is word for word
`[LJ-1.107]`'s (`ProbeLJ1107A.agda:633-634`, `ProbeLJ1156A.agda:519-520`).
**Leastness is internal to the proof, so adequacy is not a further obligation:
the conclusion is the same conclusion.**

**Why this probe and not a smaller one.** An abstract `LInj` interface would
have been cheaper and would have proved nothing (C-38). This file runs the
REAL sites over the delivered `S`, `⟪_⟫`, `sucV`, `ordSWO`, `leastOf`,
`FiniteBase` and `via-col-square`. **It imports no other probe**: the three
probes `[LJ-1.107]` rode on are replaced by delivered modules, and the one
piece with no delivered home, `NumeralPresentation`, is copied in at 41 lines
(`ProbeLJ1156A.agda:111-159`, from `agents/tasks/LJ-1-106/ProbeLJ1106A.agda:86-136`).

## 3. THE THREE SITES, EACH SHOWN CLOSING

**All three close. MEASURED, `--safe`, exit 0.**

| site | `[LJ-1.107]` route | this file | evidence |
|---|---|---|---|
| **1. `noinj²`, the square clause** | compose to `⟪α⟫ ↪ ⟪β⟫`, build the inclusion `j : ⟪β⟫ ↪ ⟪α⟫`, `CSB.csb`, `invEquiv`, `leastα` | the composite **IS** the injection `leastα` wants | `ProbeLJ1156A.agda:385-396` |
| **2. `succ-closure`, at γ = ω** | `Incl ω` plus `Shiftω.shift`, `CSB.csb`, `subst`, `leastα` | `Shiftω.shift↪` **IS** `⟪α⟫ ↪ ⟪ω⟫` after one `subst` | `ProbeLJ1156A.agda:426-432` |
| **2b. `succ-closure`, at ω ∈ γ** | `Incl γ` plus `ShiftAbs.shift`, `CSB.csb`, `subst`, `leastα` | `SA.shift↪` **IS** `⟪α⟫ ↪ ⟪γ⟫` after one `subst` | `ProbeLJ1156A.agda:433-441` |
| **3. `NonInitial`** | `κ-eqα` truncated, `κ∉ω` by inverting the equivalence | `κ-inj` truncated, `κ∉ω` **directly**; no inversion | `ProbeLJ1156A.agda:464-480` |

**The saving is larger than `[LJ-1.136]` predicted, and this is the part it
did not see.** Three constructions die, not one.

- **`CSB` dies.** 97 in-fence lines in `[LJ-1.107]`
  (`agents/tasks/LJ-1-107/lj-1.107-report.md:51`).
- **`Incl` dies.** `[LJ-1.107]`'s `Incl` (`ProbeLJ1107A.agda:441-453`) exists
  only to give `CSB` its second input at site 2. With no `CSB` there is no
  second input. **`ProbeLJ1156A.agda` has no `Incl` module.** MEASURED, one
  grep.
- **`noinj²`'s inclusion `j` dies.** `ProbeLJ1107A.agda:482-488` builds
  `j : ⟪β⟫ → ⟪α⟫` and `j-inj` for `CSB`'s second input. **Seven lines gone**;
  compare `ProbeLJ1156A.agda:385-396`, which has neither.
- **`FiniteAtω` dies.** `ProbeLJ1107A.agda:403-438` restates the finite
  exclusion and adds `no-eq-finite`, which eliminates a truncated EQUIVALENCE
  into a finite ordinal. The delivered `FiniteBase.no-inj-finite`
  (`src/L/Ordinal/SquareLaw.lagda.md:652-662`) already takes an injection, so
  this file calls it directly (`ProbeLJ1156A.agda:470`).
- **`NonInitial.κ∉ω` loses eleven lines.** `ProbeLJ1107A.agda:562-587` builds
  an embedding `emb : ⟪ω⟫ ↪ ⟪α⟫`, an identity case `id-inj`, a trichotomy
  `go4` and an inversion `f = invEq e`, all to turn the equivalence round.
  **`ProbeLJ1156A.agda:464-480` needs none of it: the injection already points
  the right way.**

**The inclusion is NOT gone from the chain.** `NonInitial.j`
(`ProbeLJ1156A.agda:482-489`) still builds `⟪κ⟫ ↪ ⟪α⟫` for the pairing.
**Two of its three uses go; one stays.** I state this rather than claim the
object away.

### 3.1 The C-38 guard, and it is stronger than "it typechecks"

**"An interface nothing satisfies is a restatement, not a supply"**
(`dev/LESSONS.md:3427`). `[LJ-1.136]` nearly shipped a vacuous probe and
`[LJ-1.154]` instantiated at a concrete singleton. **A DISSOLVED verdict
carries the higher burden, so Part 7 gives four witnesses and three of them do
not rest on any hypothesis** (`ProbeLJ1156A.agda:555-608`).

| witness | what it shows | site |
|---|---|---|
| `Guard.shiftω↪ : ⟪ sucV ω ⟫ ↪ ⟪ ω ⟫` | a REAL injection between two DIFFERENT presentations. Not the identity, and not vacuous: `sucV ω` has a member that `ω` does not | `:568-569` |
| **`Guard.κ-not-sucω : (LCω.κ ≡ sucV ω) → Empty.⊥`** | **SITE 2's refutation FIRING at concrete ordinals.** At `α = sucV ω` the least injectable δ is strictly below α, proved by feeding `shiftω↪` to `κ-min-at`. Under `[LJ-1.107]`'s bijection leastness this exact step is what needed `CSB` | `:583-588` |
| `Guard.compose↪` | SITE 1's composite as a standalone term: `sq β` plus `⟪α⟫ ↪ ⟪β⟫×⟪β⟫` gives `⟪α⟫ ↪ ⟪β⟫`, with no `CSB` | `:593-600` |
| `Guard.Runs.sq-sucω : SQ.sq (sucV ω)` | the chain applied at a REAL infinite ordinal, so its premises are SATISFIABLE and the theorem is not vacuously quantified. **This one does rest on the `inj` parameter**, and I mark it | `:603-608` |

**What witness (d) does NOT show, and I mark it rather than overclaim.**
`theorem` is `∈-induction step`, so Agda does not normalize the induction at
elaboration time. **`sq-sucω` proves the premises are satisfiable at a named
infinite ordinal; it does not prove that any particular branch was evaluated.**
The branch evidence is witnesses (a) to (c), which are terms at the sites
themselves.

**`κ-not-sucω` is the load-bearing one.** It is not inhabitation of an
interface. It is a refutation that produces `Empty.⊥` from a real injection
between two named ordinals, which is exactly the shape all three sites use.

### 3.2 What did NOT change, and it matters for honesty

**The `inj` parameter of `Chain` stays.** `[LJ-1.107]`'s wall was that
`∥ ⟪κ⟫ ≃ ⟪α⟫ ∥₁` cannot eliminate into `⟪α⟫ ↪ ⟪κ⟫`, because `↪` is not an
hProp (`agents/tasks/LJ-1-107/lj-1.107-report.md:28-32`). **Swapping the
predicate does not lift that wall**: `κ-inj : ∥ ⟪α⟫ ↪ ⟪κ⟫ ∥₁` is still
truncated, and `SQ.sq α` is still not an hProp. **MEASURED, and I say it
plainly: this task does not discharge `inj`.** `[LJ-1.136]` Probe B is what
discharges it, and it returned GO
(`agents/tasks/LJ-1-136/lj-1.136-report.md:897-928`).

**What the swap DOES buy at site 3 is a shorter road to the same parameter:**
the truncated witness is now already an injection, so the L-side selection
selects an injection code rather than a bijection code, and `κ∉ω` closes
without inverting anything.

## 4. THE SECONDS, WITH LOAD AND RUN COUNT

**All runs cold: the file's own interface under `_build/2.8.0/agda/` was
deleted before every run. All under `GHCRTS="-A64m -I0 -M8g"`, cap never
raised. ONE agda process of mine at a time. Load is the one-minute average at
the start of the run. Warm-up discarded, three kept.**

| probe | what it is | kept | seconds | load |
|---|---|---:|---|---:|
| `ProbeLJ1156B` | my import block, no body | 3 of 4 | 1.27, 1.27, 1.26 | 2.87 |
| **`ProbeLJ1156A`** | **THE CHAIN OVER INJECTIONS, whole file** | 3 of 4 | **131.99, 132.43, 134.58** | 2.85 to 3.32 |

**Mean 133.00 s whole file, 131.73 s net of my own import baseline.**
Discarded warm-ups: 1.39 s and 135.86 s. `[LJ-1.148]`'s first-run penalty is
reproduced small here: 0.12 s and 2.86 s.

**A first, separate figure, and it measures the TREE and not the probe.** The
very first run of `ProbeLJ1156A.agda` took 131.33 s at load 3.74 while it also
built the import closure cold. **It is not comparable with anything and I do
not compare it** (P-q, and `[LJ-1.136]` section 9.3 fixes the rule).

### 4.1 Where the 131 s goes, and it is NOT the design change

**The A/B.** `ProbeLJ1156D` is `LeastCardInj` alone, over INJECTIONS.
`ProbeLJ1156E` is `[LJ-1.107]`'s `LeastCard` alone, over BIJECTIONS, copied
verbatim from `agents/tasks/LJ-1-107/ProbeLJ1107A.agda:217-266`. **Both carry
Probe A's import block, both use the same `ordSWO` and the same `leastOf`.
The predicate is the only difference.**

| probe | predicate | kept | seconds | mean | load |
|---|---|---:|---|---:|---:|
| `ProbeLJ1156D` | **INJECTION** | 3 of 4 | 99.95, 100.88, 101.10 | **100.64** | 3.81 to 4.63 |
| `ProbeLJ1156E` | **BIJECTION**, `[LJ-1.107]` verbatim | 3 of 4 | 95.26, 98.18, 94.83 | **96.09** | 4.48 to 5.55 |

Discarded warm-ups: 99.46 s and 96.49 s.

**MEASURED, and it settles the cost question the swap raised.**

1. **The least-of IS the whole cost.** `ProbeLJ1156D`, which is 98 lines,
   costs 100.64 s against Probe A's 393 lines at 133.00 s. **That is 76 percent
   of the file, and 99.4 s of the 131.7 s net.** **The other 295 lines of the
   chain cost about 32 s between them**, which is 0.11 s per line.
2. **`[LJ-1.107]`'s 91.98 s reproduces.** It measured the same term at 91.98 s
   on a different day at loads 3.75/4.61/4.88
   (`agents/tasks/LJ-1-107/lj-1.107-report.md:52`). **96 to 101 s here. The
   term is the same size and the cause it named is unchanged: `⟪ sucV α ⟫`
   normalizes the union structure.**
3. **The design change costs 4.55 s, which is 4.7 percent, and I DO NOT CLAIM
   IT.** `[LJ-1.148]` prices between-series uncertainty at 12.8 percent
   (`agents/tasks/LJ-1-154/lj-1.154-report.md:148-149`), so the gap is inside
   the band. **What I do claim: the injection predicate is not materially more
   expensive than the bijection predicate at the dominant term.** Note that E
   ran at HIGHER load than D, which pushes against the gap rather than for it.

**So `CSB` was never where A5's seconds were, and neither is the swap that
removes it.** The seconds are in the least-of, and section 5.3 states what
that means for DD24.

### 4.2 The lines

Counted as non-blank non-comment lines. **`scripts/ledger.py` cannot count a
probe** and says so at `scripts/ledger.py:13-15`: the scan is scoped to
`src/*.lagda.md`. **So the caliber is the ledger's, applied by hand to a
`.agda` file, and the figures are consistent within this report.**

| part of `ProbeLJ1156A.agda` | lines | what it is |
|---|---:|---|
| header, imports, `_↪_`, `isSet⟪_⟫` | 54 | the import block alone is 50, measured as `ProbeLJ1156B` |
| Part 1, `NumeralPresentation` | 37 | the pairing on ω, from `[LJ-1.106]` |
| Part 2, **`LeastCardInj`** | 44 | **the one design change** |
| Part 3, `ShiftAbs` and `Shiftω` | 101 | from `[LJ-1.107]` verbatim |
| Part 4, `InitialCase` | 56 | sites 1 and 2 |
| Part 5, `NonInitial` | 44 | site 3 |
| Part 6, `Chain` | 33 | the `∈`-induction |
| Part 7, the C-38 guard | 24 | four witnesses |
| **whole file** | **393** | |

**Against `[LJ-1.107]`'s 582 in-fence lines** for the same chain WITH `CSB`
(`agents/tasks/LJ-1-107/lj-1.107-report.md:57`). **The comparison is not
clean and I say so:** `[LJ-1.107]` carried `FiniteAtω`, `Incl` and its own
`_↪_`, and it rode on three probe files this one does not import. **The clean
part of the comparison is the object count, not the line count**, and section
3 gives it.

## 5. A5's PRICE

### 5.1 The replacement count is ZERO. MEASURED

`[LJ-1.136]` inferred six replacements and about 25 minutes
(`agents/tasks/LJ-1-136/lj-1.136-report.md:1117-1121`). `[LJ-1.152]` refuted
the count. `[LJ-1.154]` refuted the unit price. **This task removes the last
object that could have restored one.**

| built object | verdict | classification |
|---|---|---|
| composition of two injections | **CARVES.** 2.50 s | **MEASURED**, `[LJ-1.152]` |
| the identity graph | **CARVES.** 1.73 s | **MEASURED**, `[LJ-1.154]` |
| `ShiftAbs` / `Shiftω`, used TWICE | carves from a stage bound | **INFERRED** |
| the inclusion `j`, now used ONCE not three times | carves from a stage bound | **INFERRED** |
| `pairω`, the pairing on ω | carves from a stage bound | **INFERRED** |
| the column square `pair` | carves from a stage bound | **INFERRED** |
| **the `CSB` bijection** | **NOT IN THE CHAIN. Nothing to build** | **MEASURED**, this task |

**The four inferences are `[LJ-1.154]`'s and I inherit them unchanged. P-l
forbids me from strengthening them by analogy**, and this task measured
nothing about any of the four.

### 5.2 What I state as a price, one number with its basis (DD8)

**A5's chain carries ZERO `hasReplacementL`. The basis is this task's own
elaboration at the real sites, `--safe`, exit 0.** That is a count, not an
estimate, and it is the figure the block was waiting for since `[LJ-1.131]`.

**A5's seconds, and the honest form.** The ambient chain costs **133 s cold as
a whole file, 131.7 s net of imports**, three kept runs, loads 2.85 to 3.32.
**The basis is this task's own measurement at this site, not a comparable.**

**I will NOT add the L-side seconds to that figure by multiplication.** Two of
the six objects are measured at 1.73 and 2.50 s; four are not measured at all.
`[LJ-1.152]` refused to multiply 2.50 by five and `[LJ-1.154]` refused to
multiply 1.73 by five. **The same refusal applies here.**

### 5.3 The number the block should now worry about, and it is not `CSB`

**MEASURED: 131.7 s net over 343 non-comment body lines is 0.384 s per line.
DD24's bar is 0.007913 s per line** (`dev/PLAN.md:139-142`). **That is about
48 times the bar.**

**This was true before this task and nobody had put the two numbers side by
side.** `[LJ-1.107]` measured 117 s over 582 lines, which is 0.201 s per line,
about 25 times the bar
(`agents/tasks/LJ-1-107/lj-1.107-report.md:38, 57`). **Removing `CSB` did not
create this and cannot cure it:** `CSB` was 2.03 s of `[LJ-1.107]`'s 117 s
(`:51`).

**The whole cost is one term, MEASURED.** `LeastCardInj` alone is 100.64 s of
the file's 133.00 s, which is 76 percent (section 4.1). `[LJ-1.107]` measured
the same term at 91.98 s and named the cause: "the least-of over the
well-order on the successor's presentation, `⟪ sucV α ⟫` normalizes the union
structure, the P-m instantiation class"
(`agents/tasks/LJ-1-107/lj-1.107-report.md:52, 59-63`). **The bijection
version of that term costs 96.09 s, so the swap does not cause it and cannot
cure it.**

**One comparison makes the size of it plain, and both numbers are somebody
else's measurement.** `scripts/ledger.py --brief` reports DD24's AC-only cold
baseline at **133.19 s over 16,897 lines**. **`ProbeLJ1156A.agda` costs
133.00 s over 393 lines.** **This one probe file costs the same wall-clock as
the whole delivered AC wing.** MEASURED, both figures, and the machine was not
quiet for mine.

**The rest of the chain is cheap.** The 295 lines outside `LeastCardInj` and
the import block cost about 32 s between them, which is 0.11 s per line.
**The 44 lines of `LeastCardInj` cost about 99 s, which is 2.26 s per line,
about 285 times DD24's bar.** That is the shape of the problem: one small
module and one enormous term.

## 6. WHAT DEVLIN DOES

**MEASURED from the text: Devlin's construction uses NO Cantor-Schroeder-
Bernstein step. It is an order-type computation.**

**Devlin II.6.6, the Gödel Pairing Function** (`_build/literature/dev2.txt:1747-1785`).
He defines a well-ordering `<*` of `On × On` by: `max(α,β) < max(γ,δ)`; or the
maxima agree and `α < γ`; or the maxima and first coordinates agree and
`β < δ`. **Then `G(α,β)` is the ORDER TYPE of the set of predecessors of
`(α,β)` under `<*`**, so `G : (On × On, <*) ≅ (On, <)` by construction. The
proof then shows `G` is uniformly Σ₁ over `L_α` for limit `α > ω` through the
recursion `G(0,β) = sup_{ν<β}(G(0,ν) + ν + ν)`.

**Devlin II.6.7** (`dev2.txt:1791-1840`) gets the square law in surjection
form: for limit `α > ω` there is a Σ₁(L_α) map of `α` onto `α × α`. Its proof
is an induction on `α` with three cases, using `Q = {α | G : α × α ↔ α}`,
which is closed and unbounded. **Case 3 uses `g = G ↾ C` mapping `C` one-one
onto `α` "by definition of `G` from `<*`". That is the order-type isomorphism
again, not a back-and-forth.**

**So the answer the brief asked for: `CSB` is an artifact of our stating
leastness over bijections, not a debt Devlin's argument incurs.** Devlin never
needs to manufacture a bijection out of two injections, because his `G` is a
bijection by construction.

**And the project deliberately took a DIFFERENT road from Devlin's, which is
why the question arose at all.** `src/L/Ordinal/SquareLaw.lagda.md:1-11` says
so in its own prose: the route is the via-collapse construction, and **"the
order type of the archived route is never formed"**. Order types are what
Devlin uses and what this project priced out. **The collapse replaces the
order type, and then the leastness statement had to carry the cardinal
comparison, and stating that comparison over bijections is what pulled `CSB`
in.** This task removes it by stating the comparison over injections instead.

**One more literature fact, and it is `[LJ-1.154]`'s, re-checked.** Devlin's
base theory has no replacement: `BS = ReS0 + Cartesian product + full
foundation + ω ∈ V` (`dev/literature/devlin-errata.md:202-203`), and Stanley's
DS is `S0 + Δ₀ separation + Π₁ foundation + ω ∈ V + S(x) ∈ V`
(`devlin-errata.md:179-181`). **Neither has replacement. A chain that needs one
is a chain that has left Devlin's setting**, which is the structural reason
the replacement count mattered.

## 7. PRIOR ART: THE ARCHIVED `CSB`, AND WHY IT IS NOW UNNEEDED

**The orchestrator relayed prior art mid-task, and I read it whole:**
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`, built by
`[L3.32-T71]` on the retired rud route, in `Everything`, green.

**The line count, MEASURED with the ledger's caliber applied by hand.** The
whole master is **299 in-fence non-blank lines**, and the two modules the
orchestrator asked me to count separately are:

| module | in-fence lines | what it is | site |
|---|---:|---|---|
| `CSB` | **82** | the index-level back-and-forth. `Cₙ : ℕ → ⟪a⟫ → hProp` is the chain family, `C` its union, `ĥ` the bijection | `:89-194` |
| `Graph` | **101** | the carrier-level upgrade: `F : S` as a set of Kuratowski pairs, plus the five `HostBij` clauses | `:213-284` |
| `AtHull` | 70 | the 5.4 equality half, unrelated | `:375` |
| rest | 46 | Cantor's theorem, `BijectionForm`, header | |

**What I TAKE from it: the shape claim is right, and it is better news than
`[LJ-1.152]` expected.**
`F = sett (⟪ a ⟫) (λ x → pr (⟪ a ⟫↪ x) (⟪ b ⟫↪ (M.ĥ x)))` (`:218-219`) is a
family indexed by `⟪ a ⟫`, which is SMALL. **That is exactly `[LJ-1.154]`'s
`StageBound` shape, which is generic in the index type AND the family**
(`agents/tasks/LJ-1-154/ProbeLJ1154A.agda:128-152`). **So `[LJ-1.152]`'s
framing needs a correction and I record it:** the SET is small-indexed and the
stage device reaches it; it is the DEFINING CONDITION that is a recursion, not
the set.

**What I REFUSE to take.**

- **The claim that `Graph` transfers. It does not, unchanged.**
  `Cardinal.lagda.md:61` opens `hPropStructure 𝒮ᵥ`. **The whole module lives
  over V, and `sett` builds a V-set.** `HostBij F a b` is a V-level predicate.
  **A-prime needs `F ∈ L`, and nothing in those 101 lines puts it there.**
  The delta is exactly `[LJ-1.154]`'s Part 2 and Part 4: a stage bound and one
  `hasSeparationL`.
- **The claim that the carve would go through.** `[LJ-1.154]`'s `Carve` needs
  a ONE-PLACE object-language formula (`idFo`, `ProbeLJ1154A.agda:94-95`).
  **For `Graph` that formula must describe `ĥ`, and `ĥ` is defined by a LEM
  case split on `C`, which is the ℕ-indexed union `Cₙ`
  (`Cardinal.lagda.md:104-108, 147-173`). Nobody has written that formula and
  I did not write it.** INFERRED, and not measured, in either direction.
- **Any claim of the retired route.** The old route's condensation target was
  ruled classically FALSE at `[LJ-1.11]`. **Shape only, per DD18.**

**Why none of this changes the verdict.** The dissolution was tested FIRST, as
the orchestrator directed, and it holds. **A dissolved `CSB` needs no port**,
so the 183 lines of `CSB` plus `Graph` are a price A5 does not pay.

**Where the prior art DOES stay valuable, and it is a DD4 point.** If the
OTHER trophy ever needs an equinumerosity object, `CSB` at 82 lines plus
`Graph` at 101 is a delivered, green starting shape, and `[LJ-1.154]`'s
`StageBound` covers its index type today. **That is a fact about a possible
future, not about A5.**

## 8. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. `CSB` is not needed by the chain.** `ProbeLJ1156A.agda`
  elaborates `--safe`, exit 0. The string `CSB` appears 15 times in the file
  and **all 15 are comments**; `≃` appears 5 times and all 5 are comments;
  `Cubical.Foundations.Equiv` is not imported; `Base.Classical.lowerLEM` is
  not imported. One grep over the non-comment lines returns nothing.
- **MEASURED. `[LJ-1.136]` section 9.1's three-row table is correct**, and it
  understates the saving. `Incl`, `noinj²`'s `j` and `FiniteAtω` die too.
- **MEASURED. The `inj` parameter is NOT discharged by this change.** The
  truncation wall is about `↪` not being an hProp, and swapping the predicate
  leaves it standing. `[LJ-1.136]` Probe B discharges it, not this task.
- **MEASURED. ZERO heap walls.** No run exhausted the 8 GB cap. The cap was
  never raised. **Four probe files, twenty-two runs**: Probe A seven (one
  first cold-tree run, two exit-code confirmations, four in series), Probe B
  five, Probe D five, Probe E five. **All four files end at exit 0.**
- **MEASURED. The injection predicate is not more expensive than the bijection
  predicate.** 100.64 s against 96.09 s, three kept runs each, and the
  4.7 percent gap is inside `[LJ-1.148]`'s 12.8 percent band. **I do not claim
  the gap in either direction.**
- **MEASURED. No `hasSeparationL` and no `hasReplacementL` appear in
  `ProbeLJ1156A.agda`.** This probe is the AMBIENT chain; the L-side objects
  are `[LJ-1.152]`'s and `[LJ-1.154]`'s business and I did not re-open them.
- **MEASURED. The rate is 48 times DD24's bar**, and `CSB` was never the
  cause. See section 5.3.
- **INFERRED. The four remaining built objects carve.** Inherited from
  `[LJ-1.154]` section 7.2 unchanged. **P-l: I did not transfer any measured
  cure to them by analogy.**
- **INFERRED, and NOT measured in either direction. Whether `Graph`'s `F`
  carves by separation.** Section 7 says why: the one-place formula for `ĥ` is
  unwritten. **It no longer blocks A5.**

## 9. DD4, ANSWERED AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic. No stop-line
made me write fixed.**

**The best DD4 answer this task can give is a removal.** `[LJ-1.136]` recorded
that `CSB` is generic and would serve the other trophy too
(`agents/tasks/LJ-1-136/lj-1.136-report.md:431`). **That is true and it is
now beside the point for A5: code you do not write is shared perfectly.**

| part of `ProbeLJ1156A.agda` | lines | generic in | names an L axiom or an L stage? |
|---|---:|---|---|
| `_↪_` | 2 | the two types | **NO** |
| `LeastCardInj` | 51 | the ordinal and its ordinal-hood | **NO.** It names `ordSWO`, `leastOf` and `sucV`, which are the V-side ordinal vocabulary |
| `ShiftAbs` | 103 | the ordinal, its ordinal-hood, and the numeral supply as a PARAMETER | **NO** |
| `InitialCase` | 55 | the ordinal and `leastα` as a PARAMETER | **NO** |
| `NonInitial` | 45 | the ordinal, κ, and the injection as a PARAMETER | **NO** |
| `Chain` | 30 | the honest-injection supplier as a PARAMETER | **NO** |

**MEASURED, one grep: no line of `ProbeLJ1156A.agda` names `hasSeparationL`,
`hasReplacementL`, `Lset`, `LsetS`, `stage` or `boundingOrd`.** The whole
chain is over the V-side ordinal vocabulary.

**So the J tower re-instantiates the chain rather than writing it again, IF
the J tower's ordinals present the same way.** That is the honest residue and
I name it: the file is generic in the ordinal but NOT in the carrier. It sits
over `𝒮ᵥ` and `⟪_⟫`, exactly as `[LJ-1.154]`'s `Carve` sits over `𝒮ʟ`
(`agents/tasks/LJ-1-154/lj-1.154-report.md:352-358`). **A full two-tower form
takes the structure as a module parameter, as `FOL.ZFModel` already does. That
refactor is not measured here and a probe is the wrong place to run it.**

**The DD4 answer for `CSB` itself, since the brief asked.** `CSB` survives
only as archived prior art (section 7). **It is generic in both types and it
would serve either tower.** `Graph`, its carrier-level half, is generic in the
two sets but fixed to `𝒮ᵥ`. **Neither is on A5's path any more.**

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-136/lj-1.136-report.md:504-526`**, section 9.1, read
  whole. **The three-site table and the dissolution argument. TAKEN: the
  design, exactly as written. CONVERTED from INFERRED to MEASURED.** Also
  `:446` (`CSB` absent from `src/`), `:455` (the classification I was sent to
  settle), `:897-928` (Probe B's GO, which is what discharges `inj`),
  `:1117-1121` (the six-replacement inference).
- **`agents/tasks/LJ-1-154/lj-1.154-report.md`**, read whole. TAKEN:
  section 7.2's six-object table, unchanged and still INFERRED for four rows;
  section 4.2's 1.73 s; section 8's generic-parameter discipline; section 2's
  load-reporting discipline. `ProbeLJ1154A.agda:94-95, 128-152, 167-170` for
  the one-place formula and the generic `StageBound`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md:196-243`.** TAKEN: the 2.50 s
  composition and the reason `CSB` was singled out. **CORRECTED at `:220-227`:
  the SET is small-indexed, so the stage device reaches it; it is the defining
  CONDITION that is a recursion.** Section 7 gives the evidence.
- **`agents/tasks/LJ-1-107/ProbeLJ1107A.agda`**, read whole.
  `:99-207` (`CSB`), `:217-266` (`LeastCard`, copied verbatim into
  `ProbeLJ1156E.agda` for the A/B), `:278-394` (`ShiftAbs`/`Shiftω`, copied
  verbatim), `:403-438` (`FiniteAtω`, REFUSED as superseded by the delivered
  `no-inj-finite`), `:441-453` (`Incl`, REFUSED as dead), `:464-537`
  (`InitialCase`, rewritten), `:549-618` (`NonInitial`, rewritten),
  `:630-666` (`Chain`, copied with one module name changed).
- **`agents/tasks/LJ-1-107/lj-1.107-report.md:28-40, 49-63`.** TAKEN: the
  per-step table, which is the only source for `CSB` = 2.03 s and
  `LeastCard` = 91.98 s of 117 s, and for the truncation wall's exact cause.
- **`agents/tasks/LJ-1-106/ProbeLJ1106A.agda:86-136`.** TAKEN:
  `NumeralPresentation`, verbatim minus `ω≃ℕ`, so the base case is real.
  **REFUSED: everything else in that file**, 443 lines of pullback machinery
  this chain does not use.
- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`**, read whole.
  `:89-194` (`CSB`, 82 lines), `:213-284` (`Graph`, 101 lines), `:218-219`
  (the `sett` family, which is the shape that transfers), `:202-207` (the
  prose stating the design intent), `:61` (`open hPropStructure 𝒮ᵥ`, which is
  why it does not transfer unchanged). **TAKEN: the shape and the two line
  counts. REFUSED: the transfer claim, and every claim of the retired route.**
- **`dev/LESSONS.md`**: D-1 (the criterion fixed first), C-38 as extended
  (`:3427`, four witnesses in Part 7), P-l (no cure transferred by analogy),
  C-12 (one process, `-M8g`, never raised), C-22 (skeleton first), C-36 (no
  refusal was produced, so no negative rests on a coercion failure), R-40 (the
  deep-successor cost, which section 5.3 names).
- **`dev/PLAN.md:139-142`**, DD24's bar of 0.007913 s per line, for
  section 5.3. **DD8** for the one-number-with-a-basis form in section 5.2.
- **`src/L/Ordinal/SquareLaw.lagda.md:1-11`** (the chapter's own statement
  that no order type is formed), `:146-181` (`ordSWO`), `:533-682`
  (`FiniteBase`, `no-inj-finite`), `:685-698` (`sq`, `Init`), `:958-963`
  (`via-col-square`).

## 11. LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:1747-1785`**, Devlin II.6.6, the Gödel
  Pairing Function, read whole with its proof. **The order type of the
  predecessors under `<*`. No Cantor-Schroeder-Bernstein step.**
- **`_build/literature/dev2.txt:1791-1840`**, Devlin II.6.7, the Σ₁ map of α
  onto α × α, three cases, read whole. **Case 3 uses `G ↾ C` one-one onto α
  "by definition of `G` from `<*`".**
- **`dev/literature/devlin-errata.md:179-181, 202-203`.** BS and DS both
  stated; **neither has replacement.** This re-checks `[LJ-1.154]`'s claim at
  the source it named.
- **`dev/literature/devlin-II5.md:411-418`**, II.1.1(vii) as the counting half
  of 5.5 and 5.6, which is where the square law is consumed.
- **`dev/literature/rudimentary-functions.md:68`**, the rud basis delivering
  the product outright. **CONSULTED, not used:** this task's chain builds no
  product in L.
- **`dev/literature/j-hierarchy.md:111, 149`** and
  **`dev/literature/digest.md:241`**, SZ 1.17: an ordinal closed under the
  Gödel pairing function has `otp(<^A_α) = α`. **Corroborates that the
  orthodox route to the square law is the canonical order's order type.**

## 12. MACHINE STATE

**16 cores, macOS 25.6.0, Agda 2.8.0. ONE agda process of mine at a time,
always `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**

**`[LJ-1.155]` was running throughout.** MEASURED, `ps aux` at 22:24:
`agda --profile=internal agents/tasks/LJ-1-155/ProbeLJ1155B2.agda` at 99.0
percent CPU and 12.8 percent memory; at 22:33 the same at `ProbeLJ1155B6.agda`.
**The machine was NOT quiet for any run in this report.** The one-minute load
band over all series is 2.72 to 3.74.

**Every figure carries the load at the start of its run.** The band is narrow
and no verdict turns on it: the verdict is an exit code.

## 13. WORKING TREE, AS MY REPORT DESCRIBES IT

**Nothing committed, nothing pushed. No master edited. `src/` untouched.**

New files, all in `agents/tasks/LJ-1-156/`, all tracked, none deleted:

- `lj-1.156-report.md`, this report.
- `ProbeLJ1156A.agda`, the chain over injections. **THE DELIVERABLE.**
- `ProbeLJ1156B.agda`, the import control.
- `ProbeLJ1156D.agda`, leastness over INJECTIONS alone.
- `ProbeLJ1156E.agda`, leastness over BIJECTIONS alone, `[LJ-1.107]`'s
  `LeastCard` verbatim.

**All four `.agda` files end at `agda --safe`, exit 0**, confirmed in one
final pass after the last edit.

**What is in the tree that is NOT mine.** `git status` also shows
`dev/PLAN.md` modified and `agents/tasks/LJ-1-155/` and
`agents/tasks/LJ-1-157/` untracked. **I did not write, edit or delete any of
them.**

**I did not touch `src/L/Condensation.lagda.md`, the three `*Agree` masters,
`src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.** I did not run
`make check`. I did not commit and I did not push.

**Checks I ran, all green:** `scripts/lint-prose.py --check` on this report
(exit 0), `scripts/lint-agda.py --check` (exit 0), `scripts/check-probes.py`
(clean, 1662 tracked files, no probe outside `agents/tasks/`).

## 14. WHAT IS NOT DONE, NAMED RATHER THAN HIDDEN

**1. THE NEXT GATE, and it is now the widest unmeasured term in A5.**
`LeastCardInj` is 44 lines and about 99 s. **Nobody has probed whether that
term comes down.** `[LJ-1.107]` named the cause two weeks of dispatches ago
and no dispatch has attacked it. The candidates the evidence already names:

- **R-40** (`dev/LESSONS.md`): a deep successor-chain membership witness
  normalizes super-linearly, and the cure is to state the witness at a shallow
  index and climb by `limit-succ-mem`. **`LeastCardInj` states everything at
  `sucV α`.**
- **P-l**: `⟪ sucV α ⟫` is a transparent presentation named in the TYPE of
  `w`, `InjP'`, `least`, `γ-card` and `κ-min-at`. **An `opaque` seal on the
  successor's presentation is the obvious first probe.** P-l also warns that
  the seal moved nothing at `[LJ-1.152]`'s site and that `[LJ-1.154]` measured
  its own seals were not load-bearing. **So it is a probe, not a cure.**

**A5 is priced without this, because a price is what a block costs as
written.** But 48 times DD24's bar is what A5 costs as written, and I state
it rather than leave the number for the next agent to discover.

**2. The `inj` parameter.** Not discharged here. `[LJ-1.136]` Probe B
discharges it and returned GO. **This task did not re-run Probe B and does not
re-certify it.**

**3. The four INFERRED carvings.** `ShiftAbs`/`Shiftω`, the inclusion `j`,
`pairω` and the column square. **Inherited from `[LJ-1.154]` section 7.2 and
untouched.** Each still needs its own one-place description written.

**4. The L-side of this chain.** `ProbeLJ1156A.agda` is the AMBIENT chain. It
proves what the chain needs and what it does not need. **It does not build a
single L-element**, and section 9 gives the grep that shows it. The L-side is
`[LJ-1.152]`'s and `[LJ-1.154]`'s measurement and I did not re-open it.

**5. `Graph`'s carve.** Section 7. Not measured in either direction, and no
longer on A5's path.
