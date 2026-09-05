# LJ-1.170 report: price BOTH arms of the fork

tier: opus (version `override`). **No master is edited. `git status` shows two
new files, both mine, both in `agents/tasks/LJ-1-170/`. No commit, no push.**
Every negative is marked **MEASURED** or **INFERRED** (C-36). Written
incrementally (C-22).

## 0. RECOMMENDATION, in ONE sentence

**Take a THIRD arm, ARM B-prime: keep `⌜_⌝` exactly as it is and re-KEY the code
set with the parameter split this tree ALREADY DELIVERS
(`src/L/Choice/Name.lagda.md:381`), because I MEASURED that the split key lands
at `Lset (sucIter 5 σ)` uniformly in the formula and in the parameter count, in
37 in-fence lines, exit 0.**

**ARM B as the brief states it (re-code `⌜_⌝` into finite sequences) is NOT
needed, and ARM A is ARM B-prime's obligation PLUS a closure hypothesis. Neither
of the two named arms is the cheap one.**

## 1. THE FIGURES, SIDE BY SIDE, each naming its basis (DD8)

| arm | ONE figure | basis |
|---|---:|---|
| **ARM A**, carrier to the omega-limit | **0.3 to 0.7k** | 37 lines of assembly MEASURED (`[LJ-1.169]` 12 + this probe's `prTower-ω` 4 + `powAtBlock` 3, and my BLOCK 2 exit 0); the object-level description SURVEY, anchored on the delivered `src/L/Coding/CodeSet.lagda.md` at 168 in-fence lines; **plus `closedω` at every consumer, which `[LJ-1.167]:207` MEASURED is NOT needed under a finite-iterate bound** |
| **ARM B**, re-code `⌜_⌝` as sequences | **NOT PRICED, and I say why rather than publish a number** | The change is unnecessary. Section 4. `[LJ-1.10]`'s 2.45-5.1k is a CATEGORY-MISMATCHED anchor, not merely an unmeasured one. Section 5 |
| **ARM B-prime**, re-KEY with the delivered split | **0.3 to 0.6k** | **37 lines MEASURED GREEN** (`ProbeLJ1170A.agda`, exit 0, 9.94 s); the object-level description SURVEY on the same 168-line comparable; 29 `keyS` call sites MEASURED across 4 masters |

**ARM A and ARM B-prime buy the SAME thing and differ in ONE term.** Both need
the same object-level description of the code set. ARM A reads it at `+ω δ` and
charges the consumer `closedω` on top of successor closure. ARM B-prime reads it
at `sucIter 5 δ` and charges successor closure alone. **The difference is one
hypothesis on every consumer, and it is a per-tower hypothesis.**

## 2. WHAT IS ALREADY DELIVERED

**MEASURED sizes, ledger caliber (non-blank lines inside ` ```agda ` fences).**

| tree | in-fence lines | masters |
|---|---:|---:|
| `src/L/Coding/` | **6,577** | 20 |
| `src/L/Choice/` | **5,844** | 12 |
| `src/FOL/` with `src/FOL/Manipulation/` | **1,613** | 13 |
| `src/FOL/Coding.lagda.md` alone | **169** | 1 |
| `src/L/Coding/CodeSet.lagda.md` alone | **168** | 1 |
| `src/L/Ordinal/StageArith.lagda.md` | **75** | 1 |
| `archive/.../L/Rud/SatTable.lagda.md` | **109** | 1 |

Standing is 28,940 lines over 85 masters (`scripts/ledger.py --brief`).

### 2.1 ARM A's consumer climb is DELIVERED, green, and 4 lines

**MEASURED.** `boundCloses` (`src/L/Ordinal/StageArith.lagda.md:86-89`) takes
`closedω α` and `δ ∈ˢ α` and lifts `b ∈ˢ Lset (+ω δ)` to `b ∈ˢ Lset α`.
`closedω` is at `:81-82`, `envCloses` at `:92-96`. **ARM A's climb is code to
CALL, not code to write.**

**And `envCloses` takes `env ∈ˢ Lset (sucIter 3 δ)`, a FIXED finite iterate.**
`StageArith`'s author wrote BOTH bounds into one 75-line module: `+ω` for the
code set and `sucIter 3` for the environment. **The second one is ARM B-prime's
bound, written before this wing began.**

### 2.2 DEVLIN'S SPLIT IS ALREADY IN THIS TREE, DELIVERED AND GREEN

**MEASURED, and this is the finding that decides the fork.**
`src/L/Choice/Name.lagda.md` states it in its own opening prose, `:5-9`:

> the previous chapters have said what that means twice over: once as a formula
> with parameters drawn from that stage, and once, **after the parameters left
> the syntax, as a parameter-free formula together with a vector of
> parameters**.

| name | `file:line` | what it is |
|---|---|---|
| `nameOf φ = countFo φ , (absFo φ , constantsFo φ)` | `src/L/Choice/Name.lagda.md:381` | **THE SPLIT. Arity, parameter-free formula, parameter vector** |
| `code∈limit` | `src/L/Choice/Name.lagda.md:153-165` | **the parameter-free code is in `Lset ω`, UNIFORMLY in depth** |
| `pr∈limit` | `:139-148` | the `κ → κ` pairing closure at `ω`, which is why depth is free there |
| `tag∈limit` | `:134-135` | |
| `absFo` | `src/FOL/Manipulation/Parameters.lagda.md:260-261` | **GENERIC in the constant type.** Names no tower |
| `constantsFo` | `:105` | **GENERIC.** Names no tower |
| `⊨-abs₁` | `:461-463` | **the split preserves satisfaction.** Delivered |
| `finSet∈𝒟ₒ` | `src/L/Axioms/Basic.lagda.md:352-354` | a finite family from a stage costs ONE stage |
| `keyCode` | `src/L/Choice/Adequate.lagda.md:347-349` | **3 lines. The plain key of a parameter-free formula IS `pr (# m) (limitCode χ)`** |

**`src/L/Choice/Name.lagda.md:92-99` states the mechanism outright: "The one
construction that could leave the finite world is the constant clause, which
puts an arbitrary set into the code, and a parameter-free formula has no
constants at all."**

**That sentence is `[LJ-1.169]`'s obstruction and its cure, written down on the
AC side before this wing asked the question.** `[LJ-1.169]` MEASURED the
obstruction correctly; it did not find that the tree already carries the cure.

### 2.3 The two blind spots the brief named

- **`src/L/Ordinal/StageArith.lagda.md`: READ WHOLE, 75 in-fence.** Section 2.1.
  Its second half (`envCloses`, a FIXED `sucIter 3`) has never been cited by
  this wing.
- **`src/L/Axioms/Separation.lagda.md`: READ, 321 in-fence.** `carve∈𝒟ₒ`
  (`:198-199`) is the route into `𝒟ₒ (Lset σ)`: a formula over the stage's own
  alphabet carves a member. `carveSat` (`:163-166`) needs `BoundedFo Below φ`
  and `Δ₀ φ`. **This is the site where BOTH arms pay their object-level
  description, and it is the SAME site for both.** MEASURED.
- **`src/L/Choice/`: 5,844 in-fence over 12 masters, SEARCHED.** The
  load-bearing find is `Name.lagda.md` (section 2.2), not `Limit`, `Before` or
  `Transversal`, which touch no code and no stage (MEASURED: zero hits for
  `mkTag`, `⌜`, `+ω`, `sucIter`, `𝒟ₒ`).

## 3. ARM A PRICED, AND WHAT THE ARCHIVE ACTUALLY PAID

### 3.1 THE ARCHIVE DID NOT REACH ARM A's BOUND. IT ASSUMED IT

**MEASURED, and it corrects the brief's premise 4.** The brief says the retired
route "REACHED exactly that bound at a general carrier". **It reached the
STATEMENT. The content is a named hypothesis.**

`archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md`, read WHOLE, 109
in-fence:

```agda
SatRelation R = ⟨ R ∈ˢ Sset γ ⟩
              × (Σ[ K ∈ S ] (Σ[ cod ∈ Cod ]
                  (⟨ K ∈ˢ Sset γ ⟩ × Covers K cod × Slices R cod)))
```

`:175-178`. **`blockPow-at-limit` (`:214-220`) TAKES `Coded.SatRelation (+ω δ)
C R` as an argument.** So its input is "the code set `K` and the satisfaction
relation `R` are ALREADY members of `Sset (+ω δ)`" — which is exactly
`[LJ-1.169]`'s HALF 2, the unsourced term, restated as a hypothesis.

**Three further measurements from that file, each of which changes the reading:**

1. **`C∈ : ⟨ C ∈ˢ Sset δ ⟩` and `limδ` are UNUSED in the body.**
   `blockPow-at-limit δ ordδ limδ C C∈ R sr = Coded.coded-pow (+ω δ) (+ω-limit δ
   ordδ) C R sr` (`:218-219`). **The `+ω` is cosmetic.** The real theorem is
   `pow∈J` (`:143-148`): at ANY limit `γ`, if `K ∈ˢ Sset γ` and `R ∈ˢ Sset γ`
   then `𝒟ₒ C ∈ˢ Sset γ`, with **zero offset**.
2. **What it PAID: the RUD BASIS.** `pow∈J` runs on `Jset-rud`
   (`archive/.../L/Rud/Step.lagda.md:954-956`), "a limit level is closed under
   every operation of the basis", with `F8` the collection and `F10` the slice
   (`:53`). **The live L route has no rud basis and no `Jset-rud`. MEASURED:
   `grep -rl Jset-rud src/` returns nothing.**
3. **Its own prose says so.** `:6-8`: "names the one hypothesis the step still
   needs", and `:24-26`: "One hypothesis away is the reading this chapter
   delivers."

**TAKEN: the SHAPE and the honest accounting. NOT taken: any claim.**
`[LJ-1.11]` ruled that route's condensation target classically FALSE.

**Consequence for the fork. The archive is NOT evidence for ARM A over ARM
B-prime.** It is evidence that the definable power lands with no offset ONCE the
code set is a member of the level, and it says nothing about which coding puts it
there. **That is the whole question, and the archive left it open.**

### 3.2 ARM A does not remove the obstruction. It moves it, and charges for the move

**MEASURED where marked, INFERRED where marked.**

- **MEASURED**: every code over a carrier at `δ` lies in `Lset (+ω δ)`
  (`prTower-ω`, re-checked in my BLOCK 2, exit 0). So at the carrier `+ω δ`, the
  existentials of `DefAt` have their witnesses inside the carrier.
- **MEASURED**: the assembly above that is 3 lines (`powAtBlock`,
  `agents/tasks/LJ-1-169/ProbeLJ1169A.agda:125-127`).
- **INFERRED, and it is the term ARM A does not escape**: the description ψ must
  still be WRITTEN in the object language and read inside `Lset (+ω δ)`, through
  `carve∈𝒟ₒ` with its `BoundedFo` and `Δ₀` side conditions
  (`src/L/Axioms/Separation.lagda.md:150-166`, `:198-199`). **That is the same
  object-level work ARM B-prime needs. ARM A does not avoid it.**
- **MEASURED**: the consumer pays MORE. `pow-closed-suc`
  (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:129-136`) needs `closedω lam` AND
  successor closure. `[LJ-1.167]:207` and `:456` MEASURED that under a
  finite-iterate bound `closedω` is **NOT required** and `KFacts` needs **no
  fourth parameter**.

**So ARM A's whole marginal cost over ARM B-prime is: one extra hypothesis in
`KFacts`, discharged once per tower.** That is section 8's DD4 answer.

## 4. ARM B PRICED: it is unnecessary, and I state the reason

**The brief's ARM B is "codes become finite sequences over a fixed formula set".
MEASURED: this tree does not have to change `⌜_⌝` to get Devlin's bound, and I
proved the bound with `⌜_⌝` UNCHANGED.**

### 4.1 What re-coding would cost, so the number exists

**MEASURED blast radius of changing `⌜_⌝`: 294 shape-critical lines over 16
files**, counting occurrences of `mkTag`, `payOf`, `tagOf`, `⌜⌝-inj`,
`⌜⌝ᵗ-inj`, `pr-inj`, `VCode.⌜`, `LCode.⌜`.

| file | shape-critical lines |
|---|---:|
| `src/FOL/Coding.lagda.md` | 89 |
| `src/FOL/Count.lagda.md` | 47 |
| `src/L/Coding/Sound.lagda.md` | 39 |
| `src/L/Coding/Table.lagda.md` | 29 |
| `src/L/Coding/Unique.lagda.md` | 25 |
| `src/L/Coding/InL.lagda.md` | 25 |
| the other 10 files | 40 |
| **total** | **294** |

### 4.2 And the reason re-coding is worse than expensive

**MEASURED, from `src/FOL/Coding.lagda.md`'s own prose at `:26-29`:**

> a code value is a deeply nested pair, and an equation between two of them
> forces a typechecker to unfold both. **The relation makes the shape a
> constructor index instead, so matching is syntactic and the values are never
> normalized.**

**INFERRED, and I mark it: a flat-sequence code destroys that property.** The
head of a concatenated sequence does not determine the split point without a
length computation, so `Codes`' twelve constructors could no longer index the
shape syntactically. **`⌜⌝-inj` (`:308-343`) would need a unique-readability
proof in place of two applications of `pr-inj`.** P-i is the law this walks
into. I did NOT measure a hang and I claim none.

### 4.3 ARM B-prime, and the measurement that settles the fork

**`ProbeLJ1170A.agda`, exit 0, 9.94 s, 377 MB resident. Criterion: GO at or
below 60 in-fence lines, fixed in writing at `ProbeLJ1170A.agda:5-16` before the
first `agda` ran.**

```agda
splitKey σ n k χ g = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramSet σ k g))

splitKey∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩) (n k : ℕ)
            (χ : Formula (⊥* {ℓ}) (n + k)) (g : Fin k → ⟪ Lset σ ⟫)
          → ⟨ splitKey σ n k χ g ∈ˢ Lset (sucIter 5 σ) ⟩
```

`ProbeLJ1170A.agda:113-127`.

| block | what it measures | in-fence lines |
|---|---|---:|
| BLOCK 1 | **the split key at a FIXED iterate, `sucIter 5 σ`, uniform in `χ` and in `k`** | **29** |
| BLOCK 3 | **the DELIVERED `absFo`/`constantsFo` triple feeds BLOCK 1 unchanged** | **8** |
| **ARM B-prime's core** | | **37** |
| BLOCK 2 | the contrast: this tree's delivered code shape needs `dbl n` stages | 16 |

**BLOCK 3 is the load-bearing half and I state what it proves:**

```agda
deliveredSplit σ φ = splitKey σ 1 (countFo φ)
  (absFo {ℓz = ℓ} {n = 1} φ) (λ i → lookup i (constantsFo φ))

deliveredSplit∈ : ... → ⟨ deliveredSplit σ φ ∈ˢ Lset (sucIter 5 σ) ⟩
```

`:157-166`. **For EVERY formula over the carrier, at any depth, with any number
of parameters, the delivered split's key sits at a FIXED five stages above the
carrier. `src/FOL/Coding.lagda.md` is not touched and `⌜_⌝` keeps its nested
shape.** MEASURED, exit 0.

**Why the nesting is free.** The parameter-free code has no constants, so
`code∈limit` (`src/L/Choice/Name.lagda.md:153`) puts it in `Lset ω` whatever its
depth, by the one `κ → κ` pairing closure this tree has
(`[LJ-1.166]:185-192`, MEASURED). **`[LJ-1.169]`'s growth law is real and it
applies only to the constants.**

### 4.4 ARM B-prime's blast radius, MEASURED

**29 `keyS` call sites over 4 masters.**

| master | `keyS` sites |
|---|---:|
| `src/L/Coding/CodeSet.lagda.md` | 15 |
| `src/L/Choice/Adequate.lagda.md` | 8 |
| `src/L/Choice/Internal.lagda.md` | 4 |
| `src/L/Choice/Faithful.lagda.md` | 2 |

**`keyS` is 2 lines (`src/L/Coding/CodeSet.lagda.md:300-301`).** The object-level
reading `isCodeAny A = arityNumAtL zero ∧̇ hasWitness A` (`:247-248`) gains one
conjunct for the parameter set, with its two directions.

**DD13, the rewrite side first.** The ideal form written fresh today is: one key
function (3 lines, measured), one uniform bound (29 lines, measured), one
object-level reading of a THREE-component key where the delivered one reads a
TWO-component key, and the two directions of `AllCodes`. **The delivered
comparable for that reading is `src/L/Coding/CodeSet.lagda.md` at 168 in-fence
lines total.** Adding one component to a two-component reading is priced by
survey at 0.15-0.35k, and the 29 sites at 3-8 lines each at 0.10-0.23k.
**「We already paid for `keyS`」 decides nothing, and I did not use it.**

## 5. IS `[LJ-1.10]`'s 2.45k-to-5.1k A FALSE ANCHOR? YES, AND WORSE

**MEASURED. It is not merely unmeasured. It prices a DIFFERENT CHANGE.**

`agents/tasks/archive/LJ-1-10/lj-1.10-reprice.md:129-153`. Its Candidate B is
**"the abstraction of the cone over the restriction class"**, `:120-123`:

> The re-typing is the abstraction of the cone over the restriction class.
> D-16 prescribed it. The tree did not do it. The cone is monomorphic in `𝒮ʟ`
> (`src/L/Coding/Sequence.lagda.md:61-62`).

**That is the DD4 genericity problem: make `src/L/Coding/` run at a SECOND
CARRIER. It has nothing to do with how a formula is coded as a set.** Quoting it
for a re-coding is a category error.

**And its own basis is thin.** Of the 2.45-5.1k band, `:145-152`:

| component | band | basis, as `[LJ-1.10]` states it |
|---|---:|---|
| re-typing across 21 masters | 1.2-3.0k | **survey** |
| re-run of the readings | 1.0-1.7k | **survey**, quoting R2p |
| transport certificate | 0.15-0.30k | **survey**, R2p |
| limit case | 0.1k | probe, T261 |

**MEASURED: 2.35k to 4.9k of the band is SURVEY. 0.1k is probe-measured.**
`[LJ-1.10]` itself opened by calling the 5,047 "a false anchor for today's tree"
(`:29`), and `[LJ-1.168]` confirmed that 5,047 had never been measured. **The
2.45-5.1k is one document further along the same chain, and it fails a second
test the 5,047 passed: it is not even about this question.**

## 6. THE WIDEST UNMEASURED TERM OF EACH, AND ITS PROBE

| arm | widest unmeasured term | the probe that measures it |
|---|---|---|
| **ARM A** | **`closedω lam` at the consumer: which `lam` supplies it, and does `KFacts` grow a fourth parameter?** `[LJ-1.167]:207` MEASURED that a finite bound needs only `succλ`, and no task has priced the `+ω` version | Instantiate `pow-closed-suc` (`ProbeLJ1169A.agda:129-136`) at the wing's actual `lam` and try to discharge `closedω lam` from the delivered hull facts. Abort if it needs a new ordinal-arithmetic chapter |
| **ARM B-prime** | **the object-level reading of a THREE-component key: `isCodeAny` with a parameter-set conjunct, and its two directions through `carve∈𝒟ₒ`'s `BoundedFo` and `Δ₀` side conditions** | Write ONE conjunct, `paramSetAtL`, with its `-in` and `-out`, against the delivered `arityNumAtL` (`src/L/Coding/CodeSet.lagda.md:185-205`) as the rate comparable. Stop-line 60 lines. **That measures the whole 0.15-0.35k row** |
| **ARM B** | not applicable | it is not the change to make. Section 4 |

## 7. IS THERE A THIRD ARM? YES, AND IT IS THE RECOMMENDATION

**ARM B-prime is a third arm and `[LJ-1.169]` did not name it.** `[LJ-1.169]`
named "re-code" and "move the carrier" and did not claim they were exhaustive;
it was right not to.

**ARM B-prime is neither.** It changes neither `⌜_⌝` nor the carrier. It changes
**what gets keyed**: the key carries the parameter-free code plus the parameter
set, instead of the code of the parametrized formula. **The coding is untouched
and the carrier stays at `δ`.**

**A FOURTH arm does not exist that I can see, and I say that as an observation,
not a proof.** The obstruction is that constants sit at the leaves of a nested
tree. Only three things can be done about it: change the tree (ARM B), climb
above every depth (ARM A), or take the constants out of the tree (ARM B-prime).
**I did not prove that trichotomy and I do not claim it.**

## 8. DD4: ARM B-PRIME LEAVES MORE SHARED, AND HERE IS BY HOW MUCH

**The brief's own framing was that ARM B re-codes a layer BOTH towers use while
ARM A adds a per-tower obligation. MEASURED: that framing is right, and it
points at ARM B-prime, not at ARM A.**

### 8.1 ARM A's marginal cost is EXACTLY a per-tower obligation

**MEASURED.** ARM A's only cost over ARM B-prime is `closedω lam` in `KFacts`
(section 3.2). **`closedω` is a statement about a tower's own index set
(`src/L/Ordinal/StageArith.lagda.md:81-82`), so each tower discharges it
separately. It is per-tower by construction.**

### 8.2 ARM B-prime's core is tower-blind, and the delivered half entirely so

Tokens counted: `Lset`, `𝒟ₒ`, `+ω`, `sucIter`, `sucV`.

| block | lines | naming a tower | tower-blind |
|---|---:|---:|---:|
| BLOCK 1, the split key and its bound | 29 | 18 | 11 |
| BLOCK 3, the delivered split feeding it | 8 | 3 | 5 |
| BLOCK 2, the contrast | 16 | 7 | 9 |

**And the DELIVERED half is 100 per cent tower-blind, which is the stronger
measurement.** `absFo` and `constantsFo`
(`src/FOL/Manipulation/Parameters.lagda.md:260-261`, `:105`) are generic in the
constant type and mention **no tower, no `Lset`, no stage** — MEASURED, they sit
in `src/FOL/`, above any hierarchy. **The J tower gets the split for free
because the split is a fact about FORMULAS, not about a tower.**

The tower-naming half of BLOCK 1 is `paramSet`, `paramSet∈` and `fromω`. **Each
names the tower only through its stage function and its `finSet∈𝒟ₒ`**, so it
parameterises the same way `[LJ-1.169]` described for its BLOCK 1. **I do NOT
price the generic variant, because I did not write it** (DD8, C-36).

### 8.3 The answer, in one line

**ARM B-prime leaves more shared, by the whole of `absFo`, `constantsFo`,
`⊨-abs₁` and `code∈limit`, which are delivered and tower-blind; and ARM A adds
`closedω`, which is per-tower and which `[LJ-1.167]` MEASURED is otherwise not
needed at all.**

## 9. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md`, READ WHOLE, 109
  in-fence.** TOOK `pow≡` (`:119-141`), `pow∈J` (`:143-148`), `SatRelation`
  (`:175-178`), `coded-pow` (`:180-182`), `BlockPowLim` (`:210-212`),
  `blockPow-at-limit` (`:214-219`), and its own prose at `:6-8` and `:24-26`.
  **THE CORRECTION: it ASSUMED the bound it is credited with reaching, and its
  `+ω` is cosmetic because `C∈` and `limδ` are unused in the body.** Section 3.1.
- **`archive/src/2026-08-09-rud-route/L/Rud/Step.lagda.md:954-958`, READ.**
  `Jset-rud`, the rud-basis closure that `pow∈J` runs on. **MEASURED: the live
  tree has no `Jset-rud`.**
- **`archive/src/2026-08-09-rud-route/`, SEARCHED for `SatRelation`,
  `BlockPowLim`, `coded-pow`, `blockPow`.** The hypothesis is discharged
  NOWHERE outside `SatTable` and the route patch. **MEASURED.**
- **`archive/src/2026-08-09-rud-route/L/Coding/`, SURVEYED, 11 masters.** The
  brief asks whether the retired route's coding baked parameters into the code
  tree. **It carries the SAME `Model`, `InL`, `CodeSet`, `Powerset`, `Sequence`,
  `Uniform`, `Recover`, `Bridge`, `EnvSet`, `Environment`, `Base` names as the
  live tree, so the coding is the SAME coding. ARM B has NO delivered comparable
  in the archive.** MEASURED.
- **`agents/tasks/LJ-1-169/lj-1.169-report.md`, READ WHOLE.** TOOK the fork
  (`:345-358`), the growth law (`:236-253`), the level-blindness (`:88-107`),
  `Describes` and its two halves (`:316-330`), and the archive pointer
  (`:410-422`). **Section 2.2 adds what it did not find: the tree already
  carries the split.**
- **`agents/tasks/LJ-1-168/lj-1.168-report.md`, READ.** TOOK the false-anchor
  finding on the 5,047 (`:167`, `:503`) and the `[LJ-1.10]` pointer (`:546`).
  **Section 5 applies the same test to 2.45-5.1k and it fails harder.**
- **`agents/tasks/archive/LJ-1-10/lj-1.10-reprice.md`, READ `:1-175`.** TOOK
  Candidate B's definition (`:120-123`), its four rows and their bases
  (`:145-153`), and its own "false anchor" verdict on the 5,047 (`:29`).
- `agents/tasks/LJ-1-167/lj-1.167-report.md`, READ the load-bearing rows: `:207`
  and `:456` (**`closedω` is NOT required under a finite bound; `KFacts` needs
  no fourth parameter**), and `:79-86` (the `StageArith` table).
- **`dev/LESSONS.md`: D-1, P-l, P-i, C-12, C-22, D-10, R-40 read through
  `scripts/rules.py --for recon` and `--for probe`.** **P-l is spent twice:**
  once to refuse `[LJ-1.10]`'s band as a transferred figure, once to refuse
  ARM A's archive credential.
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a coding decision
  or a line count, and I mark the omission rather than imply a survey.

## 10. LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:593-640`, READ VERBATIM.**
  - **What `K(u)` CONTAINS, exactly** (`:600-608`): the union of three sets, the
    first being "the set of finite sequences of members of the set `𝓕 ∪ {vᵢ | i
    ∈ ω} ∪ {x | x ∈ u}`", the second finite sequences of such sequences, the
    third finite sequences of finite subsets. **The formula set `𝓕` does not
    depend on `u`.**
  - **Why his bound is UNIFORM** (`:612-620`): `K(w,u)` is built by `Seq` and
    `Pow` applied to `𝓕 ∪ d ∪ e`, where `d` holds the variables and `e` holds
    the constants from `u`. **`Seq` and `Pow` are finite-bump constructions, so
    the cost above `u` does not depend on any formula's depth.**
  - `D(v,u) = ∃w [K(w,u) ∧ C(w,v,u)]` (`:628-630`), and 2.4's proof is "As in
    2.2 and 2.3. (The details are left as an exercise for the reader.)"
    (`:633`). **Re-confirmed; the line matches `[LJ-1.169]`.**
  - **Does ARM B-prime REPRODUCE that, or approximate it? REPRODUCE, and by a
    different route which I state so the difference is not hidden.** Devlin
    FLATTENS: parameters go into one sequence beside the formula symbols. This
    tree SPLITS: parameters go into a separate finite set beside a
    parameter-free code. **Both make the cost above the carrier independent of
    formula depth, and both use the same two facts — a finite set of stage
    members costs one stage, a pair costs two.** The tree's figure is `sucIter 5
    σ`, MEASURED; Devlin computes no numeral. **The tree's version has one
    advantage Devlin does not need: the nested code is free at `Lset ω`
    (`code∈limit`), so `𝓕` needs no separate treatment.**
- **`dev/literature/devlin-II5.md:240-260`, READ. It answers the fork
  directly**, `:254-256`:

  > the argument does not require them to have any particular shape, only that
  > some bounded description with a bound inside the carrier exists.

  **MEASURED: Devlin's argument does NOT fix the coding shape. It fixes the
  BOUND.** So ARM B's premise — that the shape must change — is not Devlin's
  requirement, and ARM B-prime meets the real requirement with the shape
  unchanged.
- `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s measurement
  that the errata touch no part of II.5.

## 11. RUN LOG, criterion fixed in writing before the first run

**The criterion is in the probe's own header, `ProbeLJ1170A.agda:5-16`, written
before any Agda ran: 10 minutes of wall time per invocation,
`GHCRTS="-A64m -I0 -M8g"`, ONE process, cap NEVER raised. GO at or below 60
in-fence lines for a fixed-iterate bound; NO-GO if the bound needs the formula's
depth.**

| run | file state | exit | wall | resident set |
|---|---|---|---:|---:|
| 1 | all three blocks | **1**, `NotInScope: +` | 1.68 s | 316 MB |
| 2 | `Cubical.Data.Nat` import added | **0** | **9.94 s** | **377 MB** |
| 3 | unchanged, exit code confirmed alone | **0** | not timed | not timed |

**ONE agda process at a time. No heap exhaustion. Cap never raised. The
10-minute criterion was not approached.** Basis: `/usr/bin/time -l`, warm
dependencies, the whole file.

**VERDICT: GO. 37 in-fence lines against a criterion of 60, and the bound is
`sucIter 5 σ`, which mentions neither the formula nor `k`.**

**DD24 is not usefully answered at this size and I say so rather than publish a
ratio that means nothing:** the numerator is import loading.

**P-i's implicit-index repair: applied prophylactically, never tested.** Every
implicit set index at a concrete argument is written out
(`ProbeLJ1170A.agda:104`, `:107-108`, `:147-149`). **No run walled, so this task
gives the repair no measurement.**

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,790 tracked files** |
| `scripts/lint-prose.py --check` on this report | **exit 0** |
| `make check` | **NOT RUN.** The orchestrator runs it |

**`git status --porcelain` at close:** exactly two untracked files,
`agents/tasks/LJ-1-170/ProbeLJ1170A.agda` and
`agents/tasks/LJ-1-170/lj-1.170-report.md`. **Nothing else changed.**

**Prohibitions, answered one by one.** **No master edited**; `git status` shows
exactly two new files, `agents/tasks/LJ-1-170/ProbeLJ1170A.agda` and this
report. `src/Everything.lagda.md` never opened. **I did NOT take either arm.**
**No commit, no push, no `git checkout .`, no `stash`, no `reset`, no `clean`.**
No probe under `src/`. **No `postulate`, no hole, no unsolved meta**, and
`--safe` is on.

## 12. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the two named arms are exhaustive | **MEASURED FALSE.** ARM B-prime changes neither the coding nor the carrier. Section 7 |
| the archive REACHED ARM A's bound at a general carrier | **MEASURED FALSE.** It ASSUMED it, as `SatRelation` (`SatTable:175-178`), and its own prose says so at `:6-8` |
| the archive's `+ω` is load-bearing | **MEASURED FALSE.** `C∈` and `limδ` are unused; `pow∈J` works at ANY limit with zero offset |
| the live tree can re-use the archive's proof | **MEASURED FALSE.** It runs on `Jset-rud`, the rud-basis closure, and `grep -rl Jset-rud src/` is empty |
| the archive gives ARM B a delivered comparable | **MEASURED FALSE.** The retired route carries the SAME coding masters |
| the tree must re-code `⌜_⌝` to get Devlin's bound | **MEASURED FALSE, and this decides the fork.** `ProbeLJ1170A.agda:157-166`, exit 0, `⌜_⌝` untouched |
| Devlin's argument fixes the coding shape | **MEASURED FALSE.** `dev/literature/devlin-II5.md:254-256`: it fixes the BOUND, not the shape |
| the parameter split must be built | **MEASURED FALSE.** `nameOf` is delivered at `src/L/Choice/Name.lagda.md:381`, green, on the AC side |
| `absFo` and `constantsFo` name a tower | **MEASURED FALSE.** Generic in the constant type, `src/FOL/Manipulation/Parameters.lagda.md:105`, `:260-261` |
| the split key's bound depends on the formula's depth | **MEASURED FALSE.** `Lset (sucIter 5 σ)`, uniform in `χ` and `k`. Exit 0 |
| the split key's bound depends on the parameter count | **MEASURED FALSE.** Same statement, `k` universally quantified |
| `[LJ-1.169]`'s growth law is wrong | **MEASURED FALSE.** Re-checked as my BLOCK 2, exit 0. It applies to the CONSTANTS, and a parameter-free code has none |
| `[LJ-1.10]`'s 2.45-5.1k is a measured figure | **MEASURED FALSE.** 2.35-4.9k of the band is survey; 0.1k is probe |
| `[LJ-1.10]`'s 2.45-5.1k prices this question | **MEASURED FALSE, and this is worse than unmeasured.** It prices abstracting the cone over the restriction class. Section 5 |
| ARM A avoids the object-level description | **INFERRED FALSE.** Both arms pay it at `carve∈𝒟ₒ`. I did not build either |
| ARM A's consumer cost is code to write | **MEASURED FALSE.** `boundCloses` is delivered, 4 lines, `StageArith:86-89` |
| ARM A's `closedω` is otherwise needed | **MEASURED FALSE.** `[LJ-1.167]:207`, `:456`: a finite bound needs `succλ` alone |
| `StageArith` was written only for the `+ω` reading | **MEASURED FALSE.** `envCloses` (`:92-96`) is a FIXED `sucIter 3`, which is ARM B-prime's shape |
| `src/L/Choice/` was the load-bearing blind spot last time | **MEASURED FALSE for `[LJ-1.169]`, MEASURED TRUE for this task.** `Name.lagda.md` holds the answer |
| a fourth arm exists | **NOT CLAIMED and NOT REFUTED.** Section 7 states the observation and refuses the trichotomy |
| ARM B would hang the typechecker | **NOT MEASURED. INFERRED from `src/FOL/Coding.lagda.md:26-29`**, which says why the relation exists. I ran no such test |
| the generic two-tower variant is cheaper | **NOT CLAIMED and NOT TESTED.** I did not write it |
| anything walled | **MEASURED FALSE.** Three runs, longest 9.94 s, against a 10-minute criterion |
| I took an arm | **MEASURED FALSE.** No master edited. The fork is the owner's |
