# LJ-1.171 report: the last gate before the build

tier: opus (version `override`). **No master is edited. No commit, no push.**
Every negative is marked **MEASURED** or **INFERRED** (C-36). Written
incrementally (C-22).

## 0. WHAT I FOUND DELIVERED, before what I built

**The search that this phase has paid for four times paid a FIFTH time, and it
changes the ingredient rather than only the count.**

### 0.1 THE FINDING THAT OUTRANKS THE COUNT

**`[LJ-1.170]`'s parameter component cannot be read back, and the tree already
holds the component that can.** MEASURED.

`[LJ-1.170]` wrote the parameter component as
`paramSet σ k g = finSet k (λ i → ⟪ Lset σ ⟫↪ (g i))`
(`agents/tasks/LJ-1-170/ProbeLJ1170A.agda:83-84`).

`finSet n h = sett (Lift (Fin n)) (λ i → h (lower i))`
(`src/L/Axioms/Basic.lagda.md:285-286`). **It keeps NO index.** `finSet-out`
(`:292-294`) returns `∥ Σ[ i ∈ Fin n ] (h i ≡ y) ∥₁`, a TRUNCATED index, and the
set for `n = 2, h = const a` is the same set as for `n = 1, h = const a`.

**The reading direction needs the VECTOR.** `absFo φ` substitutes the parameters
BY POSITION, so `nameOf φ = countFo φ , (absFo φ , constantsFo φ)`
(`src/L/Choice/Name.lagda.md:381`) carries `constantsFo φ` as a **vector**, not
as a set. `AllCodes-out` (`src/L/Coding/CodeSet.lagda.md:449-456`) must return a
formula over the carrier. **From a `finSet` it cannot.**

**This is NOT a second unsourced term. The tree supplies the replacement, with
both directions, and I found it before I priced anything.**

| what | `file:line` | what it gives |
|---|---|---|
| `env g = sett (Lift (Fin n)) (λ li → pr (# (toℕ (lower li))) (g (lower li)))` | `src/L/Coding/Environment.lagda.md:84-86` | **the SEQUENCE. The index is inside the pair** |
| `envIsFinSet : env g ≡ finSet n (λ i → pr (# (toℕ i)) (g i))`, by `refl` | `src/L/Coding/InL.lagda.md:177-179` | **the sequence IS a `finSet` of index pairs, so every `finSet` law applies unchanged** |
| `lookup-spec` | `src/L/Coding/Environment.lagda.md:102-116` | the graph is functional, both directions |
| `envOverAt e d B = svAt e ∧̇ (domAt e d ∧̇ (valuesInAt e B ∧̇ pairsInAt e d B))` | `src/L/Coding/Model.lagda.md:483-485` | **the OBJECT-LEVEL reading of "is an environment over the carrier", with the carrier as a SLOT** |
| `envOver-sv`, `-dom`, `-values`, `-pairs` | `src/L/Coding/Model.lagda.md:487-495` | its four projections |
| `envOverAt-transport` | `src/L/Coding/Model.lagda.md:517-546` | moves the reading between frames, 4 transports |
| `envOver` | `src/L/Coding/EnvSet.lagda.md:232-283` | **the `-in` direction, 48 in-fence lines, DELIVERED GREEN** |
| `module Recover` and `recovers` | `src/L/Coding/EnvSet.lagda.md:315-379` | **the `-out` direction: from the reading at ANY frame, recover `g : Fin n → ⟪ fst B ⟫` and `fst e ≡ fst (envS g)`. 64 in-fence lines, DELIVERED GREEN** |
| `envCloses`, at a FIXED `sucIter 3 δ` | `src/L/Ordinal/StageArith.lagda.md:92-96` | the environment's stage bound was already written down as three iterates |

**`src/L/Coding/` paid this time, not `src/L/Choice/`.** The brief named
`src/L/Choice/` as the site with four payments. **MEASURED: the answer was two
directories away, in `src/L/Coding/EnvSet.lagda.md` and
`src/L/Coding/Model.lagda.md`, and `src/L/Ordinal/StageArith.lagda.md:92-96`
named the resulting stage bound before this wing began.** `[LJ-1.170]` READ that
same line and quoted its `sucIter 3` as evidence for its own arm
(`agents/tasks/LJ-1-170/lj-1.170-report.md:57-60`) **without noticing that the
line prices an ENVIRONMENT, which is the object it did not use.**

### 0.2 So the reading is delivered machinery, not new mathematics

**The conjunct I had to write is a WIRING of delivered parts.** Nothing in it
proves a new fact about environments, codes or stages.

## 1. VERDICT: GO. 56 in-fence lines against a stop-line of 60

**The stop-line is `[LJ-1.170]`'s 60 and I did not move it.** It is written in
the probe's own header, `agents/tasks/LJ-1-171/ProbeLJ1171A.agda:10-14`, before
the first `agda` ran.

| probe | what it measures | in-fence lines | exit | wall |
|---|---|---:|---:|---:|
| `ProbeLJ1171A.agda` BLOCK 1 | **the object-level reading of the three-component key, BOTH directions** | **56** | **0** | **2.35 s** |
| `ProbeLJ1171B.agda`, new material | the bound re-measured with the SEQUENCE component | 41 | **0** | **2.21 s** |

**The delivered comparable is 22 in-fence lines**
(`src/L/Coding/CodeSet.lagda.md:185-208`, `arityNumAtL` with `-out` and `-in`).
**A three-component reading costs 2.5 times a two-component one.** MEASURED.

### 1.1 What was written, in full

```agda
paramSetAtL b c = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
  ( prAtL (lift5 c) (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
  ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
    ∧̇ ( (var zero ∈̇ con ωʟ)
      ∧̇ envOverAt (suc zero) zero (lift5 b) ) ) ) ))))
```

`ProbeLJ1171A.agda:96-101`. **Five binders where `arityNumAtL` has two:** the
arity, the payload, the code, the parameter environment, and the environment's
length. **The length is pinned in `ωʟ` by exactly the device `arityNumAtL` uses
for the arity**, which is why that half costs nothing new.

**The carrier is a SLOT, not a constant** (`lift5 b`).
`src/L/Coding/CodeSet.lagda.md:32-44` states why that is forced: the internal
hierarchy binds its stage, so a predicate that names its carrier as a constant
cannot be spoken under that binder at all. **`envOverAt` already takes its
carrier as a slot, so the delivered reading fits the constraint with no
adaptation.** MEASURED.

### 1.2 The two directions, and what they return

```agda
paramSetAtL-out : ∀ {n} (b c : Fin n) (γ : S ^ n)
                → fst (lookup b γ) ≡ fst B
                → ⟨ γ ⊨ paramSetAtL b c ⟩ → ∥ Split c γ ∥₁

Split c γ = Σ[ ar ∈ S ] Σ[ cd ∈ S ] Σ[ k ∈ ℕ ] Σ[ g ∈ EnvS.Ix B k ]
  (fst (lookup c γ) ≡ pr (fst ar) (pr (fst cd) (fst (EnvS.envS B g))))
```

`ProbeLJ1171A.agda:104-110`. **The `-out` returns the parameter VECTOR `g`,
which is the thing `finSet` could not give and which `AllCodes-out` consumes.**

## 2. THE TWO DIRECTIONS, PRICED SEPARATELY

**`-out` is dearer, and by 2 lines only.** MEASURED.

| part | `ProbeLJ1171A.agda` lines | in-fence lines |
|---|---|---:|
| `lift5`, the index shift | `:93-94` | 2 |
| **the conjunct itself** | `:96-101` | **6** |
| the module header and the `-out` target type | `:103-106` | 4 |
| **`paramSetAtL-out`** | `:108-130` | **23** |
| **`paramSetAtL-in`** | `:132-152` | **21** |
| **total** | | **56** |

**Why the gap is only 2 lines, and it is NOT the pattern this chain measured.**
`[LJ-1.162]` measured 59 of its 125 lines as two nested extensionality frames,
because an extensionality is consumed with both directions plus a membership
fact. **MEASURED: this conjunct pays no extensionality at all.** The one
extensionality in the chain is `Recover.recovers`
(`src/L/Coding/EnvSet.lagda.md:378-379`), and it is DELIVERED and CALLED, not
written. **The gate's cost is five nested `PT.rec` layers, one per binder, and
those are symmetric between the two directions.**

**So the `-in`/`-out` asymmetry that drove `[LJ-1.162]` does not appear here,
and the reason is that the delivered `EnvSet` already paid the extensionality.**
INFERRED that this generalizes; MEASURED only at this site (P-l).

## 3. IS THE CHAIN NOW MEASURED END TO END? YES, and one figure moved

**MEASURED.** Every term in the supply chain now has a measurement, and the one
figure that changed is `[LJ-1.170]`'s stage constant.

| piece | figure | state after this task |
|---|---:|---|
| the assembly, `levelIn` and `cover` | 17 | MEASURED GREEN, `[LJ-1.165]` |
| `K(u)`'s closure layer | 88 | MEASURED GREEN, `[LJ-1.166]` |
| pairing at an arbitrary limit | 35 | MEASURED GREEN, `[LJ-1.166]` |
| the satisfaction layer | about 270 | nine delivered comparables, `[LJ-1.168]` |
| `powIter` by the re-key arm | 0.3 to 0.6k | 37 lines MEASURED GREEN, `[LJ-1.170]` |
| **the key's bound, with the SEQUENCE component** | **`Lset (sucIter 7 σ)`** | **41 lines MEASURED GREEN, this task, `ProbeLJ1171B.agda`** |
| **the object-level reading of the key** | **56** | **MEASURED GREEN, this task, GO at 60** |

### 3.1 The one figure that moved, and its size

**`[LJ-1.170]` measured `Lset (sucIter 5 σ)`. With the SEQUENCE component the
bound is `Lset (sucIter 7 σ)`.** MEASURED, `ProbeLJ1171B.agda:120-129`, exit 0.

```agda
splitKeyE σ n k χ g = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv σ k g))

splitKeyE∈ : ... → ⟨ splitKeyE σ n k χ g ∈ˢ Lset (sucIter 7 σ) ⟩
```

**Two stages, and they are the index pairs: `pr (# i) (g i)` costs two above the
carrier, then the span costs one, so the parameter component is at
`sucIter 3 σ` where a `finSet` of bare members was at `sucV σ`.** MEASURED,
`ProbeLJ1171B.agda:85-107`.

**`sucIter 7` is still a FIXED finite iterate, uniform in the formula and in the
parameter count**, so `[LJ-1.170]`'s load-bearing property survives the
correction. `deliveredSplitE∈` (`ProbeLJ1171B.agda:139-142`) states it for EVERY
formula over the carrier, with `⌜_⌝` untouched. Exit 0.

**And `sucIter 7` is still below `envCloses`' consumer form:**
`src/L/Ordinal/StageArith.lagda.md:92-96` lifts a `sucIter 3` bound; the same
two-line `Lset-mono` composition lifts a `sucIter 7` one. **INFERRED, one line of
arithmetic, NOT measured: I did not write the consumer.**

## 4. DD4: the reading KEEPS the property, and the delta is ZERO lines

**MEASURED, by token count, the caliber `[LJ-1.170]` used.**

Tokens counted: `Lset`, `𝒟ₒ`, `+ω`, `sucIter`, `sucV`.

| block | in-fence lines | lines naming a stage |
|---|---:|---:|
| **`ProbeLJ1171A.agda` BLOCK 1, the whole reading** | 56 | **0** |
| **the delivered `arityNumAtL` it extends** | 22 | **0** |

**The object-level reading names NO stage and NO tower operator. Neither does
the conjunct it is modelled on.** MEASURED.

**The honest qualification, and I state it rather than claim more.** The reading
is written over `hPropStructure 𝒮ʟ`, so it names the CLASS `L` through `𝒮ʟ`,
`ωʟ` and `numeralL` — **exactly as the delivered `arityNumAtL` does.** The
reading is therefore neither more nor less tower-blind than the conjunct it sits
beside. **The DD4 delta of the re-key arm's reading is ZERO lines.**

**And it adds NO module to the J tower's re-instantiation set.** MEASURED:
`L.Coding.EnvSet` is already imported by `src/L/Coding/Sat.lagda.md`,
`src/L/Coding/Sound.lagda.md`, `src/L/Coding/Unique.lagda.md`,
`src/L/Coding/Bridge.lagda.md`, `src/L/Choice/Adequate.lagda.md` and
`src/L/Condensation/TwelveAgree.lagda.md`. **The re-key arm's reading consumes a
module the satisfaction chain already consumes.**

**So `[LJ-1.170]`'s DD4 answer stands, and this task adds a second half to it.**
`[LJ-1.170]` measured that the arm's two INGREDIENTS (`absFo`, `constantsFo`)
name no tower, so the J tower gets the SPLIT free. **This task measures that the
arm's READING names no stage either, and that it re-uses a module the J tower
must re-instantiate in any case.** The arm's DD4 cost over the delivered
two-component reading is **34 lines** (56 minus 22), **and every one of them is
as tower-blind as the 22 it replaces.**

## 5. THE ONE TERM I DID NOT INSTANTIATE, and I name it rather than imply a survey

**The conjunct I measured is the PARAMETER half of the reading. The CODE half is
the delivered `hasWitness` chain, re-read at the EMPTY alphabet, and I did not
instantiate it.** INFERRED, on a MEASURED genericity.

Under the re-key the code component is `⌜ embed χ ⌝` for a parameter-free
`χ : Formula (⊥* {ℓ}) (n + k)`, so `Decode.recover` must run at `K = ⊥*` where
today it runs at `⟪ fst A ⟫`.

**MEASURED: every module in that chain is already generic in the alphabet.**

| module | the parameter | `file:line` |
|---|---|---|
| `L.Coding.Recover` | `module Decode {K : Type ℓ} (f : K → V ℓ)` | `src/L/Coding/Recover.lagda.md:146` |
| `L.Coding.InL` | `module _ {K : Type ℓ} (f) (h)`, four times | `src/L/Coding/InL.lagda.md:132`, `:250`, `:397`, `:486` |
| `L.Coding.Closed` | same | `src/L/Coding/Closed.lagda.md:73` |
| `L.Coding.Shape` | same | `src/L/Coding/Shape.lagda.md:403`, `:464` |

**And the tree already instantiates the empty alphabet on the AC side:**
`emptySat` and `sameReading` (`src/L/Choice/Name.lagda.md:396-403`) are exactly
the `Empty.rec*` bookkeeping that instantiation costs, and that chapter's own
prose calls it "the only bookkeeping the identification costs" (`:390-392`).

**So this is a re-instantiation, not new mathematics. I did NOT write it, so I
publish no line figure for it** (DD8, C-36).

## 6. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Coding/CodeSet.lagda.md`, SEARCHED and
  the load-bearing blocks READ.** The brief asks whether the retired route gave
  its code set an object-level reading of a parameter component, **and at what
  size**. **MEASURED: it did NOT.** `grep -cE "constantsFo|absFo|paramSet|
  paramEnv|envOverAt"` over that file returns **0**. Its readers are
  `keyArityAtL` (`:143-160`) and `arityNumAtL` (`:193-216`), and its predicate is
  `isCodeAny = arityNumAtL zero ∧̇ hasWitness A` with `hasWitnessAt` at `:250-255`
  — **the SAME two-component reading the live tree carries.** **Its
  `arityNumAtL` block is 22 in-fence lines, the same 22 as the live one.**
  **TAKEN: the confirmation that the archive offers NO comparable for a
  parameter conjunct, so the 56 is the first measurement of that term anywhere
  in this repository.** No claim taken; `[LJ-1.11]` ruled that route's
  condensation target classically FALSE.
- **`archive/src/2026-08-09-rud-route/L/Coding/EnvSet.lagda.md` and
  `.../L/Coding/Model.lagda.md`, READ at the load-bearing lines.** MEASURED:
  `envOverAt` sits at `Model:483-485` and `envOverAt-transport` at `:517`, the
  SAME line numbers as the live tree; `EnvSet` carries `envOver` (`:226`) and
  `Recover` (`:311`). **The machinery this task leans on predates the route
  change and survived it unchanged in shape** (155 diff lines against the live
  file, none of them in the four conjuncts). **TAKEN: the SHAPE, and the
  robustness fact.**
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md`, READ the
  declarations.** MEASURED: it is the `Def`/`defSet` chapter
  (`:107`, `:110`, `:114`, `:137`, `:145`, `:282`) and it reads a formula over
  `⟪ A ⟫` at the META level. **It has no object-level parameter reading either.**
  **NOTHING TAKEN beyond that negative.**
- **`agents/tasks/LJ-1-170/lj-1.170-report.md`, READ WHOLE, and
  `agents/tasks/LJ-1-170/ProbeLJ1170A.agda`, READ WHOLE.** TOOK the obligation
  (`:318`), the stop-line, the DD4 measurement (`:361-366`), the `StageArith`
  reading (`:57-60`) and BLOCK 1 (`ProbeLJ1170A.agda:83-121`). **THE
  CORRECTION: its `paramSet` is a `finSet` and cannot be read back. Section
  0.1.** Its BOUND claim survives at `sucIter 7` instead of `sucIter 5`.
- **`dev/LESSONS.md`: D-1, P-l, P-i, C-12, C-22, D-10, R-40 through
  `.venv/bin/python scripts/rules.py --for probe`, and C-38, C-36, C-35, C-39,
  C-40, P-l READ WHOLE.**
  - **P-l is spent once, and it is why probe B exists.** `[LJ-1.170]`'s bound
    was measured with a different ingredient. **A measured cure does not
    transfer by analogy; I re-measured it at its own site** rather than assert
    that `env` behaves like `finSet`.
  - **C-35 binds this return.** `paramSetAtL` has **NO CONSUMER**. It is
    STAGED, not delivered, and its statements have never been asked to mean
    anything by another module. The acceptance test is the build.
  - **C-38 binds the reading.** `paramSetAtL-out` returns the parameter vector,
    so the parameter half is SUPPLIED, not restated. **The code half is
    restated until something instantiates `Decode` at `⊥*`.** Section 5.
  - **C-39 is why I did not stop at the `finSet` refutation.** The brief's
    abort criterion "the reading needs a fact nothing supplies: STOP AND SAY
    SO" has a shape a blocked search can wear. **I counted the candidates
    first, found the tree supplies the fact, and priced the term the brief
    asked for.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on an object-level
  reading or a line count, and I mark the omission rather than imply a survey.

## 7. LITERATURE USED (DD18)

**`_build/literature/dev2.txt:593-640`, READ VERBATIM.**

**`K(u)` is the union of three sets** (`:600-608`): finite sequences of members
of `𝓕 ∪ {vᵢ | i ∈ ω} ∪ {x | x ∈ u}`; finite sequences of such sequences; and
finite sequences of finite subsets of `{vᵢ | i ∈ ω}`. **`K(w,u)` is written out
at `:610-620`** with six bound sets `a, b, c, d, e, f`.

**The brief asks which of my three components corresponds to which, and whether
any has no analogue. Here is the table, and one row is a NEGATIVE.**

| my component | Devlin's | evidence |
|---|---|---|
| the arity numeral, pinned in `ωʟ` | **`d`**, the variable set: `(∀z ∈ d) Vbl(z) ∧ (∀i ∈ ω)(vᵢ ∈ d)` | `dev2.txt:612-613`. Both say how many variables are in play, and both bound the answer by `ω` |
| the code of the parameter-free formula | **`𝓕` together with `Seq(a, 𝓕 ∪ d ∪ e)`** | `:614`, `:600-602`. **Devlin FLATTENS the formula into a sequence over a fixed symbol set. The tree does NOT: it keeps the nested code and gets the same bound from `code∈limit` (`src/L/Choice/Name.lagda.md:153`), which puts a parameter-free code in `Lset ω` whatever its depth** |
| **the parameter environment** | **`e`**, the constants: `(∀z ∈ e) Const(z,u) ∧ (∀z ∈ u)(z ∈ e)` | `:613`. **AND THIS IS THE CONFIRMATION OF SECTION 0.1: Devlin's `e` is an unordered SET, and the ORDER arrives only through `Seq(a, 𝓕 ∪ d ∪ e)`. He needs a sequence for exactly the reason a `finSet` fails here** |
| **no analogue** | **the third union member**, finite sequences of finite subsets of variables, `Pow(f,d) ∧ Seq(c,f)` | `:606-608`, `:616`. **MEASURED: this tree needs none.** Devlin's clause exists to bound the quantifiers inside `Fr`, the free-variable computation. **This tree never computes free variables at the object level: `absFo` and `constantsFo` are META-level functions (`src/FOL/Manipulation/Parameters.lagda.md:105`, `:260-261`) and the reading consumes their OUTPUT** |

**So the correspondence is three-to-three with one Devlin clause unused, and the
one place the two developments differ is where the ORDER of the parameters
lives: Devlin puts it in the surrounding `Seq`, the tree puts it inside the
component, as `env`.** MEASURED both sides.

`dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s measurement
that the errata touch no part of II.5.

## 8. RUN LOG, criterion fixed in writing before the first run

**The criterion is in each probe's own header, written before any `agda` ran:**
`ProbeLJ1171A.agda:6-16` and `ProbeLJ1171B.agda:13-22`. **10 minutes of wall
time per invocation, `GHCRTS="-A64m -I0 -M8g"`, ONE process, cap NEVER raised.
GO at or below 60 in-fence lines.**

| run | file | exit | wall | resident set | what |
|---|---|---:|---:|---:|---|
| 1 | A | 1 | 0.80 s | 107 MB | `ParseError`, one surplus bracket |
| 2 | A | 1 | 0.06 s | 107 MB | `ParseError`, a lambda closed with `)` |
| 3 | A | 1 | 1.46 s | 348 MB | `UnequalTerms`: `ω-specL`'s payload is an equation on `fst x`, not on `x` |
| 4 | **A** | **0** | **2.35 s** | **393 MB** | **GREEN** |
| 5 | A | 0 | not timed | not timed | exit code confirmed alone |
| 6 | **B** | **0** | **2.21 s** | **356 MB** | **GREEN on the first run** |
| 7 | B | 0 | not timed | not timed | exit code confirmed alone |

**ONE agda process at a time. No heap exhaustion. Cap never raised. The
10-minute criterion was never approached.** Basis: `/usr/bin/time -l`, warm
dependencies, the whole file each time.

**DD24 is not usefully answered at this size, and I say so rather than publish a
ratio that means nothing:** the numerator is import loading. Same finding as
`[LJ-1.170]`.

**P-i's implicit-index repair: applied prophylactically, never tested.** Every
implicit set index at a concrete argument is written out
(`ProbeLJ1171A.agda:105-106`, `:151`; `ProbeLJ1171B.agda:65-67`, `:97-107`).
**No run walled, so this task gives the repair no measurement.**

| checker | result |
|---|---|
| `.venv/bin/python scripts/lint-agda.py --check` | **exit 0** |
| `.venv/bin/python scripts/check-probes.py --check` | **clean, 1,793 tracked files, no probe outside `agents/tasks/`** |
| `.venv/bin/python scripts/lint-prose.py --check` on this report | **exit 0** |
| `.venv/bin/python scripts/ledger.py --brief` | standing **28,940 lines over 85 masters**. **The ledger counts `src/*.lagda.md` only, so a probe never enters it**; the probe figures above use the non-blank, non-comment convention |
| `make check` | **NOT RUN.** The orchestrator runs it |

**`git status --porcelain` at close:** exactly three untracked files,
`agents/tasks/LJ-1-171/ProbeLJ1171A.agda`,
`agents/tasks/LJ-1-171/ProbeLJ1171B.agda` and this report. **Nothing else
changed.**

**Prohibitions, answered one by one.** **No master edited.** `src/Everything.lagda.md`
never opened. The three `*Agree` masters, `src/L/Coding/Graph.lagda.md` and
`[LJ-1.164]`'s move: never touched. **I did NOT build the arm.** No probe under
`src/`. `[LJ-1.170]`'s probe was COPIED, never edited: `git status` shows it
unmodified. **No commit, no push, no `git checkout .`, no `stash`, no `reset`,
no `clean`.** **No `postulate`, no hole, no unsolved meta**, and `--safe` is on
in both probes.

## 9. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the reading needs a fact nothing supplies** | **MEASURED FALSE, and this was the criterion that outranked the count.** `envOverAt`, `envOver` and `Recover` supply it, delivered and green |
| `[LJ-1.170]`'s `finSet` parameter component can be read back | **MEASURED FALSE.** `finSet` keeps no index (`src/L/Axioms/Basic.lagda.md:285-294`); `finSet-out` returns a TRUNCATED index; the sets for `n = 2` and `n = 1` at a constant family are equal |
| `[LJ-1.170]`'s BOUND is wrong | **MEASURED FALSE.** It is right for the object it measured. With the sequence the bound is `sucIter 7 σ`, still a FIXED iterate uniform in `χ` and `k`. `ProbeLJ1171B.agda`, exit 0 |
| the swap costs the arm its uniformity | **MEASURED FALSE.** `deliveredSplitE∈` (`ProbeLJ1171B.agda:139-142`) holds for EVERY formula over the carrier, exit 0 |
| the object-level reading exceeds 60 lines | **MEASURED FALSE. 56, and the stop-line was not moved** |
| the `-in` half is the dearer one | **MEASURED FALSE. `-out` is dearer, 23 against 21** |
| the two directions are where the cost sits, as `[LJ-1.162]` measured | **MEASURED FALSE at THIS site, and I give the reason.** `[LJ-1.162]`'s 59 lines were two nested extensionality frames; **this conjunct pays no extensionality, because `Recover.recovers` is delivered and CALLED** |
| the object-level reading breaks `[LJ-1.170]`'s tower-blindness | **MEASURED FALSE.** Zero stage tokens in 56 lines, and zero in the delivered 22 it extends. **The DD4 delta is ZERO lines** |
| the reading adds a module to the J tower's re-instantiation set | **MEASURED FALSE.** `L.Coding.EnvSet` is already imported by six live masters |
| the archive gives a comparable for a parameter conjunct | **MEASURED FALSE.** Zero hits in `archive/.../L/Coding/CodeSet.lagda.md`; its reading is the SAME two-component one at the SAME 22 lines |
| the archive's `EnvSet` machinery differs from the live one in the four conjuncts | **MEASURED FALSE.** Same names, same lines; 155 diff lines, none in the conjuncts |
| Devlin's parameter component is an unordered set | **MEASURED FALSE, and it confirms section 0.1.** His `e` is a set, but the ORDER arrives through `Seq(a, 𝓕 ∪ d ∪ e)` (`dev2.txt:613-614`) |
| every Devlin clause has an analogue here | **MEASURED FALSE.** The third union member, `Pow(f,d) ∧ Seq(c,f)`, has none: this tree computes free variables at the META level |
| the code half of the reading is measured | **NOT MEASURED. INFERRED**, on the MEASURED genericity of `Decode`, `InL`, `Closed` and `Shape` in the alphabet. **Section 5. I publish no figure for it** |
| `paramSetAtL` is delivered | **MEASURED FALSE. It is STAGED** (C-35). It has no consumer and its first consumer is its first real audit |
| anything walled | **MEASURED FALSE.** Seven runs, longest 2.35 s, against a 10-minute criterion |
| I built the arm | **MEASURED FALSE.** No master edited. `git status` shows three new files, all in `agents/tasks/LJ-1-171/` |

## 10. WHAT I RECOMMEND THE BRIEF FOR THE BUILD SAYS

**One sentence.** **Fund the build with the parameter component written as
`env`, never as `finSet`, cite `ProbeLJ1171A.agda` for the reading and
`ProbeLJ1171B.agda` for the bound, and put ONE line in the brief telling the
builder to instantiate `Decode` at `⊥*` and report the cost, because that is
the only term in the chain still carrying an inference rather than a
measurement.**
