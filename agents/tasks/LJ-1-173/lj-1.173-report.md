# LJ-1.173 report: restrict `envSetK` to a numeral arity, gated first

**STATUS: COMPLETE.** Written incrementally from a skeleton (C-22).

## 1. VERDICT

**NO-GO. 45 lines, and the adequacy that joins the two halves is NOT among
them.** The criterion was 40. **I did not apply the cure. `src/` is
byte-identical to the coordinator's commit.**

**FIRST, because the brief asks for it first: the numeral case is NOT false.**
**The level substitution does not fail outright.** For a numeral arity the
statement is TRUE, and I give the rank argument in section 3.1. **So the supply
does not need `[LJ-1.168]`'s fourth `HullStage` hypothesis on the strength of
this measurement**, and I did not reach for it.

**What failed is the PRICE, and the shape of the failure is the same shape
`[LJ-1.172]` closed on.** The gate has two halves:

| half | route | result | lines |
|---|---|---|---:|
| the SUBSET half | `paramEnv∈`, `src/L/Coding/Key.lagda.md:71-81` | **GREEN**, exactly as `[LJ-1.172]` measured | **17** |
| the MEMBERSHIP half | `carve∈𝒟ₒ`, `src/L/Axioms/Separation.lagda.md:197-199` | **GREEN** | **28** |
| **the JOIN** | the carved set IS `envSet B n` | **NOT WRITTEN** | **0 of about 120** |

**Both halves closed. They do not join.** `paramEnv∈` gives a CONTAINMENT,
`carve∈𝒟ₒ` gives a MEMBERSHIP of a DIFFERENT set, and the sentence between them
is the adequacy of a bounded description against `envSet B n`. **The gate is
spent at 45 lines before that sentence starts.**

`agents/tasks/LJ-1-173/ProbeLJ1173A.agda`, exit 0, 3 s, no hole, no
`postulate`, no unsolved meta.

## 2. THE GATE, criterion fixed BEFORE any number

**Written before the first agda run and before any line count existed (D-1).**

### 2.1 The one declaration

The probe declares ONE fact, and nothing else is a deliverable:

```agda
envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
               → ⟨ fst B ∈ Lset σ ⟩
               → ⟨ fst (envSet B n) ∈ Lset (sucIter k σ) ⟩
```

`k` is a FIXED natural, the same for every `n`. That is the brief's
"uniformly in `n`".

**One notation correction, and it moves nothing.** I first wrote the third
hypothesis as `ω ∈ Lset σ`. It is `ω ∈ σ`, ORDINAL membership, because that is
what `paramEnv∈` takes (`src/L/Coding/Key.lagda.md:71-73`). **The criterion,
the 40 and the wall clock are unchanged.**

### 2.2 The criterion

| outcome | condition |
|---|---|
| **GO** | the declaration typechecks, with no `postulate`, no hole and no unsolved meta, at **40 or fewer** non-blank, non-comment lines of Agda, module header and imports excluded |
| **NO-GO** | it typechecks above 40 lines, or it cannot be closed from delivered material. Report the figure and STOP |
| **STOP FIRST** | the numeral case is FALSE. Say it before anything else |

**Wall clock, fixed here:** ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap
never raised. **20 minutes per invocation.** A run past 20 minutes is a wall,
and the step stops.

**I do not move this criterion after I see a number.**

## 3. WHAT THE 45 LINES MEASURED, half by half

`agents/tasks/LJ-1-173/ProbeLJ1173A.agda`. One agda process. Exit 0.

### 3.1 The numeral case is TRUE, and I say it first because the brief asks

**INFERRED, and I mark it because I built no Agda counterexample and no Agda
proof of it (C-36).** It is rank accounting and nothing more.

Let `lam` be `HullStage`'s successor-closed limit and let `fst B ∈ Lset lam`.
Levels are cumulative, so `fst B ∈ Lset σ` for some `σ ∈ lam`. Then:

1. **Every member of `envSet B n` lies in `Lset (sucIter 3 σ)`.** This half is
   **MEASURED**, in Agda, this task, at `ProbeLJ1173A.agda:85-104`. It is
   `paramEnv∈`, and the 3 does not depend on `n`.
2. `envSet B n` is a definable subset of `Lset (sucIter 3 σ)`, with parameters
   `fst B` and `# n`, both in that level.
3. So `envSet B n ∈ Lset (sucIter 4 σ)`, and `sucIter 4 σ ∈ lam` because `lam`
   is successor-closed.

**So the numeral restriction is sound and the level substitution survives it.**
**The general arity is what a level cannot carry**, because `envSetGen B ar` at
an arbitrary `ar` is the FULL constructible function space, and step 2 fails for
it at every fixed iterate. `[LJ-1.172]` section 15.3 is confirmed, not
corrected.

**Uniformity, stated exactly.** Step 1 is uniform in `n`. Steps 2 and 3 are per
`n` only in the parameter `# n`, and the iterate 4 is the same for every `n`.
**So the bound is uniform in `n`.**

### 3.2 The SUBSET half: GREEN, 17 lines

`ProbeLJ1173A.agda:85-104`. Two declarations, both green:

- `memberIn`: one environment over `B` of numeral length `n` lands at
  `Lset (sucIter 3 σ)`, through `paramEnv∈` (`src/L/Coding/Key.lagda.md:71-81`)
  and the level's transitivity.
- `setSub`: therefore the whole set is INSIDE that level, through `envSet-out`
  (`src/L/Coding/EnvSet.lagda.md:385-394`).

**`[LJ-1.172]`'s measurement is confirmed in Agda, at its own site.**

### 3.3 The MEMBERSHIP half: GREEN, 28 lines, and it is about a DIFFERENT set

`ProbeLJ1173A.agda:116-152`. **A subset of a level is a MEMBER of the next
level only when it is DEFINABLE there.** The tree's only stage-controlled
carve is `AtStage.carve` (`src/L/Axioms/Separation.lagda.md:193-199`), and
**`carveSat` takes a `Δ₀ φ` as a real argument**
(`src/L/Axioms/Separation.lagda.md:163-168`).

**MEASURED: the delivered description is NOT Δ₀.** Four reads, no inference:

| formula | `file:line` | the unbounded quantifier |
|---|---|---|
| `svAt f` | `src/L/Coding/Model.lagda.md:210-211` | `∀̇ (∀̇ (∀̇ ...))` |
| `inDomAt f x` | `src/L/Coding/Model.lagda.md:269-270` | `∃̇ ...` |
| `domAt f d` | `src/L/Coding/Model.lagda.md:278-280` | `∀̇ ...` |
| `envFo n`, `envFoGen` | `src/L/Coding/EnvSet.lagda.md:176-180`, `:450-454` | `∃̇ (∃̇ ...)` |

`envOverAt` is their conjunction (`src/L/Coding/Model.lagda.md:483-485`), and
`envSetAt` wraps it in `extAt`, itself a `∀̇` (`:1149-1150`). **So no delivered
formula about the environment set can be carved at a controlled stage.**

So the probe WRITES a bounded one, `envFoB`, with every quantifier bounded by
`con d`, by `con B` or by the carved variable itself. It closes:

- `Δ₀-envFoB`, through the delivered `Δ₀-appAt` and `Δ₀-prAtL`
  (`src/L/Condensation.lagda.md:94-95`, `:88-89`);
- `bddEnvFoB`, the constant certificate;
- `carved∈ : carved ∈ Lset (sucV α)`, through `carve∈𝒟ₒ`
  (`src/L/Axioms/Separation.lagda.md:197-199`) and `Lset-suc`.

**Nothing in those 28 lines says `carved` is `envSet B n`.**

### 3.4 THE JOIN, and it is where the gate is spent

**`paramEnv∈` gives a CONTAINMENT. `carve∈𝒟ₒ` gives a MEMBERSHIP of a
DIFFERENT set. The sentence joining them is the adequacy**

```
    (x : S) → ⟨ fst x ∈ Lset α ⟩ → ⟨ (x ∷ []) ⊨ envFoB ⟩ ⟺ ⟨ x ∈ˢ envSet B n ⟩
```

**and it is NOT written.** The gate's 40 lines are already spent at 45 before
it starts.

**Its price, ONE number naming its basis (DD8): about 120 lines, anchored on
delivered comparables I counted at their own sites.**

| what the adequacy needs | new? | comparable, and I COUNTED it | lines |
|---|---|---|---:|
| bounded `envFoB` to unbounded `envOverAt` | NEW | `envOver`, the same four conjuncts, `src/L/Coding/EnvSet.lagda.md:232-283` | **47** |
| unbounded `envOverAt` back to bounded `envFoB` | NEW, and it is only restriction | half of the same | about 20 |
| `envOverAt` to `x ∈ˢ envSet B n`, both ways | **DELIVERED** | `Recover` at `src/L/Coding/EnvSet.lagda.md:315-381` (**57**, reusable) and `envSetIn` at `:282-283` | about 10 of plumbing |
| the carve identification by `extensionalV` | NEW | `separateAt`'s `spec`, `src/L/Axioms/Separation.lagda.md:283-330` | **45** |
| **the adequacy** | | | **about 120** |

**Basis: three delivered blocks, each counted by me at its own `file:line`, in
the masters the work would sit in. It is a SURVEY, not a probe measurement, and
it is weaker for that (P-l).** **Total about 165 against a gate of 40.**

## 4. THE JOIN THE CURE ITSELF NEEDS: step 6 DOES get what it consumes

**The gate failed, so I did not apply the cure. This section answers the
brief's other question, and the answer is favourable to the cure.**

**What step 6 consumes `envSetK` for.** MEASURED from the record: five fields
conclude that the environment SET lies in `K` from a satisfaction —
`envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin`
(`src/L/Condensation/TwelveAgree.lagda.md:183-202`). `[LJ-1.168]`'s L4 and L8
consume it again (`agents/tasks/LJ-1-168/lj-1.168-report.md:341-348`).

**The objection to the cure, stated at its strongest.** Every one of those
fields quantifies over a BARE `ar : S`. Example, `envK-mem`
(`src/L/Condensation/TwelveAgree.lagda.md:183-187`): the telescope is
`(yc b a ar c E : S)` and nothing in it pins `ar` to a numeral. **So a
numeral-restricted `envSetK` looks unable to supply them.**

**MEASURED FALSE, and the joining sentence is three delivered facts.** I show
it at the JOIN and not at the two ends:

| the step | `file:line` | what it gives |
|---|---|---|
| the site's code lies in the code slot, and its shape is a pair with the arity first | `src/L/Condensation/TwelveAgree.lagda.md:161-168` (`codesK`) | `fst c ≡ pr (fst ar) (pr (# k) ...)` |
| **the code set's FIRST conjunct is that the arity is a numeral** | `src/L/Coding/CodeSet.lagda.md:247-248` (`isCodeAny A = arityNumAtL zero ∧̇ hasWitness A`) | every member has a numeral arity |
| and the tree already carries the reader | `src/L/Coding/CodeSet.lagda.md:189-197` (`arityNumAtL-out`) | `∥ Σ m z. fst c ≡ pr (# m) (fst z) ∥₁` |
| and the pair is injective | `src/V/Coding.lagda.md:178` (`pr-inj`) | `fst ar ≡ # m` |

**So `ar` IS a numeral at every site that consumes `envSetK`, and the tree
delivers all four steps.** **The restricted field is not a weakening into
something true because it says nothing: it says exactly what the consumers can
use.**

**CLASSIFICATION, and I keep it honest.** The four parts are **MEASURED**, each
at its `file:line`. **The assembly into Agda is INFERRED: I did not write it,
because the gate failed and the brief says stop.** **The one step I did not
check is whether the `envK-*` sites reach `codesK` with the same `c`**, and I
mark that rather than assume it.

## 5. CONSUMER VERDICTS (C-40)

**I edited no master, so there is nothing for C-40 to re-typecheck.**
`TwelveAgree` and its consumers are untouched, and I state that rather than
report a green run I did not need.

| item | verdict |
|---|---|
| `src/L/Condensation/TwelveAgree.lagda.md` | **NOT EDITED.** The gate failed |
| `src/L/Coding/Key.lagda.md` | **NOT EDITED** |
| every other file under `src/` | **NOT EDITED** |
| `src/Everything.lagda.md` | **NEVER OPENED** |
| new modules for the coordinator to wire | **NONE** |

## 6. CHECKER COUNTS

| checker | result |
|---|---|
| `agda agents/tasks/LJ-1-173/ProbeLJ1173A.agda` | **exit 0**, 3 s, `GHCRTS="-A64m -I0 -M8g"`, ONE process |
| `postulate`, hole, unsolved meta in the probe | **all three ABSENT.** Agda printed no warning |
| `.venv/bin/python scripts/lint-prose.py --check` on this report | **exit 0** |
| `.venv/bin/python scripts/lint-agda.py --check` | **exit 0** |
| `.venv/bin/python scripts/check-unbound-hyp.py` | **2**, unchanged. `src/L/Reflect.lagda.md:365` and `src/L/StageCardinal.lagda.md:281` |
| `.venv/bin/python scripts/check-probes.py` | **clean**, 1802 tracked files, no probe outside `agents/tasks/` |
| `make check` | **NOT RUN.** The brief reserves it for the coordinator |

`.venv/bin/python scripts/ledger.py --brief` reports standing 29,357 lines over
88 masters. **The probe does not move it: `ledger.py` scans `src/*.lagda.md`
only, so `agents/` is outside it by construction.** I counted the probe by the
ledger's own caliber, non-blank lines minus comments.

## 7. DD4

**MEASURED over the probe's 45 body lines: 32 name NO L-tower token, 13 do.**
The tokens counted as L-tower are `Lset`, `𝒟ₒ`, `isL`, `𝒮ʟ`, `LsetS` and the
`L.` module prefix.

**Where the 13 sit, and it is the useful half of the answer.** Twelve of them
are in BLOCK 1, which is `Lset`-shaped throughout because `paramEnv∈` is
delivered at `Lset`. **But `paramEnv∈` itself is NOT L-specific**: it lives in
`KeyOver` (`src/L/Coding/Key.lagda.md:41-51`), a module over an ABSTRACT stage
function `T` with five closure facts, and the L tower is one `open ... public`
at `:117`. **So BLOCK 1 re-instantiates at the J tower by opening `KeyOver` at
the J stage function, and the twelve tokens are a call-site cost, not a rewrite
cost.**

**BLOCK 2 is where the sharing is real and where I would spend the next
line.** `envFoB`, `Δ₀-envFoB` and `bddEnvFoB` name no tower at all: they are
`Formula S 1`, a `Δ₀` witness and a constant certificate. **28 of the 45 lines
are tower-free by construction.** The single L token in BLOCK 2 is `carve∈𝒟ₒ`,
and it is the one step that IS about the L tower's definability operator.

**So the honest DD4 answer: 32 of 45 shared as written, and 44 of 45 shared
once `KeyOver` is opened at the second tower.** **I did not write anything
fixed to L that could have been written generic.**

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the gate passes at 40 lines** | **MEASURED FALSE. 45**, with the adequacy unwritten |
| **the numeral case is FALSE** | **MEASURED FALSE.** It is TRUE. Section 3.1 gives the rank argument, and its first step is green Agda |
| the level substitution fails outright | **MEASURED FALSE.** It fails only at a general arity |
| `envSetK` has a consumer in `src/` today | **MEASURED FALSE.** ONE occurrence, its own declaration. Section 9 |
| the delivered `envFo`, `envFoGen`, `envOverAt` or `envSetAt` is Δ₀ | **MEASURED FALSE**, four reads, section 3.3 |
| the tree has a stage-controlled carve that does not need Δ₀ | **MEASURED FALSE.** `carveSat` takes `dφ : Δ₀ φ` as a real argument, `src/L/Axioms/Separation.lagda.md:163-168`. The only non-Δ₀ separation, `hasSeparationL`, returns no stage bound |
| the two green halves join | **MEASURED FALSE.** One is a containment, the other a membership of a different set |
| **a numeral-restricted `envSetK` says nothing its consumers can use** | **MEASURED FALSE.** The arity at every consuming site is a numeral, and the tree carries the reader. Section 4 |
| the `envK-*` fields pin `ar` in their own telescopes | **MEASURED FALSE.** `ar` is a bare `S`. The numeral comes from `codesK` and the code set, not from the field |
| I added the fourth `HullStage` hypothesis | **MEASURED FALSE. I did not reach for it**, and section 3.1 says why it is not forced by this measurement |
| I edited any master | **MEASURED FALSE. `src/` is byte-identical to the coordinator's commit** |
| I ran `make check` | **MEASURED FALSE.** The brief reserves it |
| **`[LJ-1.172]`'s root cause is exactly right** | **PARTLY FALSE, and section 10 is the correction.** Devlin's `Pow` is applied to the VARIABLE set, never to the parameter `u` |
| a cheaper route to the identification exists | **NOT CLAIMED. C-36.** I measured one route and priced it |
| the 45 is the whole price | **NOT CLAIMED.** It is the price of the two halves. The adequacy is a survey at about 120 |

## 9. CONSUMERS

**MEASURED, before any edit, and re-run at this task's date.** `envSetK`
occurrences in `src/`:

```
$ grep -rn "envSetK" src/
src/L/Condensation/TwelveAgree.lagda.md:271:    envSetK : (B ar : S)
```

Count = 1, over every file type under `src/` (`.agda`, `.md`, and I checked the
file-type list rather than assume it). The single occurrence is the field's own
declaration inside `TFacts`. **The brief's measurement is confirmed: the field
has no consumer in the tree today, and narrowing it would break nothing that
exists.**

## 10. THE CORRECTION TO THE ROOT CAUSE, and it favours the cure

**`[LJ-1.172]` wrote that Devlin builds `K(u)` with sequences AND POWER, and
that `envSetK` corresponds to his `Pow`. MEASURED: the second half is FALSE,
and the first half is true but does not mean what it was read to mean.**

`_build/literature/dev2.txt:600-608` gives `K(u)` in words. It is a union of
three sets, and every one of them is a set of **finite sequences**:

- finite sequences of members of `𝓕 ∪ {vᵢ | i ∈ ω} ∪ u`;
- finite sequences of finite sequences of members of the same;
- finite sequences of **finite subsets** of `{vᵢ | i ∈ ω}`.

**MEASURED: `u` enters only through its MEMBERS, and only inside a FINITE
sequence. Devlin never takes the power of `u`.**

`_build/literature/dev2.txt:610-618` gives the LST formula `K(w,u)`, and its
`Pow` clause is `[Pow(f,d) ∧ Seq(c,f)]`, where the same formula pins `d` by
`(∀z ∈ d) Vbl(z) ∧ (∀i ∈ ω)(vᵢ ∈ d)`. **MEASURED: `d` is the set of
VARIABLES. The power is the power of a FIXED countable set, and only its finite
subsets are used.**

**So the departure from the source is not that the tree took a level where
Devlin took a constructed set. It is that the tree's `envSetGen B ar` admits a
GENERAL arity, and Devlin's construction has no such object: his arities are
all finite, so all numeral.** **The numeral restriction is DEVLIN'S OWN FORM,
and it is a return to the source rather than a departure from it.**

**And the archive says the same thing, which is why I state it twice.**
**MEASURED by me: `grep -rn "envSetGen\|envFoGen" archive/` returns ZERO.** The
retired route carried `envSet : (n : ℕ) → S` and nothing else
(`archive/src/2026-08-09-rud-route/L/Coding/EnvSet.lagda.md:183`). **The
general arity entered with this tree's `module Generic (B ar : S)`
(`src/L/Coding/EnvSet.lagda.md:396`). Two independent sources, the literature
and the archive, both hold the numeral form.**

**What survives of `[LJ-1.172]`'s account, and most of it does.** Its
measurement that `envSetGen B ar` is the full constructible function space
(`:741-750`), its refutation of `envSetK` at a general arity (`:752-767`), its
correction of `[LJ-1.168]`'s `mkReflect` route (`:814-848`), and its
measurement that six names carry one closure obligation (`:850-871`): **all
confirmed by this task.** **The one sentence I correct is the one that assigned
`envSetK` to Devlin's `Pow`.**

## 11. RUN LOG

| # | command | wall | result |
|---|---|---:|---|
| 1 | `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-173/ProbeLJ1173A.agda` | 2 s | one error, a de Bruijn index in a hand-written `Δ₀` witness |
| 2 | the same, after routing the witness through the delivered `Δ₀-appAt` and `Δ₀-prAtL` | 3 s | **exit 0** |

**ONE agda process at a time. The cap was NEVER raised. No heap wall, and no
run came near the 20-minute criterion.** The interfaces under `_build/2.8.0`
were warm, which is why the runs are seconds; **I do not report these seconds
as a cold figure and DD24 is untouched.**

## 12. PROHIBITIONS, ANSWERED ONE BY ONE

| prohibition | answer |
|---|---|
| `src/L/Choice/Name.lagda.md` | **NEVER OPENED** |
| `src/L/Coding/Graph.lagda.md`, `[LJ-1.164]`'s move | **NEVER OPENED** |
| the probe outside `agents/tasks/LJ-1-173/` | **NO.** `check-probes.py` is clean |
| `src/Everything.lagda.md` | **NEVER OPENED.** No new module exists to wire |
| the fourth `HullStage` hypothesis | **NOT ADDED, and not reached for** |
| commit, push, `git checkout .`, `stash`, `reset --hard`, `clean` | **NONE of them** |
| `make check` | **NOT RUN** |
| the heap cap | **`-M8g` throughout, never raised** |
| applying a cure whose gate failed | **NOT APPLIED** |

## 13. WHAT THE NEXT BRIEF COULD FUND, offered not assumed

**Three options, and I price them rather than choose.**

1. **Fund the adequacy at about 120 lines and take the numeral cure.** Section
   4 measures that the consumers can use it and section 10 measures that it is
   Devlin's own form. **This is the option the evidence favours, and its cost
   is a build, not a probe.**
2. **Re-price the gate.** 40 lines was set before anyone had measured that the
   delivered description is not Δ₀. **The 40 priced a one-declaration
   re-statement; the work is a bounded re-encoding.** A re-priced gate is not a
   moved criterion, provided the re-pricing is written down before the run.
3. **`[LJ-1.168]`'s fourth `HullStage` hypothesis.** **I do not recommend it on
   this evidence**, because section 3.1 measures that the numeral case does not
   need it. **That is a route decision and it is not mine.**

**One line for the brief writer, and it is this task's own lesson.** The gate
named two delivered lemmas, `paramEnv∈` and `carve∈𝒟ₒ`, and both closed on the
first try. **What was never named is the sentence between them.** **That is the
third time in two tasks that the error sat between the numbers rather than in
one, and a gate that names its two ENDS does not gate the JOIN.**

## 14. ARCHIVE USED (DD18)

**I took SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
target classically FALSE, so no archived statement is evidence here. **And I
re-ran the load-bearing grep myself rather than accept it**, because the brief
records one archive claim measured FALSE this phase.

- **`archive/src/2026-08-09-rud-route/L/Coding/EnvSet.lagda.md`.** THE BRIEF'S
  QUESTION, ANSWERED: **the retired route's environment set quantified over
  NUMERAL arities only.** `envSet : (n : ℕ) → S` at `:183`, `envFo : (n : ℕ) →
  Formula S 1` at `:170`, and the arity enters the description as the PINNED
  CONSTANT `con (nn n)` at `:167-173`. `envSet-out` at `:379-380` and `Recover`
  at `:309-312` both take `n : ℕ`, and `Recover` demands `qd : fst (lookup di
  γ) ≡ # n`.
- **MEASURED BY ME, and it is the sharpest thing the archive gives:**
  `grep -rn "envSetGen\|envFoGen" archive/` returns **ZERO**. **The general
  arity does not exist anywhere in the retired route.** It entered with the
  live tree's `module Generic (B ar : S)` at `src/L/Coding/EnvSet.lagda.md:396`.
  **So the general-arity field is not inherited: it was added, and the numeral
  restriction returns the tree to what BOTH the archive and Devlin had.**
- **`archive/.../L/Coding/Model.lagda.md:1149-1150` and `:2320`.** SHAPE TAKEN:
  the object-language `envSetAt E ar B` had a general `ar` SLOT there too, and
  the archive's own prose says the clause "describes, not constructs" the
  ambient set. **The same gap existed and never bit, because
  `negClauseAt`/`negClause-in`/`negClause-out` had no consumer outside their own
  master.**
- **`archive/.../L/Coding/EnvSet.lagda.md:85-86`, `:176-177`, `:180`.** SHAPE
  TAKEN: the archived route bounded the individual environments by one stage,
  through `stageFor`, and then separated inside it. **It never stated the SET
  in a stage.** `grep` shows `envSet` only ever on the RIGHT of `∈ˢ`.
  **So the archive answers the gate's question the same way this task does:
  the containment is delivered, the membership is not.**
- **`agents/tasks/LJ-1-172/lj-1.172-report.md` sections 13 to 23, READ
  WHOLE.** TOOK the refutation (`:726-812`), the `mkReflect` correction
  (`:814-848`), the six-names table (`:850-871`), the missing-supplier
  measurements (`:873-906`) and the cure with its gate (`:907-939`). **Section
  10 corrects one sentence of its literature reading and confirms the rest.**
- **`agents/tasks/LJ-1-168/lj-1.168-report.md:330-412`.** TOOK the nine-lemma
  build table, which is where L4 and L8 are named as `envSetK`'s consumers, and
  the fourth-hypothesis fallback at `:410-412`. **I did not take the fallback.**
- **`dev/LESSONS.md`: D-1, C-36, C-38 as extended, C-40, C-35, C-39, C-12,
  C-22, P-l, P-i, D-10.** **D-1 is the rule this task turns on**: the criterion
  was written before the run and I did not move it after I saw 45. **C-36 is
  why section 3.1 is marked INFERRED**, and **P-l is why section 3.4's 120 is
  called a survey and not a price.**

## 15. LITERATURE USED (DD18)

**`_build/literature/dev2.txt:593-645`, read whole, and section 10 is the
result.**

- **`:600-608`**, `K(u)` in words. **TOOK: all three components are sets of
  FINITE sequences, and `u` enters only through its members.**
- **`:610-618`**, the LST formula `K(w,u)`. **TOOK: the `Pow` clause is
  `Pow(f,d)` with `d` the VARIABLE set, pinned in the same formula by
  `(∀z ∈ d) Vbl(z) ∧ (∀i ∈ ω)(vᵢ ∈ d)`. The power is never of `u`.**
- **`:619-628`**, lemma 2.4 and corollary 2.5. **TOOK: the closure of `L_α`
  under `Def` at limit `α > ω` is a parenthetical, and its proof is "left as an
  exercise for the reader".** `[LJ-1.172]:867-871` measured this and I confirm
  it.

**THE BRIEF'S QUESTION, ANSWERED.** **Devlin's arities ARE numeral.** Every
sequence in `K(u)` is finite, and the only power is of a fixed countable
variable set. **So restricting `envSetK` to a numeral arity is HIS FORM. The
general arity is the departure, and it entered with this tree's `envSetGen`.**
