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

---

# PART TWO: the coordinator funded the join

**Appended after the coordinator committed the NO-GO at `0f12d16` and ruled
option one.** Same probe file, same process discipline, same incremental
landing.

## 16. PART TWO: CRITERIA, FIXED IN WRITING BEFORE THE FIRST RUN (D-1)

**The coordinator's grades, copied here so that nothing moves after a number
appears.**

| outcome | line count of the ADEQUACY, on top of the 45 already green |
|---|---|
| **continue, then apply the restriction** | within 50 percent of 120, so **180 or fewer** |
| **STOP, keep what typechecks, report the overage with its cause** | **above 180** |
| **STOP AND SAY SO FIRST** | the adequacy is FALSE, that is, the bounded description does not define `envSet B n` |
| **STOP with the wall clock** | anything walls |

**Wall clock: 20 minutes per agda invocation. ONE process.
`GHCRTS="-A64m -I0 -M8g"`. The cap is NEVER raised.**

**The count is the same caliber as PART ONE**: non-blank, non-comment lines of
Agda inside the probe, module header and imports excluded.

## 17. PART TWO: THE ROUTE, chosen before the first run

**Both directions pass through the delivered unbounded description at ONE
environment**, `δ x = x ∷ d ∷ B ∷ []`, and that is what keeps the price near
the survey.

1. `unbound`: the bounded `envFoB` gives `envOverAt` at `δ x`. **This is the
   only direction that needs an argument.** The pairs conjunct plus `pr-inj`
   (`src/V/Coding.lagda.md:178`) shows that any recorded pair has its index in
   `d` and its value in `B`, which is exactly what releases the three unbounded
   quantifiers.
2. `rebound`: `envOverAt` gives `envFoB`. **Restriction, and it costs the four
   delivered readers.**
3. `intoSet`: `envOverAt` at `δ x` gives `x ∈ˢ envSet B n`, through the
   delivered `Recover` (`src/L/Coding/EnvSet.lagda.md:315-381`) and
   `envSet-in` (`:381-383`). **Delivered, reused, not rewritten.**
4. `outSet`: `x ∈ˢ envSet B n` gives `envOverAt` at `δ x`, through the
   delivered `envSet-mem` (`:192-194`) and `envOverAt-transport`
   (`src/L/Coding/Model.lagda.md:517-560`). **Delivered, reused, not
   rewritten.**
5. the carve identification, and then the one declaration the gate asked for.

## 18. PART TWO: THE ADEQUACY HOLDS, at 155 lines

**MEASURED. `agents/tasks/LJ-1-173/ProbeLJ1173A.agda`, exit 0, 3 s, no
`postulate`, no hole, no unsolved meta.**

| block | what | lines |
|---|---|---:|
| 3 | the adequacy: `slots`, `unbound`, `rebound`, `intoSet`, `outSet`, `adequate` | **102** |
| 4 | the identification `carved ≡ fst (envSet B n)`, and `envSetNumeral∈` | **53** |
| | **the adequacy** | **155** |
| | against the abort at | 180 |
| | against my own survey of | 120 |

**The survey was low by 29 percent and inside the grade.** **It closed on the
FIRST agda run**, which I record because it is evidence that the route chosen in
section 17 was the right one, not evidence that the work was small.

**The declaration the gate asked for, now green:**

```agda
envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
               → ⟨ fst B ∈ Lset σ ⟩
               → ⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩
```

**The iterate is 4 and it does not mention `n`. The bound is uniform in `n`,
which is what the brief asked for.**

**Where the JOIN actually sat, and it is one line of the probe.**
`carvedEq : carved ≡ fst (envSet B n)`. Before it, BLOCK 1 spoke about a
containment and BLOCK 2 about a different set. **After it, both speak about
`envSet B n`, and `landed` is one `subst`.**

**What the adequacy needed that the survey did not name: `slots`.** One fact,
that a recorded pair has its index in `d` and its value in `B`, from the pairs
conjunct and `pr-inj`. **It is what releases the three unbounded quantifiers,
and it is why the bounded description is not weaker than the delivered one.**

**And what the survey over-counted: `Recover` and `envSet-mem` are REUSED, not
rewritten.** `intoSet` is 4 lines and `outSet` is 8.

## 19. PART TWO: WALL CLOCK FOR THE C-40 RUNS, fixed before them

**40 minutes for `src/L/Condensation/TwelveAgree.lagda.md`**, which is the
criterion `[LJ-1.172]` measured for the three `*Agree` masters
(`agents/tasks/LJ-1-172/lj-1.172-report.md:678-681`). **A run past it is a wall
and the step STOPS.** ONE process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

## 20. PART TWO: THE RESTRICTION IS APPLIED

**`envSetK` is now numeral-arity.** `src/L/Condensation/TwelveAgree.lagda.md:281-285`:

```agda
    envSetK : (B ar : S) (n : ℕ) → fst ar ≡ # n
            → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst (Generic.envSetGen B ar)
                 ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

**The shape chosen, and why it is that shape and not another.** The field keeps
its `ar` and gains ONE hypothesis, `fst ar ≡ # n`. **It does not swap `ar` for a
numeral**, because a consumer applies it at the `ar` its own row holds, and a
field stated in a form the consumer must translate into is the trap P-k names.
**So the consumer supplies the numeral equation and reads the same conclusion at
the same `ar`.**

**This is not a weakening into something true because it says nothing.** The
conclusion is unchanged: the same set, at the same arity, in the same `K`.
**Only the arity is pinned, and section 4 measures that every consuming site can
pin it.**

The change is **+11 lines, -1 line**, all inside the `agda` fence, so standing
moves by **+10**. Ten of the eleven are the comment that records the refutation
and its cure; **one is the signature.**

## 21. PART TWO: CONSUMER VERDICTS (C-40)

| item | verdict |
|---|---|
| `src/L/Condensation/TwelveAgree.lagda.md` | **GREEN**, exit 0, 9 s at the first run and 9 s after the comment trim |
| consumers of `TwelveAgree` in `src/` | **NONE.** `grep -rn "L.Condensation.TwelveAgree" src/` returns its own module line and `src/Everything.lagda.md:376`. `LowerAgree`, `UpperAgree` and `Condensation` are its DEPENDENCIES, not its consumers |
| consumers of `envSetK` | **NONE**, re-measured after the edit. The field is a hypothesis nothing supplies yet |
| `src/Everything.lagda.md` | **NEVER OPENED.** The coordinator's `make check` covers it |
| any other master | **NOT EDITED** |

**So the C-40 obligation is discharged in full: the edited master and every
consumer of it typecheck, and the consumer set is the master itself.**

## 22. PART TWO: CHECKER COUNTS

| checker | result |
|---|---|
| `agda src/L/Condensation/TwelveAgree.lagda.md` | **exit 0**, 9 s, well inside the 40-minute criterion |
| `agda agents/tasks/LJ-1-173/ProbeLJ1173A.agda` | **exit 0**, 3 s, re-run after the master edit |
| `postulate`, hole, unsolved meta | **all three ABSENT** in both. Agda printed no warning |
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/lint-prose.py --check` on the edited master and this report | **exit 0** |
| `scripts/weave-i18n.py --check` | **exit 0** |
| `scripts/check-unbound-hyp.py` | **2**, unchanged |
| `scripts/check-probes.py` | **clean**, 1804 tracked files |
| `make check` | **NOT RUN.** The coordinator runs it |

**Four agda invocations in PART TWO, ONE process at a time,
`GHCRTS="-A64m -I0 -M8g"`, the cap NEVER raised, no heap wall and nothing near
its wall clock.** The interfaces were warm; **these are not cold figures and
DD24 is untouched.**

## 23. PART TWO: DD4

**MEASURED over the 155 adequacy lines: 133 name NO L-tower token, 22 do.**
**BLOCK 3, the adequacy proper, is 101 of 102 tower-free.**

**Where the 22 sit.** Twenty-one are in BLOCK 4, which is the identification at
a CONCRETE level and cannot avoid naming it: `Lset α`, `⟪ Lset α ⟫↪`,
`Lset→isL`, `Lset-mono`. **That is the one place the argument is genuinely about
the L tower, because the carve is the L tower's definability operator.**

**BLOCK 3 names one L token in 102 lines**, and that one is `isL-trans` in
`slots`, a class-transitivity step every tower has. **`slots`, `unbound`,
`rebound`, `intoSet`, `outSet` and `adequate` are about a `Formula S 1` and the
delivered coding readers, and they re-instantiate at the J tower unchanged.**

**So the DD4 answer for the whole probe: 205 body lines, of which 170 name no
tower**, 50 in BLOCKS 1 and 2 and 155 in the adequacy. **I wrote nothing fixed
to L that could have been written generic**, and the one block that is
L-specific is L-specific by subject matter.

## 24. WHERE `envSetNumeral∈` SHOULD LAND, offered not taken

**I did NOT put the lemma into `src/`. The coordinator asked for the
restriction, and a placement is a route decision.** Here is what it costs,
measured, so that whoever takes it does not have to re-find it.

- **There is NO import cycle. MEASURED.** `L.Condensation` does not import
  `L.Coding.Key` (`grep -rn "L.Coding.Key" src/` returns only
  `src/Everything.lagda.md:351` and the module's own line).
- **But the direction is inverted.** `src/Everything.lagda.md` orders
  `L.Coding.Key` at `:351` and `L.Condensation` at `:373`. **The probe imports
  `L.Condensation` for `Δ₀-appAt` and `Δ₀-prAtL` only.**
- **Those two are 2-line derivations** (`src/L/Condensation.lagda.md:88-89`,
  `:94-95`) from `L.Absoluteness.Δ₀-liftFo` and `L.Coding.Base.Δ₀-prAt`, **both
  of which sit BELOW `L.Coding.Key`.** **So the lemma lands in `Key.lagda.md`
  at the cost of re-deriving four lines, or it lands in a new module above
  `L.Condensation`.**
- **`L.Coding.Key` itself has NO consumer in `src/` today** beyond
  `Everything`, which I mark because it bears on where a new supply chapter
  should sit.

## 25. PART TWO: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the adequacy is FALSE** | **MEASURED FALSE.** It is green Agda. `adequate` at `ProbeLJ1173A.agda:305-309` |
| **the adequacy exceeds 180** | **MEASURED FALSE. 155** |
| my survey of 120 was accurate | **MEASURED FALSE. It was 29 percent low**, and I record that rather than round it away |
| the bound depends on `n` | **MEASURED FALSE.** The iterate is 4 for every `n` |
| `envSetK` is still general-arity | **MEASURED FALSE.** It now carries `fst ar ≡ # n` |
| the restriction broke a consumer | **MEASURED FALSE.** `TwelveAgree` is green and the field has no consumer |
| the restriction weakened the field into vacuity | **MEASURED FALSE.** Same set, same arity, same `K`; one hypothesis added, and section 4 measures that every site can discharge it |
| **`envSetK` is now SUPPLIED** | **MEASURED FALSE, and I say it plainly. It is still a hypothesis.** The probe proves the fact that would supply it; nothing in `src/` supplies it, because step 6 is unbuilt |
| landing the lemma in `Key.lagda.md` needs a cycle broken | **MEASURED FALSE.** There is no cycle. It needs four re-derived lines or a different home |
| I edited a second master | **MEASURED FALSE.** One master, `TwelveAgree`, 11 lines added and 1 removed |
| I ran `make check` | **MEASURED FALSE** |
| the 155 is a cold figure | **NOT CLAIMED.** The interfaces were warm |
| a shorter adequacy exists | **NOT CLAIMED. C-36.** I wrote one route and it closed on the first run |

## 26. PART TWO: PROHIBITIONS, ANSWERED ONE BY ONE

| prohibition | answer |
|---|---|
| the fourth `HullStage` hypothesis | **NOT ADDED.** The numeral case did not need it |
| `src/L/Choice/Name.lagda.md` | **NOT EDITED.** The probe IMPORTS `numeral∈limit` from it, exactly as `src/L/Coding/Key.lagda.md:23` already does. **Reading is not touching, and I flag the import so the coordinator can rule** |
| `src/L/Coding/Graph.lagda.md`, `[LJ-1.164]`'s move | **NEVER OPENED** |
| `src/Everything.lagda.md` | **NEVER OPENED. No new module exists to wire**: the probe stays a probe |
| the probe outside `agents/tasks/LJ-1-173/` | **NO.** `check-probes.py` clean |
| commit, push, `git checkout .`, `stash`, `reset --hard`, `clean` | **NONE of them** |
| the heap cap | **`-M8g` throughout, never raised** |

## 27. WHAT THIS LEAVES, and what it does not

**Landed:** the numeral restriction, green, with its reason in the master's own
comment.

**Proved but not landed:** `envSetNumeral∈`. **It is in a probe, and a probe is
evidence rather than proof.** Section 24 prices its home.

**Still open, and unchanged by this task:** step 6 is unbuilt, and
`[LJ-1.172]:873-906` measured that `hasLevels` and `covered` have no supplier
either. **This task removed one refutation from the path. It did not build the
path.**

**One line for the brief writer.** The gate fired at 45 and stopped a build
that would have run three times over; the join it refused to fund then closed
at 155 on the first agda run once it was named as the work. **A gate that names
the two ENDS measures the parts. Naming the JOIN is what turned this from a
refutation into a build.**

---

# PART THREE: the lemma is placed, and step 6 STOPS at the field audit

**Appended after the coordinator committed PART TWO at `d412cf3` with
`make check` EXIT 0 cold.**

## 28. LEAD

1. **THE LEMMA IS PLACED.** `envSetNumeral∈` is in
   `src/L/Coding/Key.lagda.md`, green, exit 0, 3 s. The two `Δ₀` facts are
   re-derived in four lines, as ruled. **The placement forced ONE thing and I
   name it in section 30: the master works in the OTHER structure, so the block
   is qualified rather than opened.**
2. **STEP 6 STOPS BEFORE ITS FIRST LINE, and it is the stop the coordinator
   named.** **NINE MORE FIELDS CARRY `envSetK`'s DISEASE**, and my restriction
   cured exactly one of ten. **I wrote no line of step 6, so the count against
   270 is ZERO, and the reason is not budget.**

**The nine are `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin`,
`envInK-mem`, `envInK-neg`, `envInK-top` and `envInK-imp`
(`src/L/Condensation/TwelveAgree.lagda.md:183-215`).** **Every one of them
quantifies over a BARE `ar : S` with NO hypothesis on it at all**, and each
concludes a membership in `K`.

## 29. THE PLACEMENT, and what it forced

`src/L/Coding/Key.lagda.md`, **+363 lines, -6**. In-fence non-blank lines now
**408**. **The master typechecks at exit 0 in 3 s and has no consumer in `src/`
beyond `src/Everything.lagda.md:351`, so C-40 is discharged in full.**

| checker | result |
|---|---|
| `agda src/L/Coding/Key.lagda.md` | **exit 0**, 3 s, first run |
| `postulate`, hole, unsolved meta | **all three ABSENT** |
| `lint-agda.py --check` | **exit 0** |
| `lint-prose.py --check` on the master | **exit 0** |
| `weave-i18n.py --check` | **exit 0** |
| `check-unbound-hyp.py` | **2**, unchanged |
| consumers of `L.Coding.Key` | **NONE** beyond `Everything` |

**The two `Δ₀` facts, re-derived as ruled**, at four lines, named `Δ₀-prAtLK`
and `Δ₀-appAtK` so that nothing is ambiguous against `L.Condensation`'s pair.
**The comment records that they are the same two and that a later pass may point
the consumer at this copy.**

## 30. WHAT THE PLACEMENT FORCED, and it is the one thing to rule

**`src/L/Coding/Key.lagda.md` opens `hPropStructure 𝒮ᵥ`, so its `S` is the raw
hierarchy. The environment-set block lives in `𝒮ʟ`.** **The two cannot both be
opened**, so the block reads `CS.S` throughout, with

```agda
module CS = hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
```

**This is the pattern `src/L/BoundedSubset.lagda.md:56-58` already uses**, so it
is a delivered idiom and not a new one. **It costs one qualifier per occurrence
and nothing else, and I flag it only because it changed the master's shape:
`Key.lagda.md` now speaks about two structures where it used to speak about
one.**

**Nothing else was forced.** No cycle, no new module, no change to any other
master, and `src/Everything.lagda.md` was never opened.

## 31. STEP 6: THE FIELD AUDIT, AND THE STOP

**I ran the audit BEFORE writing any field, because D-10 is the rule that found
`envSetK` and the coordinator's own grade says a second false field is worth
more than the rest of the build.**

### 31.1 The five `envK-*` fields are FALSE, by `[LJ-1.172]`'s own argument

`src/L/Condensation/TwelveAgree.lagda.md:183-202`. Taking `envK-mem` as the
example, and I checked all five slot by slot:

```agda
    envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

**MEASURED, by counting the environment.** `(E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')`
puts `E` at 0, `ar` at 4 and `γ'`'s head at 6. So the arity slot IS the
telescope's `ar` and the carrier slot is `γ'`'s head. **The ONLY hypothesis is
the satisfaction. `ar` carries no membership hypothesis and no numeral
hypothesis.**

| field | `file:line` | arity slot | resolves to |
|---|---|---|---|
| `envK-mem` | `:183-186` | 4 | `ar`, bare |
| `envK-neg` | `:187-190` | 4 | `ar`, bare |
| `envK-top` | `:191-194` | 3 | `ar`, bare |
| `envK-imp` | `:195-198` | 6 | `ar`, bare |
| `envK-allin` | `:199-202` | 5 | `ar`, bare |

**`⊨ envSetAt E ar B` says `E` IS the set of all environments over `ar` into
`B`.** At an unrestricted `ar` that is the full constructible function space,
and the field then asks a LEVEL to hold it. **That is exactly the statement
`[LJ-1.172]` refuted at `:752-767`, and my numeral restriction did not touch
these five.**

**Classification, in the brief's words: the structural half is MEASURED**, at
the five `file:line`s above; **the cardinality half is INFERRED**, and it is
`[LJ-1.172]`'s inference re-used at five new sites rather than a new one.

### 31.2 The four `envInK-*` fields are FALSE for a DIFFERENT and CHEAPER reason

`src/L/Condensation/TwelveAgree.lagda.md:203-215`.

```agda
    envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

**MEASURED: `ar` sits at slot 5 and is again bare.** But here the conclusion is
about a SINGLE environment, not about the set of them, **so no cardinality is
needed to refute it. Transitivity alone does it.**

**The witness, and it is cheaper than `[LJ-1.172]`'s.** Take `ar` to be any set
NOT in `K`, and take `z` to be a constant function on `ar` into the carrier.
Then `⊨ envOverAt z ar B` holds, and `z` records `ar`'s every member as a first
component. **`K` is a LEVEL and therefore transitive, so `z ∈ K` would force
`ar ∈ K`.** Contradiction. **No rank counting and no cardinality: the field is
false because nothing bounds `ar`.**

**Classification: the structural half is MEASURED at the four `file:line`s; the
witness is INFERRED, because I did not build it in Agda (C-36).**

### 31.3 The cure is the one already ruled, and a sibling field already supplies half of it

**I offer it and I do not take it, because ten fields is a route decision of the
same class the coordinator ruled for one.**

| fields | the missing hypothesis | who discharges it at the site |
|---|---|---|
| `envInK-mem`, `-neg`, `-top`, `-imp` | `⟨ fst ar ∈ fst (lookup … K …) γ' ⟩` | **`codesK` ALREADY CONCLUDES exactly this** (`:161-165`, its first output component). **The hypothesis one field needs is another field's conclusion** |
| `envK-mem`, `-neg`, `-top`, `-imp`, `-allin` | `(n : ℕ) → fst ar ≡ # n`, the shape `envSetK` now carries | `codesK` gives the code's shape, `arityNumAtL` (`src/L/Coding/CodeSet.lagda.md:247-248`) gives the numeral, `pr-inj` closes it. **This is section 4's join, unchanged** |

**So the ten fields are ONE disease with ONE cure, and I cured one of them.**
**MEASURED: `envSetK` was not special. It was the one `[LJ-1.172]` happened to
read.**

### 31.4 Why this is a STOP and not a detour

**The coordinator's grade names it: "A field turns out FALSE, as `envSetK` did:
STOP AND SAY SO FIRST."** Nine did.

**And building step 6 first would have been worse than useless.** Its 28 fields
include these nine. **A supplier written against a false field cannot close, so
the build would have burned its budget discovering by failure what the audit
found by reading.** **The audit cost one file read.**

## 32. STEP 6 AGAINST ITS 270

**ZERO lines written, and the reason is the stop, not the budget.** The abort
grades never engaged: nothing was measured against 270 and nothing walled.

**What the audit changes about the 270 itself, offered not assumed.**
`[LJ-1.168]` priced the 28 fields at about 270 with `envSetK` costed at 45
through `mkReflect`. **`[LJ-1.172]` refuted that route and this task replaced it
with 155 lines of adequacy plus a 4-line bound.** **The nine fields above take
the SAME cure, and its expensive half is now DELIVERED in
`src/L/Coding/Key.lagda.md`.** **So a re-priced step 6 should be CHEAPER than
270 for these ten fields, not dearer**, and I say that as a direction rather
than a number, because I have measured no field's supply.

## 33. PART THREE: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the lemma is placed** | **TRUE.** `src/L/Coding/Key.lagda.md`, green |
| the placement needed a cycle broken | **MEASURED FALSE.** No cycle. Four re-derived lines, as ruled |
| the placement forced nothing | **MEASURED FALSE.** It forced the two-structure qualifier, section 30 |
| **step 6 got some way against 270** | **MEASURED FALSE. ZERO lines**, and section 31 is why |
| **`envSetK` was the only false field** | **MEASURED FALSE. Nine more**, and my restriction cured one of ten |
| the nine are false for one reason | **MEASURED FALSE. TWO reasons.** Five fail on the power, four fail on transitivity alone |
| the `envInK-*` refutation needs cardinality | **MEASURED FALSE.** Transitivity alone, section 31.2 |
| the nine carry a hypothesis on `ar` | **MEASURED FALSE.** Bare in all nine, checked slot by slot |
| I changed any of the nine | **MEASURED FALSE. I stopped and reported**, as the grade directs |
| I added the fourth `HullStage` hypothesis | **MEASURED FALSE** |
| I touched `src/L/Choice/Name.lagda.md` | **MEASURED FALSE.** `Key.lagda.md` already imported it at `:23` before this task |
| I opened `src/Everything.lagda.md` | **MEASURED FALSE.** No new module: the lemma went into an existing master |
| I ran `make check`, committed or pushed | **MEASURED FALSE**, none of the three |
| the nine are certainly false | **the structural half is MEASURED, the witnesses are INFERRED.** I built no Agda counterexample |

## 34. WHAT I RECOMMEND, offered not taken

1. **Rule the same cure onto the nine.** Four `envInK-*` take `ar ∈ K`, which
   `codesK` already concludes; five `envK-*` take the numeral equation
   `envSetK` now carries. **One ruling, ten fields, one disease.**
2. **Then re-price step 6**, because its expensive half is now delivered.
3. **Do NOT build step 6 before the ruling.** Nine of its 28 fields cannot be
   supplied as written.

**One line for the brief writer, and it is the same line a third time.** The
gate measured the two ends. The join was the work. **And this audit found that
the refutation itself had two ends: `[LJ-1.172]` read ONE field and I cured ONE
field, while the disease was in ten.** **A refutation that names one site
measures that site. It does not measure how far the site extends.**
