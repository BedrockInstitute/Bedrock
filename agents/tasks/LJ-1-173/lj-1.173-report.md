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

---

# PART FOUR: the sweep you ordered found a third layer, and it changes the cure

**Appended after the coordinator committed PART THREE at `584ae24`.**

## 35. LEAD

**THE TEN ARE NOT CURED, AND I STOPPED BEFORE CURING ANY OF THEM. The sweep you
ordered is why, and it is the third layer you said would outrank the build.**

1. **The same shape is in TWO MORE RECORDS.** `LFacts`
   (`src/L/Condensation/LowerAgree.lagda.md:137-160`, **6 fields**) and `UFacts`
   (`src/L/Condensation/UpperAgree.lagda.md:137-160`, **6 fields**). **So the
   family is 21 fields across three records, not 9 across one.**
2. **The cure is ATOMIC across the three, and I MEASURED that rather than
   inferred it.** I added the hypothesis to ONE `TFacts` field and typechecked:
   **`TwelveAgree` goes RED at `:409`**, the `lf` record's pass-through
   `envInK-mem = envInK-mem`. **Curing nine without curing twenty-one is not a
   smaller change. It is a broken tree.** I reverted; `src/` is byte-identical
   to your commit.
3. **The five dear fields need a NEW FIELD, not just a new hypothesis.**
   `codesK` concludes `ar ∈ K`, so the four cheap ones are free as you said.
   **But nothing in the frame concludes `fst ar ≡ # n`.** `arityNumAtL`
   lives in `src/L/Coding/CodeSet.lagda.md:247-248`, and the frame never
   receives it. **So the numeral equation has to enter the three records as a
   new field.**
4. **And the fields are threaded into `src/L/Condensation.lagda.md`**, which
   names them `envK` and `envInK` in about ten `*Agree` telescopes: **24 and 37
   occurrences.** **`KFacts` is CLEAN** (`:5996-6030`): its fields are closure
   facts with no satisfaction antecedent and no bare set, which is why
   `[LJ-1.166]`'s four classes survived.

**Step 6 re-prices at about 260. The CURE prices at about 190 and it is not
part of that number.** Section 38.

## 36. THE SWEEP, field by field

**`grep` over every record in the condensation cluster**, then each field read
slot by slot.

| record | `file:line` | diseased fields | clean? |
|---|---|---|---|
| `TFacts` | `TwelveAgree.lagda.md:183-215` | 5 `envK-*`, 4 `envInK-*` | no |
| `LFacts` | `LowerAgree.lagda.md:137-160` | 3 `envK-*` (`mem`, `neg`, `imp`), 3 `envInK-*` (`mem`, `neg`, `imp`) | no |
| `UFacts` | `UpperAgree.lagda.md:137-160` | 3 `envK-*` (`neg`, `top`, `allin`), 3 `envInK-*` (`neg`, `top`, `imp`) | no |
| `KFacts` | `Condensation.lagda.md:5996-6030` | **NONE** | **CLEAN** |

**21 fields. I cured one, `envSetK`, and it is not among these 21: it is the
twenty-second.**

**Why `KFacts` is clean, and it is worth saying because it is the contrast that
makes the diagnosis certain.** Every `KFacts` field is a CLOSURE fact:
`innerK`, `innerPairK`, `pairK`, `carrierK`, the twelve `numK`, the twelve
`tagEq`. **None takes a satisfaction as an antecedent and none quantifies over a
bare set.** **The disease is exactly "decode a satisfaction at an unbounded set,
then conclude a membership", and `KFacts` never does that.**

## 37. THE ATOMICITY, MEASURED

**I did not reason about this. I ran it.**

Edit: `envInK-mem` in `TFacts` gains `⟨ fst ar ∈ fst (lookup … K …) γ' ⟩`.
Run: `GHCRTS="-A64m -I0 -M8g" agda src/L/Condensation/TwelveAgree.lagda.md`.

```
src/L/Condensation/TwelveAgree.lagda.md:409.20-30: error: [UnequalTerms]
  … when checking that the expression envInK-mem has type …
```

**`TwelveAgree` builds `LFacts` and `UFacts` VALUES from its own fields by
pass-through** (`:404-409` and `:447-452`, the lines `envInK-mem = envInK-mem`
and their siblings). **Change one side and the pass-through stops typing.**

**So the change is one atomic edit across `TwelveAgree`, `LowerAgree`,
`UpperAgree` and the `*Agree` telescopes in `L.Condensation` that consume
them.** **I reverted the experiment. `git diff src/` is empty.**

## 38. THE TWO PRICES, each ONE number naming its basis (DD8)

### 38.1 The cure: about 190 lines

| part | count | lines |
|---|---|---:|
| 21 field types in three records | 21 | 25 |
| the new numeral field, three records | 3 | 12 |
| `envK` / `envInK` telescopes in `L.Condensation` | about 10 | 30 |
| application sites, at 3 to 5 lines each | about 30 | 120 |
| | **the cure** | **about 190** |

**Basis: I counted the occurrences myself.** `envK` 24 and `envInK` 37 in
`src/L/Condensation.lagda.md`, plus 21 declarations and about 12 pass-throughs
in the three records. **It is a survey and not a probe measurement (P-l).**

**And it carries a RISK I must name.** The change touches module telescopes in
`src/L/Condensation.lagda.md`. **`[LJ-1.165]` measured an UNCURED wall in this
exact cluster at 20 min 1 s and 9.14 GB, and `[LJ-1.172]` set a 40-minute
criterion for it.** **A telescope change re-elaborates every stored type in the
module (the `[LJ-1.62]` and `[LJ-1.158]` effect), which is the operation that
walled.** **I would gate this with a one-telescope probe before funding the
other nine.**

### 38.2 Step 6: about 260 lines, after the cure and not including it

**Basis: `[LJ-1.168]`'s nine-lemma allocation, with the three diseased lemmas
re-costed against work this task DELIVERED.**

| `[LJ-1.168]`'s lemma | its figure | now | why |
|---|---:|---:|---|
| L9, `envSetK` via `mkReflect` | 45 | **25** | `mkReflect` was refuted; `envSetNumeral∈` is DELIVERED in `src/L/Coding/Key.lagda.md`, so what remains is the `envSet` to `envSetGen` identification through `NumeralFromGeneric.derived` |
| L4, `envOverAt` to `z ∈ K` | 15 | **20** | plus the `ar ∈ K` discharge at the site |
| L8, `someEnv` | 30 | **35** | plus the same |
| the other six lemmas and the 28 entries | 181 | **181** | untouched by the refutation |
| | **271** | **about 261** | |

**So: about 260. It is LOWER than 270, as I predicted, but only just**, because
the delivered half bought back 20 lines and the discharges cost 10. **I give one
number and I do not widen it into a band (DD8).**

**Round it as ONE figure for the brief: step 6 is about 260, and the cure that
must precede it is about 190.** **Nobody should read 260 as the cost of getting
step 6 green from today: that number is about 450.**

## 39. WHY I STOPPED INSTEAD OF APPLYING THE RULING

**You ruled nine fields in one record, taking a hypothesis each. The sweep you
ordered in the same message measured that this is 21 fields in three records,
plus a new field, plus about ten telescopes in the master that has walled
twice.** **That is a different change from the one ruled, so AGENTS.md says
surface it with a recommendation rather than charge ahead on one reading.**

**And the ruling's own reasoning still holds.** One disease, one cure, and
curing part of it is the dangerous state. **The measurement does not argue
against your ruling. It argues that the ruling's scope was priced at one
record and the disease sits in three.**

## 40. PART FOUR: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **all ten are cured** | **MEASURED FALSE. NONE are.** `git diff src/` is empty |
| **the cure is nine fields in one record** | **MEASURED FALSE. 21 fields in three** |
| curing `TFacts` alone works | **MEASURED FALSE**, by running it. `TwelveAgree:409` goes red |
| `codesK` supplies both missing hypotheses | **MEASURED FALSE.** It supplies `ar ∈ K`, not the numeral equation. That needs a new field |
| **`KFacts` has the disease** | **MEASURED FALSE. It is CLEAN**, and section 36 says why that is the diagnostic contrast |
| the disease reaches `L.Condensation` | **TRUE**, as `envK` and `envInK` telescope parameters, 24 and 37 occurrences |
| any record outside the condensation cluster has it | **NOT CHECKED, and I mark it.** I swept the four records of this cluster and `L.BoundedSubset`; I did not sweep the whole tree |
| I left `src/` modified | **MEASURED FALSE.** The atomicity experiment was reverted and `TwelveAgree` re-typechecks green |
| step 6 is cheaper than 270 | **TRUE but barely: about 260**, and the cure at about 190 is not in that number |
| I ran `make check`, committed or pushed | **MEASURED FALSE**, none of the three |
| the 190 and the 260 are probe measurements | **NOT CLAIMED. Both are surveys**, counted by me at their own sites |

## 41. WHAT I RECOMMEND

1. **Re-rule the cure at its measured scope: 21 fields, three records, one new
   field, about ten telescopes, about 190 lines.** Same cure, same reasoning,
   correct extent.
2. **Gate it with ONE telescope first.** Change `envInK` in a single `*Agree`
   module and typecheck `src/L/Condensation.lagda.md` under the 40-minute
   criterion. **`[LJ-1.165]`'s wall is in that master and a telescope change is
   the operation that triggers it.** **GO if it comes in under the criterion;
   NO-GO and re-plan if it walls.**
3. **Then step 6 at about 260.**

**One line, and it is the fourth time.** `envSetK` measured one field. PART
THREE measured nine. This sweep measured twenty-one and a new field and ten
telescopes. **Each layer was found by looking one level out from the last, and
each was cheaper to find than to hit.**

---

# PART FIVE: the one-field gate

**Appended after the coordinator committed PART FOUR at `ee6c864` and re-ruled
at the measured scope.**

## 42. PART FIVE: CRITERIA, FIXED IN WRITING BEFORE THE FIRST RUN (D-1)

**The gate.** Cure ONE field, `envInK-mem`, through every record, telescope and
site it touches, then typecheck `src/L/Condensation.lagda.md`.

**`envInK-mem` is the right one and the coordinator's reason is the measured
one:** it needs only `ar ∈ K`, which `codesK` already concludes, so it isolates
the TELESCOPE cost from the NEW-FIELD cost that section 38.1 bundled.

**What "cold" means here, fixed before I measure it.** `L.Condensation`'s own
interface is deleted and rebuilt; every dependency stays warm. **That is the
figure a field change actually pays**, and it is NOT the tree's cold figure.

| outcome | condition |
|---|---|
| **GO** | `L.Condensation` typechecks, and the delta over its own baseline extrapolates to a price worth funding |
| **NO-GO, wall** | it walls. **Cap at 40 minutes.** `[LJ-1.165]` measured this cluster uncured at 20 min 1 s and 9.14 GB. **A heap exhaustion is a wall, never a failure** |
| **NO-GO, price** | it typechecks but 21 times the per-field delta exceeds what step 6 is worth. **Say so and stop** |

**Method.** ONE agda process. `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.
**Two runs per side, the first DISCARDED as warm-up**, and the machine load
reported beside every absolute figure.

**I do not move this criterion after I see a number.**

## 43. THE IMPORT-AGAINST-FIELD QUESTION, ANSWERED: NEITHER

**You asked me to spend ten minutes on whether the frame can RECEIVE
`src/L/Coding/CodeSet.lagda.md` instead of taking a new field. I did, and the
answer is that both options are wrong. There is a third and it is cheaper than
either.**

### 43.1 The import is ALREADY THERE, and it does not help

**MEASURED: `src/L/Condensation.lagda.md:55` reads**

```agda
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
```

**So the master already imports that chapter. The import was never the
obstacle.**

**And it still does not help, for a reason that is about the frame and not about
the import.** `codesK`'s antecedent is `⟨ fst c ∈ fst (lookup C γ) ⟩`, a bare
membership in **whatever the `C` slot happens to hold**. **Nothing in the frame
says the slot holds the code set.** `arityNumAtL` is a statement about the code
set; the frame never learns that its slot is one. **Only the INSTANTIATOR knows
that, so the fact has to arrive as a hypothesis. An import cannot supply it.**

**I also checked the one name that looked like it might already be the fact.**
`keyArityAtL` (`src/L/Coding/CodeSet.lagda.md:135-136`) is
`∃̇ (tagAtL (suc c) k zero)`: **a FORMULA, at a FIXED metalevel numeral `k`.**
It says "this code's arity tag is `k`", not "this code's arity is SOME
numeral". **It is not the reader, and I mark that I checked it rather than
assumed it.**

### 43.2 The third option: no new field, one extra component on `codesK`

**`codesK` already exists in all three records, it already takes exactly the
right antecedents, and it already returns a tuple:**

```agda
    codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup … C …) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ K ⟩ × ⟨ fst a ∈ K ⟩ × ⟨ fst b ∈ K ⟩
```

`src/L/Condensation/TwelveAgree.lagda.md:161-165`. **Add a fourth component,
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, and the numeral arrives with no new name.**

**And it reaches every site that needs it. MEASURED, module by module:**

| `*Agree` module | `codesK` param | `envK` / `envInK` params |
|---|---:|---:|
| `BotAgree` `:2774` | 1 | **0** |
| `TopAgree` `:3659` | 2 | 7 |
| `NegAgree` `:3725` | 2 | 4 |
| `MemAgree` `:4373` | 1 | 4 |
| `AllInAgree` `:4965` | 1 | 4 |
| `ExInAgree` `:5086` | 2 | 4 |
| `ImpAgree` `:5206` | 2 | 6 |
| `EqAgree` `:5299` | 1 | 4 |

**EVERY module that hosts a diseased parameter already hosts `codesK`.**
`BotAgree` is the one with no environment parameter at all, which is right: the
false row binds no environment set.

**So the new field is REFUTED as the cheapest route, and I recommend the fourth
component instead.** **It removes the "new field × three records" line from
section 38.1 and, more importantly, it removes a NEW PARAMETER from about ten
telescopes — which is the operation the wall risk attaches to.**

## 44. THE ONE FIELD'S SITE LIST, MEASURED BEFORE THE EDIT

**`envInK-mem` touches EIGHT places and I found every one by `grep` and then
read each.**

| # | `file:line` | what changes |
|---|---|---|
| 1 | `src/L/Condensation/TwelveAgree.lagda.md:203` | the `TFacts` field type |
| 2 | `src/L/Condensation/LowerAgree.lagda.md:149` | the `LFacts` field type |
| 3 | `src/L/Condensation.lagda.md:4399` | `MemAgree`'s `envInK` telescope entry |
| 4 | `src/L/Condensation.lagda.md:5325` | `EqAgree`'s `envInK` telescope entry |
| 5-8 | `:4431`, `:4453`, `:5357`, `:5379` | the four partial applications `(envInK yc b a ar c E)` |

**`UFacts` does NOT carry `envInK-mem`**, so two records move and not three.
`TwelveAgree:407` (`envInK-mem = envInK-mem`) and `LowerAgree:241, :248` stay
VERBATIM, because both sides move together.

### 44.1 THE FIND THAT CHANGES THE PRICE: the witness is already bound

**MEASURED at all four application sites. The line IMMEDIATELY ABOVE each one
reads**

```agda
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E)
```

**`arK` is already in scope and already passed to the sibling argument.** It
comes from `(arK , (aK , bK)) = codesK c ar a b c∈ shEq` a few lines up.

**So each site is a ONE-TOKEN edit: `(envInK yc b a ar c E arK)`.** **My section
38.1 survey priced these at 3 to 5 lines each. MEASURED: they are zero lines
each, plus one token.**

**And the reason is structural rather than lucky.** `module EnvSet`
(`src/L/Condensation.lagda.md:2925-2933`) already takes
`(ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)` **as a parameter of its
own.** **The cure asks `envInK` for a fact its own call site already had to
produce for the module beside it.** **That is why the four cheap fields are
cheap: the hypothesis was already computed and thrown away.**

## 45. THE BASELINE, measured before the edit

**`src/L/Condensation.lagda.md`, own interface deleted, dependencies warm.**

| run | wall | exit | load average at the run |
|---|---:|---|---|
| 1, **DISCARDED as warm-up** | 115 s | 0 | 2.26 2.33 3.18 |
| 2, **the figure** | **114 s** | 0 | 2.14 2.34 3.08 |

**BASELINE = 114 s.** One agda process, `GHCRTS="-A64m -I0 -M8g"`, cap not
raised. **The two runs agree to within 1 s, so the figure is stable and the load
did not move it.**

**And the first thing to say about it is a correction to my own risk note.**
Section 38.1 warned that a telescope change in this master might hit
`[LJ-1.165]`'s uncured wall at 20 min 1 s and 9.14 GB. **MEASURED: the master
typechecks in 114 s from its own cold interface.** **The wall `[LJ-1.165]` hit
was NOT `L.Condensation` re-elaborating; it was a different target.** **So my
risk note was right to be raised and wrong in its size, and I record that
before the delta rather than after it.**

## 46. THE TRUNCATION RISK, CHECKED BEFORE THE COMPONENT IS WRITTEN

**You asked me to confirm that each of the five dear fields concludes into a
PROPOSITION, because a truncated existential eliminates only into one. I
checked all five. The truncated form is safe, and I give the two reasons
separately because they are different facts.**

### 46.1 Every one of the five concludes an hProp. MEASURED

`src/L/Condensation/TwelveAgree.lagda.md:183-202`. **All five conclude**

```agda
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

**`⟨ P ⟩` for `P : Ω` is a proposition by construction**, so `PT.rec` eliminates
into it. **MEASURED, by reading all five conclusions, not one and a
generalization.** The same holds for the four `envInK-*`
(`:203-215`), which conclude `⟨ fst z ∈ … ⟩`.

### 46.2 And no conclusion MENTIONS the numeral. MEASURED

**This is the half that actually decides it, and it is separate from 46.1.** A
prop conclusion is not enough on its own: if the conclusion's TYPE mentioned
`n`, the numeral would be needed computationally and no truncation would
survive.

**MEASURED: it does not.** The cured `envSetK`
(`src/L/Condensation/TwelveAgree.lagda.md:281-285`) concludes
`⟨ fst (Generic.envSetGen B ar) ∈ … ⟩`. **The conclusion names `ar`, never
`n`.** `n` appears only in the hypothesis `fst ar ≡ # n`, so it is consumed
inside the proof and never escapes into a type.

**So the numeral is used PROPOSITIONALLY at every one of the ten sites, and the
truncated fourth component on `codesK` eliminates.** **The untruncated form is
NOT needed, and I do not price it.**

### 46.3 One consequence for the price, and it sharpens section 44.1

**The four cheap fields stay ONE-TOKEN edits at their sites**, because `arK` is
an ordinary term already in scope.

**The five dear fields do NOT.** Each site must eliminate the truncation before
it can apply the field:

```agda
        EK = PT.rec (snd (fst E ∈ fst (lookup K γ)))
               (λ { (n , q) → envK yc a ar c E n q hE }) arNum
```

**So budget about 2 lines per dear site rather than one token.** **MEASURED as a
shape from the delivered `PT.rec` idiom, INFERRED as a line count, because I
have not written one.**

## 47. THE 115 s AGAINST 20 min 1 s, ADDRESSED

**One line first: the two figures were never about the same target, and
attaching one to the other was MY error, not a cured wall and not a
mismeasurement.**

**MEASURED, from the primary source rather than from a summary.**
`agents/tasks/LJ-1-165/lj-1.165-report.md:144` and `:298-311` put wall 2 at
**`σ₁-up` applied to the level-hood Levy witness**. `σ₁-up` is
`src/FOL/Absoluteness.lagda.md:182`, and the level-hood certificate is the
`src/L/BoundedSubset.lagda.md` work. **`L.Condensation` is not the target and
never was.**

**So my section 38.1 risk note transferred a measured wall by ANALOGY to a
different site, which is exactly what `dev/LESSONS.md` P-l forbids.** **P-l says
re-measure a cure at its own site; the same binds a WALL, and I did not apply it
to my own note.** **The 114 s is `L.Condensation`'s real figure and the 20 min 1 s
still stands, undisturbed, at `σ₁-up`.**

**And a figure drifted on the way here, which I flag because it is the pattern
this project has measured before.** `[LJ-1.165]:144` records **9.40 GB**.
`agents/tasks/LJ-1-172/lj-1.172-report.md:895-898` reports the same wall as
**9.14 GB**, and my PART FOUR repeated the 9.14 from that summary. **The primary
is 9.40. Nothing turns on the 0.26 GB, and that is the point: it drifted because
three documents quoted it and none re-read the first.**

**What this does NOT license.** It does not say the cluster is safe. It says
**`L.Condensation` re-elaborates in 114 s**, and that the wall belongs to a
different master which this cure does not touch. **Marked MEASURED, both
halves.**

## 48. THE GATE: GO. +6 s PER FIELD, and about +126 s for all twenty-one

**MEASURED. Same machine, same session, same cap, one agda process throughout,
warm-up discarded on both sides.**

| side | run 1, DISCARDED | run 2, **the figure** | load at the figure |
|---|---:|---:|---|
| baseline | 115 s | **114 s** | 2.14 2.34 3.08 |
| one field cured | 122 s | **120 s** | 2.70 2.38 2.84 |
| **delta** | | **+6 s** | |

**PER-FIELD COST: +6 s, which is +5.3 percent of the master's own cold
figure.** Both sides agree across their two runs to within 2 s, so the 6 s is
above the noise but not far above it, and I say that rather than let the reader
assume precision I did not measure.

**TIMES TWENTY-ONE, the figure you asked for: +126 s, taking
`src/L/Condensation.lagda.md` from 114 s to about 240 s.**

**And I mark that extrapolation as an OVER-estimate, with the reason.** The 21
fields do NOT each add a fresh telescope: they share the same eight `*Agree`
modules (section 43.2's table). **`envInK-mem` alone moved 2 of about 20
telescope entries, so 21 times its cost double-counts the modules the fields
share.** **The true figure is between +126 s and something smaller, and only
the full cure measures it.** **I do not quote a smaller number I have not
measured.**

**VERDICT: GO.** **A cure that takes one master from 114 s to at most 240 s is
fundable against a step 6 priced at about 260 lines.** **The wall risk that
made this gate necessary is measured away for THIS master** (section 47), and
nothing came within two orders of magnitude of the 40-minute cap.

## 49. THE STAGING QUESTION, ANSWERED FROM THE GATE AND NOT BY ARGUMENT

**YES. The cheap four stage independently of the dear five, and the gate proves
it rather than predicting it.**

**MEASURED: `git diff src/ | grep -c "^[+-].*envK-"` returns ZERO.** **Not one
line of any `envK-*` field moved, and the tree is green**: `L.Condensation`,
`LowerAgree`, `UpperAgree` and `TwelveAgree` all at exit 0, verified by explicit
exit code and not by absence of output.

**Your expectation was right and now it is measured.** The pass-through couples
the records **per FIELD NAME** — `TFacts.envInK-mem` to `LFacts.envInK-mem` —
and nothing couples `envInK-mem` to `envK-mem`. **They are different names with
different pass-throughs.** So the split is real:

| stage | fields | needs the `codesK` component? | measured cost |
|---|---:|---|---|
| **cheap first** | the four `envInK-*` | **NO.** `ar ∈ K` is already bound at every site | **+6 s and about +6 lines per field**, measured on one of the four |
| **dear second** | the five `envK-*` | **YES**, plus a `PT.rec` per site | not measured |

**So the cheap four can land NOW, on this measurement, and the new-field
decision is deferred to the five.** **That is a smaller first landing and it
de-risks the component exactly as you hoped.**

## 50. THE PER-FIELD LINE COST, MEASURED

```
8	6	src/L/Condensation.lagda.md
3	1	src/L/Condensation/LowerAgree.lagda.md
3	1	src/L/Condensation/TwelveAgree.lagda.md
```

**+14 lines, -8 lines, NET +6 for one field**, covering 2 record fields, 2
telescope entries and 4 application sites.

**Against my section 38.1 survey, which priced the sites at 3 to 5 lines each
and the whole cure at about 190: the measured per-field figure is +6 lines, so
the four cheap fields are about +24 lines, not about 80.** **The survey was
high by roughly a factor of three on this half, and I record that against my own
number rather than quietly replacing it.**

## 51. THE STATE OF THE TREE, said plainly

**`src/` carries the one-field cure and it is GREEN.** That is **1 of 21**, and
**it is the partial state I myself called dangerous in PART FOUR.**

**I left it rather than reverting, and here is the reason and the risk, so you
can rule either way in one line.**

- **Why left:** it typechecks, it is the gate's artifact, and it is the first
  member of the cheap stage that section 49 measures as landable now.
- **The risk, unchanged from PART FOUR:** the tree now holds twenty statements
  that LOOK like the cured one and are not. **`envInK-mem` is cured;
  `envInK-neg`, `envInK-top`, `envInK-imp` and the five `envK-*` are not.**
- **Reverting costs nothing:** I backed up all three masters before the edit and
  the revert is a plain `cp`. **I used no `git checkout`, no `stash`, no
  `reset`, no `clean` at any point.**

**My recommendation is to complete the cheap four rather than revert**, because
the measurement now exists and the four are one field's work each.

## 52. PART FIVE: CHECKERS

| checker | result |
|---|---|
| `agda` on `L.Condensation`, `LowerAgree`, `UpperAgree`, `TwelveAgree`, `Key` | **exit 0**, all five, verified by explicit exit code |
| `postulate`, hole, unsolved meta | **all three ABSENT.** Agda printed no warning on any run |
| `lint-agda.py --check` | **exit 0** |
| `lint-prose.py --check` on the three edited masters | **exit 0** |
| `weave-i18n.py --check` | **exit 0** |
| `check-unbound-hyp.py` | **2**, unchanged |
| `check-probes.py` | **clean**, 1805 tracked files |
| `make check` | **NOT RUN.** Yours |
| agda invocations in PART FIVE | **11.** ONE process at a time, `-M8g` never raised, no heap wall, nothing near the 40-minute cap |

## 53. PART FIVE: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the gate walls** | **MEASURED FALSE. 120 s against a 40-minute cap** |
| **the cheap four need the new field** | **MEASURED FALSE.** Zero `envK-*` lines moved and the tree is green |
| the sites cost 3 to 5 lines each | **MEASURED FALSE.** One token each; the witness `arK` was already bound |
| my 190-line survey was accurate | **MEASURED FALSE on this half. High by about three times** |
| **`[LJ-1.165]`'s 20-minute wall is in `L.Condensation`** | **MEASURED FALSE.** It is at `σ₁-up`, and attaching it here was MY analogy error against P-l |
| the wall figure was 9.14 GB | **MEASURED FALSE. The primary says 9.40 GB**; 9.14 is a drift through two summaries |
| the first cure attempt worked | **MEASURED FALSE.** It failed at `:4432`: the hypothesis must precede the bound `z`, not follow the set telescope |
| a new field is the cheapest route to the numeral | **MEASURED FALSE.** A fourth component on `codesK` reaches every site with no new parameter |
| an import can supply the numeral | **MEASURED FALSE.** The frame is abstract over its `C` slot; only the instantiator knows it holds the code set |
| `keyArityAtL` is the reader | **MEASURED FALSE.** It is a formula at a FIXED numeral |
| the truncated component is unsafe | **MEASURED FALSE.** All ten conclusions are hProps and none mentions `n` |
| the times-twenty-one figure is a measurement | **NOT CLAIMED. It is a linear extrapolation from ONE field**, and an over-estimate because the fields share telescopes |
| the whole cure is now priced | **NOT CLAIMED.** The dear five are unmeasured |
| I ran `make check`, committed or pushed | **MEASURED FALSE**, none of the three |

## 54. WHAT I RECOMMEND

1. **Land the cheap four.** Measured: +6 s and +6 lines each, no new field, the
   witness already bound. **About +24 s and +24 lines for the stage.**
2. **Then rule the `codesK` fourth component** and land the dear five, budgeting
   about 2 lines per site for the `PT.rec`.
3. **Then step 6 at about 260.**

**And one correction to carry forward, because it is mine.** **I attached a
measured wall to a master it was never measured at, and the gate you ordered is
what caught it.** **P-l says a measured cure does not transfer by analogy. A
measured WALL does not either, and I will state it that way if the owner takes
your law.**

## 55. ONE THING IN THE WORKING TREE THAT IS NOT MINE

**`git status --porcelain` shows an untracked
`agents/tasks/LJ-1-175/lj-1.175-report.md`.** **I did not create it, I have not
opened it, and I did not touch it.** **I flag it because I am reporting on the
state of this working tree and it is not all mine.**

**My own changes are exactly four files:**

```
 M agents/tasks/LJ-1-173/lj-1.173-report.md
 M src/L/Condensation.lagda.md
 M src/L/Condensation/LowerAgree.lagda.md
 M src/L/Condensation/TwelveAgree.lagda.md
```

---

# PART SIX: the cheap four

**Appended after the coordinator accepted the GO and ruled the four-stage
order.**

## 56. A CORRECTION TO MY OWN PART FIVE, and it is the first thing to say

**I wrote that the +6 s per-field delta was "above the noise but not far above
it". MEASURED FALSE. It is INSIDE the noise, and the project had already
measured the band I failed to check it against.**

**`scripts/check-ratio.py` prints the band in its own header:**

> noise band: at least +-12.8%, MEASURED [LJ-1.148] 2026-08-13, eight separate
> warmed series on `src/L/Ordinal/StageArith.lagda.md`, quiet machine

**+6 s on a 114 s baseline is +5.3 percent. The band is at least ±12.8 percent.
So the delta is NOT ESTABLISHED at n=1**, and my PART FIVE sentence claimed a
resolution the instrument does not have.

**And an independent run says the same thing.** `check-ratio.py`, run on the
tree WITH `envInK-mem` already cured, measured
`src/L/Condensation.lagda.md` at **113.57 s**. **My own measurement of that same
tree was 120 s.** **Two measurements of ONE tree, 6.4 s apart — which is the
whole of the delta I attributed to the cure.**

**So the honest per-field figure is: BELOW THE INSTRUMENT'S RESOLUTION.**
**That is a stronger GO than +6 s, not a weaker one**, and I record it against
my own number rather than let the +126 s extrapolation stand on a delta that
was never established.

**What survives of PART FIVE's arithmetic.** The +126 s band was already marked
an over-estimate. **It is now an over-estimate resting on an unestablished
per-field cost, so the honest statement is: the cure's seconds are not
measurable one field at a time, and only the four-field and full-cure figures
can carry a number.** **That is exactly why you asked for the four measured
together, and the reason applies harder than either of us wrote.**

## 57. THE WING RATIO BEFORE THIS STAGE

**MEASURED, `scripts/check-ratio.py`, on the tree with `envInK-mem` cured and
the other twenty not.** **So this is "after stage zero", not the pristine
figure, and I mark it rather than call it a baseline.**

```
AC baseline 0.0091 s/line (module-cold, warm dependencies) | tolerance 1.15x
                                                           | bar 0.0105 s/line
wing aggregate 0.0139 s/line over 11,825 lines and 164.60 s, OVER THE BAR
                              (1.52x the AC side at the SAME caliber)
```

| the wing's rows, as measured | s/line | lines | seconds |
|---|---:|---:|---:|
| `src/L/Condensation.lagda.md` | **OVER** 0.0172 | 6,622 | 113.57 |
| `src/L/Condensation/TwelveAgree.lagda.md` | **OVER** 0.0172 | 475 | 8.17 |
| `src/L/Condensation/UpperAgree.lagda.md` | **OVER** 0.0186 | 290 | 5.40 |
| `src/L/Condensation/LowerAgree.lagda.md` | **OVER** 0.0171 | 293 | 5.00 |
| `src/L/BoundedSubset.lagda.md` | OVER 0.0110, **NOISE: the swing crosses the bar** | 1,409 | 15.44 |
| **the wing** | **0.0139, 1.52x** | **11,825** | **164.60** |

**Your brief says 1.60x and I measure 1.52x.** **I do NOT report that as a
correction**, because the two sit well inside the ±12.8 percent band the same
tool prints. **They are one figure measured twice.**

**And the trade is exactly as you framed it.** The four masters this cure
touches are four of the five rows already OVER the bar, and they carry 7,680 of
the wing's 11,825 lines. **A correctness cure lands on the wing's most expensive
rows.** **I will not soften that and I will not delete a line to improve it: P-q
measured 315 lines removed buying 11.8 seconds, and DD24's own row refuses the
shrinking denominator.**

## 58. STAGE TWO PRICED BEFORE IT IS BUILT: the `codesK` component

**You ruled the fourth component and said it adds no parameter to any telescope.
MEASURED: that is right, and it is not the whole cost. I measured the rest
before starting it.**

| what moves | count | how I counted |
|---|---:|---|
| `codesK` occurrences in `src/L/Condensation.lagda.md` | **47** | `grep -c` |
| `codesK` telescope entries there | **about 15** | `grep -n "  (codesK"` |
| **sites that DESTRUCTURE its result** | **12** | `grep -nE "= codesK "` |
| the field in the three records | 3 | `codesK` at `TwelveAgree:161-165` and its two siblings |

**The destructuring sites are the part your ruling does not cover, and they are
the reason the component is not free.** They read

```agda
        (arK , (aK , bK)) = codesK c ar a b c∈ shEq
        (arK , aK)        = codesK c ar a c∈ shEq
```

**A fourth component makes every one of these a four-tuple pattern**, so twelve
sites move by one token each. **No new parameter, as you ruled; twelve pattern
edits, which nobody had counted.**

**And `codesK` comes in TWO arities**, `(c ar a b : S)` and `(c ar a : S)`
(`src/L/Condensation.lagda.md:2779` against `:3288`), plus `codesK-un` in the
records. **So the component has to be added consistently to both, or the
suppliers will not line up.**

**Stage two's price, ONE number naming its basis: about 40 lines.** 3 field
declarations, about 15 telescope entries and 12 destructuring sites, at roughly
one line each plus the suppliers. **Basis: the four counts above, taken by me
at their own sites. It is a survey and my last survey on this family was high
by three times, so treat it as an upper bound.**

## 59. THE CHEAP FOUR: MEASURED, and the cure is free at this resolution

**Applied across all three records and every site.** MEASURED by the edit
script's own counts, then by `git diff`:

| what moved | count |
|---|---:|
| field declarations, three records | **10** (`envInK-mem` 2, `-neg` 3, `-top` 2, `-imp` 3) |
| telescope entries in `src/L/Condensation.lagda.md` | **10** |
| application sites | **18 matched, 14 changed**, the other 4 already cured |
| `envK-*` lines touched | **ZERO**, re-measured after the edit |

**Line cost: +68, -38, NET +30 for all four fields**, against my PART FIVE
per-field figure of +6 which would have predicted +24. **Close, and I report the
measured +30 rather than the predicted +24.**

### 59.1 The seconds

| tree | run 1 | load |
|---|---:|---|
| baseline, no field cured | 114 s | 2.14 2.34 3.08 |
| ONE field cured | 120 s | 2.70 2.38 2.84 |
| **FOUR fields cured** | **115 s** | 3.60 2.93 2.84 |

**FOUR fields cost 115 s against a 114 s baseline: +1 s, or +0.9 percent.**

**This settles section 56 rather than merely supporting it.** The one-field
figure of 120 s and the four-field figure of 115 s are **not ordered by the
amount of work done**. **Four fields measure CHEAPER than one.** **That is only
possible if both deltas are noise**, and the ±12.8 percent band says exactly
that.

**So: the cheap cure's cost in seconds is NOT MEASURABLE, and my +126 s
extrapolation is withdrawn.** **It was built on a per-field delta that this run
shows was never there.** **I do not replace it with a smaller number: I replace
it with "below the instrument's resolution", which is what was measured.**

**Peak resident memory during the run: about 3.5 GB, well under the 8 GB cap.
No heap wall.**

### 59.2 The second run, and the C-40 verdicts

| tree | run 1 | run 2 | verdict |
|---|---:|---:|---|
| **four fields cured** | 115 s | **115 s** | **identical across two runs** |

**Two runs at 115 s exactly.** **The four-field figure is more stable than
either the baseline (115, 114) or the one-field measurement (122, 120), which
is a further sign that the 6 s I reported in PART FIVE was drift and not
cost.**

**C-40, discharged in full, by explicit exit code and not by absence of
output:**

| master | exit |
|---|---|
| `src/L/Condensation.lagda.md` | **0** |
| `src/L/Condensation/LowerAgree.lagda.md` | **0** |
| `src/L/Condensation/UpperAgree.lagda.md` | **0** |
| `src/L/Condensation/TwelveAgree.lagda.md` | **0** |

**And the stage is still clean after the full four-field edit: `git diff src/ |
grep -c "^[+-].*envK-"` returns ZERO.** **The four cheap fields landed without
one line of the five dear ones moving**, which is the staging claim measured a
second time on four times the work.

### 59.3 Checkers

| checker | result |
|---|---|
| `lint-agda.py --check` | **exit 0** |
| `lint-prose.py --check`, four edited masters | **exit 0** |
| `weave-i18n.py --check` | **exit 0** |
| `check-unbound-hyp.py` | **2**, unchanged |
| `check-probes.py` | **clean**, 1807 tracked files |
| `postulate`, hole, unsolved meta | **all three ABSENT** |
| `make check` | **NOT RUN.** Yours |

## 60. PART SIX: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **the cheap four are landed and green** | **TRUE.** Four masters at exit 0, verified by exit code |
| **the per-field cost is +6 s** | **MEASURED FALSE, and it was MY claim.** Four fields cost +1 s; one field measured +6 s. Both are inside the ±12.8 percent band |
| **the times-twenty-one figure of +126 s** | **WITHDRAWN.** It rested on a delta this run shows was never established |
| four fields cost more than one | **MEASURED FALSE. 115 s against 120 s.** The ordering is impossible unless both deltas are noise |
| the cure needed the `envK-*` fields to move | **MEASURED FALSE. ZERO** `envK-*` lines moved, re-measured after the full four-field edit |
| the cure walled or exhausted the heap | **MEASURED FALSE.** About 3.5 GB peak against an 8 GB cap, and 115 s against a 40-minute criterion |
| my PART FIVE line prediction was exact | **MEASURED FALSE.** It predicted +24 lines and the measurement is +30 |
| the wing ratio is 1.60x | **NOT CORRECTED. I measure 1.52x** and the two sit inside the tool's own ±12.8 percent band, so they are one figure measured twice |
| the `codesK` component adds no work beyond the field | **MEASURED FALSE.** It adds **12 destructuring sites**, which your ruling did not cover and nobody had counted |
| stages two, three and four are started | **MEASURED FALSE. None of them.** Section 61 says what that leaves |
| I ran `make check`, committed or pushed | **MEASURED FALSE**, none of the three |
| the four-field seconds are a cold tree figure | **NOT CLAIMED.** Module-cold with warm dependencies, the same caliber as `check-ratio.py` |

## 61. WHAT THIS LEG LANDED, AND WHAT IT DID NOT

**LANDED: stage one, the cheap four, complete across all three records and every
site, green, and measured free at this instrument's resolution.**

**NOT STARTED: stages two, three and four.** I priced stage two at about 40
lines with its twelve destructuring sites named (section 58). **Stage three, the
dear five, and stage four, the step 6 re-price, are untouched and I did not
begin them.**

**Why I stopped here rather than pressing on.** **Most of this leg went into
measurement and into correcting two of my own figures** — the per-field delta
and the +126 s extrapolation, both withdrawn on evidence I generated after
publishing them. **A fourth stage started on a tired budget is how a figure like
the +6 s gets into a report in the first place.** **Four measured numbers hand
over better than four half-built stages.**

**The tree is green and coherent, and here is the count done properly, because
I got it wrong once in this very section before checking it.**

| family | field NAMES | DECLARATIONS across the three records | state |
|---|---:|---:|---|
| `envInK-*` | 4 | **10** (`mem` 2, `neg` 3, `top` 2, `imp` 3) | **CURED** |
| `envK-*` | 5 | **11** (`mem` 2, `neg` 3, `top` 2, `imp` 2, `allin` 2) | still diseased |
| | **9** | **21** | |

**So eleven declarations remain, under five names, and they are exactly the dear
family.** **The four cheap names are done in every record that carries them.**
**That is the clean stage boundary your ruling asked for, not a partial edit.**

## 62. THE WING RATIO AFTER THE CHEAP FOUR

**MEASURED, `scripts/check-ratio.py`, same tool and same caliber as section 57.**

| | before this stage (one field cured) | **after (four cured)** | change |
|---|---:|---:|---:|
| wing aggregate | 0.0139 s/line | **0.0141 s/line** | **+0.0002** |
| against the AC side | 1.52x | **1.54x** | **+0.02x** |
| wing lines | 11,825 | 11,849 | +24 |
| wing seconds | 164.60 | 167.01 | +2.41 |
| `src/L/Condensation.lagda.md` | 0.0172, 113.57 s | 0.0175, 115.95 s | +2.38 s |
| `TwelveAgree` | 0.0172, 8.17 s | 0.0172, 8.25 s | +0.08 s |
| `UpperAgree` | 0.0186, 5.40 s | 0.0185, 5.47 s | +0.07 s |
| `LowerAgree` | 0.0171, 5.00 s | **0.0165**, 4.89 s | **-0.11 s** |

**THE BAR MOVED FROM 1.52x TO 1.54x, and I report it without softening it.**

**But the reading that matters is that this is +1.4 percent against a band of at
least ±12.8 percent, so the movement is NOT ESTABLISHED by this run.** **One row,
`LowerAgree`, got FASTER while gaining lines.** **A cure cannot make one master
faster and its siblings slower; that spread is the instrument, and it is the
third independent sign of the same thing this leg has now measured three
times.**

**The honest summary of the DD24 consequence you asked me to state:**

- **The wing was over the bar before this cure and it is over the bar after it.**
  1.52x and 1.54x against a 1.15x tolerance. **The cure did not put it there and
  the cure cannot take it out.**
- **The cure's own contribution is +24 wing lines and about +2.4 s, and neither
  is separable from noise.**
- **It is still the right trade**, and it is a CORRECTNESS trade: **eleven false
  statements remain in the tree and ten fewer stand than this morning.**
- **I deleted no line to improve the ratio.** P-q measured 315 lines removed
  buying 11.8 s, and DD24's own row refuses the shrinking denominator.

**One accounting note, so the two line figures reconcile.** `git diff` reports
**net +30 lines from HEAD**, which has NO field cured. The ratio tool reports
**+24**, because its "before" run already had `envInK-mem` cured. **Both are
right against their own baseline and neither is the other's error.**

---

# PART SEVEN: stages two, three and four

**Appended after the coordinator committed stage one at `a01ef58`, ruled stage
two, and then STRUCK the DD27 reading he had ruled one message earlier.**

## 63. SIBLING CHECK FIRST, as instructed

**`git status --porcelain` was EMPTY for `src/` before I touched anything.**
HEAD is `142637c [LJ-1.177] …`, and my stage one is `a01ef58` beneath it.
**The sibling committed after me and left nothing uncommitted. I found no dirty
file I did not touch, so I proceeded.**

## 64. STAGE TWO LANDED: the `codesK` fourth component, +45 lines

**GREEN on all four masters.** The component is

```agda
                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

added to the conclusion of `codesK` and `codesK-un` in all three records, and to
every telescope of that shape in `src/L/Condensation.lagda.md`.

| what moved | count |
|---|---:|
| record field declarations (`codesK`, `codesK-un` × 3 records) | **6** |
| import lines added, one per record | 3 |
| telescope entries in `L.Condensation`, **first pass by name** | 19 `codesK` + 5 `unCodesK` + 4 `compK`/`unCompK` |
| telescope entries, **second pass by SHAPE** | **29** |
| result bindings with an explicit tuple annotation | 4 |
| projection sites (`ks .snd .snd` to `ks .snd .snd .fst`) | 6 |
| destructuring sites | **11** (6 binary, 5 unary) |

**LINE COST: +93, -48, NET +45.** **My survey said about 40 and called itself an
upper bound. The measurement is 45.** **That is the first survey in this task to
land close, and it landed 12 percent HIGH of my estimate rather than three times
high.**

### 64.1 What the name-based pass missed, and it is the reusable lesson

**I patched by NAME first and Agda refused four times.** The same field arrives
in `src/L/Condensation.lagda.md` under **four different local names** —
`codesK`, `unCodesK`, `compK`, `unCompK` — and `ShapesAgree`
(`:6101-6116`) binds its arity as **`N`, not `ar`**.

**The fix that worked was to patch by SHAPE rather than by name**: every
telescope entry whose body carries the code equation
`fst c ≡ pr (fst X) (pr (# k) …)`, taking `X` as that entry's own arity binder.
**One pass, 29 entries, and the four aliases stopped mattering.**

**MEASURED cost of the wrong approach: four agda rounds at about two minutes
each.** **A rename-blind edit in this master is worth writing shape-first from
the start.**

### 64.2 Checkers after stage two

| checker | result |
|---|---|
| `agda` on `L.Condensation`, `LowerAgree`, `UpperAgree`, `TwelveAgree` | **exit 0**, all four |
| `postulate`, hole, unsolved meta | **all three ABSENT** |
| `lint-agda.py --check` | **exit 0** |
| `lint-prose.py --check`, four masters | **exit 0** |
| `weave-i18n.py --check` | **exit 0** |
| `check-unbound-hyp.py` | **2**, unchanged |
| `make check` | **NOT RUN.** Yours |

## 65. THE DD27 CORRECTION, RECORDED

**The coordinator ruled that step 6 would be priced against
`ac_baseline_module_rate` 0.009143 at 1.00x, then struck that ruling as his own
misreading. DD24 is unchanged and the bar does not drift.**

**Nothing in stages two or three was built against the struck figure.** They are
correctness work and no ratio was ever going to decide them. **And I record the
strike rather than quietly dropping it, because a figure that appeared in a
brief and then vanished is exactly the kind that drifts back in later.**

**For stage four I will report step 6's lines and seconds as measured, record
any overage plainly per DD8, and judge it against nothing.**

## 66. STAGE THREE LANDED: all twenty-one fields are now cured

**GREEN on all four masters, FIRST agda run.** **The disease is out of the
tree.**

| what moved | count |
|---|---:|
| dear field declarations | **11** (TFacts 5, LFacts 3, UFacts 3) |
| `envK` telescopes in `L.Condensation` carrying `envSetAt` | **10** |
| application sites | **9**, one token each |

**Stage two plus three together: +155, -78, NET +77 lines above stage one's
commit.** Stage two was +45 of that, so **stage three is +32.**

### 66.1 A CHEAPER FORM THAN I PRICED, and it removes the `PT.rec`

**My section 46.3 priced about 2 lines per dear site for a `PT.rec` to
eliminate the truncation. MEASURED: none is needed, and the reason is the same
one that made the cheap four cheap.**

**I gave the FIELD the truncated hypothesis directly:**

```agda
    envK-mem : (yc b a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ … ⊨ envSetAt … ⟩
               → ⟨ fst E ∈ … ⟩
```

**So the site is `envK yc a ar c E arNum hE`: ONE TOKEN, and `arNum` is already
bound by stage two's `codesK` component a few lines above.** **The truncation
elimination moves INTO the field's eventual supplier, where it happens ONCE,
instead of eleven times at the consumers.**

**The field is exactly as strong either way** — it concludes an hProp and its
conclusion never mentions `n` (section 46) — **so this is a free saving of about
22 lines, and my own price for it is withdrawn.**

**That is the third time this task that a cure looked dear because nobody had
read the call site.** **`EnvSet` already took `ar∈K`; `codesK` already computed
`arK`; and now `arNum` is already bound where `envK` is applied.**

### 66.2 Completeness, checked rather than assumed

**I swept all nine field names across all three records for a declaration
without its hypothesis. NONE.** **`envK-mem`, `-neg`, `-top`, `-imp`, `-allin`,
`envInK-mem`, `-neg`, `-top`, `-imp`: twenty-one declarations, twenty-one
cured.**

### 66.3 Checkers after stage three

| checker | result |
|---|---|
| `agda` on the four masters | **exit 0**, all four |
| `postulate`, hole, unsolved meta | **all three ABSENT** |
| `lint-agda.py`, `lint-prose.py`, `weave-i18n.py` | **exit 0**, all three |
| `check-unbound-hyp.py` | **2**, unchanged |
| `make check` | **NOT RUN.** Yours |

## 67. THE WING RATIO AFTER STAGES TWO AND THREE

| | after stage one | **after stages two and three** | change |
|---|---:|---:|---:|
| wing aggregate | 0.0141 s/line | **0.0155 s/line** | +0.0014 |
| against the AC side | 1.54x | **1.69x** | **+0.15x** |
| wing lines | 11,849 | 11,926 | +77 |
| wing seconds | 167.01 | 184.68 | +17.67 |

**THE BAR MOVED FROM 1.54x TO 1.69x AND I AM NOT SOFTENING IT.**

**But this run carried a systematic shift, and I report it because otherwise the
+0.15x reads as all mine.** The tool itself printed

> note: no cached interface found for SquareLaw.lagda.md; this run is cold by
> construction

**and modules I did NOT touch moved with it:**

| untouched module | before | after | change |
|---|---:|---:|---:|
| `src/L/BoundedSubset.lagda.md` | 15.39 s | 16.40 s | **+6.6%** |
| `src/L/Ordinal/SquareLaw.lagda.md` | 7.90 s | 8.63 s | **+9.2%** |
| `src/L/Ordinal/StageArith.lagda.md` | 0.92 s | 1.02 s | **+10.9%** |
| `src/L/Condensation.lagda.md` (**touched**) | 115.95 s | 130.40 s | +12.5% |

**So the largest untouched module rose 6.6 percent in the same run that my
touched one rose 12.5 percent.** **INFERRED, and I mark it: the cure's own share
is the difference, of order 6 percent on `L.Condensation`, or about 7 s.**
**MEASURED: the whole +10.6 percent movement in wing seconds is inside the
±12.8 percent band, so it is not established at n=1 either way.**

**What I will not do is quote the 6 percent as the answer.** It is a difference
of two n=1 figures inside a band wider than both. **The honest statement is that
the wing rose in this run, that untouched modules rose too, and that separating
them needs more runs than a stage report should spend.**

**And the trade stands as you framed it.** **The wing must END inside the bar
and it is not there now.** **Twenty-one false statements left the tree for
seventy-seven lines.**

## 68. STAGE FOUR: STEP 6 RE-PRICED, and it is NOT judged against anything

**Per your correction: DD24 is unchanged, the bar does not drift, intermediate
debt is allowed, and only the whole GCH side is judged at the end. So I report
step 6's lines as measured-basis survey and its seconds as UNMEASURED, and I
judge it against nothing.**

**THE NUMBER: about 255 in-fence lines.**

**Basis, `[LJ-1.168]`'s own nine-lemma allocation
(`agents/tasks/LJ-1-168/lj-1.168-report.md:341-351`), with three lemmas
re-costed against work THIS TASK DELIVERED and one item added:**

| item | `[LJ-1.168]` | now | why it moved |
|---|---:|---:|---|
| L9, `envSetK` | 45 | **25** | `mkReflect` was refuted; `envSetNumeral∈` is DELIVERED in `src/L/Coding/Key.lagda.md`. What remains is the `envSet` to `envSetGen` identification through `NumeralFromGeneric.derived` |
| L4, `envOverAt` to `z ∈ K` | 15 | **12** | `ar ∈ K` is now a HYPOTHESIS the field receives, not something the supplier must find |
| L8, `someEnv` | 30 | **25** | same reason |
| **NEW: supply `codesK`'s numeral component** | — | **+15** | `arityNumAtL-out` at the code set, `src/L/Coding/CodeSet.lagda.md:189-197` |
| the other six lemmas | 154 | 154 | untouched by any of this |
| the 28 field entries | 42 | 42 | unchanged |
| | **271** | **about 255** | |

**SECONDS: NOT MEASURED. Step 6 is unbuilt, so it has no seconds, and I do not
project any.**

**OVERAGE, recorded plainly per DD8: NONE to record**, because 255 is below
`[LJ-1.168]`'s 271 and there is no other figure it was promised against.

**And I stop here, before building it, as instructed.**

## 69. PART SEVEN: EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **all twenty-one fields are cured** | **TRUE**, swept name by name across all three records |
| **the `PT.rec` costs about 2 lines per dear site** | **MEASURED FALSE, and it was MY price.** Giving the FIELD the truncated hypothesis costs one token per site and nothing else |
| patching by field NAME is enough | **MEASURED FALSE.** Four aliases and a different arity binder; four agda rounds lost. Patch by SHAPE |
| `KFacts` needed curing | **MEASURED FALSE.** It was clean and stays untouched |
| the wing's +0.15x is all the cure's | **MEASURED FALSE.** Untouched modules rose 6.6 to 10.9 percent in the same run |
| the cure's share is 6 percent | **NOT CLAIMED. INFERRED**, and it is a difference of two n=1 figures inside a wider band |
| step 6 is judged against 0.009143 at 1.00x | **STRUCK by the coordinator.** DD24 is unchanged and I judged step 6 against nothing |
| step 6 has measured seconds | **MEASURED FALSE. It is unbuilt.** Lines only, and those are a survey |
| I built step 6 | **MEASURED FALSE. I stopped before it**, as instructed |
| I ran `make check`, committed or pushed | **MEASURED FALSE**, none of the three |
| the tree was dirty when I started | **MEASURED FALSE.** `git status` was empty for `src/`, checked first as instructed |

## 70. WHAT THIS LEG LANDED

**Stage two: the `codesK` fourth component, +45 lines, four masters green.**
**Stage three: the five dear fields, +32 lines, four masters green on the first
run.** **Together +77 lines, and the disease is out of the tree: twenty-one of
twenty-one.**

**Stage four: step 6 re-priced at about 255 lines, seconds unmeasured, judged
against nothing, and NOT built.**

**The wing sits at 1.69x and must end inside 1.15x. That is real debt and it is
not this cure's to pay alone.**
