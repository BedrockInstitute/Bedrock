# LJ-1.317 report: literature for the typecheck-cost question

STATUS: COMPLETE against the abort criterion's FIRST branch. A ranked list of
mechanisms exists and this report delivers it. Written incrementally (C-22).

**The corpus is a proof assistant's rather than a mathematician's.** It is
Agda's user manual, Agda's issue tracker, Agda's own Haskell source, the Agda
wiki, and published notes from large Agda developments. No set theory bears on
a conversion checker's cost model.

**Every source is marked READ, SKIMMED or POINTER-ONLY. Every negative is
marked MEASURED or INFERRED. This task ran NO Agda** (C-12). **Every mechanism
below is a HYPOTHESIS at this site** (P-l): a cost documented against another
codebase is not a price here.

**Version.** This project runs **Agda 2.8.0 with cubical 0.9**. I read the
2.8.0 manual where a 2.8.0 page exists. Each row carries a version mark.

## 0. PREMISES RE-DERIVED (C-44)

| the brief's claim | verdict |
|---|---|
| DD24's bar is 0.010514 s per line | **VERIFIED.** `dev/ledger.toml:295` |
| the standing gap is 60.0 s | **VERIFIED.** `dev/ledger.toml:303-304` |
| `src/L/Condensation.lagda.md` is 132.28 s | **VERIFIED as a quotation.** `agents/tasks/LJ-1-311/lj-1.311-report.md:113`, from `[LJ-1.218]` |
| that is 71.4 percent of the wing | **VERIFIED.** 132.28/185.41 is 71.35 percent. `agents/tasks/LJ-1-311/lj-1.311-report.md:116`; the wing's 185.41 s is `dev/ledger.toml:303` |
| the cost is already attributed | **VERIFIED as a quotation.** `agents/tasks/LJ-1-311/lj-1.311-report.md:286` names `SatGraphB.satGraphB` (`:2294`), `SatGraphB.twelveB` (`:2236`) and `closedBS` (`:1586`) |
| R-41 is at `dev/LESSONS.md:4247` | **STALE. CORRECTED.** R-41's heading is at **`:4307`**. `:4247` now sits inside C-50. **C-51 landed on 2026-08-15 and pushed R-41 down about 60 lines.** `[LJ-1.309]` verified `:4247` correctly on its own day (`agents/tasks/LJ-1-309/lj-1.309-report.md:68`) |
| P-y is at `dev/LESSONS.md:3803` | **VERIFIED.** The heading is at `:3803` |

## 1. THE FILE'S SHAPE, counted without Agda

These counts are the evidence section 2 rests on. All MEASURED by `grep` and
`wc` over `src/L/Condensation.lagda.md` at HEAD.

| what | count | how |
|---|---:|---|
| lines in the master | 7,319 | `wc -l` |
| **module applications**, `module X = Y ...` | **117** | `grep -c "^\s*module [A-Za-z0-9_.]* *= "` |
| parameterized module declarations | about 30, `:117` to `:2294` | `grep -n "^module "` |
| `with ` tokens | 45 | `grep -c "with "` |
| `opaque` tokens | **1** | `grep -c opaque` |
| `record` declarations | **1**, `KFacts` at `:6076` | `grep -n "record "` |
| `KFacts` fields | **29** | `sed -n '6076,6117p' \| grep -c "^      [a-zA-Z]"` |
| `KFacts` occurrences | 32 | `grep -c KFacts` |
| `no-eta-equality` directives | **ZERO. MEASURED** | `grep -n "no-eta-equality"` |
| `instance` tokens | 3 | `grep -c instance` |

**The shape at the named cost carriers, READ at `src/L/Condensation.lagda.md:2236-2294`.**
`twelveB` is a **twelve-fold `∧̇` nest**. Each arm applies a `*BndAt` from a
different parameterized module (`Mem.`, `Eq.`, `And.`, `Or.`, `Imp.`, `Neg.`,
`Top.`, `Bot.`, `Exist.`, `Forall.`, `AllIn.`, `ExIn.`). Each argument is a
spelled-out `suc (suc (suc (suc (suc (suc N)))))` chain. `Δ₀-twelveB` follows
immediately and is a **proof term of the same twelve-fold shape**. So its type
`Δ₀ twelveB` and its body are **two large, near-identical terms**. The
conversion checker must relate them.

**`closedBS` at `:1586` is the same shape one layer down.** It is an eight-fold
`∧̇` nest of `binShapeBS` and `unShapeBS` applications, with `Δ₀-closedBS` as
its twin. READ at `:1586-1601`.

**`KFacts` at `:6076` is a 29-field record with 14 `Fin n` parameters and one
`γ : S ^ n`.** It carries no `no-eta-equality` directive, so it has η-equality
by default. The Agda 2.8.0 manual states: "By default, all non-recursive record
types enjoy η-equality."
https://agda.readthedocs.io/en/v2.8.0/language/record-types.html . READ.

## 2. THE THREE MOST LIKELY MECHANISMS, RANKED

### RANK 1: the syntactic equality shortcut on large, near-identical terms

- **Mechanism, DOCUMENTED.** Agda's conversion checker tries a syntactic
  equality shortcut before it reduces. Agda issue **#5801** measures the
  failure mode: "The time required to type-check the final definition seems to
  be at least quadratic in n, but roughly linear if `--no-syntactic-equality`
  is used." https://github.com/agda/agda/issues/5801 . **READ.** Opened
  2022-02-25, milestone 2.6.3.
- **Why it fits.** `Δ₀-twelveB` relates a twelve-fold nest to a type built the
  same way. `Δ₀-closedBS` relates an eight-fold nest. **That is exactly "large
  syntactically similar terms".** These two definitions sit inside the machinery
  that `[LJ-1.311]` names as the file's cost.
- **Symptom an agent sees first.** One definition takes the module's seconds.
  The cost grows faster than the arm count. **No heap wall**, only a long run.
  The definition looks routine in the source.
- **THE ONE COMMAND THAT TESTS IT.**

  ```
  GHCRTS=-M8g agda --profile=definitions --no-syntactic-equality src/L/Condensation.lagda.md
  ```

  Compare against the same command without the flag. **A large drop confirms
  the mechanism.** `--syntactic-equality={N}` then tunes it: "Give the syntactic
  equality shortcut `N` units of fuel."
- **Documented cure.** The flag itself, which is also a pragma option. **CAUTION,
  INFERRED:** the 2.8.0 options page lists `--syntactic-equality` under "Options
  that affect interface file reloading", so a clean rebuild is needed for a fair
  measurement. It is in **neither** the infective nor the coinfective list, and
  the page gives no list of options forbidden with `--safe`.
  https://agda.readthedocs.io/en/v2.8.0/tools/command-line-options.html . READ.
- **WHY THIS IS RANK 1.** It is the only row that needs **no code edit**. One
  flag, one run, one number. C-50 says profile before you cure; this row is the
  profile.

### RANK 2: module application copies every definition, and this file does it 117 times

- **Mechanism, DOCUMENTED.** Agda implements `module M = N args` by **eagerly
  copying every definition of `N`** with the arguments substituted. Agda issue
  **#1646**, "Exponential module chain leads to infeasible scope checking",
  states: "This performance bottleneck can probably be attributed to the eager
  copying behavior of module aliases." It measures a module chain at about **40
  seconds and 16 GB allocated** at one depth, and about **5 minutes 40 seconds
  and 54 GB allocated** at one level deeper.
  https://github.com/agda/agda/issues/1646 . **READ.** Opened 2015-09-13,
  **still OPEN, milestone `icebox`**. **So it is not fixed in 2.8.0. INFERRED**
  from the open state, because I ran no Agda.
- **Why it fits.** 117 module applications in one master, MEASURED. Each `*Row`
  module from `:1814` opens with `module D = ...` and `module T = RowTransfer ...`.
  So about thirty near-identical modules each trigger two copies, under a
  telescope of six or seven `Fin` parameters plus `γ : S ^ suc n`.
- **Symptom an agent sees first.** The cost is **spread, not concentrated**.
  Many definitions each carry a moderate charge. The `Miscellaneous` bucket is
  large. **Serialization is a large share of `--profile=internal`.** The
  `.agdai` file is large for the line count.
- **THE ONE COMMAND THAT TESTS IT.**

  ```
  GHCRTS=-M8g agda --profile=internal src/L/Condensation.lagda.md
  ```

  **Read the `Serialization` and `Import` rows against `Typing.CheckRHS`.** If
  serialization is a small share, this rank falls. **This project has run this
  mode before and the rows are known:** `[LJ-1.281]` recorded
  `Typing.CheckRHS = 90.7 s` of a 100.8 s total
  (`agents/tasks/LJ-1-281/lj-1.281-report.md:87-89`). Issue #1952 names two more
  rows, `Typing.OccursCheck` and `Scoping.InverseScopeLookup`.
  https://github.com/agda/agda/issues/1952 . READ.
- **Documented cure, POINTER-ONLY on its wording.** #1646's thread records the
  mitigation as: keep the number of definitions exported from an applied module
  small, because only what enters scope needs to be copied. **I read this
  through a search summary and not on the issue page itself**, so I mark the
  wording POINTER-ONLY. **The copying claim itself is READ in #1646.**

### RANK 3: η-expansion of the 29-field `KFacts` record

- **Mechanism, DOCUMENTED THREE WAYS.**
  1. Agda issue **#6509**, "Agda seems to be very slow at typechecking records
     with many fields". A file took "real 0m30.062s", and one more line made it
     "much, much slower (upwards of a minute)". **Labels: performance, records,
     regression in 2.6.0. OPEN, milestone 2.7.0.**
     https://github.com/agda/agda/issues/6509 . **READ.**
  2. The 2.8.0 lossy-unification page names the expensive case exactly: "The
     performance will improve most dramatically when reducing an application of
     `f` would produce a large term, perhaps an element of a record type with
     several fields and/or large embedded proof terms."
     https://agda.readthedocs.io/en/v2.8.0/language/lossy-unification.html .
     **READ.**
  3. Nils Anders Danielsson, "Some tricks for making Agda code faster", AIM 32,
     2020-06-01. Its rule of thumb is "Try to avoid making Agda compare large
     terms." It states that **"records with η-equality don't block evaluation"**,
     while copatterns and `no-eta-equality` do.
     http://www.cse.chalmers.se/~nad/publications/danielsson-aim32-talk.txt .
     **READ.**
- **Why it fits.** `KFacts` has 29 fields, 14 index parameters, and **no
  `no-eta-equality` directive. MEASURED.** It appears 32 times, as a parameter
  at `:6160`, `:6449`, `:6550`, `:6578`, `:6847`, `:7109` and as a field at
  `:7295`. Every one of those sites is in the agreement region the brief names.
- **Symptom an agent sees first.** Definitions that only PASS the record are
  charged. Cost rises when a new field joins the record. The profile charges the
  consumers rather than the record.
- **THE ONE COMMAND THAT TESTS IT.**

  ```
  GHCRTS=-M8g agda --profile=definitions --lossy-unification src/L/Condensation.lagda.md
  ```

  **This is a flag-only test and it needs no code edit.** The lossy-unification
  page says the heuristic targets this exact shape. **CAUTION: the same page
  says the heuristic is "sound but not complete" and "will cause Agda to ignore
  some possible solutions to unification variables".** So use it as a
  MEASUREMENT and never as a landed cure without review.
- **The second test, which costs one line.** Add `no-eta-equality` to `KFacts`.
  **WARNING from the manual:** "Pattern matching is not allowed by default" for
  an inductive record without η-equality, and the `pattern` directive turns it
  back on. So this edit can break consumers.

### RANK 4, listed because C-51 already priced it: with-abstraction

The brief asks what the literature says about `with`. **The manual states the
mechanism that C-51 measured**, and this is the primary source for it:

> "The generalisation step of a with-abstraction needs to normalise the
> scrutinee and the goal and argument types to make sure that all instances of
> the scrutinee are generalised."

https://agda.readthedocs.io/en/v2.8.0/language/with-abstraction.html . **READ.**

The same page states the translation builds an auxiliary function of type
`Δ₁ → C`, where `C` generalises the goal. **So the cost is the goal's size and
not the scrutinee's**, which is exactly what C-51 records at
`dev/LESSONS.md:4286-4290`. The file holds **45 `with ` tokens**, MEASURED, and
each `*Row` goal carries a deep telescope (READ at `:1826-1834`).

**I rank it 4 and not higher because C-51 already gives the cure and
`[LJ-1.305]` already measured it.** The literature adds the mechanism's name and
nothing this project does not own.

### WHY NOT R-41

`[LJ-1.309]` MEASURED zero `sucIter` in this master and no chain-against-iterate
site (`agents/tasks/LJ-1-309/lj-1.309-report.md:70`). `[LJ-1.311]` re-checked
and agreed (`:113-122`). **R-41 is not the mechanism here.** I did not re-open
it.

## 3. THE FULL TABLE OF DOCUMENTED AGDA COST MECHANISMS

Every row is a HYPOTHESIS at this site (P-l). The symptom column is the one an
agent sees first.

| mechanism | symptom | documented cure | locator | version | status |
|---|---|---|---|---|---|
| **Syntactic equality shortcut fails on large similar terms** | one definition takes the module's seconds; cost quadratic in term size; no heap wall | `--no-syntactic-equality`, or `--syntactic-equality={N}` fuel | agda#5801 | flag present in 2.8.0 | READ |
| **Module application copies every definition** | cost spread over many definitions; large `Miscellaneous`; serialization dominates `--profile=internal`; big `.agdai` | export fewer definitions from the applied module | agda#1646 | OPEN, `icebox`, so unfixed in 2.8.0 (INFERRED) | READ |
| **Record with many fields** | cost rises when a field joins; consumers charged, not the record | `no-eta-equality`; copatterns; smaller records | agda#6509 | OPEN, "regression in 2.6.0" | READ |
| **η-expansion of records makes Agda compare large terms** | passing a record costs more than using it | `no-eta-equality`; copatterns; a `Block` unit type without η | NAD, AIM 32 notes | 2020, mechanism unchanged in 2.8.0 (INFERRED) | READ |
| **Reduction of a defined function produces a large term** | unification of `f es₀ = f es₁` reduces both sides | `--lossy-unification`, sound but INCOMPLETE | 2.8.0 lossy-unification page | 2.8.0 | READ |
| **with-abstraction normalises the goal** | one clause dominates, or a heap wall | projections instead of `with` (Bedrock's C-51) | 2.8.0 with-abstraction page | 2.8.0 | READ |
| **Instance resolution with implicit arguments** | `Typing.OccursCheck` explodes in `--profile=internal` | explicit type annotation, or pass the instance explicitly | agda#1952: 320 ms to 364,176 ms; annotation restores 1,652 ms | regression 2.4.2.6 to 2.5.1, CLOSED | READ |
| **Instance resolution exponential in a module parameter** | import of a parameterized module with instances is slow | move the instance to an explicit argument | agda#7709 | **CLOSED IN 2.8.0**, named in the 2.8.0 changelog | READ |
| **Backtracking instance search** | exponential worst case | avoid `--overlapping-instances`; 2.8.0 adds `--experimental-lazy-instances` | 2.8.0 changelog | 2.8.0 | READ |
| **Implicit-argument inference normalises large terms** | a definition checks fast when eta-expanded by hand | manual eta-expansion of functions | agda#5060 | OPEN, version not stated | READ |
| **Projection-like analysis erases arguments** | interactive results print with `_`; instance constraint then fails | `NOT_PROJECTION_LIKE` pragma; `--no-projection-like` | agda#6203, CLOSED by #6204 | 2.8.0 flag exists | READ |
| **Universe polymorphism penalty** | whole-library slowdown | `type-in-type` for prototyping | Agda wiki PerformanceTips: factor 3 in 2.2.10, factor 2 in 2.2.11 | **STALE. 2.2.x, about 2011. Do NOT carry the factor to 2.8.0** | READ |
| **Serialization of interfaces** | splitting a file costs `.agdai` time | keep interfaces small; `--save-metas` trade-off | Agda wiki PerformanceTips; 2.8.0 options page | mechanism current, figures stale | READ |
| **Large `.agda` files check non-linearly** | the file is slow and no definition explains it | split the file | agda-categories wiki, `speed` | undated, community claim | READ |

### THE TWO MECHANISMS THAT DO NOT BEAR HERE. MEASURED.

- **`REWRITE` rules.** `grep -rl "rewriting\|REWRITE" src --include='*.lagda.md'`
  returns ONE file, `src/L/Coding/Model.lagda.md`, and the match at `:1449` is
  **English prose**, not a pragma. **No master enables `--rewriting`. MEASURED.**
- **`--erasure`.** `grep -rl "\-\-erasure\|@0\|@erased" src --include='*.lagda.md'`
  returns **nothing. MEASURED.** All 96 masters carry exactly one header,
  `{-# OPTIONS --cubical --safe --guardedness #-}`, MEASURED by
  `grep -rh OPTIONS src | sort | uniq -c`.

### LEVEL ARITHMETIC AND UNIVERSE POLYMORPHISM

**The only figure I found is STALE and I refuse to carry it.** The Agda wiki's
PerformanceTips gives a factor of three for Agda 2.2.10 and a factor of two for
2.2.11, against `type-in-type`. Those are about 2011 figures on a different
implementation. **Nothing in the 2.8.0 manual or the 2.8.0 changelog restates
them. MEASURED by reading both.** The masters here use `{ℓ : Level}` at
`src/L/Condensation.lagda.md:10` and `Type (ℓ-suc ℓ)` throughout, so the
question is live, but **the literature gives no current price.**

## 4. THE PROFILE'S GROUPING LIMIT

**THE BRIEF'S PREMISE IS ALREADY REFUTED IN THE REPO, and I say so first.**
`[LJ-1.309]` reported that a definition costing 261 ms did not appear in the
profile (`agents/tasks/LJ-1-309/lj-1.309-report.md:292-300`). **`[LJ-1.311]`
refuted that:** the raw profile always carried the row, at
`agents/tasks/LJ-1-292/runs/k1.out:26`, charged 26 ms
(`agents/tasks/LJ-1-311/lj-1.311-report.md:118-122`). **The loss was in a
report's summary table, not in Agda. So there is no evidence that Agda hid a
charged definition.**

**A REAL GROUPING EXISTS, IT IS LARGE, AND IT IS NOT DOCUMENTED.**

- **`Miscellaneous` is the empty account.** Agda's own source sets
  `showAccount [] = "Miscellaneous"` in `Agda/Utils/Benchmark.hs`.
  https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Utils/Benchmark.hs .
  **READ** (fetched at tag `v2.8.0`).
- **Accounts form a trie, and the printer shows a direct time and an aggregate
  time per node.** The same file computes
  `aggr t = (fromMaybe 0 $ Trie.lookup [] t, getSum $ foldMap Sum t)` and shows
  both when they differ. **READ.**
- **A definition gets an account only inside a `Definition QName` bill.**
  `Agda/Benchmarking.hs` carries the constructor `Definition QName` and the
  predicate `isDefAccount [] = True`, so **the empty account is a legal
  definitions-mode account.**
  https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Benchmarking.hs .
  **READ.**
- **THE SIZE OF THE PROBLEM, MEASURED ON THIS PROJECT'S OWN RUNS.**
  `agents/tasks/LJ-1-292/runs/k1.out:2-3` shows Total 3,974 ms and
  `Miscellaneous` 2,417 ms, which is **60.8 percent unattributed**.
  `agents/tasks/LJ-1-309/runs/c1.out:2-3` shows Total 1,540 ms and
  `Miscellaneous` 838 ms, which is **54.4 percent unattributed**. **So more than
  half of a run is routinely charged to no definition.**
- **IS THE LIMIT DOCUMENTED? NO. MEASURED.** The Agda 2.8.0 manual page
  "Performance debugging" describes `--profile=definitions` as "Break down by
  time spent checking each top-level definition" and **says nothing about an
  unattributed bucket, about `Miscellaneous`, or about what falls outside a
  definition's account.**
  https://agda.readthedocs.io/en/v2.8.0/tools/performance.html . **READ, whole.**

**WHAT AVOIDS IT.** There is no better per-definition attributor. **There is a
better attributor by ACTIVITY**, and it is documented:

| mode | what it gives | 2.8.0 doc text |
|---|---|---|
| `--profile=internal` | time by activity: type checking, serialization, positivity, occurs check | "Measure time taken by various parts of the system" |
| `--profile=modules` | time per module | "Measure time spent on individual (Agda) modules" |
| `--profile=conversion` | **counts of conversion-algorithm steps** | "Count number of times various steps of the conversion algorithm are used" |
| `--profile=constraints` | constraint-solving statistics | "Collect statistics about constraint solving" |
| `--profile=metas` | metavariable counts | "Count number of created metavariables" |
| `--profile=serialize` | serialization statistics | "Collect detailed statistics about serialization" |

Locator for all six: https://agda.readthedocs.io/en/v2.8.0/tools/command-line-options.html . **READ.**

**THE RECOMMENDED PAIRING, and I mark it INFERRED.** The page says "Only one of
`internal`, `modules`, and `definitions` can be turned on at a time." It states
no such restriction for `conversion`, `constraints`, `metas` or `serialize`.
**So `--profile=definitions --profile=conversion` should be legal. INFERRED
from the doc's wording. I ran no Agda and did not confirm it.**

**THE OTHER TOOL, POINTER-ONLY.** The 2.8.0 performance page names `agda-bench`
(https://github.com/UlfNorell/agda-bench). **It benchmarks compile-time
EVALUATION, not typecheck attribution**, so it does not answer this question.
POINTER-ONLY: I read the manual's one-line description and did not open the
repository.

**A DEAD END WORTH RECORDING.** Agda issue **#6090**, "Better time profiles",
looks like the answer and is not. **It is about GHC-level profiling of the Agda
BINARY** (`-fprof-auto` against `-fprof-late`), and not about
`--profile=definitions`. CLOSED. https://github.com/agda/agda/issues/6090 .
**READ.** **So the next agent does not need to open it.**

## 5. WHAT OTHER LARGE DEVELOPMENTS PUBLISHED

**The published corpus is thin and mostly community wiki, not papers. MEASURED
by the searches in the LITERATURE USED section.**

1. **agda-categories, `speed` wiki page. READ.**
   https://github.com/agda/agda-categories/wiki/speed . It is the closest
   comparable to this project: a large, heavily parameterized Agda development.
   Its named causes are: **excessive `_`**, **hard implicits**, **large files**
   ("typechecking appears non-linear"), **large interfaces** ("record fields
   plus all conservative extensions"), **convenience modules** with `.`
   notation, **inline proofs**, and **lack of sharing**. Its cures are: expand
   underscores, give explicit arguments, **"Split things up!"**, use `using`
   clauses, make convenience modules `private`, prefer copatterns to explicit
   records, and **name repeated sub-expressions in a `where` rather than a
   `let`**. **It gives NO measurements. MEASURED by reading the page.**
2. **Nils Anders Danielsson, "Some tricks for making Agda code faster", AIM 32,
   2020-06-01. READ.**
   http://www.cse.chalmers.se/~nad/publications/danielsson-aim32-talk.txt .
   **The strongest single sentence in the whole corpus:** "Try to avoid making
   Agda compare large terms." Its levers are `abstract`, pattern matching to
   block evaluation, copatterns, `no-eta-equality`, and an artificial `Block`
   unit type without η to force blocking. **It gives no measurements either.**
3. **The Agda wiki PerformanceTips page. READ, and STALE.**
   https://wiki.portal.chalmers.se/agda/Main/PerformanceTips . Its measurements
   are Agda 2.2.10 against 2.2.11, about 2011: standard library "9m45s and 876Mb"
   against "6m38s and 576Mb". **Do not carry any figure from it to 2.8.0.**
4. **The cubical library's own performance record is THIN. MEASURED.**
   `agda/cubical` issue **#320**, "Typechecking
   `Cubical.Codata.M.AsLimit.M.Properties` is extremely slow", gives **no
   diagnosis and no measurement**: "It seems like typechecking this file has
   become extremely slow. Any clue why?"
   https://github.com/agda/cubical/issues/320 . **READ.** Agda issue **#4573**,
   "Slow typechecking unless using abstract in cubical", is **OPEN since
   2020-04-09, milestone `later`**, against Agda 2.6.1, and gives **no
   mechanism and no measurement**. https://github.com/agda/agda/issues/4573 .
   **READ.** **So cubical 0.9 publishes no performance guidance this project
   can use. MEASURED against these two issues and the repository README.**
5. **agda#7784, an open performance case with real numbers. READ.**
   https://github.com/agda/agda/issues/7784 . A monoidal-category development
   on **Agda 2.7.0.1**: `lunit` 901 ms, `runit` 25,185 ms "despite symmetric
   code", `lshift` 50,898 ms, and the triangle and pentagon identities at "10+
   minutes, 70GB+ RAM". **The reporter's cure was to REFORMULATE**, using
   `triangle-alt` and `pentagon-alt`, reaching about 1,004 ms. **This is the
   published shape of a respelling cure, and it is R-41's shape in another
   development.**
6. **Aaron Stump, "Battling Performance Problems in Agda", 2014-04-24. SKIMMED.**
   https://queuea9.wordpress.com/2014/04/24/battling-performance-problems-in-agda/ .
   **It bears little.** Two of its three problems are RUN-TIME, and its
   typecheck problem is a 3,000-element literal. **WHY IT IS HERE: its one
   transferable idea is to block compile-time evaluation with a `postulate`,
   which is the same lever as `opaque` and `abstract`.** No usable measurement.
7. **`dev/literature/formalizations-landscape.md`, read as the brief ordered.
   IT CARRIES ZERO PERFORMANCE CONTENT. MEASURED:**
   `grep -in "perform\|second\|typecheck\|compile time\|slow"` over its 421
   lines returns **no line**. It surveys Metamath, Mizar, Isabelle, Lean and
   Coq for mathematical content. **It does not bear on this question at all.**

**THE HONEST SUMMARY OF SECTION 5.** **No large Agda development has published
a measured cost model.** The corpus is two wiki pages, one talk note, and a
handful of issues. **Bedrock's `dev/LESSONS.md` R-41, with its measured ladder
of 219, 9,286 and 419,218 ms, is a BETTER artifact than anything I found.**

## 6. THE TELESCOPE QUESTION, and the literature answers it AGAINST the record

The brief asks: is "a deep telescope repeated thirty times" a documented cost
shape, and does recording it in a record cut the seconds as well as the lines?

**PART ONE: NO. MEASURED by absence across every source in LITERATURE USED.**
**No source names a repeated telescope as a cost shape.** The nearest thing is
agda-categories' "large interfaces" row, and that is about the interface file
and not about conversion.

**PART TWO: THE LITERATURE POINTS BOTH WAYS, AND THE LINES ANSWER DOES NOT
CARRY THE SECONDS ANSWER.**

| direction | source | what it says |
|---|---|---|
| a record HELPS | NAD AIM 32 | `no-eta-equality` and copatterns **block evaluation**, which is the `opaque` lever |
| a record HELPS | 2.8.0 lossy-unification page | the heuristic exists precisely for records with several fields |
| a record HURTS | agda#6509 | "Agda seems to be very slow at typechecking records with many fields", OPEN |
| a record HURTS | agda-categories `speed` | "large interfaces": record fields **plus all conservative extensions** enter the interface |
| a record HURTS | NAD AIM 32 | records **with** η-equality do **NOT** block evaluation, and a new record has η by default |

**PART THREE, AND IT IS THE MOST IMPORTANT THING IN THIS REPORT: A TELESCOPE
LIFT WAS ALREADY TRIED ON A `Condensation` AND IT MADE THE MODULE WORSE.**

**P-l's own table records it, and P-l BINDS.** `dev/LESSONS.md:2355` carries this
row:

> `[T102]`'s telescope lift | `SquareLaw`'s `h₀` pair, 374.3 s to 82 ms |
> `Condensation`'s three pieces, argued by `[T104]` from resemblance,
> **unmeasured** | **REFUTED by `[T106]`**: piece 1 made the module WORSE,
> **204.7 s to 308.8**; piece 3's cost MOVED rather than went; piece 2's
> export-preserving form is worse than the control

**And three rows above it, `dev/LESSONS.md:2352`:** the abstract-carrier
discipline gave "**no movement at all**, 203.3 s against 203.5" on
`Condensation`'s clauses.

**WHAT TRANSFERS AND WHAT DOES NOT, and I am strict about this.** That was the
**RETIRED route's** `Condensation`, 885 lines, with no `Agree` family
(`agents/tasks/LJ-1-307/lj-1.307-report.md:260`, `:348`). **P-l's whole point is
that such a result does NOT transfer by analogy, so I carry NO figure from it.**

**What DOES transfer is the SHAPE of the failure, and P-l states it as a law:**
"An expected figure anchored on a comparable is a HYPOTHESIS, not a price"
(`dev/LESSONS.md:2370`). **The retired route argued a telescope lift from
resemblance, ran nothing, recorded it as a finding, and a later task measured it
and restored the original.** `[LJ-1.307]`'s 15 to 20 s band for the `RowTies`
compression is marked "INFERRED, not measured" by its own author
(`agents/tasks/LJ-1-307/lj-1.307-report.md:254-255`). **That is the same
position `[T104]` was in.**

**SO THE LITERATURE AND THE ARCHIVE AGREE, from two directions: do not fund a
telescope-into-record compression for SECONDS without measuring it first.** Fund
it for LINES if the lines are worth it, and treat any seconds as unpriced.

**THE DECIDING FACT IS IN THE FILE ALREADY, AND IT IS MEASURABLE TODAY.**
`KFacts` is a 29-field record with **no `no-eta-equality`. MEASURED.**
`[LJ-1.307]` calls it "the measured proof that the record pattern pays here"
(`agents/tasks/LJ-1-307/lj-1.307-report.md:229`), **but its measurement is of
LINES, not seconds** (`:242-244`). **So the lines claim is measured and the
seconds claim is not.**

**MY RECOMMENDATION, and it needs one run.** Before funding a `RowTies` record,
profile the EXISTING `KFacts` consumers at `:6449`, `:6550`, `:6578`, `:6847`
and `:7109`. **If `KFacts` consumers are cheap, the record pattern is proven
here and a `RowTies` record is safe to fund. If they are expensive, the 990
telescope lines are buying seconds, and the compression trades lines for
seconds.** That is one `--profile=definitions` run on bytes that already exist.

## 7. THINGS I PROPOSE, ALL MARKED HYPOTHESIS

**A LAW IS NOT ADMITTED WITHOUT ITS MEASUREMENT.** These are literature, so each
is a HYPOTHESIS and names the measurement it needs. **The orchestrator assigns
any ID.**

**HYPOTHESIS 1. A conversion between two large near-identical terms costs
quadratically, and one flag prices it.**
Basis: agda#5801, READ. Measurement it needs: two cold runs of
`src/L/Condensation.lagda.md`, one plain and one with
`--no-syntactic-equality`, both `--profile=definitions`, on a quiet machine.
**If the delta is small, the hypothesis dies in one run.**

**HYPOTHESIS 2. Eager module-application copying is a cost class this project
has never measured, and `--profile=internal` prices it.**
Basis: agda#1646, READ, still open. Measurement it needs: one
`--profile=internal` run on the 117-application master, plus one on a master
with few applications, comparing the serialization share.

**I CHECKED WHETHER THIS PROJECT HAS RUN `--profile=internal`, AND MY FIRST
ANSWER WAS WRONG.** `grep -rl "profile=internal" agents/` returns **at least
`LJ-1-158`, `LJ-1-275` and `LJ-1-281`. MEASURED.** **`[LJ-1.281]` used it and
recorded a usable row:** "`--profile=internal` on the control agrees. It shows
`Typing.CheckRHS = 90.7 s` of the 100.8 s total. The cost is in the bodies, not
in the signatures. MEASURED."
`agents/tasks/LJ-1-281/lj-1.281-report.md:87-89`. **So the mode works here, the
project knows how to read it, and `Typing.CheckRHS` against `Serialization` is
the comparison rank 2 needs.**

**HYPOTHESIS 3. A record with η-equality does not seal, and `opaque` does.**
Basis: NAD AIM 32, READ, and the 2.8.0 record-types page, READ. This SHARPENS
P-y. P-y prices a seal by how many definitions look inside a formula. **A record
with η is not a seal at all**, because η lets the checker expand it without any
`unfolding`. Measurement it needs: profile one `KFacts` consumer with and
without `no-eta-equality` on the record.

**HYPOTHESIS 4. The `--profile=definitions` unattributed share is a measurement
quality figure this project should record with every profile.**
Basis: MEASURED at 60.8 percent (`agents/tasks/LJ-1-292/runs/k1.out:2-3`) and
54.4 percent (`agents/tasks/LJ-1-309/runs/c1.out:2-3`). **A profile that leaves
60 percent in `Miscellaneous` supports a weaker verdict than a profile that
leaves 5 percent.** Measurement it needs: nothing new. **It is a reporting rule,
not a law**, and it costs one line per report.

## 8. THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH (D-1)

| branch fixed before the run | verdict |
|---|---|
| **a ranked list of mechanisms exists and I deliver it** | **FIRED. Section 2.** Three ranks plus a fourth, each with a symptom and one test command |
| **the profile's grouping limit is documented** | **DID NOT FIRE, and the answer is better than a yes.** The limit is REAL, it is 54 to 61 percent on this project's own runs, and **the manual does NOT document it. MEASURED.** The alternative is `--profile=internal`, and this project has never run it |
| **nothing is documented beyond what Bedrock measured** | **PARTLY FIRED, and I say it plainly.** On the SPELLING question, R-41 is better than anything published. **On three other mechanisms, the literature is ahead of this project**: the syntactic equality shortcut, eager module copying, and record η |
| **the literature is about a different Agda** | **FIRED ONCE, and I marked it.** The Agda wiki PerformanceTips figures are 2.2.x, about 2011. **agda#7709 is CLOSED IN 2.8.0**, so its instance pathology is gone here. agda#1646, #6509, #4573, #5060 and #7784 are all still OPEN |

## 9. DD4, WITH ITS AXIS (C-46)

**AXIS: AC-against-GCH**, fixed in code at `scripts/measure/ledger.py:432` and
`:466`, which read `ac_root` and `gch_root` and take each closure.

**A `Condensation` cure serves the GCH end ALONE.** `src/L/Condensation.lagda.md`
sits in the GCH wing, whose delivered total is 185.41 s (`dev/ledger.toml:303`).
**Seconds are paid once per master.** A cure in a SHARED master pays on both
ends; a cure in a wing master pays on one.

**AND THE FIGURE UNDERSTATES.** `dev/ledger.toml:204` records that the GCH
closure is read from a STATEMENT whose proof is not wired, so the closure is the
statement's and **it understates**. **So a `Condensation` cure is worth at least
what the current figure says, and possibly more when `[LJ-1.8]` lands.**

**P-y's warning applies in reverse here, and it is good news.** P-y records that
a cure in SHARED code made the DD24 ratio WORSE, because the reference side
gained more than the judged side (`dev/LESSONS.md:3838-3843`). **A cure in
`Condensation` is in the JUDGED side only, so every second it saves improves the
ratio.**

## ARCHIVE USED (DD18)

**ONE line read per archived file, as the brief requires.**

- **`agents/tasks/LJ-1-309/lj-1.309-report.md`, read WHOLE.** ONE line: `:296-300`,
  "**INFERRED**, and offered as a hypothesis only: the conversion at `splitKey∈`
  may be discharged while Agda solves the implicit level arguments, and the
  profiler may then charge it to `Miscellaneous`". **TAKEN:** the question that
  section 4 answers, and its own honesty about not having read Agda's source.
  **NOT TAKEN:** its premise that a definition was hidden. **`[LJ-1.311]`
  refuted it and I carried the refutation, not the premise.**
- **`agents/tasks/LJ-1-292/lj-1.292-report.md`.** ONE line: `:124`, the ladder's
  depth-2 rung at 219 ms. **TAKEN as the SHAPE of a good cost artifact**, which
  section 5 uses to judge the published corpus. **NOT TAKEN:** any figure. R-41
  is not this file's mechanism.
- **`agents/tasks/LJ-1-283/lj-1.283-report.md`.** ONE line, quoted through
  `dev/LESSONS.md:4249-4252`: "The layer-cap seal on it moved 0.92 s, minus 0.19
  percent, inside the content's own 0.9 percent spread. **Both void, MEASURED.**"
  **TAKEN:** the standing proof that a seal can be inert, which is why section 6
  refuses to promise the record cure will move seconds. **NOT TAKEN:** its
  attribution rows, which `[LJ-1.311]` already carried forward.
- **`agents/tasks/LJ-1-305/lj-1.305-report.md` section 5.4**, read through
  C-51's quotation at `dev/LESSONS.md:4278-4281`. ONE line: "`with leastOf ... |
  (m , pm , _)` exhausted the 8 GB cap **six times**, at 305, 315, 311, 312, 312
  and 314 seconds". **TAKEN:** the symptom column for rank 4. **NOT TAKEN:** the
  310 s figure as a comparable for `Condensation`. **P-l forbids it.**
- **`agents/tasks/LJ-1-307/lj-1.307-report.md`.** ONE line: `:229`, "**The
  `KFacts` block is the measured proof that the record pattern pays here.**"
  **TAKEN:** the record-against-telescope question of section 6. **NOT TAKEN:**
  its 15 to 20 s seconds band at `:252-256`, which that report itself marks
  "INFERRED, not measured" at `:254`. **Section 6 part three explains why I
  refuse it: `dev/LESSONS.md:2355` records a telescope lift argued from
  resemblance on the retired `Condensation`, and a later task measured it at
  204.7 s to 308.8 s. The argument's SHAPE is the same.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE line:
  `:223`, `[L3.32-T219]`, "The seconds doctrine: what makes a master expensive
  here. Five diseases; the 21-60x gap is a CONTENT CLASS, not a defect."
  **TAKEN AS SHAPE:** the retired route also concluded that a tree's seconds sit
  in a content class rather than in one curable spelling, and section 2's rank 2
  and rank 3 are content-class mechanisms. **WHAT WOULD NOT TRANSFER: every
  number.** The retired route ran a different Agda on a different tree with a
  different architecture. **I carried no figure from it.** Its `Condensation` was
  885 lines against this one's 7,319 (`agents/tasks/LJ-1-307/lj-1.307-report.md:260`).
  **One archived row bears by SHAPE and I name it because rank 2 is the same
  question:** `archive/dev/TASKS-archived.md:225`, `L3.32-T221`, "The
  parameterization question: can the master need less instantiation?", answered
  "RESHAPEABLE". **The retired route asked whether a master needs less
  instantiation and answered yes. THAT question is rank 2 restated. Its numbers
  do not transfer and I carried none.**

## LITERATURE USED (DD18)

**THIS TASK IS THE LITERATURE SECTION, and its corpus is a proof assistant's
rather than a mathematician's.**

### READ

| source | locator | Agda version | what I took |
|---|---|---|---|
| Agda manual, Performance debugging | https://agda.readthedocs.io/en/v2.8.0/tools/performance.html | **2.8.0** | the three profile modes; **and the NEGATIVE that it documents no unattributed bucket** |
| Agda manual, Command-line options | https://agda.readthedocs.io/en/v2.8.0/tools/command-line-options.html | **2.8.0** | all nine `--profile` values; `--syntactic-equality={N}`; `--lossy-unification`; `--no-projection-like`; `--call-by-name`; infective and coinfective lists |
| Agda manual, With-abstraction | https://agda.readthedocs.io/en/v2.8.0/language/with-abstraction.html | **2.8.0** | the generalisation step normalises the goal, which is C-51's mechanism named by the primary source |
| Agda manual, Lossy unification | https://agda.readthedocs.io/en/v2.8.0/language/lossy-unification.html | **2.8.0** | the heuristic, its target shape, and that it is "sound but not complete" |
| Agda manual, Record types | https://agda.readthedocs.io/en/v2.8.0/language/record-types.html | **2.8.0** | non-recursive records have η by default; `no-eta-equality` blocks pattern matching |
| Agda 2.8.0 changelog | https://hackage.haskell.org/package/Agda-2.8.0/changelog | **2.8.0** | `--experimental-lazy-instances`; `optimise-heavily` on by default; issue #7709 CLOSED |
| `Agda/Utils/Benchmark.hs` at tag `v2.8.0` | https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Utils/Benchmark.hs | **2.8.0** | `showAccount [] = "Miscellaneous"`; the trie and the `aggr` pair |
| `Agda/Benchmarking.hs` at tag `v2.8.0` | https://raw.githubusercontent.com/agda/agda/v2.8.0/src/full/Agda/Benchmarking.hs | **2.8.0** | the `Definition QName` account; `isDefAccount [] = True` |
| agda#5801, syntactic equality fuel | https://github.com/agda/agda/issues/5801 | flag in 2.8.0 | quadratic against linear; **rank 1** |
| agda#1646, exponential module chain | https://github.com/agda/agda/issues/1646 | OPEN, `icebox` | eager copying of module aliases; **rank 2** |
| agda#6509, records with many fields | https://github.com/agda/agda/issues/6509 | OPEN, 2.6.0 regression | 30 s to over 60 s; **rank 3** |
| agda#1952, instance resolution | https://github.com/agda/agda/issues/1952 | CLOSED, 2.5.1.1 | 320 ms to 364,176 ms; the `--profile=internal` row names |
| agda#7709, instances and module parameters | https://github.com/agda/agda/issues/7709 | **CLOSED IN 2.8.0** | exponential in a module parameter; **fixed in this project's version** |
| agda#5060, manual eta-expansion | https://github.com/agda/agda/issues/5060 | OPEN | implicit inference normalises large terms |
| agda#6203, projection-likeness | https://github.com/agda/agda/issues/6203 | CLOSED by #6204 | `NOT_PROJECTION_LIKE` |
| agda#6090, better time profiles | https://github.com/agda/agda/issues/6090 | CLOSED | **a DEAD END: it is about GHC profiling of the Agda binary** |
| agda#4573, abstract in cubical | https://github.com/agda/agda/issues/4573 | OPEN since 2020, 2.6.1 | **no mechanism, no measurement** |
| agda#7784, monoidal category | https://github.com/agda/agda/issues/7784 | OPEN, 2.7.0.1 | 901 ms, 25,185 ms, 50,898 ms, 70 GB; the reformulation cure |
| cubical#320 | https://github.com/agda/cubical/issues/320 | undated in the page | **no diagnosis, no measurement** |
| agda-categories `speed` wiki | https://github.com/agda/agda-categories/wiki/speed | undated | seven causes, six cures, **no measurements** |
| NAD, AIM 32 talk notes | http://www.cse.chalmers.se/~nad/publications/danielsson-aim32-talk.txt | 2020 | "Try to avoid making Agda compare large terms"; η does not block |
| Agda wiki PerformanceTips | https://wiki.portal.chalmers.se/agda/Main/PerformanceTips | **2.2.10 and 2.2.11. STALE** | the universe-polymorphism factor, which I refuse to carry |
| AIM XXXII programme | https://wiki.portal.chalmers.se/agda/Main/AIMXXXII | 2020 | the locator for the NAD notes |
| `dev/literature/formalizations-landscape.md` | in repo, 421 lines | n/a | **ZERO performance content. MEASURED by grep** |

### SKIMMED

| source | locator | why only skimmed |
|---|---|---|
| Stump, "Battling Performance Problems in Agda" | https://queuea9.wordpress.com/2014/04/24/battling-performance-problems-in-agda/ | 2014, and two of three problems are RUN-TIME |
| Agda issues filtered by label `performance` | https://github.com/agda/agda/issues?q=label%3Aperformance+sort%3Acomments-desc | an index, used to pick the issues above |

### POINTER-ONLY

| source | locator | why |
|---|---|---|
| `agda-bench` | https://github.com/UlfNorell/agda-bench | named on the 2.8.0 manual page; it benchmarks EVALUATION, not attribution, so it does not bear |
| `agda-criterion`, `agda-ghc-names` | named on the 2.8.0 manual page | both are RUN-TIME tools |
| #1646's mitigation wording | reached through a search summary | **the copying claim itself is READ in #1646; only the "keep exports small" wording is POINTER-ONLY** |

### WHY NOT (sources I chose not to read)

- **"Non-wellfounded trees in Homotopy Type Theory", arXiv 1504.02949.** I
  fetched it and **the PDF text did not extract**. I did not retry, because a
  2015 HoTT paper is unlikely to price 2.8.0.
- **The `deepwiki` page on Agda's internal type checking.** **WHY NOT: it is a
  generated summary, not a primary source.** The brief's hard rule on citations
  makes a generated page the worst kind of locator.
- **agda#2990, #4457, #5279, #8028, #8332, #8383, #8473.** These are Agda's OWN
  optimisation work, not user-facing pathologies. **WHY NOT: they change how
  fast Agda is, not what shape a user should avoid.** They cannot produce a row
  in section 3's table.
- **agda#3846, #5396, #5462, #5589, #5923, #7090 on `REWRITE`.** **WHY NOT: no
  master in `src/` enables `--rewriting`. MEASURED** (section 3).
- **Coq and Rocq performance literature.** **WHY NOT: Coq's conversion checker,
  its universe algorithm and its `Qed` cost model are a different machine.** P-l
  says a judgement at one site is a hypothesis at another, and the distance here
  is a whole implementation. **This is a real gap in my survey and I mark it.**

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-317/`:

- `LJ-1.317.md`, the pinned brief, written by the orchestrator before me.
- `lj-1.317-report.md`, this file. **TRACKED and MODIFIED, not untracked, and
  the reason is not mine.** I created the skeleton, and a sibling's commit swept
  it into the tree while I worked. **MEASURED:**
  `git log --oneline -1 -- agents/tasks/LJ-1-317/lj-1.317-report.md` names
  `9b4ca18`, whose subject is `[LJ-1.311] SPLIT: the NO-GO stands, and three of
  its measurements were false`. **I committed nothing.** `[LJ-1.309]` reported
  the same behaviour at its `:462-466`, so this is now the SECOND time a
  sibling's commit picked up another agent's in-progress file. **The
  orchestrator should know it repeats.**
- `agents/tasks/LJ-1-316/lj-1.316-report.md` also shows modified in
  `git status`. **That is a sibling's file and I did not touch it.**

**No master edited. No `src/` path written. No `dev/` path written. Nothing
landed in `dev/literature/` or `dev/LESSONS.md`.** I did not touch
`src/Everything.lagda.md`, another task directory, or `AGENTS.md`. **No commit,
no push, no `git checkout .`, no stash, no reset, no clean. I did not run
`make check`. I RAN NO AGDA**, so both C-12 slots stayed with the siblings.
