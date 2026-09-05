# LJ-1.581 report: an L-set injection code for the pairs of κ into κ

## HEAD
head_slot: coder
machine: shared
verdict: STOP

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-581/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event: the largest resident set was 668 MB against the 8 GB
cap (`agents/tasks/LJ-1-581/runs/s6-2.out:5`). Nothing is postulated and no hole
is left, so every reduction in the probe is a measurement and not a claim. Every
file of this task is raw `.agda` or `.md`, so none carries an ` ```agda ` fence,
all count 0 in-fence lines, and the ratio bar cannot fire on them.

## VERDICT

**STOP, AND IT IS A REFUTATION AND NOT A SHORTFALL.** The obligation is not
inhabited: the witness reports `missing exit=42`, `1 UNRESOLVED of 1`,
`probe_red=False` (`agents/tasks/LJ-1-581/runs/witness-2.out:3-4`). The stated
stop is `agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md`.

Three results, each a term that typechecks in a green file:

1. **THE BRIEF'S TYPE IS `[LJ-1.556]`'S `BriefTarget`.** Two identity functions
   say so: `Probe581.agda:133-134` and `:136-137`, both `λ x → x`. The brief
   states it does not re-dispatch that type. It does.
2. **THE TYPE IS FALSE.** `obligation-false : Obligation → Empty.⊥`
   (`Probe581.agda:376`). The counterexample is κ := 2. `IsOrd` and
   `IsCardinalL` hold at 2 and every finite ordinal, and four pairs do not
   inject into two places.
3. **`SquareStep`, THE CORRECTION `[LJ-1.556]` TOLD THE NEXT BRIEF TO FUND, IS
   ALSO FALSE.** `squarestep-false : P556.SquareStep → Empty.⊥`
   (`Probe581.agda:387`), and it costs no construction: the induction hypothesis
   at 2 is supplied by `SquareStep` itself, used at 0 and at 1 first.

**W3 IS GO** and green on the first run (`runs/w3-1.out:23`, `EXIT=0`).

**AND THE CHAPTER IS 90 TIMES CHEAPER THAN IT LOOKED.** See `## PRICES`.

## D-10, BEFORE ANY AGDA

The brief orders this section first and names its source: `[LJ-1.567]`'s
`## WHAT SQUARESTEP STILL WANTS`. That section is
`agents/tasks/LJ-1-567/lj-1.567-report.md:177-191`, and it lists three things.

**WHICH OF THE THREE DOES THIS OBLIGATION NEED? ALL THREE, AND THE THIRD IS THE
ONE THAT DECIDES THE TASK.**

- **First, the well-order on `Square.sqL κ` as a formula**
  (`lj-1.567-report.md:182-185`). Needed. `[LJ-1.567]` filled the ORDER SLOT and
  says its witness is neither total nor well-founded (`:214-217`), so no
  collapse runs on it yet.
- **Second, the recursion itself, an `f` with `Approx O κ f`**
  (`lj-1.567-report.md:185-188`). Needed, and no chapter builds it at this
  domain today.
- **Third, the induction hypothesis `InternalSquare β` at every smaller infinite
  ordinal, plus the range staying inside κ** (`lj-1.567-report.md:188-191`).
  **Needed, AND IT IS ABSENT FROM THE OBLIGATION'S HYPOTHESES.** The obligation
  offers `IsOrd (fst κ)` and `IsCardinalL κ` and nothing else. In `SquareStep`
  the third item is a HYPOTHESIS (`agents/tasks/LJ-1-556/Probe556.agda:361`); in
  this brief there is no such hypothesis at all.

**THAT IS WHERE D-10 STOPPED BEING A PRICING QUESTION AND BECAME A TRUTH
QUESTION.** D-10 says a target can be false and that the check is five minutes,
and it names the cardinality obstruction as the usual killer. The check here is
one line of arithmetic: `IsCardinalL` (`src/L/Cardinal.lagda.md:230`) is the
initial-ordinal condition, every finite ordinal satisfies it, and the square law
fails at every finite ordinal above 1. I then spent the task turning that line
into terms rather than into a sentence, because a sentence is not evidence.

**AND THE THIRD ITEM DOES NOT REPAIR IT EITHER**, which is the finding worth the
most to the next brief. `[LJ-1.567]`'s prose says "at every smaller INFINITE
ordinal" and `[LJ-1.556]`'s comment says the same
(`agents/tasks/LJ-1-556/Probe556.agda:340-341`). **The Agda of `SquareStep`
says every smaller ordinal, and restricts κ not at all**
(`Probe556.agda:357-362`). So the correction, as written, is false at the same
κ := 2. The prose was right and the type did not carry it.

## W3, THE WIDEST UNMEASURED TERM

The brief names it: "the pairs of κ, as an L-SET with its two projections, TYPE
ONLY", and attaches one question: "`[LJ-1.556]` reports its section 1 delivers
the product and its two readings; **check whether that is the same object**
before you build anything on top of it."

**IT WAS WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
task.** The slice is `agents/tasks/LJ-1-581/runs/W3.agda`, 83 lines. It states
`PairsOf` at the AMBIENT pair `pr`, with both components as INDICES and the
second reading untruncated, and it inhabits that type from `[LJ-1.556]`'s
section 1 alone. Inhabiting is the only way to answer the question the brief
attached, so the slice is TYPE ONLY plus that one answer, and it builds no set.

**GREEN ON THE FIRST RUN, exit 0.** `runs/w3-1.out` (202.25 s, everything cold),
`runs/w3-2.out` (1.85 s, own interface deleted, the import warm). There is no
red predecessor.

**THE ANSWER IS YES, AND ONE BRIDGE IS THE WHOLE OF IT.** `[LJ-1.556]` states
both readings at the L-pair `prʟ`; the type above states them at the ambient
pair `pr`. `prʟ-fst` (`src/L/Coding/Model.lagda.md:329`) crosses that gap, and
nothing else had to be checked. `same-object` is `Probe581.agda:94`.

**THE BRIEF ESTIMATED "about 15 lines, under 90 seconds". The measured numbers
are 83 lines and 1.85 s warm, or 202.25 s cold.** The cold number is NOT this
slice's price: `LJ-1-556.Probe556` is imported rather than transcribed, and that
probe alone costs about 187 s on a cold interface here (`runs/final-2.out:5` at
189.41 s, against 2.03 s with the import warm at `runs/final-1.out:4`). **I
report the number I measured and not the number the brief guessed.**

## WHAT I COPIED

**FROM `[LJ-1.556]`, BY IMPORT AND NOT BY TRANSCRIPTION.** `import
LJ-1-556.Probe556 {ℓ} lem as P556` (`Probe581.agda:51`), which is how
`[LJ-1.567]` took the same object (`agents/tasks/LJ-1-567/runs/W3.agda:42`).
Three names of its section 1 are used, and nothing else of that probe is:

- `Square.sqL` (`agents/tasks/LJ-1-556/Probe556.agda:148`), the set. Used as the
  domain object. Unchanged.
- `Square.sqL-in` (`:156`), reading one. Used under `fiber` to build
  `ix→mem` (`Probe581.agda:165-172`). **Changed only by composing with `prʟ-fst`**,
  because my type speaks in `pr` and its type speaks in `prʟ`.
- `Square.sqL-out` (`:186`), reading two, untruncated. Used in `same-object`
  (`Probe581.agda:107-110`), and composed with `prʟ-fst` the same way.

Its sections 2, 3 and 4 are NOT used as mathematics. Sections 3 and 4 are named
only as the types this task refutes (`Probe581.agda:133-137`, `:384`, `:387`).

**FROM `[LJ-1.567]`, NOTHING.** No term of that probe is imported and no line of
it is copied. Its report is used, at `lj-1.567-report.md:177-191`, and only to
answer D-10 above. `col-step` is not needed by this obligation: the obligation
asks for the CODE, and `col-step` is one formula of the recursion that would
BUILD a code. **A task that cannot state its target truly does not need its
recursion step.**

**FROM `src/`, ONE TERM DID THE WORK OF A CHAPTER.** `readL`
(`src/L/CantorBernstein.lagda.md:33`) turns the four `InjCode` conjuncts into an
honest ambient injection. Every one of the three cardinal facts
(`Probe581.agda:299`, `:305`, `:322`) and the refutation itself go through it.
It was already in the tree and no probe of this chapter had used it.

## WHAT ROW 5 NOW NEEDS

`[LJ-1.574]` says: "If it lands, step 3 is a `hasSeparationL` over the
description this file already carries, and the selection machinery of sections 3
and 4 is reused unchanged"
(`agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md:94-97`).

**I AGREE WITH THE SHAPE, AND I ADD ONE CONDITION THE SENTENCE DOES NOT STATE.**

`hasSeparationL` takes `(a : S) (φ : Formula S 1)`
(`src/L/Axioms/Full.lagda.md:144`), so step 3 carves a subset of κ out of κ by a
one-place formula, and the code must enter that formula as an OBJECT-LANGUAGE
CONSTANT. `[LJ-1.556]`'s `sqFo` shows the pattern with `con κ`
(`agents/tasks/LJ-1-556/Probe556.agda:105-108`). **So a code is exactly the
right currency and an ambient function is not**, which is what the brief said
and what this task confirms: my `square-from-code` (`Probe581.agda:193`) reads a
code DOWN to an ambient injection in a few lines, and nothing reads one up.

**BUT ROW 5 CANNOT CONSUME A SQUARE LAW UNTIL IT CARRIES AN INFINITY CLAUSE.**
`[LJ-1.574]`'s `Obligation` (`agents/tasks/LJ-1-574/Probe574.agda:766`) and
`[LJ-1.549]`'s `Residue` (`agents/tasks/LJ-1-549/Probe549.agda:668`) are stated
under `SuccCardL δ κ` and carry no infinity clause on κ. The clause exists
upstream, in the trophy statement itself (`src/L/GCH.lagda.md:64`), and nothing
threads it down today. **So the order of work changes**: thread the clause
first, then state the square law at a κ that carries it.

So row 5 needs, in this order:

1. **The infinity clause threaded from `GCHStatement` into row 5's own types.**
   Small, and it decides the shape of everything after it.
2. **`SquareStepInf`** (`Probe581.agda:427`) funded, or the same type in the
   `γ∉ω`-plus-`numerals` spelling of `src/L/CodedShift.lagda.md:37-39`. That
   type is not inhabited here and it is not refuted here.
3. **Then the three of `[LJ-1.567]`'s list**, in that order: the well-order as a
   formula, the recursion, and the induction hypothesis. **Item 3 of that list
   is now a HYPOTHESIS with a corrected quantifier and not a construction.**

## THE MEASURED CURE, AND IT IS THE LARGEST NUMBER OF THIS TASK

**THE PAIRS-OF-κ MACHINERY IS NOT EXPENSIVE. ONE COMBINATOR WAS.**

The first green whole probe cost 202.45 s (`runs/s6-1.out:4`). `agda
--profile=definitions` put 199,369 ms of 201,645 ms on ONE term, `Read.ix→mem-inj`
(`runs/price-3.out:5,:7`). Neither import was the cause: `L.Cardinal {ℓ} lem`
alone is 1.65 s (`runs/price-1.out:4`) and `L.CantorBernstein {ℓ} lem` alone is
1.64 s (`runs/price-2.out:4`).

I sealed the term's two inputs with `opaque` first. **That was measured and it
was wrong**: 202.45 s to 178.45 s (`runs/s6-2.out:4`), with the same term still
at 173,465 ms of 175,278 ms (`runs/price-4.out:4,:6`). **P-i is not the law that
applies to this term**, and the seal is not in the file.

The bisection then took the term apart, in `agents/tasks/LJ-1-581/runs/Bisect.agda`:

| slice | what it held | seconds |
|---|---|---|
| `runs/bisect-1.out:4` | the term's second half, nothing of `sqL` in scope | 159.78 |
| `runs/bisect-2.out:4` | `pr-inj` and `↪-inj`, each standing alone | 0.679 total |
| `runs/bisect-4.out:4-7` | the same three lines written three ways | see below |

**THE THIRD RUN IS THE RESULT.** One profiled file, three ways to write the same
path between two pairs:

- `ΣPathP (↪-inj (fst split) , ↪-inj (snd split))`: **160,042 ms**
- `cong₂ _,_ (↪-inj (fst split)) (↪-inj (snd split))`: **161,723 ms**
- `λ i → (↪-inj (fst split) i , ↪-inj (snd split) i)`: **below the profiler's
  reporting threshold, so it does not appear in the table at all**

Applied at my own site, the whole probe fell from 202.45 s to 2.23 s
(`runs/s6-3.out:4`), and to 2.03 s in its final form (`runs/final-1.out:4`).
**That is a factor of 90, from rewriting one expression.**

**WHAT THIS DOES AND DOES NOT SAY.** It is measured at THIS site, on paths
between pairs of `⟪ fst κ ⟫` whose components come from `pr-inj`. `[LJ-1.556]`
writes the `ΣPathP` form at `agents/tasks/LJ-1-556/Probe556.agda:178`, inside
`isPropComp`, and its probe costs about 187 s cold here. **I did not edit that
file and I did not measure the cure there. `AGENTS.md:45` forbids me to claim
it transfers.** It is a prediction with an address, and it costs one line to
test.

**WHY THIS MATTERS MORE THAN THE REFUTATION FOR PRICING.** The brief says "the
square law is the largest single object on the remaining bill", and every price
this chapter has quoted was taken with this expression in it. If the cure holds
at `Probe556.agda:178`, the pairs object is a few seconds and not a few minutes,
and the chapter should be re-priced before it is funded.

## W2

**The rule is answered and it was not weakened.** The mathematics is written
once at a generic carrier and instantiated. `PairsOf`, `same-object`, `Coded`,
`Obligation` and the whole `Read` module (`Probe581.agda:86`, `:94`, `:127`,
`:130`, `:153`) take κ as a parameter and name no numeral. Only section 4
instantiates, at κ := 2 (`Probe581.agda:242-245`), and it instantiates because a
counterexample is a site and not a generality. `pigeon` (`Probe581.agda:337`) is
stated at an arbitrary type `X` and is not about ordinals at all. Nothing is
written twice, and no deadline forced a fixed form.

## PRICES, EVERY ONE MEASURED ON THIS PANE

| run | what | seconds | exit |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, everything cold | 202.25 | 0 |
| `runs/w3-2.out` | W3 alone, own interface deleted, import warm | 1.85 | 0 |
| `runs/s3-1.out` | sections 1 to 3, missing `ΣPathP` import | red | 42 |
| `runs/s3-2.out` | sections 1 to 3, after the import fix | 207.73 | 0 |
| `runs/s3-3.out` | sections 1 to 3, unchanged, interface cached | 1.77 | 0 |
| `runs/s45-1.out` | sections 4 to 6 as a slice, `V` at the wrong level | red | 42 |
| `runs/s45-2.out` | sections 4 to 6 as a slice, green | 2.23 | 0 |
| `runs/s6-1.out` | the whole probe, 6 sections, first green | 202.45 | 0 |
| `runs/s6-2.out` | the whole probe, the seal tried | 178.45 | 0 |
| `runs/s6-3.out` | the whole probe, the interval form | 2.23 | 0 |
| `runs/s6-4.out` | the whole probe, the useless seal removed | 2.43 | 0 |
| `runs/price-1.out` | `L.Cardinal {ℓ} lem` alone | 1.65 | 0 |
| `runs/price-2.out` | `L.CantorBernstein {ℓ} lem` alone | 1.64 | 0 |
| `runs/price-3.out` | attribution, profiled, before the cure | 201.6 total | 0 |
| `runs/price-4.out` | attribution, profiled, after the seal | 175.3 total | 0 |
| `runs/bisect-1.out` | the term's second half alone | 159.78 | 0 |
| `runs/bisect-2.out` | `pr-inj` and `↪-inj` apart, profiled | 0.679 total | 0 |
| `runs/bisect-3.out` | the three-way file, `Raw` at the wrong level | red | 42 |
| `runs/bisect-4.out` | the three-way file, profiled | 322.5 total | 0 |
| `runs/final-1.out` | the whole probe, own interface deleted | 2.03 | 0 |
| `runs/final-2.out` | the whole probe, `Probe556` ALSO cold | 189.41 | 0 |
| `runs/final-3.out` | the whole probe, final file state, interface deleted | 2.07 | 0 |
| `runs/witness-1.out` | the program's obligation witness | 1.96 | 1 |
| `runs/witness-2.out` | the obligation witness on the final file | 1.76 | 1 |
| `runs/confirm.out` | all five files of this task, final state, back to back | 1.74, 1.56, 1.73, 0.90, 1.62 | 0 each |

`agents/tasks/LJ-1-581/Probe581.agda` is 441 lines,
`agents/tasks/LJ-1-581/runs/W3.agda` is 83 lines. **The brief estimated about
230 lines with about 60 for the obligation.** The line count is close; the
obligation is not there, and what stands in its place is its refutation, at
`Probe581.agda:337-441`, which is 105 lines with its comments.

**THE PROFILED RUNS ARE ATTRIBUTIONS AND NOT PRICES.** `--profile=definitions`
adds overhead, and each of those four run files says so in its own header.

## ARCHIVE USED

The brief's corpus search returned five candidates. Every one is named.

- **`archive/dev/LJ-dispatch-index.md`**: READ, and it is premise 11. `:100`
  says "| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master |
  fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and
  levelIn survive on the hull adequacy |". **Nothing in this task is funded
  against that figure**, as the brief orders and as `[LJ-1.556]` said of itself.
  It is a number in a table row about a different object at an older tree, and
  `AGENTS.md:17-18` refuses it.
- **`dev/ARCHIVE.md`**: READ. `:1` says "# ARCHIVE.md: the archive registry". I searched it for
  `SquareLaw`, for `Cardinal` and for `square`: it has no row for any of them,
  so no module of this chain has ever been retired and the registry has nothing
  to say about this task. W4 is not engaged: I retired no module.
- **`archive/dev/JOURNAL-archived.md`**: NOT USED, declined. Not read. It is the
  closed narrative journal, and the Boundary says a live document carries no
  history. Nothing in this task turns on what an older session recorded: the
  three types I needed are in two probes that are live and tracked.
- **`archive/dev/JOURNAL.md`**: NOT USED, declined. Not read, for the same
  reason as the entry above.
- **`archive/dev/DD-archived.md`**: NOT USED, declined. Not read. The `DD`
  series is SET ASIDE in that form, and the clause that binds me here is W2,
  which the slot file states directly.

## LITERATURE USED

The brief's corpus search returned five candidates. Every one is named.

- **`dev/literature/devlin-II5.md`**: READ, and it corroborates the finding.
  `:281` says "(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal
  fact". **The source states its cardinal fact FOR INFINITE α.** The dossier
  therefore agrees with the refutation from the other side: the clause the two
  refuted types dropped is a clause the literature never drops.
- **`dev/literature/truncation-and-selection.md`**: READ. `:83` says "**So a
  proof that only needs cardinal arithmetic never needs an injection as". This
  is why `Coded` (`Probe581.agda:127`) is TRUNCATED and why the refutation may
  spend `PT.rec` freely: the target is `Empty.⊥`, which is a proposition, so no
  choice is needed anywhere in this file.
- **`dev/literature/terms-2026-08.md`**: NOT USED, declined. Not read. It is the
  terminology dossier for the owner's naming ruling. This task names nothing new
  outside its own probe and adds no glossary entry, which the Boundary forbids
  me to do anyway.
- **`dev/literature/geology.md`**: NOT USED, declined. Not read. Set-theoretic
  geology is not on the route to either trophy and nothing in this obligation
  touches it.
- **`dev/literature/digest.md`**: NOT USED, declined. Not read. It pins the
  orthodox form of the RUD route, and this obligation is on the collapse route,
  as `[LJ-1.556]` also recorded when it declined the same file.

## ONE CORRECTION TO A PREMISE, AND IT DOES NOT CHANGE THE BRIEF

Premise 6 cites `agents/tasks/LJ-1-556/lj-1.556-report.md:298` for "`[LJ-1.556]`
is a NO-GO and calls my wider type under-hypothesized". That line is the heading
`## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE`. The sentence is two lines later,
at `:300`. **The premise is TRUE and the reading is right.** I record the slip
only because the next agent will follow the citation.

## WHAT WAS NOT DONE

I did not inhabit the obligation, and no term of any file of this task is named
`pairs-into-kappa-coded`. I did not postulate and I left no hole. I did not
weaken the obligation and call it the obligation: the brief's type stands
written out as `Obligation` (`Probe581.agda:130`) and is refuted rather than
approximated. I did not build row 5 and I did not touch the assignment. I did
not build a code at any cardinal, and the `SquareStep` refutation needs none. I
did not edit `agents/tasks/LJ-1-556/Probe556.agda`, so the cure at its line 178
is a prediction and not a measurement. I did not fund anything against the
775-line figure. Nothing lands in `src/`. I did not set `GHCRTS`. I did not
commit and did not push.

**I DID RUN THE INDIVIDUAL GATES, because the Boundary says to run them while
working, and every one is clean on this tree**: `lint-prose`, `lint-agda`,
`check-probes` ("no probe outside agents/tasks/ and no generated file"),
`check-fences`, `check-rule-ids`, `check-glossary`, `check-closure`,
`check-spec-surface`, `weave-i18n --check`, and `ledger.py --check`
("declaration clean; standing 33,523 lines measured over 100 masters"). I did
not run `make check` as a whole, because I committed nothing and `typecheck`
rebuilds `src/Everything.lagda.md`, which this task does not touch.
