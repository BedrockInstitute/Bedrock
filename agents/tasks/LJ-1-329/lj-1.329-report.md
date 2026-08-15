# LJ-1.329 report: code ONE ambient function as a member of an L-set

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: WRONG-OBJECT

**The brief's premise is FALSE, and this is the third brief in a row that
carried a false premise.**

**Consumer A does not want ONE ambient function coded. It wants a TOTAL
injective map out of the ambient type `sq α`.** `pullOrder`'s parameter is a
function, not a point (`src/L/Choice/Step.lagda.md:236-237`). One coded function
is a point of the carrier. **Negative control 3 made Agda say this in one line:**
`C !=< (sq α → C)`.

**And I MEASURED what that total map buys.** At every infinite ordinal `α` where
the descent stands, the map consumer A asks for well-orders the ambient
decidable power set of `⟪ α ⟫`, and then selects, untruncated, from every
ambient property of those subsets. **That is an ambient choice principle over a
power set. It is not a coding obligation and no formula discharges it.** Term:
`descent-crossing→choice`, `agents/tasks/LJ-1-329/ProbeLJ1329A.agda:204-213`,
exit 0.

**The positive object the brief names is ALREADY DELIVERED, three times.**
`ShiftGraph` codes the ambient successor shift as a member of an L-set
(`src/L/Absorption.lagda.md:538-551`), and `InclGraph` and `OrdIncl` code the
inclusion (`src/L/InjChain.lagda.md:575-576` and `:604-607`). I re-ran
`[LJ-1.326]`'s probe under my own hand to confirm the `InjCode` tuple at
`ShiftGraph`'s site: exit 0, 1.83 s.

**So there is no third thing.** Either the function is DEFINABLE, and the tree
already carves such functions at three sites, or the function is ARBITRARY, and
then the crossing is `AmbientToCode`, which `[LJ-1.300]` labelled **INDEPENDENT**
at `agents/tasks/LJ-1-300/lj-1.300-report.md:195-207`. **Consumer A's `sq α` is
the arbitrary case.** The convergence of three tasks is a convergence on a NAME,
not on an object.

## 1. WHICH FUNCTION I CHOSE, AND WHY THE CHOICE REFUTED THE ORDER

The brief orders me to choose the function first and to justify the choice at
`file:line`. I did that first, and the choice step is the result.

**`[LJ-1.321]` states the shape:** an injection of `sq α` into
`Mem (Lset β)`, at `agents/tasks/LJ-1-321/lj-1.321-report.md:267-285`, built as
`code→order` at `agents/tasks/LJ-1-321/Door.agda:415-418`.

**I re-derived that term under my own hand** (C-44), at
`ProbeLJ1329A.agda:60-63`. Its third parameter has type `sq α → C`. **That is a
function out of the whole ambient type.** `sq α` is
`Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] (injectivity)`,
`src/L/Ordinal/SquareLaw.lagda.md:685-688`. Its elements are AMBIENT injective
pairing functions, all of them, not the definable ones.

**So the function to choose does not exist.** The obligation names no single
function. It names a map defined at every ambient function at once. **MEASURED**
by the type, and MEASURED again by negative control 3.

**I therefore chose the smaller question the brief permits:** what does that
total map cost, in the ambient theory Bedrock has. Section 2 answers it.

## 2. THE TERM: THE CROSSING IS AN AMBIENT CHOICE PRINCIPLE

The probe is `agents/tasks/LJ-1-329/ProbeLJ1329A.agda`. **238 lines, 118 code
lines, of which 74 are Parts 2 to 4 and the rest are the module header and the
imports.** Exit 0. Longest single invocation 1.83 s.

### 2.1 The ambient power set injects into `sq α`

`ProbeLJ1329A.agda:82-121`, `module Encode`. Given ONE member `s` of `sq α` and
two distinct points `a₀` and `a₁` of `⟪ α ⟫`, each decidable subset `S` names
its own member of `sq α`:

```agda
tag S (x , y) = fn (fn (x , y) , pick (S x))
```

`:107`. The subset rides in the second argument of the outer application.
`tag-inj` (`:109-111`) reads the value back through the injectivity of `fn`
alone. `enc-inj` (`:116-121`) recovers `S` pointwise. **Nothing in this block
names the tower, an ordinal, a stage or a formula. MEASURED** by reading the
module header.

### 2.2 What the crossing buys

```agda
crossing→powerWO : (α : V ℓ) (a₀ a₁ : ⟪ α ⟫) → (a₀ ≡ a₁ → Empty.⊥)
                 → ∥ sq α ∥₁ → SWO {ℓ} (sq α)
                 → SWO {ℓ} (⟪ α ⟫ → Bool)
```

`:134-142`. It takes exactly what consumer A asks for. It returns a well-order
of the ambient decidable power set of the index type. `powerChoice` (`:144-150`)
then applies `leastOf` and selects an untruncated witness for every ambient
property of those subsets.

**The two points are FREE at the descent's own site.** `module Points`
(`:171-199`) builds them from `IsOrd α` and `⟨ ω ∈ˢ α ⟩` alone. The descent runs
at infinite ordinals: `BoundedSubsetAt` excludes omega and below
(`src/L/BoundedSubset.lagda.md:1388-1391`), and `Init`'s second row is
`⟨ ω ∈ˢ α ⟩` (`src/L/Ordinal/SquareLaw.lagda.md:692-694`). So the final statement
carries no point hypothesis:

```agda
descent-crossing→choice
  : (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩
  → ∥ sq α ∥₁ → SWO {ℓ} (sq α)
  → (P : (⟪ α ⟫ → Bool) → hProp (ℓ-suc ℓ))
  → ∥ Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩ ∥₁
  → Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩
```

`:204-213`. Green.

### 2.3 What this measurement says, and what it does not

**IT SAYS:** the object `[LJ-1.321]` reduced the debt to is not weaker than a
choice principle over an ambient power set. Bedrock's ambient theory takes `LEM`
only (`src/Base/Classical.lagda.md:41-42`). **INFERRED, and I mark it INFERRED:**
no ambient choice axiom is available to build the map, so the map cannot be
built from the delivered tree. I did not search for a proof and I did not find
one.

**IT DOES NOT SAY:** that the map is false. It is TRUE whenever the ambient
universe well-orders its power sets. That is the same position `[LJ-1.300]` put
`AmbientToCode` in, and the correct word is the same word: **INDEPENDENT**.

**IT DOES NOT SAY:** that no `2-Constant` map exists by another route.
`[LJ-1.321]` section 8 lists three live candidates and this probe touches none
of them. C-36: the door is not closed, and this report closes only the route
through `pullOrder`.

### 2.4 The census, re-derived (C-44)

`[LJ-1.321]` measured that no `SWO` in the tree carries a function type. **I
re-ran the census myself.** `grep -rn ": SWO" src/` returns **35** lines. The
constructed carriers are `⟪ A ⟫`, `⟪ α ⟫`, `⟪ Lset δ ⟫`, `New δ`,
`Mem (Lset γ)`, `Mem (Lset boundOrd)`, `Name`, `Pair`, `PairA`, `Point n`,
`Limit`, `SL`, `ℕ`, and products of those. **NONE is a function type. MEASURED.**

## 3. WHAT RAN, WITH THE MACHINE LOAD BESIDE EVERY FIGURE

Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. It returned **1** every
time, so one sibling process was live and I took the second slot. C-12 was never
exceeded. `GHCRTS="-A64m -I0 -M8g"` on every run. One process. No heap wall. The
longest single invocation was 1.83 s, far under the 30-minute line.

| run | what | exit | real s | agda slots before | 1-minute load |
|---|---|---:|---:|---:|---:|
| 1 | first check, four import errors | error | 1.53 | 1 | 5.20 |
| 2 | imports fixed, GREEN | **0** | 1.53 | 1 | 4.91 |
| 3 | **NEGATIVE CONTROL 1** | **42** | 1.53 | 1 | 4.91 |
| 4 | **NEGATIVE CONTROL 2** | **42** | 1.52 | 1 | 5.50 |
| 5 | **NEGATIVE CONTROL 3** | **42** | 1.59 | 1 | 6.16 |
| 6 | controls reverted, final GREEN | **0** | 1.61 | 1 | 6.16 |
| 7 | `[LJ-1.326]`'s probe re-run under my hand | **0** | 1.83 | 1 | 6.12 |

**Every figure is WARM.** Every interface was already built. **No cold cost is
measured here.** The machine was not quiet; my deliverable is a term, so the
load figures do not bear on it.

## 4. THE THREE NEGATIVE CONTROLS, AND WHAT EACH ONE NAMED

Each control was applied, run and reverted. The backups sit in the session
scratchpad, outside the repository. The controls are recorded in the probe at
`ProbeLJ1329A.agda:215-238`, because nothing typechecks the file after this task
closes.

**CONTROL 1, on the encoding.** I set `pick true = a₀`, so the two points
collapse. Agda refused at line 93, the `pick-inj false true` clause:

```
error: [UnequalTerms] a₀ != a₁ of type ...
when checking that the expression e has type a₀ ≡ a₁
```

**So the encoding really consumes the distinctness of the two points.** The
injection is not an accident of a loose type.

**CONTROL 2, on the readback.** I changed `cong fst` to `cong snd` in
`tag-inj`. Agda refused at line 111:

```
error: [UnequalTerms] pick (S x) != fst s (x , y) of type ...
```

**So the readback really reads the composite value and not the tag.**

**CONTROL 3, AND IT MEASURES RATHER THAN CHECKS.** I wrote the brief's own
premise as a type: ONE coded function, that is a point `c₀ : C` of the
well-ordered carrier, offered where `code→order` takes its map. Agda refused and
named the blocker:

```
error: [UnequalTerms] C !=< (sq α → C)
when checking that the expression c₀ has type sq α → C
```

**That error is the whole report in one line.** The obligation is a function out
of `sq α`. One code is a point. **The gap between them is the ambient type
`sq α` itself, and no description closes it.**

## 5. WHAT THE DESCENT RE-PRICES TO

**Nothing in this report changes a delivered term.** It changes which term the
project should fund next.

| object | status after this probe |
|---|---|
| **the crossing for a DEFINABLE function** | **DELIVERED, three sites.** `InclGraph` (`src/L/InjChain.lagda.md:575`), `OrdIncl` (`:604`), `ShiftGraph` (`src/L/Absorption.lagda.md:538`). `[LJ-1.326]`'s 8-line tuple re-runs green under my hand |
| **the crossing for an ARBITRARY function** | **INDEPENDENT.** `AmbientToCode`, `agents/tasks/LJ-1-299/NoInj2.agda:131-133`, ruled at `agents/tasks/LJ-1-300/lj-1.300-report.md:195-207` |
| **consumer A's `sq α → Mem (Lset β)`** | **the ARBITRARY case, and this probe measures its strength**: it well-orders the ambient power set of `⟪ α ⟫`. `ProbeLJ1329A.agda:204-213` |
| **a fourth `Carve`** | **NOT NEEDED for consumer A.** `[LJ-1.327]` priced it at about 127 lines (`lj-1.327-report.md:197`). That price buys a description, and consumer A's wall is not a description |
| **`[LJ-1.327]`'s about 820 for the coded square law** | **UNCHANGED, and still not consumer A's object.** Its two consumers are ambient (`lj-1.327-report.md:215-227`) |

**THE ONE-LINE RECOMMENDATION, and it is a STOP.**

**Do not fund the ambient-to-code crossing for a function. There is no such
object.** Fund one of two things instead, and say which:

1. **A CANONICAL element of `sq α` at non-initial `α`.** The tree already
   delivers `via-col-square` at INITIAL `α`
   (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) and `squareω` at omega
   (`src/L/InjChain.lagda.md:184-185`), both untruncated and both canonical.
   **The gap is exactly the non-initial ordinals**, which `[LJ-1.300]` measured
   at `lj-1.300-report.md:162-165`. A canonical element needs no well-order on
   `sq α`, no crossing and no choice.
2. **Move the descent's `sq` hypothesis inside L.** `BoundedSubsetAt` takes `sq`
   as an AMBIENT family (`src/L/BoundedSubset.lagda.md:1388-1391`), and the
   restated trophy says「no ambient function type crosses the `⊨` boundary」
   (`src/L/GCH.lagda.md:58`). **The two statements disagree about which side the
   pairing function lives on.** That disagreement, and not the crossing, is what
   generated three tasks of search. **I did not price either option and I do not
   guess a number.**

## 6. DD4, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's own axis is AC closure against GCH
closure, fixed in code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the term name a tower, a stage or an ordinal presentation?**

**Answer: my whole term is TOWER-BLIND, and I say so in one line as the brief
asks: YES.** MEASURED by reading my own module headers.

- `module Encode` (`ProbeLJ1329A.agda:82`) takes an ambient set and two of its
  index points. It names no `L`, no `Lset`, no stage and no formula.
- `crossing→powerWO` (`:134`) and `powerChoice` (`:144`) name `sq` and `SWO`
  only.
- `module Points` (`:171`) names `IsOrd` and `ω`, so it names the AMBIENT
  ordinals. It does not name `L`.

**WHICH CLOSURE IT WOULD LAND IN: NEITHER, and that is the point.** My term is a
refutation, not a supplier. It adds no mathematics to either trophy. **I did not
measure closure figures and I do not guess them**, because the term is not
landed and its placement is not a question that arises.

**AND THE DD4 READING THE BRIEF ASKED FOR IS THE OPPOSITE OF ITS HOPE.** The
brief calls this crossing「the best shared candidate left」because `pullOrder`
lives in the AC trophy's own machinery. **`pullOrder` IS shared and it IS
generic, and that is exactly why it cannot help here.** Being generic in the
carrier `B` means it demands a total map out of `B`. **The share is real and the
leg it would share is unbuildable.** DD4 measures what two proofs SHARE, and it
never certifies that a shared device reaches a given site.

**And `[LJ-1.326]` measured that the restatement's DD4 rise is an artifact the
proof hands back exactly (`lj-1.326-report.md:191-195`). I read the SHARED row
and not the share, and my term moves neither.**

## 7. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **YOU CODE IT** | **NOT TAKEN, and the reason is the result.** There is no ONE function to code at consumer A's site. The three definable ones are already coded |
| **THE DESCRIPTION IS THE WALL** | **NOT TAKEN.** The description is not the wall. `hasSeparationL` takes an arbitrary `Formula S 1` with no certificate (`src/L/Axioms/Full.lagda.md:144-145`), and `[LJ-1.327]` measured that. **The wall is the ambient TYPE, not the object language** |
| **THE FUNCTION IS NOT WHAT THE DESCENT NEEDS** | **TAKEN, AND THIS IS THE RESULT.** The descent needs a canonical ELEMENT of `sq α`, or an internal restatement of the `sq` hypothesis. Section 5 names both |
| **IT NEEDS THE Π₁ HALF** | **NOT TAKEN.** I met no `Π₁` demand. Nothing I built touches the Levy hierarchy |
| **A WALL past 30 minutes** | **NOT TAKEN.** Longest single invocation 1.83 s |

## 8. WHAT I DID NOT SETTLE

I name these rather than guess.

1. **Whether a canonical element of `sq α` exists at non-initial `α`.** That is
   section 5's option 1 and I did not probe it. `[LJ-1.321]` section 8 lists
   four candidates, and its item 4, the `stage-card-upper` transplant, is still
   the strongest lead. P-l forbids me from pricing it by analogy.
2. **Whether the ambient `sq` hypothesis can move inside L.** Section 5's option
   2. Not attempted, not priced.
3. **Whether `sq α → Mem (Lset β)` is refutable.** It is not, and I did not try:
   `[LJ-1.300]` settled the same question for `AmbientToCode` with two models,
   and my statement sits on the same fence.
4. **A cold check cost.** Every figure here is warm.
5. **The closure figures.** Not measured. Section 6 says why.
6. **Whether `⟪ α ⟫ → Bool` equals the full ambient power set of `⟪ α ⟫` under
   `lem`.** I did not build that equivalence. My statement is about the
   DECIDABLE power set, in that word, and it is the weaker claim.

## 9. PROHIBITIONS, ANSWERED

- **Writes:** `agents/tasks/LJ-1-329/` only, two files, this report and
  `ProbeLJ1329A.agda`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.
- **I READ and RE-RAN `agents/tasks/LJ-1-326/ProbeLJ1326A.agda` and changed no
  line of it.** I read `agents/tasks/LJ-1-321/Door.agda` and
  `agents/tasks/LJ-1-314/CodeUntrunc.agda` and changed neither.
- **I read the CURRENT `src/L/GCH.lagda.md` and `src/L/BoundedSubset.lagda.md`**
  at HEAD, as the brief ordered. `GCH.lagda.md` is 70 lines and its statement is
  fully internal; `:58` is quoted in section 5.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda:** seven invocations, one at a time, load counted before each and equal
  to 1 every time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- The three control backups sit in the session scratchpad, outside the
  repository.
- `lint-prose.py --check` and `lint-agda.py --check` pass on what I wrote.

## 10. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-328/lj-1.328-report.md`, READ WHOLE.** Line read
  `:206-208`:「`orderAt` is AMBIENT and DELIVERED. So consumer A needs NO coded
  order at all. What it needs is `c : sq α → Mem (Lset β)` with injectivity」.
  **TOOK: the statement, and it is CORRECT.** Its next sentence calls that「the
  coding of an ambient FUNCTION as a member of an L-set」. **That half is
  MEASURED FALSE.** A total injective map out of `sq α` is not a coding of a
  function. Negative control 3 names the difference.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ `:1-120` and `:240-480`.**
  Line read `:384-385`:「the tree owes an injection of `sq α`, or of
  `⟪ α ⟫ ↪ ⟪ δ₀ ⟫`, into a carrier the tree already well-orders」. **TOOK: the
  shape, and I measured its strength.** Its `code→order` at `Door.agda:415-418`
  is re-derived at `ProbeLJ1329A.agda:60-63`, so I compile the claim I act on.
- **`agents/tasks/LJ-1-327/lj-1.327-report.md`, READ WHOLE.** Line read
  `:99-104`:「NO Δ₀ CERTIFICATE AND NO Σ₁ CERTIFICATE. MEASURED.
  `hasSeparationL` ... is FULL separation for an arbitrary formula」. **TOOK:
  the fact, and it is what rules out「the description is the wall」row.**
- **`agents/tasks/LJ-1-326/lj-1.326-report.md`, READ WHOLE, and its probe
  RE-RUN.** Line read `:84-92`:「`ShiftGraph γ oγ γ∉ω numerals` gives
  `InjCode SG.G SG.D SG.C` ... GO, at 8 lines」. **TOOK: the site, and I
  re-compiled it.** It is the delivered answer to the brief's positive question.
- **`agents/tasks/LJ-1-300/lj-1.300-report.md`, READ `:120-240`.** Line read
  `:207-209`:「Two models on opposite sides means INDEPENDENT. A statement true
  in some model is not false as mathematics」. **TOOK: the ruling and its word,
  and my section 2.3 uses the same word for the same reason.** D-10 says search
  before you build; this search saved the build.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:179` (L3.32-T144):「Execute D32: delete the Crossing section. DELETED, 86
  lines」. **TOOK, SHAPE ONLY:** the retired route ALSO carried a section named
  for a crossing between ambient and coded, and it RETIRED that section rather
  than building it. **WHAT WOULD NOT TRANSFER:** every figure in that row prices
  the rud presentation, whose code moved to `archive/src/2026-08-09-rud-route/`
  (`dev/PLAN.md:787`). The retired route had no `hasSeparationL` in this form and
  no `Formula S 1`, so its 86 lines price nothing here. **And `[LJ-1.293]`
  refuted the retired route's identity by machine, so no claim there is evidence
  for anything in `src/` today.**

## 11. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`. IT BEARS, and it settles the
  brief's own question.** READ `:14-20`, `:60-90`, `:180-200` and `:305-320`.
  **THE ONE LINE THE BRIEF ASKED FOR: my crossing puts the object on the WRONG
  side, and the digest says so before I did.** Line read `:313-316`:「A canonical
  injection needs a well-order on the INJECTIONS, which is what `<_L` supplies
  classically and what an ambient function type does not have」. **TOOK: that
  sentence, and my probe measures its price.** The classical move works because
  the injections `<_L` orders are SETS OF L. `sq α` is an ambient function type,
  so no order of L reaches it, and forcing an order onto it costs a power-set
  choice principle.
  **AND THE DIGEST'S SECOND CLAUSE BEARS TOO.** Line read `:68-70`:「The
  selection device is a definable well-order plus a universal guard. The guard
  turns "some witness" into "THE witness", and that is what makes the selection a
  function rather than a choice」. **TOOK: the criterion, and it names section
  5's option 1.** A CANONICAL element needs no order on the injections at all.
- **`dev/literature/devlin-II5.md`. IT DOES NOT BEAR ON THIS PROBE. WHY NOT:**
  my question is whether an ambient function type can be well-ordered. Devlin
  works under V = L, so he has no ambient function type to order, and
  `[LJ-1.327]` measured at `lj-1.327-report.md:382-389` that he never needs the
  pairing definable in L. Nothing in II.5 prices an ambient obligation.
- **WHY NOT re-fetched:** both digests landed with locators and I take only
  statement-level facts from them.

## 12. THE RULES THIS CHAIN EARNED, ANSWERED

- **C-44.** The brief asked me to assume a third false premise. **There is one,
  and it is the central one.** Section 1.
- **C-45.「`exit 0` is not a supply.」** My probe is green and it supplies
  nothing to the descent. I say so in the lead.
- **C-36.「A failed substitution is not a proof of impossibility.」** Section 2.3
  states what I did NOT prove. The door is not closed; only the `pullOrder`
  route is measured.
- **D-10.「Price the TRUTH of a recorded residue before pricing its proof.」**
  I searched first. `[LJ-1.300]` had already ruled the general crossing
  INDEPENDENT, and that search is why this task cost one probe and not a build.
- **P-l, C-42.** My measurement is at ONE site, consumer A's. **I did not sweep
  for the shape elsewhere and I do not claim the count.**
