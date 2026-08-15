# LJ-1.330 report: a CANONICAL element of `sq α` at non-initial α

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: CANONICAL

**A canonical element of `sq α` at a non-initial α exists. I built it. It is
green.**

`square-sucω : sq (sucV ω)`, `agents/tasks/LJ-1-330/ProbeLJ1330A.agda:151-152`.
`sucV ω` is non-initial, and I refute `Init (sucV ω)` by machine in the same
file at `:62-66`. The construction is generic: `sq-suc` gives the law at the
successor of every infinite ordinal that already has it, `:120-127`.

**AND THE BRIEF'S OWN ROW IS HALF FALSE, so I say it first.** The row reads
「a canonical element exists, then the descent's whole truncation line
dissolves」. **The line does NOT wholly dissolve.** The successor band
dissolves. The residue is the **non-initial LIMIT ordinals**, and the wall
there is exact and named in section 2.2.

**Three parts of the brief's premise are FALSE, and one correction is the
reason the build worked.**

## 1. THE PREMISE ABOUT THE INITIAL ORDINAL BELOW α

The premise reads「a non-initial α has an INITIAL ordinal below it of the same
cardinality, and a canonical bijection to it」. It has three parts. I measured
each.

### 1.1 Part one is FALSE. MEASURED.

`Init α` demands STRICT membership `⟨ ω ∈ˢ α ⟩`,
`src/L/Ordinal/SquareLaw.lagda.md:692-699`. The chapter says so itself at
`:694`:「it has omega as a member (so omega itself is not initial)」.

**So `Init ω` is refutable.** Term: `no-Init-ω`, `ProbeLJ1330A.agda:58-59`,
green. It applies `∈-irrefl` to the second row.

Every countable ordinal above ω has ω as its least equinumerous ordinal. **For
that whole band there is no `Init` ordinal below α at all.** `via-col-square`
therefore serves none of it, and the brief's「`via-col-square` serves that one」
is **MEASURED FALSE** across the countable band.

**The repair exists and the brief did not name it.** `squareω : sq ω`,
`src/L/InjChain.lagda.md:184-185`, is the canonical element at ω. It is in a
different chapter and it is not `via-col-square`.

### 1.2 The tree has no bijection, and the object it does have is truncated

`src/L/Cardinal.lagda.md:61-152`, `module LeastCardInjL`, is the tree's
least-of cardinal search. It gives two things:

| what | at | status |
|---|---|---|
| `κ`, the least ordinal that α injects into | `src/L/Cardinal.lagda.md:126-127` | **UNTRUNCATED and CANONICAL** |
| `κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁` | `src/L/Cardinal.lagda.md:133-134` | **TRUNCATED** |

The chapter's own comment at `:132` reads「The witness, an injection, still
truncated, still not an hProp」.

**So the ordinal is canonical and the map is not.** The brief asked for a
bijection. The tree offers one direction only, and that one is truncated.

### 1.3 Part three is FALSE, and this is the correction that made the build work

**A bijection is NOT what the square law transports along. TWO injections are
enough.** Term: `transport-sq`, `ProbeLJ1330A.agda:78-88`, green.

```agda
transport-sq : (α δ : S) → ⟪ α ⟫ ↪ ⟪ δ ⟫ → ⟪ δ ⟫ ↪ ⟪ α ⟫ → sq δ → sq α
```

The pairing is `g ∘ pair_δ ∘ (f × f)`. Injectivity composes three injections.
No inverse and no round trip is used.

**This matters because ONE leg is free at every ordinal.** `ord-emb`,
`src/L/BoundedSubset.lagda.md:1370-1379`, embeds the index of a member into the
index of the ordinal. I re-derived it at `ProbeLJ1330A.agda:98-108` (C-44).

**So the whole obligation is ONE untruncated injection `⟪ α ⟫ ↪ ⟪ δ ⟫`.** The
brief asked for an equivalence. The task is half that size.

## 2. THE TERM, AND THE WALL

### 2.1 The term: the square law at every successor ordinal

**The hard leg at a successor is ALREADY DELIVERED and it is UNTRUNCATED.**

```agda
shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
```

`src/L/Absorption.lagda.md:188-190`, in `module ShiftAbs`. That module is
AMBIENT. Its own header at `:63-71` says「THE AMBIENT SHIFT, over the
hierarchy. This part builds no element of L」.

Put the three pieces together:

```agda
sq-suc : (γ : S) → IsOrd γ → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
       → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩) → sq γ → sq (sucV γ)
```

`ProbeLJ1330A.agda:120-127`. `sq-suc-inf` at `:131-138` discharges both side
conditions from `⟨ ω ∈ˢ γ ⟩` alone, which is the descent's own infinity
hypothesis.

**Nothing here selects. Nothing here is truncated. No well-order on a function
type appears.** The construction reads `squareω` and `shift↪`, both of them
delivered terms.

Two instantiations are green: `square-sucω : sq (sucV ω)` at `:151-152`, and
`square-sucsucω : sq (sucV (sucV ω))` at `:156-158`. The second shows the chain
climbs.

**The sites are non-initial, and I prove that too.** `no-Init-suc`,
`:62-63`, refutes `Init (sucV γ)` for EVERY γ. The third row of `Init` is
closure under successors, and it would need `sucV γ ∈ˢ sucV γ`.

### 2.2 The wall: the non-initial LIMIT ordinals

**The residue is exact.** After this probe the ordinals split into four bands.

| band | supplier | status |
|---|---|---|
| ω | `squareω`, `src/L/InjChain.lagda.md:184-185` | **DELIVERED** |
| `Init` ordinals | `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` | **DELIVERED** |
| successor ordinals above ω | `sq-suc`, `ProbeLJ1330A.agda:120-127` | **BUILT HERE, canonical** |
| limit ordinals above ω that fail `Init` | none | **WALL** |

**The wall is `src/L/Cardinal.lagda.md:133-134`, and it is one line of type.**
At a limit λ that fails `Init`, the least equinumerous ordinal is still
canonical, but its injection is `∥ ⟪ λ ⟫ ↪ ⟪ κ ⟫ ∥₁`. Negative control 1 shows
what that does.

**INFERRED, and I mark it INFERRED:** the limit case cannot be reached by
recursion over the ordinal either. The Gödel ordering restricted to
`⟪ λ ⟫ × ⟪ λ ⟫` collapses inside λ exactly when the exclusion rows hold, which
is `Init`. I did not build a refutation of the limit case and C-36 forbids me
from calling it impossible.

### 2.3 A live lead that this probe RETIRES

`[LJ-1.321]` section 8 item 3 proposes trying `godSWO` against the limit
target, and says「neither was tried against this target」
(`agents/tasks/LJ-1-321/lj-1.321-report.md`, section 8 item 3).

**MEASURED: `godSWO` IS the target's own device, and it is already tried.**
`godSWO` at `src/L/Ordinal/SquareLaw.lagda.md:308-314` is the max-then-lex
Gödel order. `col` at `:384` is its collapse. `col∈α` at `:931-932` is the step
that puts the collapse inside α, and it consumes the `Init` exclusion rows
through `InitialCore`. **So `Init` is precisely the hypothesis under which the
Gödel collapse lands.** Item 3 needs a different device, not that one.

**Item 4 of that section, the `stage-card-upper` transplant, is untouched by
this probe.** It remains the strongest lead for the limit band.

## 3. LINES, SECONDS AND LOAD

The probe is `agents/tasks/LJ-1-330/ProbeLJ1330A.agda`. **206 lines, 70 of them
code**, counted as non-blank lines that are not comments.

**The new mathematics is 25 code lines**: `transport-sq` 10, `sq-suc` 8,
`sq-suc-inf` 7. `ord-emb` adds 10 more if a landing site cannot reach
`src/L/BoundedSubset.lagda.md:1370`. The refutations are 6 lines and the two
instantiations are 5.

Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. `GHCRTS="-A64m -I0
-M8g"` on every run. One process. No heap wall. The longest single invocation
was 6.30 s, far under the 30-minute line.

| run | what | exit | real s | agda slots before | 1-minute load |
|---|---|---:|---:|---:|---:|
| 1 | first check, one instantiation error | error | 2.60 | 0 | 15.95 |
| 2 | instantiation fixed, **GREEN** | **0** | 6.02 | 0 | 13.13 |
| 3 | **NEGATIVE CONTROL 1** | error | 6.30 | 0 | 12.41 |
| 4 | **NEGATIVE CONTROL 2** | error | 5.94 | 0 | 10.47 |
| 5 | **NEGATIVE CONTROL 3** | error | 6.25 | 0 | 19.57 |
| 6 | controls reverted, GREEN, warm | **0** | 1.86 | 1 | 16.77 |
| 7 | controls recorded in comments, final GREEN | **0** | 6.12 | 0 | 13.13 |

**Every figure is WARM.** Every interface of `src/` was already built. **No cold
cost is measured here.** The machine was not quiet, and my deliverable is a
term, so the load figures do not bear on it.

**I did not measure the landing cost.** A landed `sq-suc` would add to a
master's own check, and I did not run that master. P-l forbids me from pricing
it by analogy.

## 4. THE THREE NEGATIVE CONTROLS, AND WHAT EACH ONE NAMED

Each control was applied, run and reverted. The green backup sits in the
session scratchpad, outside the repository. All three are recorded at
`ProbeLJ1330A.agda:160-206`, because nothing typechecks this file after the
task closes.

**CONTROL 1, ON THE TRUNCATION, AND IT MEASURES.** I offered the truncated
injection where `transport-sq` takes the honest one. Agda named the blocker:

```
error: [UnequalTerms]
∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ !=<
(Σ (⟪ α ⟫ → ⟪ δ ⟫) (λ f → (x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y))
when checking that the expression t has type ⟪ α ⟫ ↪ ⟪ δ ⟫
```

**That is the limit band's whole story in one line.** The transport needs a
function. `κ-inj` supplies a truncation.

**CONTROL 2, ON THE ELIMINATION.** I tried to eliminate the truncation with
`PT.rec`, and I gave `refl` as the propositionality argument. Agda refused:

```
error: [UnequalTerms]
x != y of type
Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
(λ f → (x₁ y₁ : ⟪ α ⟫ × ⟪ α ⟫) → f x₁ ≡ f y₁ → x₁ ≡ y₁)
when checking that the expression refl has type x ≡ y
```

**So the target is not a proposition, and Agda names the two arbitrary pairing
functions that cannot be identified.** That is `[LJ-1.321]`'s `2-Constant`
obligation, stated by the machine.

**CONTROL 3, ON THE SUCCESSOR STEP.** I replaced `shift↪` by the free
embedding, asked for in the direction it cannot go. Agda demanded a premise
that `∈-irrefl` refutes:

```
when checking that the expression self∈sucV γ has type
⟨ sucV γ ∈ˢ γ ⟩
```

**So absorption carries the WHOLE content of the successor step.** The free
leg cannot do it, and the result is not an accident of a loose type.

## 5. WHAT THE DESCENT RE-PRICES TO

**Nothing in this report changes a delivered term.** It changes which term the
project should fund next, and it makes the remaining target much smaller.

| object | status after this probe |
|---|---|
| **`sq` at the successor ordinals** | **BUILDABLE TODAY, canonical, about 25 lines.** `ProbeLJ1330A.agda:120-138`. It needs no new principle |
| **`sq` at ω** | **DELIVERED.** `squareω`, `src/L/InjChain.lagda.md:184-185` |
| **`sq` at `Init` ordinals** | **DELIVERED.** `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` |
| **`sq` at non-initial LIMIT ordinals** | **THE ONLY WALL LEFT.** `src/L/Cardinal.lagda.md:133-134` |
| **the truncation line, `[LJ-1.321]` and `[LJ-1.326]` to `[LJ-1.329]`** | **NARROWED, not closed.** It now bears on ONE band, not on all non-initial ordinals |
| **`[LJ-1.329]`'s alternative 2** | **NOT FORCED by my work, and I did not attempt it** |

**THE LANDING SITE IS A REAL QUESTION AND IT IS NOT MINE TO SETTLE.** `sq-suc`
reads `L.Absorption`. `L.Absorption` imports `L.Ordinal.SquareLaw` at `:25` and
`L.InjChain` at `:36`. So `sq-suc` cannot live in `L.Ordinal.SquareLaw`.

**And the consumer does not import `L.Absorption` today. MEASURED.**
`src/L/BoundedSubset.lagda.md` imports fourteen `L.` modules, at `:26-34`,
`:876-882` and `:1040-1041`. Neither `L.Absorption` nor `L.InjChain` is among
them.

**The `sq` hypothesis has no supplier anywhere in `src/`. MEASURED.**
`BoundedSubsetAt` is declared at `src/L/BoundedSubset.lagda.md:1385` and
`grep -rn "BoundedSubsetAt" src/` returns that one line only. So this probe
supplies a band of a hypothesis that nothing consumes yet.

**THE ONE-LINE RECOMMENDATION.** Fund the successor band as a landed lemma,
about 25 lines, and send ONE probe at the limit band with `stage-card-upper` as
its candidate. **Do not send another probe at the successor band. It is done.**

## 6. DD4, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One
rule, two ends, no metric and no checker. DD4's own axis is the AC closure
against the GCH closure, fixed in code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the term name a tower, a stage, an ordinal presentation or a
formula?**

**Answer: my whole term is TOWER-BLIND. MEASURED**, by reading my own imports
at `ProbeLJ1330A.agda:26-46`.

- `transport-sq` (`:78`) names two ambient sets and three injections. It names
  no ordinal at all. It is generic in both carriers.
- `ord-emb` (`:98`) names `IsOrd` and ambient membership only.
- `sq-suc` (`:120`) names `ShiftAbs`, which its own header calls ambient
  (`src/L/Absorption.lagda.md:63-71`).
- No import of mine reaches `Lset`, a stage, a `Formula` or `⊨`.

**WHICH CLOSURE IT LANDS IN, AND THE ANSWER MOVES A MEASURED FIGURE.** Landing
`sq-suc` where the descent can use it adds an import edge from the GCH wing to
`L.Absorption`, and `L.Absorption` pulls `L.InjChain`.

**Those two chapters LEFT the GCH closure at the `[LJ-1.323]` restatement.**
`dev/ledger.toml:193-196` records it: the GCH closure went 51 masters and 9,967
lines to 48 and 8,889, and `L.Absorption` and `L.InjChain` both left.

**`[LJ-1.326]` already bounded what bringing them back costs**, at
`dev/ledger.toml:206-211`: 51 masters and 9,953 lines, SHARED 44 and 7,632,
share 39.1 percent, which is exactly the pre-restatement figure.

**INFERRED, and I mark it INFERRED:** my term would ride that same edge, so it
would hand back the same 2.0-point rise. **I did not re-run `ledger.py` with my
term, because the term is not landed.** Today's figures are AC 73 masters and
17,197 lines, GCH 48 and 8,889, SHARED 43 and 7,596, measured by
`ledger.py --reuse` under my own hand.

**AND THE DD4 READING IS THE OPPOSITE OF `[LJ-1.329]`'s.** `[LJ-1.329]`
measured a shared generic device that could not reach its site, because generic
in the carrier means it demands a total map out of the carrier. **My term is
generic in the carrier and it reaches the site, because it demands a POINT of a
delivered injection type and never a map out of `sq α`.** That is the
difference between the two returns, in one sentence. **Read the SHARED row and
never the share** (`dev/ledger.toml:198-200`).

## 7. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **A CANONICAL ELEMENT EXISTS AND YOU BUILD IT** | **TAKEN, and HALF the row's promise is FALSE.** The element exists at every successor ordinal and I built it. **The truncation line does not wholly dissolve.** The limit band survives |
| **THE TRANSPORT IS THE ROUTE AND THE BIJECTION IS TRUNCATED** | **PARTLY TAKEN.** The transport is the route, and it needs two injections, not a bijection. At successors the injection is DELIVERED and untruncated. At limits it is truncated, at `src/L/Cardinal.lagda.md:133-134` |
| **NO CANONICAL ELEMENT IS POSSIBLE** | **NOT TAKEN, and it is refuted by a green term** |
| **THE OBVIOUS ROUTE IS WRONG** | **PARTLY TAKEN.** The route through「the initial ordinal below α」is wrong at the countable band, because `Init ω` is refutable. The right route at successors is absorption, not cardinality |
| **A WALL past 30 minutes** | **NOT TAKEN.** Longest single invocation 6.30 s |

## 8. WHAT I DID NOT SETTLE

I name these rather than guess.

1. **The limit band.** I did not build it and I did not refute it. C-36 binds:
   my controls measure the truncation route only.
2. **The landing site and its check cost.** Section 5 names the import problem.
   I did not price the master that would carry `sq-suc`.
3. **Whether `[LJ-1.329]`'s alternative 2 is forced.** My work does not force
   it. I did not attempt it, as the brief ordered.
4. **`[LJ-1.321]` section 8 items 1, 2 and 4.** Untouched. Item 4,
   `stage-card-upper`, is still the strongest lead for the limit band.
5. **A cold check cost.** Every figure here is warm.
6. **Whether `Init` is equivalent to `IsCardinal`.** `IsCardinal`
   (`src/L/BoundedSubset.lagda.md:1046-1047`) forbids an injection into a
   member. `Init`'s fourth row forbids an injection into a member's SQUARE.
   The second is stronger without the square law below. I did not measure the
   gap.
7. **The sweep (C-42).** I measured ONE shape, `sq` at successors. I did not
   sweep `src/` for other hypotheses with the same non-initial gap.

## 9. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-330/` only**, two files, this report and
  `ProbeLJ1330A.agda`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.
- **I read the sibling probes and changed no line of them.** I read
  `agents/tasks/LJ-1-329/ProbeLJ1329A.agda` and the reports of `[LJ-1.321]`,
  `[LJ-1.300]` and `[LJ-1.329]`.
- **I read the CURRENT `src/L/GCH.lagda.md` and `src/L/BoundedSubset.lagda.md`
  at HEAD**, as the brief ordered. `GCH.lagda.md` is 70 lines.
  `BoundedSubset.lagda.md` is 1,626 lines and `BoundedSubsetAt` is at `:1385`.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda: seven invocations, one at a time.** Load counted before each, with
  the brief's command. `GHCRTS="-A64m -I0 -M8g"`. Cap never raised.
- The green backup sits in the session scratchpad, outside the repository.
- `lint-prose.py --check` and `lint-agda.py --check` pass on what I wrote.

## 10. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-329/lj-1.329-report.md`, READ WHOLE.** Line read
  `:222-228`:「A CANONICAL element of `sq α` at non-initial `α`. The tree
  already delivers `via-col-square` at INITIAL `α` and `squareω` at omega」.
  **TOOK: the two sites, and I compiled against both.** `squareω` is the base
  of my chain. **The same lines say「The gap is exactly the non-initial
  ordinals」. That half is now NARROWED: the gap is the non-initial LIMIT
  ordinals.**
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ section 8 whole.** Line
  read, item 3:「the tree has `godSWO` and `god` already, and neither was tried
  against this target」. **TOOK: the lead, and I RETIRE it.** Section 2.3
  measures that `godSWO` is the device `via-col-square` already runs, and that
  `Init` is exactly its landing condition. **Item 4 stays live.**
- **`agents/tasks/LJ-1-300/lj-1.300-report.md`, READ `:155-175`.** Line read
  `:162-165`:「MEASURED: `via-col-square` cannot reach a non-cardinal ... The
  infinite non-cardinals need the transport from their own cardinality, whose
  successor case is `absorbs`」. **TOOK: the pointer to `absorbs`, and it is
  the whole build.** `[LJ-1.300]` named the successor case ten tasks ago and
  nobody built it.
- **`archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`, READ
  `:118-136`.** Line read `:131-134`:「That is precisely where the square-law
  chapter's extraction risk bites: its least-of cardinal search returns
  equinumerosity only as a truncation, and a truncated witness cannot supply a
  function」. **TOOK, SHAPE ONLY:** the retired route recorded the same wall in
  the same words. **WHAT WOULD NOT TRANSFER:** every figure and every term
  there prices the rud presentation, whose code sits under
  `archive/src/2026-08-09-rud-route/`. `[LJ-1.293]` refuted that route's
  identity by machine. **So I re-measured the wall in the CURRENT tree**, at
  `src/L/Cardinal.lagda.md:133-134`, and I quote the current comment, not the
  archived one.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:78` (L3.32-T43):「Where counting calls the square law | RED (wall
  confirmed)」. **TOOK, SHAPE ONLY:** the retired route also spent a dispatch
  locating this call site and returned RED. **WHAT WOULD NOT TRANSFER:** its
  report lives in `_build/`, which is a temporary folder, so no figure of it is
  readable today and I quote none.

## 11. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`. IT BEARS, and the brief's one-line question
  has a clean answer.** READ `:275-284`, `:355-360` and `:411-417`.

  **THE ONE LINE: Devlin's construction is NOT canonical at non-initial
  ordinals. He reduces every site to its initial ordinal by cardinal
  arithmetic.** Line read `:280-284`:「|L_α| = |α| for infinite α (1.1(vii)),
  and the cardinal fact |γ| = |α| < κ with κ a cardinal implies γ < κ ...
  Strength: ... the level-size equation and initial-ordinal arithmetic」.
  **TOOK: the shape of his reduction, and it is exactly the transport this
  probe corrects.**

  **AND HIS STATEMENT IS AN EQUINUMEROSITY, WHICH IS THE TRUNCATION.** Line
  read `:411-415`:「|L_α| = |α| for α ≥ ω ... is generic cardinal arithmetic
  over the level-size equation」. A cardinality equation asserts that a
  bijection exists. In this setting that is `∥ ... ∥₁`, and no function comes
  out of it. **So Devlin never owes the untruncated map, and the tree does.
  That asymmetry is why four tasks searched for an object his proof does not
  contain.**

  **WHY NOT re-fetched:** the digest carries locators into `dev2.txt` and I
  take statement-level facts only.
- **`dev/literature/truncation-and-selection.md`. NOT READ, and WHY NOT:**
  `[LJ-1.329]` used it to price a well-order on the injections. My route needs
  no order on any function type, so its subject does not reach my term.

## 12. THE RULES THIS CHAIN EARNED, ANSWERED

- **D-10.「Price the TRUTH of a recorded residue before pricing its proof.」**
  I priced the truth first. Three parts of the premise are false, and part
  three's correction is what made the build possible.
- **C-44.** The brief asked me to expect a false premise. **There is one, and
  it is central.** Section 1.
- **C-36.「A failed substitution is not a proof of impossibility.」** Section
  2.2 says what I did NOT prove. The limit band is not closed.
- **C-45.「`exit 0` is not a supply.」** My probe is green and it lands nothing.
  A landed `sq-suc` would supply one band of the descent's `sq` hypothesis, and
  that hypothesis has no consumer in `src/` today.
- **C-42.** My measurement is at ONE shape. **I did not sweep for the same gap
  elsewhere and I do not claim a count.**
- **P-l.** I did not price the landing cost by analogy with this probe's warm
  seconds. Section 3 says so.
- **D-1.** The abort criterion was fixed before the run and section 7 answers
  it row by row.
