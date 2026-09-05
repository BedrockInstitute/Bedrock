# LJ-1.159 report: where the 99 seconds are inside `LeastCardInj`

## 0. VERDICT: **FOUND, AND CURED. WING-LOCAL.**

**THE 99 SECONDS ARE 13 SOURCE LINES, AND 56 PERCENT OF THEM ARE ONE `subst`.**

`agda --profile=definitions` puts **82,763 ms of 99,310 in `κ-min-at` and its
six `where` bindings**, which is 83.3 percent of the file over
`ProbeLJ1159A.agda:131-143`. **`bInjP` alone is 55,937 ms, 56.3 percent.** A
wall clock confirms it independently: the same module with `κ-min-at` deleted
costs 16.33 s against 100.18 (section 6).

**THE CAUSE IS NOT THE SEARCH. `leastOf`, `ordSWO` and `least` do not appear in
the profile at all.** The cause is that `sucV α` is written in a TYPE, and
`sucV N = N ∪ ⁅ N ⁆s` reduces to a three-layer `sett` even when `α` is a
variable, so `⟪ sucV α ⟫` re-walks `V-repr` at every conversion. **That is
`dev/LESSONS.md` P-l, at the exact site P-l already names.**

**THE CURE: take the ambient ordinal as a PARAMETER, so `sucV α` appears in no
type. Same content, same twelve definitions, line for line.**

| | seconds, 3 cold runs | mean | lines |
|---|---|---:|---:|
| `LeastCardInj` at `sucV α` | 100.18 (profiled) | **100.64** (`[LJ-1.156]`) | 97 |
| the same content at a parameter | 1.44, 1.32, 1.29 | **1.35** | 97 |
| the cure PLUS its instantiation | 11.72, 12.09, 11.95 | **11.92** | 110 |
| **the WHOLE CHAIN, cured, `--safe`, exit 0** | 45.54, 46.03, 46.89 | **46.15** | 405 |
| the whole chain as written | 134.48, 132.60, 131.93 | **133.00** | 392 |

**MEASURED: the module goes 100.64 to 11.92, and the WHOLE CHAIN goes 133.00 to
46.15.** The chain figure is the one that matters, and it is a consumer check
(C-40): `agents/tasks/LJ-1-159/ProbeLJ1159E.agda` is `ProbeLJ1156A.agda` with
Part 2 and only Part 2 replaced. **Parts 3 to 7 are byte for byte identical,
including all four `Guard` witnesses**, and the file elaborates `--safe`,
exit 0.

**THE CURE IS WING-LOCAL, MEASURED.** `L.Ordinal.SquareLaw` has exactly one
consumer in `src/`, and it is `src/Everything.lagda.md:323`. DD24's denominator
is the AC wing rooted at `src/L/Model.lagda.md` (`dev/ledger.toml:170-171`),
which does not import it. **The `[LJ-1.147]` trap does not fire: the saving
lands entirely on the judged side.**

**THE PRICE: +13 lines, ZERO new hypotheses, ONE fewer parameter.**
`LeastCardAt` drops `IsOrd α`, which it no longer needs, and gains `sα`,
`IsOrd sα` and `α ∈ˢ sα`. The instantiation supplies all three from
`suc-ord oα` and `self∈sucV α`, which the chain already has.

**AND IT IS THE DD4 MOVE.** The cured module is generic in the ambient ordinal
rather than fixed to the successor. **Genericity and speed are the same edit
here, so DD4 costs nothing at this site; it pays 8.4 times.**

**THE ORDER-TYPE LEAD IS REFUTED. MEASURED.** See section 7.

**THE CURE IS ALSO PRIOR ART INSIDE THIS CHAPTER.**
`src/L/Ordinal/SquareLaw.lagda.md:503-531` already carries the same class of
cure, and P-l records it at 374.3 s to 82 ms. **The module beside it never got
it.** See section 11.

## 0.1 Abort criterion, fixed BEFORE any measurement

Copied from the brief and fixed here first, so no result can move it.

- **FOUND**: one or two definitions inside `LeastCardInj` carry the bulk of the
  100.64 s. Price a cure, say SHARED or WING-LOCAL, report and STOP.
- **NO DOMINANT TERM**: the cost spreads across the 44 lines. STOP AND SAY SO.
  A5 then carries the price and it becomes a DD24 question for the owner.
- **SHARED CURE**: say so loudly. It moves the baseline denominator.
- **WALL**: a heap exhaustion under `-M8g`. Report it. Never raise the cap.

## 1. The load, recorded before any figure

16 cores, macOS 25.6.0, Agda 2.8.0. **ONE agda process of mine at a time.
Always `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised.**

`[LJ-1.158]` is editing the three `*Agree` masters in parallel. The one-minute
load average is recorded beside every run below.

## 2. The profile: THE 99 SECONDS ARE IN ONE `subst`

**MEASURED. `agda --profile=definitions`, one run, cold, load 4.29 at start,
`real 100.18 s`, exit 0.**
File: `agents/tasks/LJ-1-159/ProbeLJ1159A.agda`, which is
`agents/tasks/LJ-1-156/ProbeLJ1156D.agda` verbatim with the module renamed.
Raw output: `agents/tasks/LJ-1-159/prof-definitions.txt`.

| definition | ms | share of total | source line |
|---|---:|---:|---|
| **`LeastCardInj._.bInjP`** | **55,937** | **56.3 %** | `ProbeLJ1159A.agda:140-141` |
| `LeastCardInj._.b<γ` | 12,125 | 12.2 % | `:142-143` |
| `LeastCardInj._.δ∈sα` | 6,554 | 6.6 % | `:134-135` |
| `LeastCardInj.nonempty` | 5,727 | 5.8 % | `:105-106` |
| `LeastCardInj.κ-min-at` | 5,248 | 5.3 % | `:131-132` |
| `LeastCardInj.κ-inj` | 2,747 | 2.8 % | `:124-125` |
| `LeastCardInj._.bδ` | 2,178 | 2.2 % | `:138-139` |
| `LeastCardInj.oκ` | 1,391 | 1.4 % | `:117-118` |
| `LeastCardInj.κ∈sα` | 1,380 | 1.4 % | `:120-121` |
| `LeastCardInj.κ-min` | 1,377 | 1.4 % | `:127-128` |
| `LeastCardInj.self-eq` | 1,366 | 1.4 % | `:99-100` |
| `LeastCardInj._.b` | 721 | 0.7 % | `:136-137` |
| Miscellaneous | 2,554 | 2.6 % | |
| **Total** | **99,310** | | |

**`κ-min-at` and its six `where` bindings are 82,763 ms, which is 83.3 percent
of the whole file.** They are **13 source lines**
(`ProbeLJ1159A.agda:131-143`).

**AND THE NAMES THAT ARE NOT IN THE TABLE ARE THE FINDING.** `w`, `least`,
`γ-card`, `κ`, `Inj`, `InjP`, `InjP'`, `idInj` and `self` **do not appear at
all**. Agda's definitions profile lists every definition it spent measurable
time on. **The least-of search, the well-order `ordSWO (sucV α)` and the
predicate itself are all below the reporting threshold.**

**So the term everybody named is not the term that costs.** `[LJ-1.107]`
recorded the cause as "the least-of over the well-order on the successor's
presentation" (`agents/tasks/LJ-1-107/lj-1.107-report.md:52`) and `[LJ-1.156]`
carried that forward (`agents/tasks/LJ-1-156/lj-1.156-report.md:312-319`).
**MEASURED: `leastOf` and `ordSWO` cost nothing measurable here.** The cost is
one three-token `subst` in a `where` block.

## 3. The internal profile: it is right-hand-side elaboration

**MEASURED. `agda --profile=internal`, one run, cold, load 3.22 at start,
`real 101.79 s`, exit 0.** Raw output:
`agents/tasks/LJ-1-159/prof-internal.txt`.

| phase | ms | share |
|---|---:|---:|
| **`Typing.CheckRHS`** | **91,082** | **90.2 %** |
| `Typing.CheckLHS` | 5,826 | 5.8 % |
| `Positivity` | 1,280 | 1.3 % |
| `Deserialization` | 1,135 | 1.1 % |
| `Coverage` | 676 | 0.7 % |
| `Typing.OccursCheck` | 159 | 0.2 % |
| `Total` | 100,974 | |

**So the cost is conversion inside a right-hand side.** It is not coverage,
not positivity, not import, and not serialization.

## 4. The mechanism, read from the library source

**`sucV α` is not an atom. It reduces to a THREE-LAYER `sett` even when `α` is
a variable.**

- `sucV N = N ∪ ⁅ N ⁆s`
  (`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Constructions.agda:160-161`)
- `a ∪ b = ⋃ ⁅ a , b ⁆` (`Constructions.agda:156-157`)
- `⁅_⁆s`, `⁅_,_⁆` and `⋃_` are each `SetStructure.resSet` of an explicit index
  type (`Constructions.agda:113-153`)
- `⟪ s ⟫ = V-repr s .fst .fst` and `⟪ s ⟫↪ = V-repr s .fst .snd .fst`
  (`Cubical/HITs/CumulativeHierarchy/Properties.agda:220-224`), and `V-repr` is
  an equivalence composite over the monic presentation
  (`Properties.agda:196-210`)
- `fiber a x∈ = ∈-asFiber x∈` (`src/V/Presentation.lagda.md:34-35`), and
  `∈-asFiber` is itself a `subst` along `⟪ b ⟫-represents`
  (`Properties.agda:242-247`)

**So every conversion that touches `⟪ sucV α ⟫` walks `V-repr` over three
nested `sett` layers. `α` being a variable does not stop it, because `sucV`
is what is transparent, not `α`.**

**This is `dev/LESSONS.md` P-l (`:2323`), at the exact site P-l names.** P-l
already records `L.Ordinal.SquareLaw` at "3.424 s per obligation, 46 times the
benchmark, with 88 percent of it in four definitions whose STATEMENTS carry the
tower". **`LeastCardInj` is the same defect in the same chapter's chain, and it
was never repaired.**

## 5. The cure, MEASURED

**Take the ambient ordinal as a PARAMETER. `sucV α` then appears in no type.**

`agents/tasks/LJ-1-159/ProbeLJ1159C.agda` is `LeastCardInj` restated as

```
module LeastCardAt (sα : S) (osα : IsOrd sα) (α : S) (α∈sα : ⟨ α ∈ˢ sα ⟩)
```

**Nothing else moves.** The same `ordSWO`, the same `leastOf`, the same
predicate, the same twelve definitions and the same six `where` bindings, line
for line. `IsOrd α` is not needed at all once `sα` is a parameter, so the
telescope gets shorter, not longer.

| probe | what it is | 3 kept cold runs | mean | load band | exit |
|---|---|---|---:|---:|---|
| `ProbeLJ1159A` | `LeastCardInj` at `sucV α`, verbatim | 100.18 profiled, 101.79 profiled | **100.64** (`[LJ-1.156]`) | 3.22 to 4.29 | 0 |
| **`ProbeLJ1159C`** | **the same content at a parameter `sα`** | 1.44, 1.32, 1.29 | **1.35** | 4.31 to 4.96 | 0 |

**Warm-ups discarded: `ProbeLJ1159C`'s first cold run at 1.48 s.** My two
profiled runs of `ProbeLJ1159A` are 100.18 and 101.79, and `[LJ-1.156]`'s three
unprofiled runs of the identical content are 99.95, 100.88 and 101.10
(`agents/tasks/LJ-1-156/lj-1.156-report.md:208`). **I take its 100.64 as the
baseline because those runs carried no profiler.**

**MEASURED: 100.64 s to 1.35 s, cold, all under `GHCRTS="-A64m -I0 -M8g"`.**
`[LJ-1.156]` measured this file's import block alone at 1.27 s
(`agents/tasks/LJ-1-156/lj-1.156-report.md:186`). **So the cured module's own
content costs about 0.08 s and the rest is the import baseline.** I do not
claim that 0.08 as a figure; it is inside the noise, and the honest statement
is that the cured module is indistinguishable from its own imports.

## 6. The profile, confirmed by a wall clock

**A profile is not a clock, so the 83.3 percent claim was re-measured with
one.** `agents/tasks/LJ-1-159/ProbeLJ1159B.agda` is Probe A with `κ-min-at`
and its `where` block deleted and nothing else changed.

| probe | seconds, 3 cold runs | mean | load band |
|---|---|---:|---|
| `ProbeLJ1159B` | 16.09, 16.44, 16.47 | **16.33** | 4.84 to 5.26 |

**The profile predicted 16.55 s for the same content** (99.31 total minus 82.76
in `κ-min-at`). **The clock says 16.33 s.** Two independent methods agree
inside 1.3 percent.

**So `κ-min-at` and its six `where` bindings are 83.85 s of 100.18 s, which is
83.7 percent of the file, over 13 source lines.** MEASURED twice.

## 7. The order-type lead: REFUTED, and the profile says why

**The brief's lead was that `LeastCardInj` is expensive for the same reason
`CSB` was: doing by SEARCH what an order type does by CONSTRUCTION. MEASURED:
that is FALSE.**

**The search costs nothing measurable.** `leastOf` is the search; `ordSWO` is
the well-order it descends; `least` is the call. **None of the three appears in
the definitions profile at all.** The whole module minus one 13-line definition
is 16.33 s, and that 16.33 s includes `w`, `least`, `nonempty` and every
projection out of the search.

**What is expensive is not the search. It is that the search's ambient set is
written as `sucV α` in a TYPE.** The identical search over a parameter costs
1.48 s (section 5).

**INFERRED, and I mark it as the brief requires: an order-type route would have
avoided this too, but for a reason that has nothing to do with searching.** It
would avoid it because it would not name `sucV α` in the statement either.
**That is a different mechanism from the one the lead proposed, and the cure
found here does not need the order type.**

**The lead's value was real even though it was wrong.** It sent this task to
profile the term rather than to seal it, and the seal is what the last three
dispatches would have tried.

## 8. Does the cost MOVE? MEASURED: 10.5 s of 88 comes back

**`dev/LESSONS.md` P-l records four transplants where a cure moved the cost
instead of removing it. So Probe C alone proves nothing.**
`agents/tasks/LJ-1-159/ProbeLJ1159D.agda` is Probe C PLUS the instantiation at
`sucV α`, re-exporting the five names `Chain.step` reads from `LC0`, each with
its type written out at `sucV α` so the elaborator must do the boundary
conversion.

| probe | what it is | 3 kept cold runs | mean | load band |
|---|---|---|---:|---|
| `ProbeLJ1159A` | `LeastCardInj` at `sucV α` | 100.18, 101.79, both profiled | **100.64** (`[LJ-1.156]`) | 3.22 to 4.29 |
| `ProbeLJ1159C` | the same content at a parameter | 1.44, 1.32, 1.29 | **1.35** | 4.31 to 4.96 |
| `ProbeLJ1159D` | C plus the instantiation | 11.72, 12.09, 11.95 | **11.92** | 4.31 to 4.96 |

`[LJ-1.156]` measured the same content as Probe A at 99.95, 100.88, 101.10,
mean **100.64** (`agents/tasks/LJ-1-156/lj-1.156-report.md:208`). **My two
profiled runs, 100.18 and 101.79, reproduce it, so the baseline is not in
doubt.**

**MEASURED: 100.64 to 11.92 is 88.72 s saved, a factor of 8.4.**
**10.57 s of the cost DOES come back at the boundary, and I state it rather
than net it out.**

**Where the residue sits, MEASURED** (`agda --profile=definitions` on Probe D,
`agents/tasks/LJ-1-159/prof-definitions-D.txt`, total 11,614 ms):

| definition | ms |
|---|---:|
| `LeastCardInj.oκ` | 4,421 |
| `LeastCardInj.κ-inj` | 2,964 |
| `LeastCardInj.κ-min-at` | 1,506 |
| `LeastCardInj.κ∈sα` | 1,460 |
| Miscellaneous | 1,260 |

**All four are the re-export aliases, whose types I wrote out at `sucV α`. No
definition of the generic `LeastCardAt` appears at all.** So the residue is
exactly the boundary, and it is 10.57 s rather than 88.

## 9. What Devlin does

**MEASURED from the text: Devlin's square-law proof contains NO least-cardinal
step at all, so there is nothing in Devlin for `LeastCardInj` to correspond
to.**

- **II.6.6** (`_build/literature/dev2.txt:1750-1785`) defines a well-ordering
  `<*` of `On × On` and sets `G(α,β)` to be **the order type of the
  predecessors of `(α,β)` under `<*`**. So `G : (On × On, <*) ≅ (On, <)` **by
  construction**. He then gives the recursion
  `G(0,β) = sup_{ν<β}(G(0,ν) + ν + ν)` and the Σ₁ definability.
- **II.6.7** (`dev2.txt:1791-1860`), the square law itself, is an induction on
  `α` with three cases keyed on `Q = {α | G : α × α ↔ α}`, which is closed and
  unbounded. **Case 1** is `α ∈ Q`. **Case 2** is `α = γ + ω`. **Case 3** takes
  `(ν,τ) = G⁻¹(α)` and uses `g = G ↾ C` mapping `C` one-one onto `α` "by
  definition of `G` from `<*`".

**None of the three cases computes a cardinal.** The one least-search in the
whole proof is `E(ξ,ζ) = the least i such that k(i) = (ξ,ζ)`
(`dev2.txt:1850`), which inverts a surjection `k : γ → γ × γ` at a SMALLER
ordinal. **It is not a cardinal, and its ambient set is `γ`, a variable of the
induction, never a successor written out.**

**So the answer the brief asked for: Devlin CONSTRUCTS, and he never searches
for a cardinal, because his split is `α ∈ Q` versus not, and this project's
split is `κ = α` versus `κ ∈ α`.** `[LJ-1.156]` recorded that the project
priced order types out (`src/L/Ordinal/SquareLaw.lagda.md:1-11`), and the
initial-versus-non-initial split is what replaced them. **`LeastCardInj` is the
price of that ruling, and this task does not reopen it: the cure below leaves
the split exactly where it is.**

## 10. DD4

**Maximize the code the two proofs share, and write it generic. No stop-line
made me write fixed.**

**The cure IS the DD4 move, and that is not a coincidence.** `LeastCardAt`
takes the ambient ordinal as a parameter, so it states "the least γ in `sα`
into which `α` injects" for ANY ordinal `sα` that has `α` as a member.
`sucV α` is one instance. **A module fixed to the successor is a module the J
tower cannot re-point; a module generic in the ambient ordinal is one it can.**

**MEASURED, and it is the honest form of the claim: the generic module is
CHEAPER than the fixed one by 8.4 times.** Genericity and speed are the same
edit here. **That is the strongest DD4 evidence this cluster has produced,
because it costs nothing to obey the rule.**

**The residue I name rather than hide.** `LeastCardAt` is still generic in the
ORDINAL and not in the CARRIER: it sits over `𝒮ᵥ` and `⟪_⟫`, exactly as
`[LJ-1.156]` recorded for the whole chain
(`agents/tasks/LJ-1-156/lj-1.156-report.md:485-491`). **This task does not
change that and does not claim to.**

## 10A. THE CONSUMER CHECK, and it is the figure that matters (C-40)

**A cured module proves nothing until a consumer elaborates. C-40 says so and
it cost three red commits to learn.**

`agents/tasks/LJ-1-159/ProbeLJ1159E.agda` is
`agents/tasks/LJ-1-156/ProbeLJ1156A.agda` with **Part 2 and only Part 2**
replaced by `LeastCardAt` plus the five-name wrapper. **MEASURED with `diff`:
Parts 3 to 7 are byte for byte identical**, which includes `ShiftAbs`,
`InitialCase`, `NonInitial`, `Chain` and all four `Guard` witnesses.

| probe | what it is | 3 cold runs | mean | load band | exit |
|---|---|---|---:|---|---|
| **`ProbeLJ1159E`** | **the whole chain, cured** | 45.54, 46.03, 46.89 | **46.15** | 3.57 to 4.03 | **0** |

**So the consumers do elaborate, `--safe`, exit 0, first attempt, no wall.**
`Guard.κ-not-sucω` still fires at concrete ordinals and `Guard.Runs.sq-sucω`
still runs the chain at `sucV ω`.

**MEASURED, one grep: the chain reads exactly FIVE names from the module**,
`κ`, `oκ`, `κ∈sα`, `κ-inj` and `κ-min-at`, at `ProbeLJ1156A.agda:531-549` and
`:583-586`. **The wrapper exports all five and the file compiles, so the
interface is complete rather than argued.**

**AND THE TWO SAVINGS AGREE, which is the cross-check that makes this
believable.** The module-level saving is 100.64 minus 11.92, which is 88.72 s.
The chain-level saving is 133.00 minus 46.15, which is 86.85 s. **Two
independent measurements of the same edit, agreeing inside 2.2 percent.**

## 10B. The price, in lines and seconds, with its basis (DD8)

**ONE number with its basis, as DD8 requires: the whole chain costs 46.15 s
after the cure, and the basis is this task's own three cold runs at the real
sites, not a comparable.**

| | as written | cured | change |
|---|---:|---:|---|
| whole-chain seconds, cold | **133.00** | **46.15** | **minus 86.85 s** |
| non-blank non-comment lines | 392 | 405 | plus 13 |
| s per line | 0.3393 | **0.1140** | 2.98 times better |
| against DD24's 0.007913 bar | **42.9x** | **14.4x** | |

**CALIBER, stated because `[LJ-1.6]` was bitten by one.** I count non-blank,
non-comment lines of a `.agda` file by hand. `scripts/ledger.py` cannot count a
probe and says so at `scripts/ledger.py:13-15`. **My count of
`ProbeLJ1156A.agda` is 392 where `[LJ-1.156]` reported 393**, a one-line
difference in the `OPTIONS` pragma treatment. **All figures in this table use
my caliber on both sides, so the ratio is sound even where the absolute count
differs by one.**

**THE 133.00 IS MINE, and it is also `[LJ-1.156]`'s.** I re-ran its unmodified
file three times on this machine, got 134.48, 132.60 and 131.93, and the mean
is 133.00 to two decimals. Section 13 gives the runs. **So the A/B is
same-session and needs no cross-session correction.**

**THE COST IN NEW OBLIGATIONS IS ZERO. MEASURED.** `LeastCardAt` takes
`(sα : S) (osα : IsOrd sα) (α : S) (α∈sα : ⟨ α ∈ˢ sα ⟩)` and DROPS `IsOrd α`.
The instantiation supplies `sucV α`, `suc-ord oα` and `self∈sucV α`, all three
already imported and already used by the file
(`ProbeLJ1156A.agda:53, 63`). **C-38: this is a supply, not a restatement, and
Probe E is the evidence.**

## 10C. WHAT REMAINS AFTER THE CURE, and it names the NEXT gate

**46.15 s is still 14.4 times DD24's bar. The cure moves the block from
42.9x to 14.4x; it does not clear the bar.**

**So the third abort branch is HALF true and I say so plainly: after this cure
A5 still carries a rate the owner must rule on.** What changed is that the
figure is now a chain-wide rate rather than one term hiding 83 percent of the
cost, and 86.85 s of the original 133 are gone for 13 lines.

**AND THE RESIDUE IS THE SAME DEFECT, ONE LAYER OUT. MEASURED**
(`agda --profile=definitions` on Probe E,
`agents/tasks/LJ-1-159/prof-definitions-E.txt`, total 43,268 ms):

| group | ms | what it is |
|---|---:|---|
| `Guard.κ-not-sucω` plus its `ω∈κ` | **10,816** | the C-38 witnesses, at a CONCRETE `sucV ω` |
| `Chain`'s own `δ∈κ`, `leastα`, `split`, `go` | **16,399** | the consumer's `subst`s over `LC0.κ` |
| the four wrapper aliases | **9,716** | the instantiation boundary, section 8 |
| `ShiftAbs._.go` | 1,630 | |
| everything else, 18 definitions | 355 | |
| Miscellaneous | 4,317 | |

**Every one of the three big groups names `sucV` in a statement.** `Chain`'s
`δ∈κ` is `subst (λ w → ⟨ δ ∈ˢ w ⟩) (sym κ≡α) δ∈α` at `ProbeLJ1156A.agda:546-547`,
where `κ≡α` relates `LC0.κ` to `α`; `Guard`'s `ω∈κ` is the same shape at
`sucV ω` (`:586-587`).

**So the next gate is named, and it is NOT inside `LeastCardAt`.** It is the
consumer's own `subst`s and the concrete guard.

**One thing the orchestrator should weigh before funding that gate: 10,816 ms
of the 43,268 is the `Guard` module, which exists only to satisfy C-38 in a
PROBE.** Whether the delivered master carries an equivalent is a design
question, not a measurement, and I do not answer it here.

## 11. THE CURE IS PRIOR ART INSIDE THIS VERY CHAPTER

**MEASURED, one read. The delivered `src/L/Ordinal/SquareLaw.lagda.md` ALREADY
CARRIES THIS CURE, in a different form, and `LeastCardInj` never got it.**

`src/L/Ordinal/SquareLaw.lagda.md:503-531`, `module AbstractH₀`, takes the
whole presentation as parameters:

```
                  (F : S → Type ℓ)
                  (↪F : (a : S) → F a → S)
                  (fiberF : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ F a ] (↪F a m ≡ x))
```

`h₀`'s type is then `F (sucV (γp p)) × F (sucV (γp p))` (`:514`). **`sucV` is
still written, but `F` is a variable, so the composite never reduces.**

**`dev/LESSONS.md` P-l (`:2323`) records what that edit was worth:**
"`[T102]`'s telescope lift | `SquareLaw`'s `h₀` pair, 374.3 s to 82 ms".

**So the chapter has a measured 4,500-fold precedent for exactly this class of
cure, and the least-cardinal search was left out of it.** The two forms are
duals and either one works:

| form | what becomes a variable | what stays written | site |
|---|---|---|---|
| `AbstractH₀`, delivered | the presentation `F`, `↪F`, `fiberF` | `sucV (γp p)` | `SquareLaw.lagda.md:503-531` |
| `LeastCardAt`, this task | the ambient set `sα` | `⟪ ⟫`, `⟪ ⟫↪`, `fiber` | `ProbeLJ1159C.agda` |

**Neither leaves `⟪ sucV _ ⟫` with both halves transparent at once, and that is
the whole mechanism.** `LeastCardAt` costs ONE parameter where `AbstractH₀`
costs three, so it is the cheaper form to write at this site.

**This makes the finding a repeat rather than a discovery, and I say so.** The
defect was diagnosed and cured once in this chapter, in August, and the cure
was never carried to the module beside it.

## 11A. THE DISEASE CLASS, against P-i's own table

**`dev/LESSONS.md:2378-2381` gives three classes and their tests.** This term
is **BODY-BOUND**, and the cure is the one that row prescribes: "only an
interface change: restate the obligation so the concrete application is not
built".

**The evidence I have, and its limit, stated honestly.**

| set of definitions | `sucV α` in the STATEMENT? | `sucV α` applied in the BODY? | seconds |
|---|---|---|---:|
| Probe A's twelve, at `sucV α` | yes | yes | **100.64** |
| Probe D's five re-export aliases | yes | yes, through `module M = LeastCardAt (sucV α) ...` | **10.57** |
| Probe C's twelve, at a parameter | no | no | **1.35** |

**WHAT THIS DOES NOT DO: it does not re-earn the WITHDRAWN statement-bound
category.** `dev/LESSONS.md:2381` asks for "a properly gutted experiment", and
mine is not one: **Probe D's five definitions are not the same definitions as
Probe A's twelve**, so the 10.57 against 100.64 compares two different sets and
cannot separate statement from body. **I state that rather than claim the
category back.**

**What it DOES confirm is P-i's warning at `:2390-2398`.** "The test is not
'is the body short' but 'does any concrete application remain anywhere in the
definition, including inside its arguments'." **Probe D's bodies are one
projection each and they still cost 10.57 s, because the module application
passes `sucV α`.** A short body is not a gutted body, measured again, here.

## 12. SHARED or WING-LOCAL: WING-LOCAL. MEASURED

**The brief asked this loudly because `[LJ-1.147]` cured shared code, made
every master faster and made the DD24 verdict WORSE.**

**MEASURED, one grep: `L.Ordinal.SquareLaw` has exactly ONE consumer in
`src/`, and it is `src/Everything.lagda.md:323`.** No other master imports it.

**DD24's denominator is the AC wing, whose root is `src/L/Model.lagda.md`
(`dev/ledger.toml:170-171`). `L.Model` does not import `L.Ordinal.SquareLaw`,
directly or transitively, because nothing but `Everything` does.**

**So the cure is WING-LOCAL. It cannot move `ac_baseline_module_rate`, and the
`[LJ-1.147]` trap does not fire here.** The saving lands entirely on the judged
side.

**One honest qualification.** A5 is not delivered, so this is a cure to code
that does not exist in `src/` yet. **What it changes is the price A5 will
carry, not a price already paid.**

## 13. THE BASELINE, RE-MEASURED ON THIS MACHINE

**`[LJ-1.156]` ran at loads 2.85 to 3.32 and I run at 3.5 to 5.3, so I
re-measured its file myself rather than compare across sessions (P-q).**

**`agents/tasks/LJ-1-156/ProbeLJ1156A.agda`, unmodified, three cold runs, each
with its own interface deleted first, `GHCRTS="-A64m -I0 -M8g"`, exit 0 each
time.**

| file | 3 cold runs | mean | load band |
|---|---|---:|---|
| `ProbeLJ1156A.agda`, the chain as written | 134.48, 132.60, 131.93 | **133.00** | 4.19 to 4.95 |
| **`ProbeLJ1159E.agda`, the chain cured** | 45.54, 46.03, 46.89 | **46.15** | 3.57 to 4.03 |

**MEASURED: my mean is 133.00 and `[LJ-1.156]`'s mean is 133.00**
(`agents/tasks/LJ-1-156/lj-1.156-report.md:187-189`). **Two sessions, two load
bands, the same number.** So the A/B is same-machine, same-session, and no
cross-session correction is needed.

**THE HEADLINE, in its final form: 133.00 s to 46.15 s, both measured by me,
both three cold runs, both exit 0.** That is **minus 86.85 s, a factor of
2.88 on the whole chain**, for **plus 13 lines**.

**A note on the load, since the cured runs sat lower.** Probe E ran at loads
3.57 to 4.03 and the baseline at 4.19 to 4.95. **That pushes FOR my result, so
I flag it.** The gap is 0.9 in one-minute load against a 2.88-fold difference,
and `[LJ-1.148]`'s whole between-series band is 12.8 percent, so the load
cannot account for more than a few seconds of the 86.85.

## 14. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The 99 seconds are 13 source lines.** `κ-min-at` plus its six
  `where` bindings is 82,763 ms of 99,310 by profile, and 83.85 s of 100.18 by
  wall clock. **Two methods, agreeing inside 1.3 percent.**
- **MEASURED. `bInjP`, one `subst`, is 55,937 ms, 56.3 percent of the file.**
- **MEASURED. The least-of search is NOT the cost.** `leastOf`, `ordSWO`,
  `least`, `w`, `γ-card`, `Inj`, `InjP`, `InjP'`, `idInj` and `self` appear
  nowhere in the definitions profile.
- **MEASURED. `[LJ-1.107]`'s named cause is WRONG, and `[LJ-1.156]` carried it
  forward.** "The least-of over the well-order on the successor's presentation"
  (`agents/tasks/LJ-1-107/lj-1.107-report.md:52`) puts the blame on the
  least-of. The least-of is free. **The successor's presentation is the whole
  of it.**
- **MEASURED. The cost is right-hand-side elaboration.** `Typing.CheckRHS` is
  91,082 ms of 100,974, which is 90.2 percent.
- **MEASURED. The cure works: 100.64 to 11.92 at the module, 133.00 to 46.15
  at the whole chain, `--safe`, exit 0.**
- **MEASURED. 10.57 s of the saving comes back at the instantiation boundary**,
  and all of it is in the four re-export aliases whose types I wrote out at
  `sucV α`. **I report it rather than net it out.**
- **MEASURED. The cure is WING-LOCAL.** One grep: `L.Ordinal.SquareLaw` has
  one consumer in `src/` and it is `src/Everything.lagda.md:323`.
- **MEASURED. ZERO heap walls.** No run exhausted the 8 GB cap and the cap was
  never raised. **Five probe files of mine plus `ProbeLJ1156A.agda`,
  twenty-one timed runs and four profiled runs, all exit 0.**
- **MEASURED. The residue after the cure is the SAME defect one layer out.**
  Of Probe E's 43,268 ms, 16,399 is `Chain`'s own `subst`s over `LC0.κ` and
  10,816 is the concrete `Guard`. **Section 10C.**
- **MEASURED. The archived W7 scope-gate ruling does not bear on the injection
  swap.** Different layer and different shape; see ARCHIVE USED.
- **MEASURED. Devlin's square-law proof computes no cardinal.** Three cases,
  none of them a least-cardinal search.
- **REFUTED, MEASURED. The order-type lead.** The search is free, so
  "doing by search what an order type does by construction" is not the
  mechanism. See section 7.
- **REFUTED, MEASURED. R-40 is not the cause.** R-40 is about a DEEP iterated
  successor chain and prescribes climbing by small closures. **Here the depth
  is ONE successor and there is no chain to climb.** `[LJ-1.156]:618-621`
  proposed R-40 as a candidate; it does not apply.
- **NOT TRIED, and I say so rather than guess. The `opaque` seal.**
  `[LJ-1.156]:622-626` proposed it as the obvious first probe. **The parameter
  removes the term instead of hiding it, so the seal was never needed.**
  Whether a seal would ALSO have worked is **UNMEASURED in either direction.**
- **INFERRED. The same defect may sit in other modules of this chapter.**
  `sucV` appears 40 times in `src/L/Ordinal/SquareLaw.lagda.md`. **I did not
  measure any of them and I do not transfer this cure by analogy (P-l).**
- **INFERRED. `LeastCardAt` is generic in the ORDINAL, not in the CARRIER.** It
  still sits over `𝒮ᵥ` and `⟪_⟫`. **Not measured, and unchanged from
  `[LJ-1.156]`'s own residue.**

## 15. MACHINE STATE

**16 cores, macOS 25.6.0, Agda 2.8.0. ONE agda process of mine at a time,
always `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**

**The machine was NOT quiet.** `[LJ-1.158]` was working the three `*Agree`
masters throughout. **The one-minute load band over every run in this report is
3.22 to 5.26**, and each run's own load is recorded beside it in
`agents/tasks/LJ-1-159/runs.txt`.

**No verdict here turns on the load band.** The two headline comparisons are
100.64 against 1.35 and 133.54 against 46.15, both far outside any load effect
this machine shows, and `[LJ-1.148]`'s between-series uncertainty is 12.8
percent.

## 16. WORKING TREE, AS MY REPORT DESCRIBES IT

**Nothing committed, nothing pushed. No master edited. `src/` untouched.
`src/Everything.lagda.md` untouched. The three `*Agree` masters untouched.
`agents/tasks/LJ-1-156/` not edited.** I did not run `make check`.

**What is in the tree that is NOT mine.** `git status` shows
`src/L/Condensation/LowerAgree.lagda.md`, `TwelveAgree.lagda.md` and
`UpperAgree.lagda.md` modified, and `agents/tasks/LJ-1-158/` untracked.
**Those are `[LJ-1.158]`'s and I did not write, edit or delete any of them.**

**Checks I ran, all green:** `scripts/lint-prose.py --check` on this report
(exit 0), `scripts/lint-agda.py --check` (exit 0), `scripts/check-probes.py`
(clean, no probe outside `agents/tasks/`).

New files, all in `agents/tasks/LJ-1-159/`, none deleted. **They sit in the
tracked location the rule requires and are not yet added to the index, because
the orchestrator commits:**

- `lj-1.159-report.md`, this report.
- `ProbeLJ1159A.agda`, the transplant. `ProbeLJ1156D.agda` verbatim, renamed.
- `ProbeLJ1159B.agda`, the same minus `κ-min-at`. The wall-clock control.
- `ProbeLJ1159C.agda`, **THE CURE.** The ambient ordinal as a parameter.
- `ProbeLJ1159D.agda`, the cure plus its instantiation.
- `ProbeLJ1159E.agda`, **THE DELIVERABLE.** The whole chain, cured, exit 0.
- `prof-definitions.txt`, `prof-internal.txt`, `prof-definitions-D.txt`,
  `prof-definitions-E.txt`, the raw profiles.
- `runs.txt`, every timed run with its load.
- `run-profA.load`, `run-profA-internal.load`.

## 17. WHAT IS NOT DONE

1. **The cure is not applied to any master.** The brief forbids it and this is
   a diagnosis. **`ProbeLJ1159E.agda` is the form to land.**
2. **The residual 46.15 s is not attacked.** Section 10C profiles it and names
   the next gate: `Chain`'s own `subst`s and the concrete `Guard`.
3. **The 10.57 s boundary cost is not optimized.** A wrapper that re-exports
   without writing the types out might pay less. **UNMEASURED.**
4. **No other module of this chapter was measured.** `sucV` appears 40 times in
   the delivered `SquareLaw`. **P-l forbids transferring this cure by analogy,
   so each site needs its own measurement.**
5. **The `inj` parameter is still undischarged**, exactly as `[LJ-1.156]` left
   it. This task did not touch it.

## ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`**, read
  whole, **399 in-fence non-blank lines, counted by hand at the ledger's
  caliber** (`scripts/ledger.py` scans `src/*.lagda.md` only). **The scope-gate
  ruling is at `:3-13` and `:22-25`.**

  **VERDICT ON THE RULING: it is about a DIFFERENT LAYER and it does NOT bear
  on `[LJ-1.156]`'s swap. Two independent reasons, both checkable.**

  1. **Different layer.** The W7 gate governs the OBJECT-LANGUAGE predicate:
     `eqFo a b = ∃̇ (bijFo zero (suc a) (suc b))` (`:536-537`), a reified
     `Formula` with an adequacy certificate (`:539-546`), satisfied inside the
     hierarchy. **`LeastCardInj` is an AMBIENT type-theoretic predicate over
     presentations. It builds no formula, carries no certificate, and never
     enters L.** `[LJ-1.156]` measured that the whole chain names no L object
     (`agents/tasks/LJ-1-156/lj-1.156-report.md:481-483`).
  2. **Different shape, and this is the sharper reason.** The gate refused
     **"an injection EACH WAY"**, which is a SYMMETRIC definition of
     equinumerosity, that is, an EQUALITY. Its stated cost is that "every
     equality becomes a per-consumer Cantor-Bernstein obligation" (`:8-10`).
     **`[LJ-1.156]` uses ONE injection in ONE direction.** `⟪ α ⟫ ↪ ⟪ γ ⟫`
     says "α is no bigger than γ": it is an ORDER, not an equality, and the
     probe records the direction and why the other one fails
     (`ProbeLJ1156A.agda:170-175`). **No consumer can incur the obligation the
     gate feared, because no consumer ever needs a bijection.**

  **MEASURED, one grep over `ProbeLJ1156A.agda`: `κ-inj` is read at exactly two
  sites, `:468` (`κ∉ω`, which produces `Empty.⊥`) and `:548` (passed on as a
  hypothesis), and `κ-min-at` at `:544` and `:584`, both producing `Empty.⊥`.
  No equality is manufactured anywhere, and `≃` occurs in no non-comment
  line.** So the gate's failure mode is absent by construction.

  **SHAPE TAKEN, per DD18: none of the code. The ruling is the deliverable
  here, and the answer is that it does not reach this layer.**
- **`archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`**, 166 in-fence
  lines, and
  **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md`**, 907
  in-fence lines. **CONSULTED, and NOT used.** Neither states a least-cardinal
  search over a successor's presentation, so neither prices this term. Line
  counts by hand at the ledger's caliber.
- **`agents/tasks/LJ-1-156/lj-1.156-report.md`, read WHOLE.** TAKEN:
  section 4.1's A/B table (`:206-211`), which is the only source for the
  100.64 s baseline; section 5.3's rate arithmetic (`:299-332`); section 14's
  naming of this term as the next gate (`:613-630`), including the two
  candidate cures it lists. **BOTH OF ITS CANDIDATES ARE REFUTED HERE:** R-40
  does not apply, because the depth is 1 and not a chain, and the `opaque`
  seal was not needed, because the parameter removes the term instead of
  hiding it. `ProbeLJ1156A.agda` read whole; `ProbeLJ1156D.agda` copied
  verbatim as `ProbeLJ1159A.agda`; `ProbeLJ1156B.agda` for the 1.27 s import
  baseline.
- **`agents/tasks/archive/LJ-1-107/`.** **NOT FOUND at that path**; the brief
  named `agents/tasks/archive/LJ-1-107/ProbeLJ1107A.agda` and the live copy is
  `agents/tasks/LJ-1-107/ProbeLJ1107A.agda`. **I read the live copy.** Its
  `LeastCard` at `:217-266` states every type over `⟪ sucV α ⟫`, exactly as
  `[LJ-1.156]`'s injection version does. **So the defect is `[LJ-1.107]`'s and
  the swap inherited it, which is what `[LJ-1.156]` measured at 96.09 against
  100.64.**
- **`dev/LESSONS.md`**: **P-l** (`:2323-2418`), the law this task confirms and
  the site it already names. **P-y** (`:3704`), read whole: it is why I did NOT
  price a seal by the name count, and its warning about shared cures is what
  section 12 answers. **P-t** (`:2619`), **P-s** (`:2587`), **P-m** (`:2478`):
  the content-class vocabulary; I timed each piece WHOLE and divided nothing.
  **P-x** (`:3582`) and **P-w** (`:3112`): why Probe D exists at all, since a
  module application copies and the copy is paid at use. **R-40** (`:929`):
  **REFUTED as the cause here**, the depth is one successor and not an
  iterated chain. **C-12**: one process, `-M8g`, never raised. **C-22**:
  skeleton first. **C-36**: no refusal text was produced by any run, so no
  negative in this report rests on a coercion failure. **C-38**: Probe E is
  the supply, not a restatement. **C-39**: the brief's third abort branch let
  me report a cure instead of stopping at "no dominant term", and there WAS a
  dominant term. **C-40**: Probe E exists because a cured module proves
  nothing until a consumer elaborates.
- **`dev/PLAN.md:139-142`**, DD24's measured bar, 0.007913 s/line.
  **`dev/ledger.toml:170-171`** for the AC root, which is what makes section 12
  answerable. `:270-311` for the GCH wing's seconds budget.
- **`src/L/Ordinal/SquareLaw.lagda.md:503-531`**, `AbstractH₀`. **THE MOST
  USEFUL THING I READ.** It is the same cure, delivered, in this chapter,
  measured by `[T102]` at 374.3 s to 82 ms. Also `:146-182` (`ordSWO`),
  `:1-11` (the order-type ruling).
- **`src/V/Presentation.lagda.md:31-38`** and the cubical library at
  `Cubical/HITs/CumulativeHierarchy/Properties.agda:196-247` and
  `Constructions.agda:113-161`. **These are what turn the diagnosis from a
  correlation into a mechanism.**

## LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:1750-1785`**, Devlin II.6.6, read whole with
  its proof. **`G(α,β)` is the ORDER TYPE of the `<*`-predecessors, so
  `G : (On × On, <*) ≅ (On, <)` by construction.**
- **`_build/literature/dev2.txt:1791-1860`**, Devlin II.6.7, the square law,
  read whole. **Three cases keyed on `Q = {α | G : α × α ↔ α}`. NO cardinal is
  computed in any of them.** The one least-search is
  `E(ξ,ζ) = the least i such that k(i) = (ξ,ζ)` at `:1850`, which inverts a
  surjection at a smaller ordinal and is not a cardinal.
- **`_build/literature/dev2.txt:200-219`**, II.1.1(vii), where `|α|` and
  `|L_α|` are used. **CONSULTED: Devlin uses cardinality as ORDINARY set
  theory in the ambient, never as a constructed least-search inside a
  hierarchy proof.**
- **`dev/literature/devlin-II5.md`**, consulted for II.5's use of the square
  law. **NOT used for any figure in this report.**
