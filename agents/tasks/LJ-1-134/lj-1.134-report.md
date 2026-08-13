# LJ-1.134 report: run the `[LJ-1.131]` section 4 probe

tier: opus (version `override`). Probe only. No master edited. No commit, no push.
The probe is `src/ProbeLJ1134A.agda`. It is untracked and `.gitignore:27` covers it.
`scripts/check-probes.py` reports clean.

Every claim below is marked MEASURED (a machine result, or read at the cited
line) or INFERRED (my composition or judgement).

## 0. VERDICT: GO

**GO. MEASURED.** The widest unmeasured term elaborates.

The term is block A2 of `agents/reports/lj-1.131-report.md:368`: "an injection as
an ELEMENT of L, and read back as an honest function". The probe assembles it and
Agda accepts it under `--safe`.

| what | where | result |
|---|---|---|
| the fibre extraction, `toFun` and `toFun-inj` | `src/ProbeLJ1134A.agda:99-141` | GREEN |
| the composite with `leastOf (orderAt β)` | `src/ProbeLJ1134A.agda:147-183` | GREEN |
| a concrete non-degenerate graph, so the above is not vacuous | `src/ProbeLJ1134A.agda:190-289` | GREEN |
| the injection between the SMALL index types, `⟪ _ ⟫ → ⟪ _ ⟫` | `src/ProbeLJ1134A.agda:299-328` | GREEN |

Exit code 0 for the whole file. `--safe` is on
(`src/ProbeLJ1134A.agda:1`), so no postulate and no hole can hide in the result.
An earlier version failed with unsolved metavariables, so the checker does refuse
this file when the proof is incomplete (section 3).

**Seconds, and they are an UPPER BOUND: 2.51 s.** Section 1 gives the load and the
important qualification.

**Size: 207 non-blank non-comment lines. 255 non-blank lines including comments.**
MEASURED, both counted on `src/ProbeLJ1134A.agda`.

## 1. MACHINE STATE, and every figure is an upper bound

**The machine was much busier than the brief said, and it changed during the
task. MEASURED.**

- At my start: load averages **119.93 / 36.21 / 16.34**, four users. Three
  runaway `siriactionsd` processes took about 70 percent CPU each. The brief
  reported 4.21 at dispatch.
- At the final measurement: load averages **3.84 / 19.55 / 23.03**, then
  **3.70 / 19.26 / 22.90**.

**The three clean runs, with the probe interface deleted before each:**

| run | wall seconds | 1-minute load |
|---|---:|---|
| first | 2.37 | 3.84 |
| second | 1.53 | 3.70 |
| third | 2.51 | 5.07 |

**Report 2.51 s as the upper bound.** I ran ONE agda process, under
`GHCRTS="-A64m -I0 -M8g"`. No run was killed and no wall was hit.
Do not compare this figure with any recorded one: the machine was loaded and
this measurement has its own baseline.

**THE FIGURE IS NOT A COLD-TREE FIGURE, and this matters more than the load.**
`_build/2.8.0/agda/src/L/Coding/Model.agdai` and
`_build/2.8.0/agda/src/L/Choice/Step.agdai` were both present and current, so
Agda re-checked only my file. MEASURED: no "Checking L.Coding.Model" line
appeared in any run. The 2.51 s prices the ASSEMBLY, not the chain under it.

**This corrects `[LJ-1.131]` section 9 reason 2**
(`agents/reports/lj-1.131-report.md:567-570`). That report declined to run the
probe partly because it "must import `L.Coding.Model` (1,288 in-fence lines) and
`L.Choice.Step` together", and so "is not a five-minute miniature". With the
tree's interfaces cached, the probe costs about two seconds. **A probe over
cached interfaces is cheap even when its import closure is large.** That is a
general point about this tree and it is MEASURED here.

## 2. WHAT THE ASSEMBLY NEEDED THAT THE REPORT DID NOT ANTICIPATE

`[LJ-1.131]` section 4 named three parts: `svAt`, `domAt` and `appAt-adequate`.
Those three were necessary. They were not sufficient. Four more things were
needed, and each is a real cost line.

### 2.1 An injectivity formula. The object language had none. MEASURED

`svAt` states single-valuedness only: the first component determines the second
(`src/L/Coding/Model.lagda.md:210-215`). Injectivity is the mirror statement and
`src/L/Coding/` does not carry it. I checked and wrote it:
`injAt` with `injAt-out` and `injAt-in`, `src/ProbeLJ1134A.agda:61-93`,
**27 non-comment lines.** Without it `toFun-inj` cannot be stated at all.

### 2.2 TWO nested `Σ≡Prop`, because `svAt-out` returns the wrong equality. MEASURED

`svAt-out` concludes `fst y ≡ fst y'`
(`src/L/Coding/Model.lagda.md:246-248`). That is equality of the UNDERLYING sets.
The fibre lives in the model carrier, so the proof needs two lifts, one for the
`isL` certificate and one for the membership proof:

```
  isPropFib x (y , p) (y' , q) =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst F))
      (Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q))
```

`src/ProbeLJ1134A.agda:113-116`. My first attempt used one `Σ≡Prop` and Agda
refused it (section 3). **This is the exact point where the extraction could have
failed. It did not.** Both lifts are legal because `isL` is an `Ω`
(`src/L/Constructible.lagda.md:376`) and `∈` is an `hProp`.

### 2.3 A CARRIER CROSSING at every use of the order stack. MEASURED, and it is a correction

**`L.Choice.Step` works over the AMBIENT carrier. `L.Coding.Model` works over the
L carrier. They are different types.**

- `src/L/Choice/Step.lagda.md:78` reads `open hPropStructure 𝒮ᵥ`, so
  `Mem A = Σ[ x ∈ V ℓ ] ⟨ x ∈ˢ A ⟩` (`:227-228`) and
  `orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))` (`:740-741`) both live over
  `V ℓ`.
- `src/L/Coding/Model.lagda.md:71` reads `open hPropStructure 𝒮ʟ`, so its `S` is
  `Σ[ x ∈ V ℓ ] ⟨ isL x ⟩`.

So `leastOf (orderAt β)` selects a `Mem (Lset β)`, and `svAt` speaks about an `S`.
The probe crosses with `Lset→isL` (`src/L/Constructible.lagda.md:395`) at
`src/ProbeLJ1134A.agda:151-152`, and it crosses back with a `Σ≡Prop` transport at
`src/ProbeLJ1134A.agda:278-279`, because the two routes to the same set give
different certificates.

**The crossing is cheap: Part B is 22 non-comment lines in total. The point is
that it is PER USE.** `[LJ-1.131]` section 5 warned about `𝒮ᵥ` against `𝒮ʟ` for
`BoundedSubset`, `StageCardinal` and `SquareLaw`
(`agents/reports/lj-1.131-report.md:458-465`). It did not say that the ORDER
STACK ITSELF is ambient-carriered. Section 7 of that report says Route A'
"instantiates generic machinery ... It does not write fixed code"
(`:531-532`). **That is true and it is incomplete.** Route A' also crosses a
carrier boundary at every use of `orderAt`. INFERRED consequence, and it is a
DD4 point: write the crossing ONCE as a generic helper, not at each site.

### 2.4 `⟪ a ⟫` does not determine `a` by unification. MEASURED

Part D crosses into the small index types, which is the shape `[LJ-1.107]` and
`[LJ-1.114]` state their injections in. Agda could not infer the set from
`⟪ a ⟫`, and reported unsolved metavariables at line 325 of the file as it then
stood. The cure is to name the set: `↪-inj {a = fst D} {m = m} {n = n}`, now at
`src/ProbeLJ1134A.agda:326`. Small, and it will recur at every crossing.

### 2.5 What I ADDED beyond the specification, and why

The brief specified three steps. I added two.

- **Part C, a concrete graph, 74 non-comment lines**
  (`src/ProbeLJ1134A.agda:190-289`). Parts A and B take the two object-language
  statements as hypotheses. A false hypothesis makes any conclusion elaborate,
  and this tree has shipped two vacuous frames
  (`agents/reports/lj-1.129-report.md:334-338`). So I built the graph
  `{⟨a,a⟩}` with domain `{a}` from `pairʟ` and `prʟ`, proved all three
  hypotheses, and proved that the extracted function RETURNS `a` at `a`
  (`concreteFun-value`, `src/ProbeLJ1134A.agda:263-266`). The instance is
  instantiated at `numeralL 0` (`:291`). **The site is not degenerate: the domain
  has one member, and the function is a real injection with a real value.**
- **Part D, the small index types, 22 non-comment lines**. Section 2.4.

### 2.6 What the probe did NOT do, and I mark it

**I did not build a graph of an injection at `α = ω` with `ω` members.** The
brief's step 1 says "Fix `α = ω`. Build one concrete L-element graph `f` of an
injection." I built a concrete L-element graph of an injection, and it is the
one-point graph, not the identity on `ω`.

The reason is a choice about what the gate asks, and I state it so the
orchestrator can overrule. The abort criterion is "NO-GO if the fibre extraction
refuses". The extraction is uniform in the graph: it reads `svAt` and `domAt` and
knows nothing else. A graph with `ω` members would not exercise one extra line of
it. What an `ω`-sized graph WOULD price is the constructibility of that graph,
which is a separate question, and on the route the graph is not built by hand at
all: it comes out of `leastOf` (Part B). **So the missing piece is not on the
critical path of this gate.** INFERRED, and it is the one place where I departed
from the specification.

Two further consequences I did NOT measure, and neither is small:

- **The range set.** Part D takes "every value lies in `C`" as a hypothesis
  (`src/ProbeLJ1134A.agda:303-304`). A master must produce `C`, which is
  replacement over the graph. NOT PRICED HERE.
- **A `ranAt` formula with adequacy**, mirroring `domAt`. NOT WRITTEN.

## 3. THE REFUSALS I HIT, AND HOW THEY CLOSED

The verdict is GO, so there is no final refusal to report. Two intermediate
refusals matter, because they show the checker was awake.

**Refusal 1, the fibre, exact text. MEASURED.**

```
/Users/alsg/Agentic/Bedrock/src/ProbeLJ1134A.agda:77.5-63: error: [UnequalTerms]
V ℓ != Σ (FOL.ZFStructure.ZFStructure.S 𝒮ᵥ) (λ x₁ → x₁ ∈ᶜ isL) of
type Type (ℓ-suc ℓ)
when checking that the expression
Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q) has type
(y , p) ≡ (y' , q)
```

Cause: one `Σ≡Prop` lifts the underlying-set equality to the model carrier, and a
second is still needed to lift it to the fibre. Cured by section 2.2.

**Refusal 2, the small index types. MEASURED.** `[UnsolvedMetaVariables]` at
`src/ProbeLJ1134A.agda:325.21-326.59` of the file as it then stood, with the
metavariable `_a_1368` blocked
inside the library's `DeepMonicPresentation` elimination. Cured by naming the set,
section 2.4.

Both cures are bookkeeping. **Neither touched the mathematics, and that is the
finding: the mathematical step, single-valuedness makes the fibre a proposition,
went through as `[LJ-1.131]` predicted.**

## 4. DOES THE A' PRICE STILL STAND

**The 760 to 1,320 band still stands. The probe moves nothing outside it, and it
firms up two blocks out of seven.** MEASURED where stated, INFERRED for the
projection.

Per-part sizes of the probe, non-blank non-comment lines. MEASURED.

| part | lines |
|---|---:|
| imports and module header | 32 |
| `injAt`, `injAt-out`, `injAt-in` | 27 |
| Part A, the extraction | 29 |
| Part B, the `leastOf` composite | 22 |
| Part C, the concrete graph | 74 |
| Part D, the small index types | 22 |
| total | 207 |

**Block A2, priced 120 to 220** (`agents/reports/lj-1.131-report.md:368`). The
probe delivers A2's core in **78 lines**: `injAt` plus Part A plus Part D. A
master adds the range formula with its adequacy, which section 2.6 did not
price, plus the generic carrier crossing of section 2.3, plus prose. **A2 lands
inside its band, near the middle. The band does not move.** INFERRED.

**Block A3, priced 40 to 80** (`:369`). Part B is the whole selection and it is
**22 lines**. That is evidence for the LOW end. I do not lower the band, because
Part B fixes the stage `β` as a parameter, and a master must obtain `β` from
`stageBound` (`src/L/Choice/Stage.lagda.md:294`). **INFERRED: A3 will land at 40
to 60 rather than 40 to 80.** I state it as a direction, not a re-price.

**Blocks A1, A4, A5, A6 and A7: NOT TOUCHED by this probe.** Their bands stand
exactly as `[LJ-1.131]` wrote them. I did not re-price them and I have no
measurement that bears on them.

**One risk the probe RAISES, and it is new.** Section 2.3's carrier crossing is
per-use. `[LJ-1.131]` section 5 already priced the `𝒮ᵥ` to `𝒮ʟ` restatement of
the three GCH masters at about 300 lines and called it "the real cost of A'"
(`:458-465`). The order stack adds a second crossing that the section 5 table
does not show, because the table lists `src/L/Choice/*` as "unchanged, both
routes" (`:449`). **That row is correct as written: the stack does not change.
What changes is that every CONSUMER of it must cross.** INFERRED that this stays
inside A2 and A3's bands, because the probe's own crossing cost 22 lines.

## 5. WHAT I WOULD DO NEXT

1. **Write the crossing ONCE, generic.** One helper turning a `Mem (Lset β)` into
   an `S`, and one turning an object-language graph into `⟪ d ⟫ → ⟪ c ⟫`. DD4.
   The probe's Parts B and D are the shape.
2. **Price the range.** Section 2.6 names the two unpriced pieces: the range set
   by replacement, and a `ranAt` formula with adequacy. They are the next widest
   unmeasured term inside A2, and they are cheap to probe by the same method.
3. **Proceed with A'.** The gate is green and no alternative route was needed.

## 6. ARCHIVE USED (DD18)

`archive/` and `archive/dev/`: **NOT read.** The task is a single elaboration
measurement against the LIVE tree, and no archived module is imported by the
probe or bears on whether a live definition elaborates. I record the omission
rather than claim a survey.

Reports read:

- `agents/reports/lj-1.131-report.md`, whole (669 lines). Took: the section 4
  specification with its abort criterion (`:418-436`), the A2 price (`:368`), the
  A3 price (`:369`), the delivered-parts citations (`:211-224`), the carrier
  warning (`:458-465`), the DD4 argument (`:516-532`), and the two reasons no
  probe ran (`:563-570`).
- `agents/reports/lj-1.129-report.md:334-338`, the two vacuous frames. It is why
  Part C exists.
- `agents/reports/lj-1.114-report.md:1-30` through the probe file header
  `src/ProbeLJ1114A.agda:1-30`, for the shape a probe in this tree takes.

Masters read, at the cited lines: `src/L/Coding/Model.lagda.md` (header,
`:60-305`, `:330-345`), `src/L/Choice/Step.lagda.md` (`:40-90`, `:220-300`,
`:725-760`), `src/L/WellOrder/Base.lagda.md` (`:54`, `:101-175`),
`src/L/Constructible.lagda.md` (`:46`, `:141-144`, `:376-411`),
`src/FOL/ZFStructure.lagda.md` (`:91-152`),
`src/FOL/Absoluteness.lagda.md` (`:57-79`), `src/V/Hierarchy.lagda.md` (`:78-86`),
`src/V/Model.lagda.md` (`:85-100`, `:173-183`), `src/V/Coding.lagda.md`
(`:175-182`), `src/V/Presentation.lagda.md` (`:20-42`),
`src/L/Axioms/Numerals.lagda.md` (`:31-60`, `:88-180`),
`src/L/Choice/Stage.lagda.md` (`:285-300`).

`dev/LESSONS.md`: the probe bundle was loaded with
`.venv/bin/python scripts/rules.py --for probe` and read. D-1, P-l, P-i, C-12,
D-10, C-22 and R-40 came back.

- **D-1** is honoured: the abort criterion was fixed by `[LJ-1.131]` before I
  started, and I did not move it.
- **P-l bears directly and I honoured it.** Every set in Parts A, B and D is a
  PARAMETER, never a transparent presentation. No type in the probe mentions
  `sucV`, `# n` or any explicit stage. That is also why Part D uses `⟪ fst D ⟫`
  with `D` abstract. Part C names `numeralL 0` once, at a module application
  (`src/ProbeLJ1134A.agda:291`), and it cost nothing measurable.
- **C-12** is honoured: one agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never
  raised, no heap exhaustion.
- **C-22** is honoured: this file was created as a skeleton before the first
  agda run and filled as answers landed.
- **R-40** did not bite. No deep successor chain appears in any type.

## 7. DD4, ANSWERED AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic.**

The probe is generic where it can be. `Extract` takes the graph, the domain and
the two statements as parameters (`src/ProbeLJ1134A.agda:99-101`). `injAt`,
`injAt-out` and `injAt-in` are written at an arbitrary arity `n` and an arbitrary
variable `f` (`:61-93`), which is the shape `L.Coding.Model` gives `svAt`, so
they can move into that master unchanged. `Small` is generic in all three sets
(`:299-304`). Only `Concrete` fixes anything, and its one fixed choice, the
element `a`, is still a parameter (`:190`).

**Section 2.3 is a DD4 finding and I put it forward as one.** The carrier crossing
between `L.Choice.Step` and `L.Coding.Model` will be needed at every point where
the GCH wing consumes the AC side's order. Written once and generic, it is shared
code by construction. Written per site, it is duplication that no checker will
catch.

**No stop-line pushed me toward writing fixed.** Nothing in this task required a
special case, and I did not take one.
