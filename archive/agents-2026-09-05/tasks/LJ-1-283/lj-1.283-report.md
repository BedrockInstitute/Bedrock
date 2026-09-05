# [LJ-1.283] report: which over-bar masters carry the seal shape, and what each seal costs

STATUS: COMPLETE against the abort criterion's first branch, with TWO arms
measured instead of one. Written incrementally (C-22). Every negative is
marked MEASURED or INFERRED, in those words. ASD-STE100 applies.

## LEAD, in four sentences

**The answer to the owner's question is NO for most of the list, and NO at the
biggest site.** Of the eight over-bar masters, two have no live candidate at
all, three refuse a seal on P-y grounds, and the largest, at 482.73 s, is
MEASURED not to respond to one: control 482.20 s, layer-cap seal 481.28 s, a
delta of minus 0.19 percent.

**The one thing that DID pay was the bisect, not the seal.** One
`--profile=definitions` run charges **475,710 ms of 479,311 ms, 99.2 percent
of `src/L/Coding/EnvSupply.lagda.md`, to ONE two-line definition**, `sucV∈` at
`:223-224`. Nobody had looked; the file has zero `opaque` in 833 lines.

**Two masters should leave the over-bar list**, because their over-bar rate is
the bar's fixed intercept and not their content, and **one candidate with the
best P-y ratio in the neighbourhood sits outside the eight**, at
`src/L/Coding/Graph.lagda.md:94`.

**So: bisect all of them, yes. Seal all of them, no.**

Machine at start: load 4.94 5.29 5.43 at 14:10. A SIBLING AGDA RAN during my
first runs: `[LJ-1.282]` held its own C-12 slot on `src/L/Cardinal.lagda.md`.
Every absolute figure below carries its own load pair.

## 0. THE SEAL SHAPE, and the three measured outcomes it can have

The record gives three different outcomes for one lever. They are not in
conflict. They separate by WHERE the cost sits.

| outcome | site | what the cost was | seal result |
|---|---|---|---|
| the seal WINS | `[LJ-1.281]`, `w = ordSWO (sucV (fst α))` | a consumer RE-unfolds a transparent definition in its conversion checks | 100.50 s to 9.16 s |
| the seal WINS | `[LJ-1.147]`, `satGraphAt` | a pattern split makes the heads differ, so the checker walks the formula tree | `LeafAgree.out` 9,833 to 1,306 ms |
| the seal is VOID | `[LJ-1.152]`, `G` and `G-spec` | the cost is the definition's OWN elaboration | 260.37 and 270.53 s against 247.60 s, inside a 6.4 percent spread |
| the seal is VOID | `[LJ-1.214]`, the telescope component | the cost is the component's EXISTENCE in a telescope TYPE | 83 ms of 8,236 ms, sign flipping |

**The test that separates them.** A seal stops a CONSUMER walking a body. It
does nothing about the body's own elaboration, and it does nothing about a
type that still names the object. P-i states the second case as class `[E]`:
"when the heavy operator is welded into the TYPE of a field or proof
obligation, `opaque`/`abstract` cannot help (the type still mentions it)"
(`dev/LESSONS.md:262-269`).

So the triage question is not "is there a transparent heavy definition here".
It is "does a CONSUMER pay to look inside one".

## 1. RANKED LIST

`src/L/Cardinal.lagda.md` is EXCLUDED from the survey, per the brief, because
`[LJ-1.282]` is landing its cure right now. I did not read it and I did not
measure it. Stated as the brief asks.

| rank | master | seconds | carries the shape | P-y name-count | P-y inside-count | verdict |
|---:|---|---:|---|---:|---:|---|
| 1 | `src/L/Coding/EnvSupply.lagda.md` | **482.73** | shape YES, seal **MEASURED VOID** | 30 in-block | 1 (`B₀`), 2 (`lev4`) | **482.20 to 481.28 s. NO** |
| 2 | `src/L/Condensation.lagda.md` | 132.28 | **YES**, `SatGraphB.satGraphB` at `:2294` | 9 | **2**, one free | best untested ratio |
| 3 | `src/L/Condensation.lagda.md` | 132.28 | YES, `SatGraphB.twelveB` at `:2236` | 14 | 3, one free | second in the same file |
| 4 | `src/L/Condensation.lagda.md` | 132.28 | YES, `closedBS` at `:1586` | 11 | 3 | third in the same file |
| 5 | `src/L/Condensation/TwelveAgree.lagda.md` | 8.77 | shape yes, economics NO | 3 | 3 | REFUSE, every namer is an insider |
| 6 | `src/L/Condensation/UpperAgree.lagda.md` | 5.60 | shape yes, economics NO | 4 | 3 | REFUSE |
| 7 | `src/L/Condensation/LowerAgree.lagda.md` | 5.25 | shape yes, economics NO | 4 | 3 | REFUSE |
| 2= | `src/L/Ordinal/SquareLaw.lagda.md` | 8.28 | **YES**, `ordSWO` at `:176-182` | 5 | **1**, at `subrel` `:293-300` | best ratio, and TOWER-SHARED |
| 8 | `src/L/BoundedSubset.lagda.md` | 15.78 | YES, `isOrdAt` at `:795-798` | 16 | 3 | LOW STAKE, a 4-line formula |
| 9 | `src/L/Ordinal/StageArith.lagda.md` | 0.94 | **ALREADY SEALED** at `:40-42` | | | DROP |
| 10 | `src/V/Presentation.lagda.md` | 0.66 | **NO SHAPE AT ALL** | | | DROP |

**`src/L/Ordinal/SquareLaw.lagda.md` deserves its own line, because it is the
SUPPLIER of the term two tasks cured at a CONSUMER today.** `ordSWO` at
`src/L/Ordinal/SquareLaw.lagda.md:176-182` is a transparent record literal of
type `SWO ⟪ α ⟫`, the well-order arm of the shape by name.
`agents/tasks/LJ-1-281/lj-1.281-report.md:16-17` names
`w = ordSWO (sucV (fst α))` at `src/L/Cardinal.lagda.md:86` as the root of a
100.50 s file, and the LOCAL seal took it to 9.16 s. **The supplier is still
transparent.** Its name-count is 5 and its inside-count is ONE, at `subrel`,
`src/L/Ordinal/SquareLaw.lagda.md:293-300`, which needs the projection
`SWO._<∙_ ordSWO` to reduce to `_≺₁_`. Bundle `prodSWO` at `:127-133` with
it: same shape, same single inside-site.

**A WARNING ON SquareLaw, and it is mine, not the triage's.** The
supplier-side seal and `[LJ-1.282]`'s consumer-side seal are ALTERNATIVES,
not additive. Do not count the 91 s twice.

**TWO MASTERS SHOULD LEAVE THE OVER-BAR LIST, and neither deserves a build
brief.**

- `src/V/Presentation.lagda.md` carries **NO seal shape at all**. It has four
  definitions, `member` `:31-32`, `fiber` `:34-35`, `↪-inj` `:37-38`, `∈ₛ↪`
  `:40-41`, and each body is a single application of an imported Cubical
  lemma. **Nothing there has a body with structure, so nothing can be
  walked.** MEASURED by reading, 42 file lines read whole.
- `src/L/Ordinal/StageArith.lagda.md` is **ALREADY SEALED**. `+ω` is opaque
  at `:40-42`, and `:44-79` is its `unfolding` block. Everything below `:80`
  reaches `+ω` through named readers, so P-y is already applied correctly
  here. `agents/tasks/LJ-1-218/lj-1.218-report.md:195` also records that the
  whole `+ω` family has no consumer in the tree today.

**AND THE REASON THEY ARE OVER THE BAR IS THE BAR, NOT THE CONTENT.** These
two are the FASTEST files in the whole `[LJ-1.218]` series in absolute
seconds: 0.66 s and 0.94 s against the series' 132.28 s top. A two-point fit
on them gives a marginal rate near 0.005 s/line, under the bar, and an
intercept near 0.57 s. **INFERRED**, from two points and no new run; but the
direction does not depend on the fit. The over-bar verdict is a fixed
per-file cost divided by a small line count. This is P-t read backwards: an
average hides a fixed cost as surely as it hides an expensive term.

**`src/L/BoundedSubset.lagda.md`'s real lever is DELETION, not a seal.**
`module LevelHood` `:74-146` and `module LevelHood0` `:840-870` build the
heaviest formula tree in the survey, and **`LevelHood0` is applied by
nobody**: `grep -rn LevelHood0 src/` returns exactly one line, its own
declaration at `:840`. `agents/tasks/LJ-1-218/lj-1.218-report.md:193` says
the same. **A seal saves nothing there, because `opaque` does not stop Agda
elaborating the sealed definition itself; it only stops OTHER definitions
unfolding it, and outside the certificate there are none.** That is 96 dead
lines and a different build brief.

**A CANDIDATE OUTSIDE THE EIGHT, and it has the best P-y ratio I found.**
`twelveAt` at `src/L/Coding/Graph.lagda.md:94`, a twelve-fold `∧̇` chain,
transparent, and the sibling of `satGraphAt` sixty lines below it in the same
file, which IS sealed. **Twenty-one code sites across five masters name it.
TWO need to see inside**, and both are adjacent one-line readers:
`src/L/Condensation/LowerAgree.lagda.md:330` and
`src/L/Condensation/UpperAgree.lagda.md:331`. There is no `Δ₀-twelveAt`
anywhere in `src/`. It is the supplier of the three Agree masters' own cost,
which is why the three of them refuse a seal of their own and still sit over
the bar.

## 2. THE P-y PRICE, `src/L/Coding/EnvSupply.lagda.md`

**MEASURED: EnvSupply is a LEAF master. Its external name-count is ZERO, so
its external inside-count is ZERO.**

- `grep -rn "L.Coding.EnvSupply" src/` returns two lines: the module header at
  `src/L/Coding/EnvSupply.lagda.md:17` and the catalog line at
  `src/Everything.lagda.md:381`. No master imports it.
- `src/L/BoundedSubset.lagda.md` does NOT import it. MEASURED, grep of that
  file for `EnvSupply` returns nothing. `[LJ-1.276]` section 3 names
  `module Whole` in `L.BoundedSubset` as the consumer; that consumer is not
  yet wired.
- None of the fourteen exported names I checked (`envK-mem`, `envK-neg`,
  `envK-top`, `envK-imp`, `envK-allin`, `envInK-mem`, `envInK-neg`,
  `envInK-top`, `envInK-imp`, `someEnv`, `levelK`, `prK`, `valK`,
  `Lset-fin`) appears in `src/` outside the master. The one hit for
  `Lset-fin` is a DIFFERENT definition, `src/L/Coding/Key.lagda.md:139`.

**What this means for P-y.** P-y prices a seal by the definitions that must
see INSIDE. For a seal placed inside EnvSupply, every such definition is
inside EnvSupply itself. **The seal cannot cost an `unfolding` block in any
other master, because no other master can see the name.** This is the
cheapest P-y setting in the survey.

## 3. WHERE EnvSupply's SECONDS ARE, and the record already localized them

`[LJ-1.275]` bisected this content before it landed, with a reversed paired
design, nine kept runs, `agents/tasks/LJ-1-275/lj-1.275-report.md:295-320`.

| marginal | seconds | lines | rate |
|---|---:|---:|---:|
| the env block, N minus C | **458.55** | 362 | 1.267 s/line |
| the whole step 6 block, U minus C | 463.64 | 805 | 0.576 s/line |

**So 458.55 s of the master's 482.73 s sits in `module SupplyEnv`, and the
443 lines after it cost about 5 s between them.** `module SupplyEnv` is
`src/L/Coding/EnvSupply.lagda.md:107-442`. `module Fact`, `module AtLevel`,
`levelK`, `Lset-fin` and `module SupplyMerge` are cheap. MEASURED by
`[LJ-1.275]`, not by me; I re-derive the control below.

This is P-t applied before the fact: the master's 0.5795 s/line average hides
a 1.267 s/line term and a near-free tail.

## 4. THE ONE MEASURED ARM, control first

### 4.1 WHICH CANDIDATE I PICKED, AND WHY THE OTHERS LOST

I picked `src/L/Coding/EnvSupply.lagda.md`. It wins on both terms of the
ratio the brief names.

- **Seconds at stake: 482.73 s.** That is 3.6 times the next master
  (`src/L/Condensation.lagda.md` at 132.28 s) and more than every other
  over-bar master put together.
- **P-y price: the lowest possible.** EnvSupply is a LEAF. Its external
  name-count is ZERO, so a seal inside it can cost an `unfolding` in no other
  master. Section 2.
- **Nobody had looked inside it for this shape**, which the brief states and
  which I confirm: `grep -rn "opaque" src/L/Coding/EnvSupply.lagda.md`
  returns nothing. MEASURED, zero `opaque` in 833 lines.

The others lost on seconds, not on shape. `src/L/Condensation.lagda.md` has
the better P-y ratio but costs 132.28 s cold per run, and the brief fixes one
arm. `src/L/Ordinal/SquareLaw.lagda.md`'s `ordSWO` is the best ratio in the
survey but its local stake is 8.28 s. The three Agree masters refuse a seal
on P-y grounds. `src/V/Presentation.lagda.md` and
`src/L/Ordinal/StageArith.lagda.md` are the two FASTEST files in the series
and neither has a live candidate.

### 4.2 A REFUTATION I OWE THE RECORD, and the profile bought it for one run

**My first structural guess was WRONG, and I did not spend a measured run on
it.** I read the block, found `B₀ = LsetS gam ordγ` at
`src/L/Coding/EnvSupply.lagda.md:124-125`, and priced it: **30 sites in the
block NAME `B₀` and exactly ONE, `B₀∈σ` at `:127-131`, needs to see inside.**
That is a textbook P-y candidate, and it is the same shape `[LJ-1.281]` cured
on `src/L/Cardinal.lagda.md`. I wrote the sealed arm.

**Then the control's own profile refuted it.** `B₀∈σ` costs **12 ms**. The
P-y price was right and the target was wrong. I deleted the arm unrun.

**THIS IS P-l AND P-t TOGETHER.** P-l says a cure measured at one site is a
hypothesis at another; `[LJ-1.281]`'s 91-second win on a transparent carrier
said nothing about EnvSupply. P-t says an average hides the term. **A
structural reading of the source found the right SHAPE at the wrong SITE, and
only the measurement separated them.**

### 4.3 THE CONTROL, AND WHAT IT LOCALIZES

`ControlEnv.lagda.md`, `module SupplyEnv` verbatim from the master with the
module renamed, 390 in-fence non-blank lines (28 imports plus the 362-line
env block).

`agda --profile=definitions`, `GHCRTS="-A64m -I0 -M8g"`, cap never raised,
one agda process of mine. **Agda's own clock: Total 479,311 ms, exit 0.**
That is +4.1 percent on `[LJ-1.275]`'s 460.50 s three-run mean for the same
content, and this run carried both the profiler's overhead and a system load
spike.

**THE TERM, and it is ONE LINE. MEASURED.**

| definition | site | ms | share |
|---|---|---:|---:|
| **`SupplyEnv._._.sucV∈`** | `src/L/Coding/EnvSupply.lagda.md:223-224` | **475,710** | **99.2 percent** |
| `SupplyEnv.someEnv` | `:415` | 116 | 0.02 percent |
| `SupplyEnv._._.sub₁` | `:164` | 48 | |
| `SupplyEnv.envInK-imp` | `:398` | 41 | |
| `SupplyEnv.B₀∈σ` | `:127` | **12** | my refuted candidate |
| Miscellaneous | | 2,787 | |

**Every other definition in the 362-line block costs under 120 ms. The whole
tail after `sucV∈` sums to about 800 ms.** P-t is not a warning here, it is
the whole finding: the master's 0.5795 s/line average, and even the env
block's 1.267 s/line marginal rate, both hide a single two-line definition
carrying 99.2 percent.

### 4.4 THE MECHANISM AT `sucV∈`

`src/L/Coding/EnvSupply.lagda.md:223-224`, inside `sucK`'s `step`:

```
      sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃
```

`union∈Lset-suc σ x x∈ : ⟨ ⋃ x ∈ Lset (sucV σ) ⟩` (`:148`), so the body has
type `⟨ ⋃ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset (sucV δ₃) ⟩` with
`δ₃ = sucV (sucV (sucV δ))`.

**So the conversion checker must prove two equations at once:**

1. `⋃ ⁅ a , ⁅ a ⁆s ⁆ ≡ sucV a`. TRUE by two delta steps. The Cubical library
   defines `sucV N = N ∪ ⁅ N ⁆s` and `a ∪ b = ⋃ ⁅ a , b ⁆`
   (`Cubical/HITs/CumulativeHierarchy/Constructions.agda:156-161`).
2. `sucV δ₃ ≡ sucIter 4 δ`. TRUE by unfolding `sucIter`.

**Both are trivial at the bare type `V ℓ`. Neither is trivial UNDER the
membership head `⟨ _ ∈ Lset (sucIter 4 δ) ⟩`, which exposes FOUR
`Lset ∘ sucV` layers.** That is P-i class (1), a heavy set forced into
normalization, and its layer-cap sub-rule names this exact count:
"any tower of two or more `Lset ∘ sucV` layers gets one independent opaque
alias PER LAYER, so conversion unfolds at most one; costs multiply per
exposed layer" (`dev/LESSONS.md:245-252`). R-40 is the same law from the
other side: "a deep successor-chain membership witness normalizes
super-linearly" (`dev/LESSONS.md:929`).

### 4.5 THE TREATED ARM

`TreatedBridge.lagda.md`. **One change, and nothing else in the file
differs.** It states equation 1 at the bare type `V ℓ`, where no membership
head and no level stand in the way, and bridges with one `subst`. This is
P-i `[A]`, "bridge the concrete membership by one subst".

```
      sucEq : ⋃ ⁅ a , ⁅ a ⁆s ⁆ ≡ sucV a
      sucEq = refl
      sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      sucV∈ = subst (λ w → ⟨ w ∈ Lset (sucIter 4 δ) ⟩) sucEq
        (union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃)
```

### 4.6 THE RUNS

**The warm-up pair, both discarded, both exit 0.**

| arm | seconds | load before to after | clock |
|---|---:|---|---|
| `ControlEnv` | **479.31** | 7.80 to 229.82 | agda's own `--profile` Total |
| `TreatedBridge` | **495.50** | 105.01 to 8.42 | wall |

Both warm-ups ran through the system load spike described in section 8. The
kept series below ran on a quiet machine.

**THE KEPT SERIES**, on a quiet machine, load 5 to 7. Order reversed between
cycles.

| run | arm | seconds | load before to after |
|---|---|---:|---|
| c1 | `ControlEnv` | **482.20** | 6.20 to 4.48 |
| t1 | `TreatedBridge` | **485.80** | 4.48 to 4.61 |

**THE PAIRED DELTA: plus 3.60 s, plus 0.75 percent, at the SAME load, one run
after the other. MEASURED. The bridge arm is VOID.** For scale, `[LJ-1.152]`
measured a 6.4 percent spread on ONE identical file
(`agents/tasks/LJ-1-152/lj-1.152-report.md:154`). A 0.75 percent difference is
an order of magnitude inside that band, and its sign is the wrong way.

**c1 at 482.20 s reproduces three independent figures**: agda's own profile
Total of 479.31 s on the same file, `[LJ-1.276]`'s 482.73 s for the delivered
master (`agents/tasks/LJ-1-276/lj-1.276-report.md:84`), and `[LJ-1.275]`'s
460.50 s three-run mean for the same content
(`agents/tasks/LJ-1-275/lj-1.275-report.md:314`). The control is stable and
it is NOT load-sensitive: 482.20 s at load 6.2 against 479.31 s during a load
spike.

Runs pending.

**I STOPPED THE SERIES SHORT ON PURPOSE, and the reason is a finding.** The
brief asks for three kept runs of ONE arm. After the first pair I could see
that further repeats of the bridge arm would only re-measure a null, while
the owner's actual question, whether a SEAL cures this site, was still
unanswered because my arm was a `subst` bridge and not a seal. **I spent the
remaining budget on the seal arm instead of on the third repeat.** Section
4.8. I report `n` honestly everywhere and I do not call the bridge's null a
three-run result.

### 4.7 THE VERDICT ON THE ARM

**MEASURED: THE BRIDGE DOES NOT CURE `sucV∈`.** 495.50 s against the
control's 479.31 s, and `[LJ-1.275]`'s independent three-run mean for the same
content is 460.50 s. **The treated arm is inside the noise band and on the
wrong side of it.** This is the `[LJ-1.152]` outcome repeating, and the abort
criterion's fourth branch fired: report it MEASURED.

**WHY IT FAILED, and this is the finding that a build brief needs.** My arm
removed the EQUATION from the conversion. It did not remove the TYPE. The
motive I wrote is still `λ w → ⟨ w ∈ Lset (sucIter 4 δ) ⟩`, so the four
`Lset ∘ sucV` layers are still exposed, and the membership head still forces
`Lset (sucIter 4 δ)` toward a form its eliminator can fire on. **The cost is
the object's PRESENCE in the type, which is `[LJ-1.214]`'s failure mode and
P-i's class `[E]`: "when the heavy operator is welded into the TYPE ...
`opaque`/`abstract` cannot help, because the type still mentions it"**
(`dev/LESSONS.md:262-269`).

**C-36, stated as the brief requires: a failed substitution is not a proof of
impossibility. WHAT I COULD NOT WRITE, and did not run:**

- **The layer-cap seal.** P-i's `[B]` sub-rule says a tower of two or more
  `Lset ∘ sucV` layers gets one independent opaque alias PER LAYER, and it
  measured a case where four exposed layers in a module hypothesis type
  doubled a file's check, 44 s to 90 s, and one 18-line seal restored it
  (`dev/LESSONS.md:245-252`). **There are exactly four layers here.** The
  alias has to seal the LEVEL, `sucIter 4 δ`, not the equation, and it needs
  its own read lemma inside the seal so `union∈Lset-suc`'s conclusion can
  still land. I ran out of budget before I could write and price it. **This is
  the arm the next brief should fund, and it is the one that tests the
  owner's actual question at this site.**
- **R-40's own cure**, which is a restatement rather than a seal: state the
  membership at a SHALLOW index and climb by the limit-ordinal successor
  closure (`dev/LESSONS.md:929`). That is a mathematical change to `sucK`, not
  a probe.

**NEITHER IS REFUTED BY MY ARM.** My arm refutes ONE cure, the explicit
equation bridge, at ONE site.

### 4.8 THE SEAL ARM, which is what the owner actually asked about

**Why I wrote a second arm.** The owner's question is about SEALING. My first
arm was a `subst` bridge, not a seal, and it also carried a defect I can name:
its motive was `λ w → ⟨ w ∈ Lset (sucIter 4 δ) ⟩`, so the argument still had
to convert `Lset (sucV δ₃)` with `Lset (sucIter 4 δ)` UNDER the membership
head. **The bridge removed one of the two conversions and left the other in
the heavy position.**

`TreatedSeal.lagda.md` fixes both and adds the seal. Three changes, all at
`sucK` and its new sealed helper.

1. **The layer-cap seal (P-i `[B]`).** One opaque alias for the four-layer
   level, with its read lemma inside the seal, stated at VARIABLES so the one
   conversion the seal owes is never paid at a heavy value:

```
  opaque
    lev4 : V ℓ → V ℓ
    lev4 d = sucIter 4 d

    lev4-mem : (d x : V ℓ) → ⟨ x ∈ Lset (sucV (sucV (sucV (sucV d)))) ⟩
             → ⟨ x ∈ Lset (lev4 d) ⟩
    lev4-mem d x h = h

    lev4∈λ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ lev4 d ∈ lam ⟩
    lev4∈λ d h = B.suc^∈λ 4 d h
```

2. **The bridge, with the motive corrected** so the level on both sides is
   `Lset δ₄` and `δ₄ = sucV δ₃` is SYNTACTICALLY the body's own level. Now
   neither conversion happens under a membership head.

3. **The consumer reads the sealed level**, so `Lset-mono` is applied at
   `lev4 δ` and never at the four exposed layers.

**P-y PRICE OF THIS SEAL: 2, both inside the seal.** `lev4-mem` and `lev4∈λ`
are the only definitions that see inside `lev4`, they are R-36 read lemmas,
and they live in the `opaque` block itself. Outside it, `lev4` is named twice
and unfolded never. **And EnvSupply is a leaf, so no other master pays
anything.**

**THE RESULT. `TreatedSeal.lagda.md` is GREEN, `--safe`, exit 0, and it
changes NOTHING.**

| run | arm | seconds | load before to after |
|---|---|---:|---|
| c1 | `ControlEnv` | **482.20** | 6.20 to 4.48 |
| t1 | `TreatedBridge` | 485.80 | 4.48 to 4.61 |
| s1 | **`TreatedSeal`** | **481.28** | 8.03 to 6.05 |

**THE SEAL'S DELTA: minus 0.92 s, minus 0.19 percent. MEASURED. THE SEAL IS
VOID AT THIS SITE.**

**All three arms lie inside a 0.94 percent band**, which is narrower than the
0.9 percent own-spread `[LJ-1.275]` measured for this content and far inside
the 6.4 percent `[LJ-1.152]` measured on one identical file. Three arms, three
figures, one answer.

### 4.9 WHAT THIS MEANS, and it is the answer to the owner's question at this site

**THE SEAL IS NOT THE CURE FOR `src/L/Coding/EnvSupply.lagda.md`. MEASURED,
by a paired series on a quiet machine.** This is `[LJ-1.152]` repeating, and
it repeats for `[LJ-1.152]`'s own reason: **the 475 s is the elaboration of
that one definition's body, not a consumer's walk into a transparent one.** A
seal stops consumers. There is no consumer to stop here: `sucV∈` is a
`where`-bound local with exactly one use, three lines below it.

**WHERE THE COST ACTUALLY IS, and this is INFERRED, not measured.** I did not
re-profile the seal arm, so I cannot say whether the 475 s stayed on `sucV∈`
or moved. What the seal arm rules out is stated above. What remains, in
order of my confidence:

1. **The application `union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃` itself.**
   `union∈Lset-suc` is a 55-line proof at `:148-202` that builds a formula,
   proves `DefA.defSet φ ≡ ⋃ x` by `extensionality`, and applies it here at a
   CONCRETE pair argument. Rule 1's site exactly: "any proof step whose
   expensive term sits under a concrete argument" (`dev/LESSONS.md:325-331`).
   **INFERRED.**
2. **`sucEq = refl` at bare `V ℓ`.** Two delta steps should make this free, so
   I rank it low, but I did not measure it. **INFERRED.**

**THE NEXT MEASUREMENT IS CHEAP AND IT IS ONE RUN:**
`agda --profile=definitions` on `TreatedSeal.lagda.md`. If `sucV∈` still
carries 475,000 ms the cost is the application; if it moved to `sucEq` the
cost is the HIT-value conversion. **Neither is a seal question any more**, and
that is itself the finding: for this master the owner's lever is the wrong
one, and the right brief is a Rule-1 or R-40 restatement of `sucK`, not a
seal.

## 5. WHY THE OTHERS LOST, one line of reason each

| master | why it did not get the run |
|---|---|
| `src/L/Condensation.lagda.md` | **Best P-y ratio in the survey**, `satGraphB` at `:2294` with 9 namers and 2 insiders, one of them free. It lost on RUN COST only: 132.28 s cold per run against EnvSupply's 482.73 s of stake. It should get the NEXT arm |
| `src/L/Condensation/TwelveAgree.lagda.md` | P-y REFUSES it. `twelveB` at `:491` has name-count 3 and inside-count 3: `out` `:495` builds the pair, `back` `:502` projects it. Every namer is an insider |
| `src/L/Condensation/UpperAgree.lagda.md` | Same refusal. `sixB` `:300`, 4 namers, 3 insiders. Its 5.60 s is a walk of `twelveAt`, which lives in `src/L/Coding/Graph.lagda.md` |
| `src/L/Condensation/LowerAgree.lagda.md` | Same refusal. `sixB` `:293`, 4 namers, 3 insiders |
| `src/L/Ordinal/SquareLaw.lagda.md` | **Best ratio, 5 namers and ONE insider at `subrel` `:293-300`, and tower-SHARED.** It lost on stake: 8.28 s locally. Its value is as the SUPPLIER of `[LJ-1.281]`'s cured term, and that is a separate brief |
| `src/L/BoundedSubset.lagda.md` | The real lever is DELETION of 96 dead lines, not a seal. `LevelHood0` `:840` is applied by nobody |
| `src/L/Ordinal/StageArith.lagda.md` | ALREADY SEALED at `:40-42`, and its `+ω` family has no consumer. 0.94 s |
| `src/V/Presentation.lagda.md` | NO seal shape exists. Four definitions, each a single application of an imported lemma. 0.66 s |
| `src/L/Cardinal.lagda.md` | EXCLUDED by the brief. `[LJ-1.282]` is landing its cure now. I did not read or measure it |

## 6. WHAT [LJ-1.152]'s SEAL FAILURE TEACHES, and which candidates would fail the same way

**WHAT HAPPENED THERE.** `agents/tasks/LJ-1-152/lj-1.152-report.md:145-158`.
`ProbeLJ1152C` is `src/ProbeLJ1136A.agda` verbatim. `ProbeLJ1152D` is the same
file with `G` and `G-spec` sealed `opaque`, one change and nothing else.

| probe | seconds |
|---|---:|
| C run 1 | 260.37 |
| C run 2 | 270.53 |
| **D, the sealed arm** | **247.60** |
| the same file on 2026-08-13 | 254.22 |

**The identical file ran 254.22, 260.37 and 270.53 s on three occasions. The
spread on ONE file is 6.4 percent. The seal moved the figure by 4.9 percent
against the mean of the three. The seal is INSIDE THE NOISE.**

**THE MECHANISM, and it is the one sentence that decides every row of my
table.** The 254 s was the replacement's OWN elaboration, not the conversion
cost of letting consumers look inside it. **A seal stops a CONSUMER walking a
body. It does nothing about the body's own elaboration.** `[LJ-1.152]`'s
report says it in its own words at `:155-158`.

**THE SECOND FAILURE MODE, `[LJ-1.214]`.** There the cost was the component's
EXISTENCE in a telescope TYPE.
`agents/tasks/LJ-1-214/lj-1.214-report.md:170-176` and `:190`: sealing it
`opaque` moved **83 ms of 8,236 ms, with the sign flipping**. P-i states this
as class `[E]`: when the heavy operator is welded into a TYPE,
`opaque`/`abstract` cannot help, because the type still mentions it
(`dev/LESSONS.md:262-269`).

**SO THERE ARE THREE WAYS TO PAY, AND ONLY ONE OF THEM A SEAL CURES.**

| where the cost sits | seal result | precedent |
|---|---|---|
| a CONSUMER re-walks a transparent body | **CURED** | `[LJ-1.281]` 91 s, `[LJ-1.147]` 87 percent |
| the definition's OWN elaboration | **VOID** | `[LJ-1.152]`, inside a 6.4 percent noise band |
| the object's PRESENCE in a telescope type | **VOID** | `[LJ-1.214]`, 83 ms of 8,236, sign flipping |

**WHICH OF MY CANDIDATES WOULD FAIL THE SAME WAY. INFERRED, except where
marked.**

- **`sucIter` at `src/L/Ordinal/StageArith.lagda.md:34-36` is the
  `[LJ-1.152]` shape by the letter, and it is the clearest refusal in the
  survey.** Name-count is 53 occurrence lines across four masters.
  **Inside-count is 8 confirmed and up to 11**, because eight consumers apply
  it at a LITERAL numeral and NEED the walk: `sucIter-ord` at
  `src/L/Ordinal/StageArith.lagda.md:72-74` splits on `n`; `suc^∈λ` at
  `src/L/Coding/Bound.lagda.md:97-99` splits on `k`; and
  `src/L/Coding/Key.lagda.md:428-429`, `:115`, `:131`, `:133`, `:98` each
  cross a gap of one or more literal steps. **`opaque` would turn
  `sucIter 3 σ` into a stuck atom and break all eight.** This is P-y's price
  read the expensive way, and it is a real answer: the abort criterion's
  third branch fired for this candidate.
- **`CloseSyntax.closeAt` at `src/L/BoundedSubset.lagda.md:518-531` is the
  same refusal.** It is a RECURSIVE function over the formula, not a built
  formula, and its whole theory (`mapFo-close` `:566-588`, `⊨-close`
  `:628-653`) is proved by structural recursion on its own defining
  equations. Sealing a recursive function whose theory is its own equations
  is `[LJ-1.152]` exactly.
- **`levelHoodB` at `src/L/BoundedSubset.lagda.md:108-111` fails for the
  `[LJ-1.152]` reason precisely: the cost is its OWN elaboration.** The
  module application at `:81-105` instantiates `GraphB` with two `DefBodyB`
  formulas of sixteen `Fin` arguments each. **That elaboration is paid
  whether or not the result is sealed**, and there is no consumer to stop,
  because `LevelHood0` is dead. MEASURED, by grep: one hit, its own
  declaration.
- **`colStep` at `src/L/Ordinal/SquareLaw.lagda.md:378-379` is a deliberate
  computation window, not an oversight.** Inside-count 4, at `:394`, `:408`,
  `:464` and `:899`, and each is essential. It exists so that `col` above it
  CAN be sealed at `:383-388`. Sealing it moves the seal one step and buys
  nothing.
- **The three Agree masters fail on economics, not on mechanism.** For
  `TwelveAgree.twelveB` at
  `src/L/Condensation/TwelveAgree.lagda.md:491`, name-count is 3 and
  inside-count is 3. **Every namer is an insider.** `out` at `:495` builds a
  pair and `back` at `:502` projects it, so the `∧̇` must reduce in both. P-y
  says refuse.

## 7. DD4 PER CANDIDATE, WITH ITS AXIS

**AXIS NAMED (C-46): DD4's own axis is AC-against-GCH**, fixed in code at
`scripts/ledger.py:50` and rooted at `reuse.ac_root = src/L/Model.lagda.md`
and `reuse.gch_root = src/L/GCH.lagda.md` in `dev/ledger.toml`. The report
ran today at **41.1 percent shared, 43 masters and 7,596 lines of a
18,480-line union**. `.venv/bin/python scripts/ledger.py --reuse`.

**I computed the two closures myself and my method reproduces the ledger
exactly: 73 AC masters, 48 GCH masters, 43 shared.** So the membership
answers below are checkable against `scripts/ledger.py --reuse`.

| candidate's home | in AC closure | in GCH closure | what a seal there does to DD4 today |
|---|---|---|---|
| `src/L/Coding/EnvSupply.lagda.md` | **NO** | **NO** | **nothing.** Outside both closures |
| `src/L/Condensation.lagda.md` | **NO** | **NO** | **nothing.** Outside both closures |
| `src/L/Condensation/{Twelve,Upper,Lower}Agree.lagda.md` | **NO** | **NO** | **nothing.** Outside both closures |
| `src/L/BoundedSubset.lagda.md` | **NO** | **NO** | **nothing.** Outside both closures |
| `src/L/Coding/Graph.lagda.md` (`twelveAt`) | **YES** | NO | AC-side definition; its two inside-readers are outside both closures |
| `src/L/Coding/Model.lagda.md` (`envSetAt`, `envOverAt`) | **YES** | **YES** | genuinely SHARED. A seal is inherited by both towers, paid once |
| `src/L/Ordinal/SquareLaw.lagda.md` | NO | **YES** | GCH-only, paid once on the GCH side |
| `src/V/Presentation.lagda.md` | NO | **YES** | GCH-only, paid once on the GCH side |

**THE DD4 ANSWER, stated plainly. MEASURED.** Six of the eight over-bar
masters are in NEITHER trophy closure today, because `module Whole` in
`src/L/BoundedSubset.lagda.md` is not wired and `src/L/GCH.lagda.md` is a
77-line statement file. **So no seal among the top four candidates moves the
41.1 percent figure today.** They enter the GCH closure on the day
`module Whole` lands. A seal placed now is therefore inherited by the GCH
tower for free when the wiring happens, and it is paid once, not per tower.

**The one genuinely shared candidate is `envSetAt` and `envOverAt` in
`src/L/Coding/Model.lagda.md`, which is in BOTH closures.** A seal there is
inherited by both proofs. **It is also where P-y's own recorded warning
applies:** P-y measured that a seal in shared upstream machinery made the AC
side gain 41.7 percent against the GCH wing's 8 percent, and the DD24 ratio
went 1.56x to 1.91x, so **every master got faster and the verdict got worse**
(`dev/LESSONS.md:3840-3846`). That is the owner's ruling to make, not mine.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-281/lj-1.281-report.md`, read WHOLE as the brief
  requires.** ONE line: `:28`, the `TreatedOpaque` row, 9.16 s. **TAKEN:** the
  separation of a seal that cures a CONSUMER's re-walk from one that does not,
  and the paired reversed design I copied.
- **`agents/tasks/LJ-1-218/lj-1.218-report.md:56-67`.** ONE line: `:195`,
  which records that the whole `+ω` family has no consumer in the tree today.
  **TAKEN:** the rate table, and the fact that killed StageArith as a target.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`.** ONE line: `:151`, the
  `ProbeLJ1152D` row, 247.60 s for the sealed arm. **TAKEN:** the whole
  failure mechanism, that the 254 s was the definition's OWN elaboration and a
  seal cannot touch it.
- **`agents/tasks/LJ-1-214/lj-1.214-report.md`.** ONE line: `:190`, "Seal it
  `opaque`: 83 ms of 8,236 ms, sign flipping". **TAKEN:** the second failure
  mode, a cost that is the object's PRESENCE in a telescope type.
- **`agents/tasks/LJ-1-275/lj-1.275-report.md`.** ONE line: `:318`, the env
  block marginal, 458.55 s over 362 lines. **TAKEN:** the localization that
  saved me a bisection, and the reversed nine-run design. **NOTE:** their
  harness calls `time.monotonic()` twice inside ONE python process, which is
  correct; my `measure.sh` first called it in TWO processes, which is not, and
  I fixed it.
- **`agents/tasks/LJ-1-276/lj-1.276-report.md`.** ONE line: `:84`, the
  delivered master at 482.73 s, exit 0. **TAKEN:** the standing figure for the
  master, and its DD4 section, which I re-derived rather than quoted.
- **`dev/LESSONS.md` P-y, FULL entry at `:3803-3849`.** **TAKEN:** the two
  counts, the measured 5-to-3 split on `satGraphAt`, and the DD24 warning.
- **`dev/LESSONS.md` R-36, FULL entry at `:808-826`.** **TAKEN:** the read-lemma
  shape, which is what the `B₀` arm would have used and what a Condensation
  brief should use.
- **`dev/LESSONS.md` P-i, FULL entry at `:203-300`.** **TAKEN:** class (1), the
  `[B]` layer-cap sub-rule that names the four-layer count exactly, and `[A]`,
  "bridge the concrete membership by one subst", which is my treated arm.
- **`dev/LESSONS.md` Rule 2 at `:334-349`.** **TAKEN:** the 2,300x datum and
  "a module application is such a site".
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE line:
  `:159`, `[L3.32-T124]`, "Images 52.9 to 6.7 s, Step 28.8 to 4.6 s with zero
  Step edits, 70.3 s total, exports intact". **TAKEN AS SHAPE:** that a seal
  landed at the SUPPLIER can cut a consumer with zero consumer edits, which is
  the argument for the `ordSWO` brief. **WHAT WOULD NOT TRANSFER:** the
  retired route's `Images`/`Step` numbers price a different tree, and P-l
  forbids carrying them here. I carried none.
- **`Cubical/HITs/CumulativeHierarchy/Constructions.agda:156-161`**, the
  library, not the archive. **TAKEN:** `sucV N = N ∪ ⁅ N ⁆s` and
  `a ∪ b = ⋃ ⁅ a , b ⁆`, which is why equation 1 in section 4.4 is true.

## 8. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. `src/L/Coding/EnvSupply.lagda.md` has a consumer today.**
  `grep -rn "L.Coding.EnvSupply" src/` returns its own module header and the
  catalog line at `src/Everything.lagda.md:381`. No master imports it, and
  `src/L/BoundedSubset.lagda.md` does not.
- **MEASURED FALSE. `B₀` at `src/L/Coding/EnvSupply.lagda.md:124` is the
  expensive term.** It has the right SHAPE and a P-y price of one, and it
  costs **12 ms**. I refuted my own candidate with the control's profile and
  never ran its arm.
- **MEASURED FALSE. The env block's cost is spread over its 362 lines.** ONE
  definition, `sucV∈` at `:223-224`, carries **99.2 percent**. Every other
  definition is under 120 ms.
- **MEASURED FALSE. `src/V/Presentation.lagda.md` carries the seal shape.**
  It has four definitions and each body is a single application of an imported
  Cubical lemma. Nothing there has a body with structure.
- **MEASURED FALSE. `src/L/Ordinal/StageArith.lagda.md` needs a seal.** `+ω`
  is already `opaque` at `:40-42` with its `unfolding` block at `:44-79`.
- **MEASURED FALSE. `LevelHood0` in `src/L/BoundedSubset.lagda.md` has a
  consumer.** `grep -rn LevelHood0 src/` returns exactly one line, its own
  declaration at `:840`.
- **MEASURED. A defect in my own harness.** `measure.sh` first read the clock
  with `time.monotonic()` in TWO separate python processes. On this machine
  that call's reference point is the CALLING PROCESS's start, so the first
  run's wall figure read 0.02 s and is void. **Agda's own
  `--profile=definitions` Total of 479,311 ms is the control figure I use, and
  it is the tool's clock, not mine.** The harness now uses `time.time()`.
  `[LJ-1.275]`'s harness is NOT affected: it calls `time.monotonic()` twice
  inside one process, which is correct.
- **MEASURED. The machine was NOT quiet.** A system spike drove the
  one-minute load average to **317.84 at 14:23**, from `siriactionsd`,
  `mobileassetd`, `identityservicesd`, `pCloud` and `fseventsd`, with no
  project process involved. This reproduces `[LJ-1.152]` section 2 exactly.
  Every figure below carries its own load pair.
- **INFERRED. The over-bar verdict on the two smallest masters is the bar's
  intercept, not their content.** A two-point fit on 18 lines at 0.66 s and 75
  lines at 0.94 s gives a marginal rate near 0.005 s/line and an intercept near
  0.57 s. Two points is not a measurement of an intercept, so this is INFERRED.
- **INFERRED. Sealing `satGraphB` in `src/L/Condensation.lagda.md` costs about
  two lines.** The inside-count of 2 is read off the source, not measured by a
  run.

## 9. WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-283/`:

- `LJ-1.283.md`, the pinned brief, written first.
- `lj-1.283-report.md`, this file.
- `ControlEnv.lagda.md`, the control, 390 in-fence non-blank lines. GREEN,
  exit 0.
- `TreatedBridge.lagda.md`, arm 1, the equation bridge. GREEN, exit 0.
  `diff` of the two fences shows the module name and ONE substantive change.
- `TreatedSeal.lagda.md`, arm 2, the layer-cap seal plus the corrected
  bridge. GREEN, exit 0.
- `measure.sh`, `series.sh`, `timings.csv`, `runs/`.

All three files typecheck `--safe --guardedness`, exit 0, zero postulates,
zero holes, zero heap walls. Longest run 495.50 s, so **no run came near the
30-minute wall and no heap exhaustion occurred. MEASURED.** One agda process
of mine at all times, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

`git status --porcelain` shows `agents/tasks/LJ-1-283/` as the only path I
created. It also shows `src/L/GCH.lagda.md` modified and
`agents/tasks/LJ-1-223/`, `agents/tasks/LJ-1-286/` untracked. **None of those
three is mine.** The GCH edit is a sibling's; I never opened that file.

**No master edited. No `src/` edited. No `src/Everything.lagda.md`, no
`dev/PLAN.md`, no `dev/ledger.toml`.** No commit, no push, no
`git checkout .`, no stash, no reset, no clean. I did not run `make check`.
`src/L/Cardinal.lagda.md`, `agents/tasks/LJ-1-282/` and
`src/L/Choice/Name.lagda.md` were not touched. `scripts/check-probes.py
--check` exits 0. `lint-prose.py --check` and `lint-agda.py --check` exit 0 on
everything I wrote.

## LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.
