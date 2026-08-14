# LJ-1.184 report: `AmbientRead`, Devlin's clause (a) at the AMBIENT carrier

tier: opus (version `override`). **Three probes were written. All three ran
GREEN. No master was changed. No commit, no push.** Every negative is marked
**MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

### 0.1 SUPPLIED, and ONE of the four open hypotheses closed

**`AmbientRead` is SUPPLIED at its VERBATIM type**, the one
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192` states.
`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:150`, exit 0.

**`theorem` comes out at the REAL site with `amb` gone.**
`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:95`, exit 0, 19.62 s warm. The probe
enters the same `Devlin55.BoundedSubsetAt` entry that `[LJ-1.178]`'s probe B
entered, and `Site178.Open` now takes THREE named hypotheses instead of four.

**`[LJ-1.178]`'s four are now three: `sl`, `sc`, `s₁`.**

### 0.2 AND THE SUPPLY RESTS ON A NEW RESIDUE. I say so first.

**The supply is a FUNCTION of six readings that the tree has at the class
carrier only.** They are the coded step, its approximation and its graph, READ
AT THE AMBIENT CARRIER: `StepAt-out`, `StepAt-back`, `ApproxAt-dom`,
`ApproxAt-value`, `ApproxAt-step` and `Graph-out`.

**So the count is 3 named hypotheses plus a 6-reading residue, not 3.** What
changed is the KIND of the debt, and section 5 measures it:

| before | after |
|---|---|
| `amb`, Devlin's clause (a): a THEOREM about the ambient universe | six ADEQUACY readings: "this delivered description says what it says, read in `V`" |
| no reduction, no price, `[LJ-1.178]` refused a figure | the read-off above the step is **MEASURED carrier-generic at 167 lines**, and the residue is bounded by four named blocks |

### 0.3 `[LJ-1.178]`'s fixed GO/NO-GO: **GO**

`[LJ-1.178]` section 7 fixed the next probe's criterion in advance:

> **GO** if the pair restates with the carrier abstract and no new hypothesis
> beyond transitivity. **NO-GO** if either lemma needs `isL` in an essential
> position, for example through `PowOK`.

**GO, and I mark it MEASURED.** `step-Lset`, `approx-val` and the graph read-off
restate with the carrier abstract. **`isL` occurs ZERO times in the generic
module's 167 code lines.** `PowOK` is NOT an obstacle: it becomes a hypothesis
ABOUT the class, and at the ambient class it is `tt*`.

**One correction to `[LJ-1.178]`'s wording, and it is the whole result.** The
criterion said "no new hypothesis beyond transitivity". **Three closure facts
are needed, not one:** transitivity, that the class holds the levels, and that
the class holds their definable powersets. **At the ambient class all three are
`tt*`**, so the correction costs nothing here. **MEASURED**,
`agents/tasks/LJ-1-184/ProbeLJ1184A.agda:80-95` and `:335-341`.

### 0.4 The road is NOT circular, and I measured the one that is

**The second road IS circular and I confirm it as MEASURED, not INFERRED.**
`[LJ-1.178]` marked `πX ⊆ L` circular from reading. I read
`src/L/BoundedSubset.lagda.md:997-1008` whole: `πX⊆Lβ` takes `cover` and nothing
else, and concludes `πX ⊆ Lset β`. **Supplying `πX ⊆ L` in order to get `cover`
is circular. MEASURED.**

## 1. THE WHOLE-TREE SUPPLY SEARCH, RUN BEFORE ANY LINE WAS WRITTEN

`[LJ-1.163]` measured that one excluded file cost three dispatches. I report
every search, its scope and its result. **"Whole tree" means `git grep` over
every tracked file: `src/`, `archive/`, `agents/` and `dev/` together.**

| # | search | scope | result |
|---|---|---|---|
| T1 | `AmbientRead\|ambientRead\|ambient-read` | **whole tree** | Only `[LJ-1.178]`'s two probes, three reports and `dev/PLAN.md`. **Nothing in `src/`. MEASURED** |
| T2 | `⊨ᵛ` | **whole tree** | In `src/`, five masters: `FOL/Absoluteness`, `L/Ordinal/Stages`, `L/Condensation`, `L/Axioms/Separation`, `L/Definability`. **`L/Hierarchy` is NOT among them.** This re-runs `[LJ-1.178]` S5 over the WHOLE tree rather than `src/`, and the answer does not change. **MEASURED** |
| T3 | `AmbientOnly\|ValueIsL\|TransferL` | **whole tree** | **Nothing in `src/`.** The names live in `archive/dev/JOURNAL-archived.md:1875-1876` and `:2126-2128`, `dev/ARCHIVE.md:146`, and eight archived task reports. **This is the archive hit that shaped the road; section 8 spends it. MEASURED** |
| T4 | `LsetGraphAt` | `src/` | Defined in `L/Coding/Sequence`; consumed by five `L/Choice/*` masters and `L/Condensation`. **Every consumer reads at the class carrier. MEASURED** |
| T5 | `Lset-only\|Lset-defines\|LsetGraph` | `src/` | Same set. `src/L/Condensation.lagda.md:415-428` rides both and its own comment says "ridden here at the class carrier". **MEASURED** |
| T6 | `EraseTransfer\|σL-transfer\|erase-inv` | `src/` | **`src/L/Condensation.lagda.md:341-405` DELIVERS a class-to-ambient transfer, `σL-transfer`, for a Δ₀ parameter-free formula at an environment IN `L`.** It is not the term: the ambient witnesses are not in `L`. Section 2.2 |
| T7 | `Δ₀-levelHoodB\|Σ₁-levelHood\|LevelHood0` | `src/` | `src/L/BoundedSubset.lagda.md:74-146` and `:840-870`. **The level-hood matrix is Δ₀ and its Σ₁ certificate is delivered. MEASURED** |
| T8 | read `src/L/BoundedSubset.lagda.md:997-1008` whole | `src/` | `πX⊆Lβ` uses `cover` alone. **MEASURED**, upgrading `[LJ-1.178]`'s INFERRED |
| T9 | `Transitive 𝒮ᵥ\|Single 𝒮ᵥ` | `src/` | Twelve instantiation sites, every one at a NAMED class. **No carrier-generic read-off exists. MEASURED** |

**The two searches that decided the task are T3 and T6.** T3 found that the
archived route had already stated this exact obligation and had NOT proved it;
T6 found the delivered transfer and showed why it does not reach.

## 2. THE ROAD, DECIDED BEFORE ANY LINE WAS WRITTEN

The brief asked which of two roads I take. **I take the second: prove the
ambient statement directly.** Here is why, with the evidence for rejecting the
first.

### 2.1 Road 1, lift the class-carrier read-off. REJECTED, and the reason is measured

To lift `Lset-only` from `L` to `V` you must show the ambient witnesses are
constructible. That is the archived route's `TransferL` plus `ValueIsL`
(`archive/dev/JOURNAL-archived.md:1875-1876`), and the archive records that it
**stopped**: "`AmbientOnly` is NOT proved, and the stop is an obstacle rather
than a budget" (`:2126-2128`). At this site the constructibility needed is
`πX ⊆ L`, which `cover` proves (T8). **Circular. MEASURED.**

### 2.2 Why the delivered `σL-transfer` does not reach. MEASURED

`src/L/Condensation.lagda.md:365-370` gives
`σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩` for a Δ₀ parameter-free
formula. **Its environment `γ` is `S ^ m` with `S = Sʟ`: every entry is
constructible.** The ambient reading we must consume has ambient entries, and
its two outer existentials bind AMBIENT witnesses. **So the delivered transfer
is the wrong direction and the wrong environment. MEASURED**, by reading
`:341-405` whole.

### 2.3 Road 2, taken. The read-off is about a CARRIER, not about `L`

The proof of `Lset-only` never uses `isL` as a property. It uses `isL` three
times as a CLOSURE fact: members stay in the class (`isL-trans`), the class
holds the levels (`LsetS`), and the class holds their definable powersets
(`isL-𝒟ₒ`). **At the ambient class all three hold for nothing.** That is why the
ambient read-off is not harder than the class one; it is the SAME proof at a
class where the side conditions vanish.

**This is Devlin's own placement.** `dev/literature/devlin-II5.md:93-96` states
(a) with the quantifiers ranging over the real universe, and `:102-106` spends
it once at the collapsed `M`. Section 9.

## 3. THE BUILD

### 3.1 Probe A: the read-off, generic on BOTH axes

`agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, exit 0. **The generic module is 167
non-blank non-comment lines.**

It takes two axes of parameters and nothing else:

- **the tower axis:** `Tow`, `Dee`, and the tower's two decomposition legs
  `Tow-in` and `Tow-out`;
- **the carrier axis:** `Cl`, its transitivity, and the two closure facts.

Then `Machine` takes the SATISFACTION RELATION as a parameter, together with
three formulas and six readings. **The read-off proof never unfolds the
satisfaction relation.** That is the move that removes the bridge lemma: the
class instance and the ambient instance are two applications of one module, not
two theorems joined by a transfer.

`step-value`, `approx-val` and `graph-only` are `src/L/Hierarchy.lagda.md`'s
`step-Lset`, `approx-val` and `Lset-only` with the two axes abstracted.

### 3.2 The two instances

- **CLASS.** `ReadOff Lset 𝒟ₒ Lset-in Lset-out isL isL-trans ...`, with the
  three closure facts at `src/L/Axioms/Basic.lagda.md:160` and `:230`
  (`ProbeLJ1184A.agda:290-296`). This is the delivered `Lset-only`'s own
  setting, and it typechecks.
- **AMBIENT.** `ReadOff Lset 𝒟ₒ Lset-in Lset-out Full ...` with all three
  closure facts `tt*`, and the reading `ambient γ φ = (map fst γ) ⊨ᵛ φ`
  (`:318-330`). **This is Devlin's (a).**

### 3.3 `clause-a`, and one measured trap

`ProbeLJ1184A.agda:355-362` is the read-off at a two-slot environment, in
`[LJ-1.178]`'s verbatim shape. `free` (`:337-350`) is the one adapter: **an
ambient reading of a parameter-free formula does not depend on the constant
domain it is embedded into.** It is two applications of the delivered `embed-⊨`
(`src/FOL/Manipulation/Relabelling.lagda.md:184-186`) around one `funExt` over
the empty domain. **Four lines.**

**A MEASURED trap, and it cost about ten minutes.** A transitivity proof for a
class whose value does not mention its argument cannot be passed to a module
directly: Agda inserts metas for the two implicit arguments and nothing can
solve them, because `⟨ Full x ⟩ → ⟨ Full y ⟩` is constant in `x` and `y`. The
cure is to eta-expand at the application site,
`(λ {x} {y} → Full-tr {x} {y})` (`ProbeLJ1184A.agda:328`). **`isL` does not hit
this**, because `⟨ isL x ⟩ → ⟨ isL y ⟩` determines both metas. I offer this as a
candidate law and do not number it (section 10).

### 3.4 Probe B: the acceptance test

`agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, exit 0, 102 code lines.

`AmbientStep` takes the residue and produces

```agda
amb : (P : S) (Ptr : isTrans P) → P178.AmbientCross.AmbientRead P Ptr φ₀
amb P Ptr = A.clause-a fst φ₀ go
```

**One line, at `[LJ-1.178]`'s own type, checked against `[LJ-1.178]`'s own
module.** Then `Discharge.Closed` applies `Site.Whole` with `amb` supplied and
reads `levelIn` and `cover` back out at their verbatim site types.

### 3.5 Probe C: the brief's acceptance test, at the real site

`agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, exit 0, 63 code lines. It enters
`P178B.AtSite` with the site's own telescope, supplies `amb`, and reads
`theorem : ⟨ x ∈ˢ Lset κ ⟩` out. **`Site178.Open` receives three hypotheses and
one supplied term where it used to receive four hypotheses.**

## 4. MEASUREMENTS

**The machine was NOT quiet. Load averages 2.90 to 6.80, one user, 2026-08-14
09:20 to 09:45. Siblings were building, and one of them re-touched
`src/L/Condensation.lagda.md` twice during the run.** I report the load beside
every figure, as the brief instructed. Each figure discards a warm-up and keeps
three runs. **A run is forced by deleting the probe's own interface**, so no
figure is an interface load.

| run | file | result | seconds |
|---|---|---|---|
| probe A | `ProbeLJ1184A.agda` | **exit 0** | warm-up 1.96, kept **1.88, 1.88, 1.87**, mean **1.88** |
| probe A, no-op | same | exit 0 | **0.87** |
| probe B | `ProbeLJ1184B.agda` | **exit 0** | warm-up 2.75, kept **2.71, 2.67, 2.70**, mean **2.69** |
| probe B, no-op | same | exit 0 | **1.87** |
| probe C | `ProbeLJ1184C.agda` | **exit 0** | kept **19.68, 19.63, 19.55**, mean **19.62** |
| probe C, no-op | same | exit 0 | **2.78** |

**One figure I report and do NOT use.** Probe C's first run in each batch took
156.66 s and 157.80 s. **Both rebuilt `src/L/Condensation.lagda.md`, which a
sibling had touched. That is a dependency rebuild, not my probe**, and I exclude
it from the mean and say so.

`GHCRTS="-A64m -I0 -M8g"`. **One agda process. The cap was never raised. No heap
exhaustion.**

| figure | probe A | probe B | probe C |
|---|---:|---:|---:|
| all lines | 363 | 162 | 96 |
| non-blank | 318 | 135 | 78 |
| non-blank non-comment | **236** | **102** | **63** |
| the generic module alone | **167** | n/a | n/a |

**The honest reading of the seconds.** Probe A's own elaboration is
`1.88 - 0.87 = 1.01 s` over 236 lines. Probe C's is `19.62 - 2.78 = 16.84 s`
over 63 lines, and **almost all of it is entering `BoundedSubsetAt`, not my
code**: `[LJ-1.178]`'s probe B measured `10.25 - 2.69 = 7.56 s` for the same
entry with fewer imports, and probe C additionally carries probes A and B.

**Against DD24 I report the numbers and judge nothing.** A probe has no
` ```agda ` fences, so the ledger's counting rule does not apply, and no probe
here is a master. **Nothing in this report is a size claim on the GCH side.**
`scripts/ledger.py --brief`: standing **29,777 lines over 88 masters**, from
HEAD, thresholds SUSPENDED.

**Checkers.**

- `scripts/lint-agda.py --check` on all three probes: **exit 0**.
- `scripts/check-probes.py --check`: **clean**, 1,833 tracked files.
- **No `make check`.** The orchestrator runs it.

## 5. WHAT `theorem` STILL NEEDS

**Three named hypotheses, plus one residue. I price the residue and refuse one
figure inside it.**

### 5.1 The three named hypotheses, unchanged

`sl`, `sc` and `s₁`. `[LJ-1.178]` priced them and I do not re-price them: `sl`
and `sc` are the two stage facts, the priced residue; `s₁` is not a wall, and
its missing half is 2 lines written plus 4 to 8 INFERRED.

### 5.2 The residue: the coded step, READ IN `V`

Six readings, and they are the ambient twins of six delivered objects:

| reading | delivered at the class carrier | what its ambient twin needs |
|---|---|---|
| `Graph-out` | `src/L/Coding/Sequence.lagda.md:330-340` | **NOTHING.** It is the identity on a truncation. **MEASURED FREE** |
| `Approx-dom`, `Approx-value` | `:296-306` | `domAt-in`, `domAt-out` in `V` |
| `Approx-step` | `:308-313` | `appAt-adequate` in `V` |
| `Step-out`, `Step-back` | `:217-224` | `extAt-out`, `extAt-in`, `appAt-adequate`, **`DefAt-in` and `DefAt-out`** in `V` |

**Four delivered blocks, and three of them are small. MEASURED, by counting the
in-fence non-blank lines of the delivered block:**

| block | `src/L/Coding/Model.lagda.md` | in-fence lines |
|---|---|---:|
| `appAt` and `appAt-adequate` | `:160-190` | **21** |
| `domAt`, `inDomAt` and their two readings | `:269-320` | **34** |
| `extAt` and its three readings | `:662-700` | **29** |

**Those three total 84 delivered lines, and each is a plain set-theoretic
description whose ambient reading has no side condition.**

### 5.3 The one figure I REFUSE, and why (C-40, P-l)

**`DefAt-in` and `DefAt-out` in `V`. I give no line figure.**

`DefAt` (`src/L/Coding/Powerset.lagda.md:442-443`) is the definable powerset,
and its reading runs through `isCodeAt`, `satGraphAt` and `DefinesAt`, that is
through the satisfaction coding. **`src/L/Coding/Model.lagda.md` is 1,288
in-fence lines and `src/L/Coding/Powerset.lagda.md` is 395. A comparable from
those masters is a hypothesis about the ambient instance, not a price**, so I
do not transfer one. `[LJ-1.178]` refused a figure for the same reason and I
keep the refusal, one layer down.

**And `DefAt-out` carries a side condition even at the class carrier**:
`DefOK A`, discharged at a stage by `DefAt-stage` (`:720-727`). **MEASURED**,
by reading `:645-727`.

### 5.4 The next probe, with its abort criterion fixed IN ADVANCE (D-1)

> **The obligation.** `DefAt`'s ambient reading is only ever spent at a
> RECORDED VALUE, and the induction has already pinned that value to `Tow c`
> for an ordinal `c`. So ask whether the ambient reading can be spent at an
> environment whose two `DefAt` slots are CONSTRUCTIBLE, where the delivered
> `abs₀` plus the delivered `DefAt-stage` close it.
>
> **The smallest decisive miniature:** restate `StepAt-out` at the ambient
> carrier with TWO extra hypotheses, that the recorded value is `Lset c` and
> that `c` is an ordinal, and try to close it with `abs₀`, `DefAt-stage` and a
> slot-agreement lemma of `⊨-rename`'s shape.
>
> - **GO** if the two extra hypotheses are enough. Then the residue never
>   touches `L.Coding.Model`, and the whole ambient port is the 84 lines of
>   section 5.2 plus one restructuring of `step-value`.
> - **NO-GO** if `abs₀` cannot be applied because the OTHER environment slots
>   (the approximation `f`, the argument `b`) are not constructible and no
>   slot-agreement lemma reaches. Then the ambient `DefAt` reading is a port of
>   the satisfaction coding, and that IS a chapter.

**P-l binds on that probe by construction and I say so: the class-carrier
instance is NOT a price for the ambient instance.**

**INFERRED, and I mark it: I believe GO is more likely than NO-GO**, because
`Lset-only`'s own proof already carries the value equation at every step
(`src/L/Hierarchy.lagda.md:283-299`). **I did not typecheck one line of it.**

## 6. DD4

**Maximize the code the two proofs share, and write it generic.**

### 6.1 The measurement

**The generic module is 167 non-blank non-comment lines and it names NOTHING
tower-specific and NOTHING carrier-specific.**

| name | occurrences in the 167 lines |
|---|---:|
| `isL` | **0** |
| `𝒮ʟ` | **0** |
| `Lset` | **0** |
| `𝒟ₒ` | **0** |
| `Tow` (the tower parameter) | 36 |
| `Dee` (the step parameter) | 12 |

**Both axes are parameters.** The tower enters as four values, the carrier as
four, the satisfaction relation as one, and the coded step as nine.

### 6.2 What each end re-instantiates

- **The L tower at the class carrier** supplies `Lset`, `𝒟ₒ`, `Lset-in`,
  `Lset-out`, `isL` and the three closure facts. That instance IS `Lset-only`'s
  setting, and `ProbeLJ1184A.agda:290-296` builds it.
- **The L tower at the ambient carrier** supplies the same four tower values and
  `tt*` three times. That instance IS Devlin's (a).
- **The J tower** supplies its own `Tow`, `Dee` and two decomposition legs.
  **Nothing else changes, and it gets BOTH carriers for the same four values.**

**So the 167 lines are paid once and spent four times.**
`dev/literature/devlin-II5.md:374-382` classes the level-hood formula as
PER-TOWER and the absoluteness and transfer rows as EITHER TOWER; **this module
is the EITHER-TOWER content and it now carries the carrier axis as well.**

### 6.3 Generic was the SHORT form, and I re-measured it

**I first wrote the module generic in the CARRIER only, at 161 code lines, and
it was green.** Adding the TOWER axis took it to 167. **Six lines bought a
second tower. MEASURED**, by counting both states of the same file.

**No stop-line pushed me toward writing fixed.** This agrees with
`[LJ-1.159]:263`, `[LJ-1.151]` and `[LJ-1.178]`, and it is a fourth independent
site.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the tree already supplies `AmbientRead` | **MEASURED FALSE.** T1, T2, T3 |
| `AmbientRead` derives from the delivered `Lset-only` | **MEASURED FALSE.** `Lset-only`'s environment is `Sʟ ^ n`; the ambient witnesses are not constructible. Section 2.1 |
| the delivered `σL-transfer` reaches it | **MEASURED FALSE.** Wrong direction, and its environment is in `L`. Section 2.2 |
| `πX ⊆ L` is a way around | **MEASURED FALSE**, upgrading `[LJ-1.178]`'s INFERRED. `πX⊆Lβ` (`src/L/BoundedSubset.lagda.md:997-1008`) uses `cover` alone |
| the read-off needs `isL` in an essential position | **MEASURED FALSE.** Zero occurrences in 167 code lines. This is `[LJ-1.178]`'s NO-GO condition, refuted |
| `PowOK` blocks the ambient carrier | **MEASURED FALSE.** It is a hypothesis about the class and it is `tt*` there |
| "no new hypothesis beyond transitivity" | **MEASURED FALSE.** Three closure facts, not one. Section 0.3 |
| a bridge lemma between the two readings is needed | **MEASURED FALSE.** The satisfaction is a parameter, so no bridge exists to write |
| the read-off is tower-specific | **MEASURED FALSE.** Section 6.1, zero `Lset` in the machine |
| `amb` still gates `theorem` | **MEASURED FALSE.** `ProbeLJ1184C.agda:95` reads `theorem` out with `amb` supplied |
| the residue is empty | **MEASURED FALSE.** Six readings, section 5.2. **I lead with this** |
| `Graph-out` needs anything at the ambient carrier | **MEASURED FALSE.** It is the identity on a truncation |
| the ambient `DefAt` reading is cheap | **NOT CLAIMED, and I refuse a figure.** Section 5.3 |
| the ambient `DefAt` reading is a chapter | **NOT CLAIMED.** Section 5.4 fixes the probe that decides it |
| `sl`, `sc` and `s₁` moved | **MEASURED FALSE.** They are `[LJ-1.178]`'s, unchanged, and I did not re-price them |
| probe C's 156.66 s prices my code | **MEASURED FALSE.** It rebuilt a sibling's master. Section 4 |
| probe seconds price a master | **MEASURED FALSE.** No probe has fences and none is a master |

## 8. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-178/`, READ WHOLE, both probes included.** TOOK the term
  (`lj-1.178-report.md:59-62`), the four open rows (`:30-36`), the circularity
  finding (`:207-214`), the refused figure (`:226-237`), the fixed GO/NO-GO
  (`:356-372`) and the DD4 section (`:279-314`). **From `ProbeLJ1178A.agda`:
  the `AmbientCross` module (`:184-196`), `Site` (`:285-299`) and `Whole`
  (`:489-505`). From `ProbeLJ1178B.agda`: the site telescope (`:49-65`) and
  `Open` (`:88-108`). Probe C enters that module unchanged.**
- **`archive/dev/JOURNAL-archived.md`, read `:1870-1880` and `:2120-2135`.**
  **TOOK the archived route's own statement of this obligation:** `AmbientOnly`
  at the class carrier, factored into `TransferL` and `ValueIsL`, and the
  record that it **STOPPED**, "an obstacle rather than a budget". **SHAPE TAKEN,
  CLAIM REFUSED.** What does NOT transfer: the archive's obligation was at the
  CLASS carrier and its blocker was the class-carrier equivalence; mine is at
  the AMBIENT carrier and the equivalence never appears, because the class is a
  parameter.
- **`archive/dev/JOURNAL-archived.md:2197` and `:2199`**, read. TOOK the
  measured profile of `ambientOnly-from`: 128.5 s of a 203 s module, and the
  finding that ~77 s was an environment conversion between an unprojected and a
  projected premise. **THIS SHAPED THE BUILD:** my `Machine` takes the
  satisfaction relation as a parameter, so no environment conversion between
  two readings exists to pay. **The archive's most expensive row is a row this
  design does not have.**
- **`archive/dev/TASKS-archived.md:105` and `:179`**, read. TOOK the outcome:
  `L3.32-T144` deleted the section and `L.Condensation` fell 150.2 s to 11.5 s,
  `ambientOnly-from` being 92 percent.
- **`dev/ARCHIVE.md:146`**, read whole. TOOK the revival condition and the note
  that **D39 superseded it**: a revival is admissible on its own merits, not on
  its resemblance to the retired design. **That is why I did not reproduce the
  `TransferL`/`ValueIsL` factorization.**
- `agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:18`, read. TOOK
  `AmbientOnly`'s exact archived type. **It is the CLASS-carrier form; mine is
  the ambient one, and the two differ in which carrier `⊨ᵛ` is taken over.**
- **`src/L/Hierarchy.lagda.md`**, read `:43-90`, `:110-360`. **TOOK `Values`,
  `Entries`, `Domain` (`:112-124`), `step-Lset` (`:165-215`), `approx-val`
  (`:268-300`) and `Lset-only` (`:333-355`). The generic module is those four
  with two axes abstracted. NOT edited.**
- **`src/L/Coding/Sequence.lagda.md`**, read `:40-360`. TOOK `StepAt`
  (`:155-163`), `StepOf` and `PowOK` (`:158-163`), `StepAt-out`, `StepAt-back`,
  `StepAt-in` (`:217-232`), and `RecShape` with `ApproxAt`, its three
  projections and `Graph-out` (`:281-340`). **Those nine are the residue's
  types, verbatim.**
- `src/L/Coding/Model.lagda.md`, read `:32-80`, `:120-135`, `:155-200`,
  `:265-320`, `:655-700`. TOOK `prAtL` (`:122-128`), `appAt` (`:160-166`),
  `inDomAt` (`:269-275`), `domAt` (`:278`), `extAt` (`:662`) and the header
  (`:70-73`) that fixes them at `𝒮ʟ`. **Section 5.2 counts them.**
- `src/L/Coding/Powerset.lagda.md`, read `:41-95`, `:130-230`, `:290-360`,
  `:440-445`, `:640-730`. TOOK `envOneAt` (`:126-132`), `DefinesAt` (`:217-221`),
  `DefAt` (`:442-443`), `DefAt-in`/`DefAt-out` (`:645-670`) and `DefAt-stage`
  (`:720-727`). **Section 5.3 refuses to price them.**
- **`src/L/BoundedSubset.lagda.md`**, read `:55-160`, `:780-880`, `:895-1035`.
  TOOK `LevelHood` (`:74-146`), `isOrdAt` and `Amb` (`:790-821`), `erase-Δ₀`
  (`:825`), `LevelHood0` (`:840-870`) and **`HullStage.Condense` with `πX⊆Lβ`
  (`:997-1008`), which is T8's measurement.** **NOT edited.**
- `src/L/Condensation.lagda.md`, read `:240-300`, `:340-460`. TOOK `Σ₁-cert`
  (`:266-270`), **`EraseTransfer` with `σL-transfer` (`:341-405`)**, and
  `ride-only`/`ride-defines` (`:415-428`). **NOT edited.**
- `src/FOL/Absoluteness.lagda.md`, read whole. TOOK `Single` (`:57-80`), the two
  semantics (`:75-79`), `abs₀` (`:122`), `σ₁-up` and `π₁-down` (`:182-188`).
- `src/FOL/Semantics.lagda.md`, read `:45-100`. TOOK `_^_` (`:50-51`) and
  `At` with `_⊨_` (`:71-100`).
- `src/FOL/Manipulation/Relabelling.lagda.md`, read `:138-215`. TOOK `⊨-map`
  (`:154-155`) and **`embed-⊨` (`:184-186`), which is `free`'s whole content.**
- `src/FOL/ZFStructure.lagda.md`, read `:84-150`. TOOK `Transitive` (`:116-118`)
  and `_↾_` (`:141-150`).
- `src/L/Axioms/Basic.lagda.md:160` and `:230`. TOOK `LsetS` and `isL-𝒟ₒ`, the
  class instance's two closure facts.
- `src/L/Constructible.lagda.md`, read `:135-145`, `:210-220`, `:310-345`,
  `:375-412`. TOOK `IsOrd` (`:141`), `𝒟ₒ` (`:212`), `Lset-in` (`:319`),
  `Lset-out` (`:336`), `isL` (`:376`), `isL-trans` (`:379`).
- **`archive/src/2026-08-09-rud-route/`: NOT read.** T3 located the archived
  content in `archive/dev/`, and `dev/ARCHIVE.md:146` records that the code was
  deleted in place rather than moved to a file, so the records ARE the archive
  here. **I say so rather than claim a survey I did not run.**
- **`dev/LESSONS.md`**: C-12, C-22, C-36, C-38, C-40, C-42, D-1, D-10, I-5,
  P-h, P-i, P-k, P-l, P-m, P-n, R-35, R-38, R-40 loaded through
  `scripts/rules.py --for probe` and `--for build`.
- `dev/PLAN.md`: DD0, DD4, DD8, DD23, DD24 through the brief.

## 9. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-120` and `:368-396`.**

**The brief's two questions, answered directly.**

> **Say at which carrier Devlin states (a).**

**At the AMBIENT carrier.** `:93-96` states
`(a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]` with `Φ` a Σ₀ formula, and the quantifiers
range over the real universe. **`:95-96` states (b) beside it as the LOCALIZED
form**, `v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ`. **Our delivered `Lset-only` is (b) at
the class carrier. Our chain needs (a).** This confirms `[LJ-1.178]` section
3.1 and I add nothing to it.

> **Say whether his argument needs the ambient form at all.**

**YES, and it needs it exactly once.** `:102-106` gives the chain: "1.9.15
converts M's satisfaction of the Σ₀ matrix into **ambient** Φ; (a) turns Φ into
`v = L_γ`". **The step BEFORE (a) lands in the ambient universe, so (b) cannot
be applied there.** **MEASURED, by reading `:100-112` whole.**

**This is the literature's own answer to the road question in section 2**, and
it agrees with the measurement: the collapse image is not known to sit inside
`L`, so the reading must happen where the image already is.

`:374-382`, the per-step DD4 table. **TOOK row C1 (level-hood formula,
PER-TOWER), rows C3 and C4 (absoluteness and transfer, EITHER TOWER).** Section
6.2 stands on C3 and C4.

`dev/literature/devlin-errata.md`: **NOT read.** `[LJ-1.136]` measured that the
errata touch no part of II.5.

`dev/literature/j-hierarchy.md`: **NOT read.** The build is generic in the
tower, so the J tower's own stage operation plugs in without its digest.

`_build/literature/dev2.txt`: **NOT opened.** Every citation runs through the
digest.

## 10. THE RULES, ANSWERED

- **C-36.** The term is SUPPLIED, so the rule's other half applies: **section
  5.2 writes the terms I could NOT write**, at their delivered `file:line`, and
  section 5.3 refuses their price.
- **C-38 as extended.** `amb` is **DISCHARGED**, because `clause-a` SUPPLIES it.
  `sl`, `sc` and `s₁` are untouched and I say so.
- **C-42.** The refutation of `[LJ-1.178]`'s NO-GO condition measures ONE site:
  the read-off stack of `src/L/Hierarchy.lagda.md`. **I did NOT sweep the tree
  for other carrier-fixed read-offs.** T9 counted twelve `Single` sites at named
  classes and that count is the sweep's first step, not the sweep.
- **P-k.** `amb` is stated where its consumer uses it: at
  `AmbientCross.AmbientRead`'s verbatim type, checked by probe B against
  `[LJ-1.178]`'s own module and by probe C against the real site. **`Types`
  (`ProbeLJ1184B.agda:56-100`) exists for the same reason:** the consumer must
  name the six readings without re-typing a rank-2 telescope.
- **P-l.** Sections 5.3 and 5.4. **I give the ambient `DefAt` reading no figure
  anchored on the class-carrier masters**, and I mark section 5.4's expectation
  INFERRED.
- **P-h.** The definability walk stays module-parameterized: the tower, the
  carrier, the satisfaction and the step are parameters, and no body names a
  concrete formula or a concrete class.
- **P-m, P-n.** Section 5.2 classes the residue as description-reading content
  and does not price the expensive member of it.
- **C-39, C-40.** Section 0.2 leads with what my own figures do NOT cover.
- **C-12.** One agda process, `-M8g`, cap never raised, load beside every
  figure.
- **C-22.** This file existed as a skeleton before the first probe ran, and
  section 1 was written before the first line of Agda.
- **D-1.** All three probes are in `agents/tasks/LJ-1-184/`, all three ran while
  the task was live, all three are tracked. The abort criterion was the brief's,
  fixed in advance, and section 5.4 fixes the next one.
- **D-10.** The recorded residue was `AmbientRead`. I priced its truth before
  its proof: it is Devlin's own (a), it is true, and section 9 places it.
- **D-26.** Section 6.2 uses the digest's per-step carrier column.
- **D-29, D-30.** Probe C prices what the CONSUMER needs, at the consumer's own
  site entry. The reduction is reported and NOT banked as a saving.
- **DD8.** One best-effort figure per term, each with its basis: section 5.2's
  84 lines are a COUNT of delivered blocks, section 6.3's 6 lines are a COUNT of
  two states of one file. **Section 5.3 refuses a figure and says why.**
- **DD23.** No mathematical prose was written. All three probes carry comments
  only.
- **DD24.** Section 4 reports the seconds and the lines and judges nothing.
- **DD4.** Section 6.
- **I-5.** No `PT.rec` or `PT.map` branch was left to inference: every branch in
  the generic module carries a named `where` function with a written type,
  inherited from the delivered proofs.

**A candidate law, offered with its measurement and NOT numbered** (the
orchestrator assigns IDs): **a class-valued hypothesis whose type does not
mention its own implicit arguments cannot be passed to a module by name.** Agda
inserts metas for the implicits and no constraint can solve them, because the
remaining type is constant in them. **The cure is one eta-expansion at the
application site.** **MEASURED at two sites**, `ProbeLJ1184A.agda:328` and a
minimal reproduction, at about ten minutes. It fires whenever a class is
"everything", which is exactly the ambient instantiation this route now needs
repeatedly.

## 11. PROHIBITIONS, ANSWERED

**No master edited.** `src/Everything.lagda.md` not opened. Every `src/` file in
section 8 was READ ONLY. No commit, no push, no `git checkout`, `stash`, `reset`
or `clean`. No `make check`.

**My only files are** `agents/tasks/LJ-1-184/lj-1.184-report.md`,
`ProbeLJ1184A.agda`, `ProbeLJ1184B.agda` and `ProbeLJ1184C.agda`. **All three
probes are tracked, they sit beside the report, and they are never deleted.**

**One `_build/` note.** A minimal reproduction file left an interface at
`_build/2.8.0/agda/agents/tasks/LJ-1-184/T.agdai`. **I deleted it**, and no
undeclared file remains under `_build/` from this task.
