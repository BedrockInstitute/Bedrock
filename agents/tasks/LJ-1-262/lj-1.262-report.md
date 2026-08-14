# LJ-1.262 report: the DD25 review of `[LJ-1.225]`

tier: opus (deepseek-subagent-mode), the switch's ADVERSARIAL row. The target
was written by pi, so DD17's invariant holds. No Agda ran. No slot held. No
master, brief or report edited. No commit, no push. Written incrementally
(C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. VERDICT

**UPHELD BUT MISATTRIBUTED.**

**The NO is correct on every number it gives.** I re-derived all six readings,
the pin, the line count, the body end and the two scope lists. Not one figure
is wrong. `[LJ-1.238]` ported the module the target named, so the headline is
also confirmed by construction.

**Three carried claims are false, and one is the target's own error rather than
an inherited one.**

| carried claim | class | killed by |
|---|---|---|
| `amb` is SUPPLIED | **MEASURED FALSE** | `[LJ-1.242]`, `[LJ-1.243]`, `[LJ-1.250]:18` |
| the six readings are Devlin's PER-TOWER content | **MEASURED FALSE on the L-vs-ambient axis** | `[LJ-1.238]:132-138` |
| the port unblocks nothing for `[LJ-1.7]` | **MEASURED FALSE** | `[LJ-1.249]`, `ProbeLJ1249.agda:59`, `:154` |

**The misattribution is the second row.** The target used a Def-vs-J mark to
raise a doubt about an L-vs-ambient figure. Section 7 resolves that axis error.

## 1. QUESTION 1: IS THE NO CORRECT ON ITS OWN NUMBERS? YES

I re-derived every number in the target. All hold. MEASURED, by reading the
source.

| target claim | at | re-derived | class |
|---|---|---|---|
| `StepAt-out` at `:217` | `lj-1.225-report.md:40` | `Sequence.lagda.md:217` | **TRUE** |
| `StepAt-back` at `:221` | `:41` | `Sequence.lagda.md:221` | **TRUE** |
| `ApproxAt-dom` at `:295` | `:41` | `Sequence.lagda.md:295` | **TRUE** |
| `ApproxAt-value` at `:298` | `:41` | `Sequence.lagda.md:298` | **TRUE** |
| `ApproxAt-step` at `:303` | `:42` | `Sequence.lagda.md:303` | **TRUE** |
| `Graph-out` at `:325` | `:42` | `Sequence.lagda.md:325` | **TRUE** |
| the module pins `𝒮ʟ` at `:59` | `:47` | `Sequence.lagda.md:59` | **TRUE, and under-named. Section 1.1** |
| 157 non-blank in-fence lines | `:63` | `[LJ-1.238]:57` measured 157 independently | **TRUE** |
| the green body ends at `DefAt-out` `:566` | `:45` | `LJ-1-220/Probe.agda:566` | **TRUE** |
| Sequence is in neither scope list | `:48` | zero hits for `Sequence` in either report | **TRUE** |

**THE MISMATCH TEST THE BRIEF ASKED FOR RETURNS NOTHING.** `[LJ-1.238]` ported
the module the target named, and it delivered all six readings.
`lj-1.238-report.md:122-125` names the same six. No reading the target named is
missing from the port, and the port added no reading the target failed to name.
MEASURED.

### 1.1 One defect: the pin the target named carries no mathematics

The target names ONE pin site. The module has **three**. MEASURED:

- `Sequence.lagda.md:48`, `open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )`;
- `Sequence.lagda.md:59`, `open hPropStructure 𝒮ʟ`, the site the target named;
- `Sequence.lagda.md:61`, `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`.

**The two lines the port actually had to change are neither of these.**
`lj-1.238-report.md:74-77` gives them: `Sequence.lagda.md:105`
(`⟨ isL (𝒟ₒ (fst w)) ⟩` becomes `⟨ M (𝒟ₒ (fst w)) ⟩`) and
`Sequence.lagda.md:181-182` (`isL-trans` becomes `M-trans`). Those two
substitutions are, in `[LJ-1.238]`'s words, "the whole mathematical content of
the port" (`lj-1.238-report.md:71`).

So `:59` is header plumbing that the port replaced wholesale inside its 38
header lines. The claim is true. It points at the cheapest site rather than at
the two lines that carry the tower. **This is the D-10 and C-42 shape: one site
named as THE site.** MEASURED.

### 1.2 One tag is wrong, and the orchestrator caught it one dispatch later

`lj-1.225-report.md:63-65` reads: "`Sequence.lagda.md` holds 157 non-blank
in-fence lines. It pins `𝒮ʟ` at `:59`. **Its port is small and mechanical.** It
is not in the port's scope. MEASURED."

**Three of those four sentences were measurable. The third was not.** No port
existed on 2026-08-14, so "small and mechanical" was INFERRED and the
paragraph-level MEASURED tag over-claims it. MEASURED.

The orchestrator caught this without a DD25 review. `LJ-1.238.md:24` reads
"That phrase is INFERRED. Measure it." `[LJ-1.238]` then measured it TRUE at 40
written lines (`lj-1.238-report.md:153`). **The defect was real, the catch was
one dispatch later, and the cost was zero.**

## 2. QUESTION 2: DID IT REACH TOO FAR? YES, AND THE ERROR IS BOTH

**The premise was INHERITED. The error was the target's OWN.** I can separate
them at `file:line`.

### 2.1 The premise was inherited. MEASURED

At the commit that was HEAD when `[LJ-1.225]` ran, `45cf287`, `dev/PLAN.md:49`
read "`AmbientRead` is **SUPPLIED** (`[LJ-1.184]`), closing one of four
hypotheses." It carried no qualifier. **The token `q` did not occur anywhere in
`dev/PLAN.md` at that commit.** MEASURED.

`[LJ-1.184]`'s report never names `q` either. **Zero occurrences as a token**,
across the whole file. MEASURED, by search. Its section 0.2
(`lj-1.184-report.md:22-30`) declares a residue unprompted, names SIX
parameters of its own module telescope, and omits the seventh.

**So nothing in the record told the target that the supply was conditional.**

### 2.2 The error was the target's own. MEASURED

`lj-1.225-report.md:164` reads: "C-38 as extended. `amb` is discharged because
`[LJ-1.184]` supplies it."

**C-38's action forbids exactly that move.** `dev/LESSONS.md:3454-3456`: "When a
return says hypotheses are discharged, do not audit the parameter count. **Audit
the instantiation.** If none exists, the correct word is 'restated'."

The target audited neither. It cited `ProbeLJ1184B.agda:155` as the supply.
That line reads `module W = Sx.Whole el fwd bwd sl sc s₁ (amb P Ptr)`. It sits
inside `module AmbientStep`, which opens at `ProbeLJ1184B.agda:101`. That
module's telescope carries, at `ProbeLJ1184B.agda:112`:

```agda
  (q : Graph {2} zero (suc zero) ≡ embed φ₀)
```

`q` is undischarged. `amb` (`ProbeLJ1184B.agda:128-129`) reduces to `go`, and
`go` spends `q` at `ProbeLJ1184B.agda:122`. **`[LJ-1.243]` then measured that
nothing in the repository instantiates that telescope**
(`dev/LESSONS.md:3940`).

**So under C-38 as it stood on 2026-08-14, the correct word for `amb` was
"restated", not SUPPLIED.** MEASURED.

### 2.3 The catch cost one screen of a file the target already had open

`lj-1.225-report.md:120-121` records what the target read:
"`agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read. TOOK 'THE RESIDUE' at
`:44-52` and the `amb` supply at `:155`."

**`q` is at `:112`. It lies between the two lines the target took, in the header
of the module its cited line sits inside.** MEASURED.

The target read the module's own comment block at `:44-52`, which says "Nothing
else is open" (`ProbeLJ1184B.agda:52`), and trusted it instead of the telescope
at `:101-113`. **That comment is false, and it is the same self-description
`[LJ-1.184]`'s section 0.2 wrote.**

### 2.4 What the target could NOT have known

**C-45 did not exist.** `dev/LESSONS.md:3915` is dated 2026-08-15, one day after
the target ran, and `[LJ-1.243]` earned it. C-45 is the law that names this
exact shape: an equation parameter with independent terms on both sides, which
`refl` cannot close.

**So the target lacked the sharpened law. It did not lack C-38**, which its
brief handed it by name and which it cited in its own rules section.

### 2.5 The apportionment

| party | what it owns | class |
|---|---|---|
| `[LJ-1.184]` | the origin. Declared six of seven parameters | **MEASURED**, `lj-1.184-report.md:22-30` |
| `dev/PLAN.md:49` | carried it unqualified to the brief | **MEASURED**, `45cf287` |
| `[LJ-1.225]` | cited C-38 and did not perform C-38's audit | **MEASURED**, `lj-1.225-report.md:164` |

`[LJ-1.243]:697-699` reaches the same split independently: "`[LJ-1.184]` is the
origin. `[LJ-1.225]` propagated it."

**My addition to that finding is section 2.2.** `[LJ-1.243]` records the target
as a propagator. **The target was more than a propagator: it invoked the law
that would have stopped the propagation, and then did not apply it.**

## 3. QUESTION 3: DID IT REACH TOO LITTLE? YES, ON ONE SENTENCE

`lj-1.225-report.md:95` reads: "It unblocks nothing for `[LJ-1.7]`."

**MEASURED FALSE.** `[LJ-1.249]`'s green probe consumes the port directly:

- `ProbeLJ1249.agda:48`, `import LJ-1-238.GenSequence`;
- `ProbeLJ1249.agda:59`, `module GS = LJ-1-238.GenSequence {ℓ} lem M M-trans`;
- `ProbeLJ1249.agda:154`, `module Seq = GS.Body DefAt DefAt-in DefAt-out`;
- exit 0 (`lj-1.249-report.md:13-14`).

So the port is a live dependency of a green probe one layer above it. The
target under-stated what the port buys.

**Its two reasons split.** Reason one, "it stops one module short", was cured by
`[LJ-1.238]`. Reason two, "`sl` and `sc` stay open whatever the port does",
still holds: `dev/PLAN.md:798` records both as standing over `lh` as a
parameter. MEASURED.

**But its refusal to call the port a cure SURVIVES, and two later dispatches
confirm it.** `[LJ-1.250]:9-10` measured `StepAgree` and `ApproxAgree` as
"UNCONSTRAINED interfaces, not theorems", with 0 written proof lines.
`[LJ-1.251]:118-122` then measured `[LJ-1.249]`'s own sentence "the chapter does
NOT exist" as FALSE, and stated the reason as C-45: "the port is a placement and
not a discharge."

**So the target under-stated the port's LEVERAGE and stated its LIMIT
correctly.** The sentence "land it as DD4, call it DD4, and do not call it a
cure" (`lj-1.225-report.md:96-97`) is the one sentence in the report that the
next seven dispatches did not dent. INFERRED for "did not dent", from the
`[LJ-1.250]` and `[LJ-1.251]` verdicts.

## 4. QUESTION 4: DID THE BRIEF CAUSE IT? PARTLY, AND C-39 DOES NOT EXCUSE IT

**The brief handed the target the defect. MEASURED.** `LJ-1.225.md:14-21`
quotes `dev/PLAN.md:49` verbatim, including "`AmbientRead` is SUPPLIED".
`LJ-1.225.md:124-126` then says: "Read what SUPPLIED meant there; **it is your
template.**" That instruction tells the agent to copy a status, not to audit it.

**The brief also handed the target the door, in the same file. MEASURED.**
`LJ-1.225.md:76-78` reads: "**THE RESIDUE IS NOT WHAT `dev/PLAN.md:49` SAYS.**
If the record is stale or wrong, **say so with the evidence.**"

**And the brief ASKED for the audit that would have caught it.**
`LJ-1.225.md:41-45` states question 1 as: "Say which are BUILT, which are
SUPPLIED, and which are neither. **A hypothesis is discharged when something
SUPPLIES it** (C-38 as extended)."

**So C-39 does not apply here.** C-39 measures a PROHIBITION that blocks a
legitimate move (`dev/LESSONS.md:3539-3544`). **This brief carried no
prohibition on the point. It carried a false premise, an explicit licence to
refute it, and a request for the exact audit.** MEASURED, at the three line
ranges above.

**The apportionment, INFERRED.** The orchestrator owns the false premise and
the word "template". The target owns the unperformed audit. **The brief lowered
the odds of the catch. It did not remove them.**

## 5. WHY THE REVIEW IS LATE. ONE LINE

**DD25's only enforcement point is the index row, the row is written when the
return lands, and the checker reads that row and nothing else, so the lapse was
invisible until an unrelated full gate ran.** `dev/PLAN.md:266` says so in the
ruling itself ("No machine enforces the trigger today"), and
`scripts/check-dd25-review-named.py:48-51` says so in the tool ("It cannot fire
at the moment the return lands, which is when the orchestrator forgets").

### 5.1 C-44: two figures in THIS brief do not reproduce from the record

The brief instructs me to treat what I cannot find as unproven. Two figures
fail. **Both are about the lapse itself, not about the mathematics.**

**"nineteen dispatches late" does not reproduce. MEASURED.** I counted the index
rows between `dev/PLAN.md:786` (`LJ-1.225`) and `dev/PLAN.md:820`
(`LJ-1.262`) with the checker's own row regex:

| reading | count |
|---|---:|
| codes strictly between | 36 |
| non-review codes strictly between | 29 |
| commits since `46b6197` | 50 |
| negative-verdict rows strictly between | 7 |
| unreviewed negatives strictly between | 4 |

**No reading gives 19.**

**"eleven negatives DID get their reviews" does not reproduce. MEASURED.** The
index holds **SEVEN** DD25 review rows strictly between the two codes:
`dev/PLAN.md:788`, `:794`, `:801`, `:804`, `:806`, `:809`, `:814`. Seven
negative-verdict rows sit in the same window. **The correspondence is seven to
seven, not eleven.**

**The SUBSTANCE of both claims holds.** Other negatives did get their reviews,
this one did not, and the gap is real and large. **Only the two numbers fail.**
I report them because the brief that exists to correct a record-keeping lapse
carries two unchecked figures about that same record. **That is DD8's rule
applied to the orchestrator's own prose: one number, and it names its basis.**

## 6. DD4: DOES THE DD4 HALF SURVIVE ITS THREE LATER TESTS? YES

`lj-1.225-report.md:93-99` says the port is worth landing on DD4 alone, takes
`[LJ-1.223]`'s 2,971 shared and 0 residual without re-pricing them, and adds one
doubt.

| test | result | class |
|---|---|---|
| `[LJ-1.238]`, Sequence residual | 145 verbatim, 40 written, residual **0** | **SURVIVES and extends one module higher** |
| `[LJ-1.249]`, the assembly | carrier-generic, paid once, exit 0 | **SURVIVES** |
| the C2 doubt the target raised | **REFUTED** | section 7 |

**The DD4 verdict survives all three. The only claim the three tests killed is
the doubt the target raised AGAINST DD4**, not the DD4 judgement itself.

`lj-1.225-report.md:97-99` reads: "the C2 row marks the coding per-tower, which
bears on the word 'shared'. That is `[LJ-1.223]`'s claim to defend. I do not
re-price it."

**That doubt was unfounded, and section 7 says why.** The target was right to
refuse to re-price a figure it had not measured. **It was wrong to attach a
doubt to that figure from a mark on a different axis.** MEASURED.

## 7. LITERATURE: THE CONTRADICTION IS NOT ONE. IT IS TWO AXES

The brief asks me to resolve an apparent contradiction. **There is none. The two
statements are about two different axes, and neither touches the other.**

**Devlin's axis is Def tower against J tower.**
`dev/literature/devlin-II5.md:375` marks the C2 row PER-TOWER, and its D-26
carrier column reads: "Def: satisfaction bound K(u) or its coding analogue; J:
the sixteen op-graphs, syntax-free". The verdict at
`dev/literature/devlin-II5.md:387-389` fixes the same axis: "The per-tower
content is exactly two objects: the level-hood certificate (Step C) and the
definable well-order (Steps D, G)."

**`[LJ-1.238]`'s axis is L against the ambient class.** Its zero measures
genericity in the class parameter `M`, that is, L against `Full`.

**A coding can be generic in `M` and still have no J analogue**, because J
replaces satisfaction coding with op-graphs. So "PER-TOWER on the Def-vs-J axis"
and "residual zero on the L-vs-ambient axis" are consistent. Both are true.

**`[LJ-1.238]` states this itself and marks the second axis INFERRED**
(`lj-1.238-report.md:140-146`): "A residual of zero against `Full` does not say
the six readings transfer to J unchanged." `[LJ-1.249]:91-94` carries the same
caveat forward.

**So the target's error is not a misreading of Devlin.** Its reading of the C2
row is faithful. **Its error is that it applied a Def-vs-J mark to an
L-vs-ambient figure**, at `lj-1.225-report.md:97-99` and at `:106`, where it
classified "the environment lift is tower-neutral" as MEASURED FALSE on the
strength of `devlin-II5.md:375`. **That row is the misattribution in the
verdict word.** MEASURED.

**One point in the target's favour, and it is real.** The target wrote at
`lj-1.225-report.md:85` that the port "prices the coding substrate, the 'coding
analogue' of C2". **`[LJ-1.238]:200-204` reaches the same placement**, and
assigns C2's PER-TOWER mark to the "bound inside carrier" half, which is
`DefAt-stage` one module below. **So the target located the object correctly and
mislabelled its axis.**

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the target's six line numbers are wrong | **MEASURED FALSE.** All six re-derived, section 1 |
| the target's `:59` pin is wrong | **MEASURED FALSE.** The line reads `open hPropStructure 𝒮ʟ` |
| `:59` is the pin the port had to break | **MEASURED FALSE.** The two mathematical sites are `:105` and `:181-182`, section 1.1 |
| the module has one L-pinning site | **MEASURED FALSE.** Three, at `:48`, `:59`, `:61` |
| `[LJ-1.238]` built something the target failed to name | **MEASURED FALSE.** The six match exactly |
| "small and mechanical" was MEASURED | **MEASURED FALSE.** No port existed, section 1.2 |
| `amb` was SUPPLIED | **MEASURED FALSE.** `q` at `ProbeLJ1184B.agda:112`, undischarged |
| the `amb` error was purely inherited | **MEASURED FALSE.** The target cited C-38 and skipped its audit, section 2.2 |
| the record warned the target about `q` | **MEASURED FALSE.** Zero `q` tokens in `dev/PLAN.md` at `45cf287` and in `lj-1.184-report.md` |
| C-45 existed when the target ran | **MEASURED FALSE.** `dev/LESSONS.md:3915` is dated 2026-08-15 |
| the port unblocks nothing for `[LJ-1.7]` | **MEASURED FALSE.** `ProbeLJ1249.agda:59`, `:154`, exit 0 |
| the port is a cure | **MEASURED FALSE.** `[LJ-1.250]:9-10`, `[LJ-1.251]:118-122`. The target said so first |
| the brief prohibited the contradiction | **MEASURED FALSE.** `LJ-1.225.md:76-78` licensed it, section 4 |
| C-39 excuses the target | **MEASURED FALSE.** No prohibition existed on the point |
| Devlin's C2 mark contradicts `[LJ-1.238]`'s zero | **MEASURED FALSE.** Two axes, section 7 |
| the DD4 half fails a later test | **MEASURED FALSE.** It survives all three, section 6 |
| "nineteen dispatches late" reproduces | **MEASURED FALSE.** No reading gives 19, section 5.1 |
| "eleven negatives got their reviews" reproduces | **MEASURED FALSE.** Seven, section 5.1 |
| `sl` and `sc` were closed by the port | **MEASURED FALSE.** `dev/PLAN.md:798` |
| the J axis was measured by any dispatch in this chain | **INFERRED FALSE.** No `src/J/` exists; `lj-1.238-report.md:146` |

## 9. ARCHIVE USED (DD18)

One line read named per file.

- `agents/tasks/LJ-1-225/lj-1.225-report.md`, read WHOLE, FIRST. **Line read
  `:26`**, the `amb` SUPPLIED row. **This is the target.**
- `agents/tasks/LJ-1-238/lj-1.238-report.md`, read WHOLE. **Line read `:71`**,
  "The 2 substitutions are the whole mathematical content of the port."
- `agents/tasks/LJ-1-238/GenSequence.agda`: NOT opened. I took its content
  through `[LJ-1.238]`'s own measurement and through `ProbeLJ1249.agda:48`,
  `:59`, `:154`, which apply it. **I say so rather than claim a read.**
- `agents/tasks/LJ-1-242/lj-1.242-report.md`, read at `:1-60` and `:220-240`.
  **Line read `:230`**, "`amb` holds at the real `φ₀` by `[LJ-1.184]`'s supply |
  MEASURED FALSE."
- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read at `:580-620` and
  `:680-700`. **Line read `:697-699`**, "`[LJ-1.184]` is the origin.
  `[LJ-1.225]` propagated it."
- `agents/tasks/LJ-1-249/lj-1.249-report.md`, read WHOLE. **Line read `:91-94`**,
  the L-vs-J caveat carried from `[LJ-1.238]`.
- `agents/tasks/LJ-1-249/ProbeLJ1249.agda`, read the header. **Line read `:59`**,
  `module GS = LJ-1-238.GenSequence {ℓ} lem M M-trans`.
- `agents/tasks/LJ-1-250/lj-1.250-report.md`, read `:1-20`. **Line read `:18`**,
  "`amb` is NOT supplied outright."
- `agents/tasks/LJ-1-251/lj-1.251-report.md`, read `:115-130`. **Line read
  `:122`**, `[LJ-1.249]`'s chapter sentence marked MEASURED FALSE.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read `:40-60` and `:101-160`.
  **Line read `:112`**, `(q : Graph {2} zero (suc zero) ≡ embed φ₀)`.
- `agents/tasks/LJ-1-184/lj-1.184-report.md`, read for the `q` search. **Line
  read `:22-30`**, section 0.2, which names six parameters and omits the seventh.
- `agents/tasks/LJ-1-225/LJ-1.225.md`, read for question 4. **Line read
  `:124-126`**, "Read what SUPPLIED meant there; it is your template."
- `agents/tasks/LJ-1-238/LJ-1.238.md`, read for section 1.2. **Line read `:24`**,
  "That phrase is INFERRED. Measure it."
- `agents/tasks/LJ-1-220/Probe.agda`, read `:560-570`. **Line read `:566`**,
  `DefAt-out`, the body end the target named.
- `src/L/Coding/Sequence.lagda.md`, read `:44-64`, `:210-232`, `:290-360`.
  **Line read `:59`**, `open hPropStructure 𝒮ʟ`, the pin under review.
- `dev/PLAN.md` at `45cf287`, read `:36-70`. **Line read `:49`**, the
  `[LJ-1.7]` row as the brief quoted it.
- **`archive/dev/TASKS-archived.md`, read for SHAPE only. Line read `:217`**,
  `L3.32-T194`: "RED: the frame re-instantiates at 62, but the family equality
  rests on a FALSE bridge". **SHAPE TAKEN, no figure.** The retired route
  already produced a green re-instantiation resting on a false equality. **That
  is the `q` shape, one route earlier**, and it is why C-45's provenance names
  the archive too (`dev/LESSONS.md:3955-3959`).

## 10. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:365-395`, read WHOLE. **TOOK** the C1 row
  `:374`, the C2 row `:375` with its D-26 carrier column, and the verdict
  `:387-389`. **USED** in section 7 to fix Devlin's axis as Def against J.
- `dev/literature/devlin-II5.md:375`, the C2 Def cell, "satisfaction bound K(u)
  or its coding analogue", and the J cell, "the sixteen op-graphs, syntax-free".
  **USED** as the direct evidence that the mark is an axis and not a property.
- **WHY NOT.** I did not use `devlin-II5.md:301-303`, which the target cited for
  completeness. It concerns the level-hood formula's presentation, not the
  coding, so it does not bear on the axis question. I did not open Devlin's
  Steps D and G material, because the well-order is not in this chain: the
  target established at `lj-1.225-report.md:89` that both parts of `[LJ-1.7]`'s
  residue are the level-hood certificate, and `[LJ-1.238]` and `[LJ-1.249]` did
  not disturb that.

## 11. RULES ANSWERED

- **C-38 as extended.** Section 2.2 is this rule applied to the target. The
  target cited C-38 and reached the conclusion C-38 forbids.
- **C-45.** Section 2.4 records that it did not exist when the target ran. I do
  not charge the target with a law written after it.
- **C-43.** The brief refused the "DD25 review not needed" hatch. The refusal
  was correct: section 1.2, 2.2, 3 and 5.1 each found something a hatch would
  have hidden.
- **C-44.** Section 5.1. Two figures in this brief do not reproduce, and I say
  so rather than repeat them.
- **C-42.** I measured ONE site, `[LJ-1.225]`. I did not sweep for other reports
  that carried `amb` SUPPLIED. `[LJ-1.243]:596` reports six further probe
  modules with the same shape. **That extent is its measurement, not mine.**
- **D-10.** Section 1.1 prices the truth of the pin the target recorded before
  pricing anything built on it.
- **C-39.** Section 4 finds it does NOT apply, and gives the line that licensed
  the contradiction.
- **C-36.** I did not treat any failed reading as an impossibility. Section 7
  resolves the apparent contradiction rather than declaring one side wrong.
- **C-22.** This report existed as a skeleton before the first search closed.
- **P-l.** I transferred no figure by analogy. Every number here is re-derived
  at its own site or is quoted with its report of origin.
- **DD8.** One number per claim, each with its basis. Section 5.1 applies the
  same test to the brief.
- **DD18.** Sections 9 and 10, with a WHY NOT.
- **DD25.** This is the review. The verdict word is in section 0.
- **DD4.** Section 6.
- **I-5, C-12.** No Agda ran. No probe written. No slot held.
