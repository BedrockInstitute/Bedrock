# LJ-1.297 report: the DD25 adversarial review of `q`'s machine refutation

tier: opus (pi-subagent-mode), the ADVERSARIAL row. The target is
`agents/tasks/LJ-1-293/`, written by pi on `glm-5.3`. The critic is not the
author. Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**HOLDS.**

`[LJ-1.293]`'s refutation of `q` is CORRECT, and it is correct about the RIGHT
OBJECT. I re-derived the term in my own module, and I re-derived its object by
APPLICATION rather than by assertion: `AmbientStep` applied at
`Graph := LsetGraphAt` and `φ₀ := P1241.φ₀` accepts my `q`, yields `amb`, and
proves `Empty` from the same `q`
(`agents/tasks/LJ-1-297/ProbeLJ1297B.agda`, exit 0). MEASURED.

**`amb` HAS A ROUTE LEFT, and it is `q'`, alone.** The return names TWO
obligations. I discharged the second one by machine:

- **`agents/tasks/LJ-1-297/ProbeLJ1297C.agda`**, exit 0, 1.56 s. The `⊨ᵐ` to
  `⊨ᵛ` transport at the FULL class, **for every formula**, with no Δ₀ and no
  Σ₁ hypothesis. 20 lines. The return called this "INFERRED small; not
  measured by anyone".
- **`agents/tasks/LJ-1-297/ProbeLJ1297D.agda`**, exit 0, 22.81 s. All SIX of
  `AmbientStep`'s readings SUPPLIED at the ambient carrier, from `[LJ-1.238]`'s
  generic sequence coding through that transport. `AmbientStep` then keeps ONE
  open hypothesis, and it is `q`.

**So the phase's residue is `q'` and nothing beside it**, modulo the Def-step
trio, which stays a hypothesis in my probes and which `[LJ-1.224]` reports
delivered at the ambient class (TAKEN from the record, not re-measured).

**Three corrections to the record, none of which moves the verdict.**

1. The return's "mean kept 2.51 s" measures an interface RELOAD, not the
   check. Section 1.
2. The `refl` carrier check is sound but weaker than it reads: it compares
   carriers, not the `Graph` slot and not the reading. Section 3.
3. `[LJ-1.244]`'s exit 42, which the return cites as the price of `q'`, was
   measured with `Graph` ABSTRACT (`ProbeLJ1244B.agda:45`). That is the
   telescope, not the instantiation, and C-45 forbids exactly that reading.
   Section 5.2.

## 1. MY OWN RUN OF THE REFUTATION TERM

I did not re-run `[LJ-1.293]`'s file. Agda keeps an interface for it
(`_build/2.8.0/agda/agents/tasks/LJ-1-293/ProbeLJ1293A.agdai`), so a re-run of
that path reloads the interface and elaborates nothing. I copied the file into
my own module instead, which forces a full re-elaboration.

`agents/tasks/LJ-1-297/ProbeLJ1297A.agda` is `ProbeLJ1293A.agda` with ONE
character sequence changed, the module name. I checked the identity with
`diff` after masking both module names, and the two files are equal.

| run | exit | seconds | what it measures |
|---|---:|---:|---|
| 1 | 0 | 4.01 | full elaboration, dependencies cached |
| 2 | 0 | 2.57 | interface reload |
| 3 | 0 | 2.56 | interface reload |
| 4 | 0 | 2.61 | interface reload |

Load at the batch: 4.46 / 5.40 / 5.52 before, 6.98 / 6.33 / 5.89 after, 3 users.
One Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No heap
exhaustion. No run near 30 minutes.

**The term re-derives. `q-false` is green on today's tree.** MEASURED.

**One correction to the target's figure, and it is small.** `[LJ-1.293]`
section 5 reports "mean kept 2.51 s over three runs" and discards its 3.42 s
"warm-up". The discarded run is the only one that elaborated the file; the
three kept runs reload an interface. So 2.51 s is the RELOAD cost, not the
cost of the check. My figures repeat the pattern (4.01 s against 2.56 s to
2.61 s). The report does not lean on the number, and says so at
`lj-1.293-report.md:180`, "These seconds decide nothing; the term decides".
So this corrects a label, not a conclusion.

## 2. IS `IntendedQ` `q` AT THE INTENDED INSTANTIATION?

**YES, and I made the elaborator say so instead of taking the report's word.**

`agents/tasks/LJ-1-297/ProbeLJ1297B.agda`, exit 0, 40.32 s for the
elaboration and 2.71 s for a reload. Load 5.44 / 5.78 / 5.75, 3 users. One
process, same cap.

The probe does four things that the target does not.

1. **The ascription.** `Graph*` is declared at `AmbientStep`'s verbatim
   `Graph` type from `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:104`, and it is
   defined as `R.Seq.LsetGraphAt` (`ProbeLJ1297B.agda:78-80`). The elaborator
   accepts it. So the sequence coding's graph formula CAN occupy the `Graph`
   slot.
2. **The application.** `module AS = P184B.AmbientStep Step Approx Graph* ...
   P1241.φ₀ q` (`ProbeLJ1297B.agda:93-95`). This is the real module, applied
   at the intended `Graph` and the intended `φ₀`, so the `q` slot's type is
   computed by Agda from `ProbeLJ1184B.agda:112` and not restated by me.
3. **`amb` comes out.** `ambHere = AS.amb` (`ProbeLJ1297B.agda:99`). The
   telescope I refuted is the one that supplies `amb`, not an adjacent one.
4. **The same `q` proves `Empty`.** `dead = R.q-false q`
   (`ProbeLJ1297B.agda:102-103`), where `R.q-false` is `[LJ-1.293]`'s own
   term. My `q` is `AmbientStep`'s `q` because step 2 accepted it in that
   slot.

**So the object is right.** `q` at `Graph := LsetGraphAt`, `φ₀ := P1241.φ₀` is
`IntendedQ`, and `AmbientStep`'s telescope at that instantiation is
INCONSISTENT. Every reading and the whole Def-step trio stay hypotheses in my
probe, so the result does not depend on any of them. MEASURED.

The shape check behind the reading agrees. `Graph-out`'s type at
`ProbeLJ1184B.agda:94-99` asks for `∃ f, Approx zero (suc b) ∧ Step (suc w)
(suc b) zero`, and `GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w)
(suc b) zero)` at `agents/tasks/LJ-1-238/GenSequence.agda:167`, renamed to
`LsetGraphAt` at `:224`. The two match term for term. So `Graph :=
LsetGraphAt` is not one reading among many; it is the only formula the
`Graph-out` slot describes.

## 3. IS THE `refl` CARRIER CHECK SOUND?

**SOUND, and WEAKER THAN IT LOOKS. Both statements matter.**

**Sound.** `ambient≡ : S ≡ P184.Ambient.R.SC` at
`agents/tasks/LJ-1-293/ProbeLJ1293A.agda:82-83`. The left side is the carrier
of `𝒮ᵥ ↾ Full` for the probe's own `Full` (`:59-60`). The right side unfolds
to `SM = Σ[ x ∈ S ] (x ∈ᶜ M)` at `src/FOL/Absoluteness.lagda.md:64-65`, with
`M := Full` for probe A's own `Full` (`ProbeLJ1184A.agda:309-310`). Both
`Full`s are `λ _ → Unit* , isPropUnit*`, both are plain top-level definitions,
so the two carriers unfold to one type and `refl` closes a real definitional
equality. The C-45 failure shape, which is a `refl` that a metavariable
solved, is NOT present: `P184.Ambient` takes no class parameter
(`ProbeLJ1184A.agda:321`), so the only unknown is the level, and the level is
pinned by the left side.

**Weaker than it looks.** The check compares CARRIERS. It does not check that
`LsetGraphAt` fits the `Graph` slot, and it does not check that the ambient
READING `A.ambient` (`ProbeLJ1184A.agda:326-327`, `_⊨ᵛ_`) is the reading
`GenSequence` delivers its six readings at (`GenSequence.agda:45-46`, `_⊨ᵐ_`).
For the SYNTACTIC equation `q` the reading is irrelevant, so the gap does not
touch the refutation. Section 2 closes the first half by application. The
reading gap stays open and belongs to `q'`, in section 5.

## 4. DID THE BRIEF STEER THE OUTCOME?

**IT DID NOT STEER THE VERDICT. IT STEERED THE SCOPE, AND THAT COST THE PHASE
A MEASUREMENT.**

**The verdict was not steered. Three reasons, each at `file:line`.**

1. The prior existed before the brief. `[LJ-1.242]` section 2 records "`q` is
   unprovable. MEASURED", and `[LJ-1.243]` upheld the reading. The brief
   carried the record's own finding, so a refutation was the record's default,
   not the brief's suggestion.
2. The brief opened the opposite branch by name. `agents/tasks/LJ-1-293/LJ-1.293.md:76-78`
   reads "**`embed` OR `Graph` IS NOT WHAT ITS NAME SUGGESTS** ... Look for it
   again". That is exactly the "wrong object" exit, and it was available.
3. The verdict is a machine term, not a judgement. I re-derived it in my own
   module (section 1) and I re-derived its OBJECT by application (section 2).
   A prior cannot make `subst` close a goal.

**The scope WAS steered, and this is the real finding of question 3.** The
brief's abort criterion says "**`q` IS FALSE.** Report the countermodel at
`file:line`. STOP" (`LJ-1.293.md:72-74`). The return obeyed it:
`lj-1.293-report.md:128-129` reads "I cite the price and do not re-price it;
the abort criterion fired first". So the brief bought a clean stop and paid
for it with everything downstream of the stop.

**What the stop cost, MEASURED.** Section 5 below supplies all six of
`AmbientStep`'s readings at the ambient carrier, and it took one 20-line lemma
(`ProbeLJ1297C.agda`, 1.56 s) plus one 60-line supply (`ProbeLJ1297D.agda`,
22.81 s). Both were reachable inside the same dispatch. The stop left the
phase believing it had TWO obligations when it has ONE.

**C-39 read correctly.** C-39 says a brief's prohibition binds harder than its
goal. Here the binding instruction was the ABORT criterion, which is a
prohibition on continuing. It bound harder than the goal, exactly as C-39
predicts, and the loss was scope rather than truth.

## 5. THE PRICE OF THE `q'` ROUTE

### 5.1 First, the residue is SMALLER than the record says

`[LJ-1.293]` section 3 names TWO obligations: `q'`, and a second one, the
`⊨ᵐ` to `⊨ᵛ` transport, which it calls "a one-time step no delivered lemma
states for non-Δ₀ formulas", marked "INFERRED small; not measured by anyone".

**The second obligation is now DELIVERED. MEASURED.**
`agents/tasks/LJ-1-297/ProbeLJ1297C.agda`, exit 0, 1.56 s, load 6.47 / 5.55 /
5.58, 3 users.

```agda
absFull : ∀ {n} (φ : Formula SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)
```

**For EVERY formula, with no Δ₀ hypothesis and no Σ₁ hypothesis.** Twelve
cases, one induction, 20 lines of code. The reason it is free is the class:
at the class carrier the statement is FALSE for non-Δ₀ formulas, and at the
AMBIENT carrier the class is everything, so `fst : SM → S` is an equivalence
and the two unbounded quantifier cases are its two halves
(`ProbeLJ1297C.agda:88-97`). The delivered `abs₀`
(`src/FOL/Absoluteness.lagda.md:122-123`) is the Δ₀ version of the same
induction, so the shape was already in the tree; only the instance was
missing.

**And with it, the six readings SUPPLY at the ambient carrier. MEASURED.**
`agents/tasks/LJ-1-297/ProbeLJ1297D.agda`, exit 0, 22.81 s, load 4.12 / 4.87 /
5.30, 3 users. `[LJ-1.238]`'s generic sequence coding delivers the six
readings at `⊨ᵐ`; `absFull` moves each one to `A.ambient`
(`ProbeLJ1297D.agda:95-117`); `module Left` then applies `AmbientStep` with
every reading SUPPLIED and ONE hypothesis left, which is `q`
(`ProbeLJ1297D.agda:124-130`), and `amb` comes out.

**So `AmbientStep`'s residue at the intended instantiation is `q` ALONE**,
modulo the Def-step trio, which stays a hypothesis in my probe. I did not
re-measure the trio's ambient delivery; `[LJ-1.224]` reports it, and I take
that from the record and mark it TAKEN.

### 5.2 The price of `q'` itself

**`q'` is the BS-against-At bridge, and I confirm the return's citation.**
`φ₀` is built from `LH.levelHoodB` (`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:103`,
`base = Cnt.erase LH.levelHoodB refl`), and `levelHoodB` lives in
`src/L/BoundedSubset.lagda.md:108-109`. So `φ₀` is the BoundedSubset coding,
erased and pinned, and `LsetGraphAt` is the sequence coding. `q'` moves one to
the other at one carrier.

**One correction to the price the return inherits, and it is C-45's own law.**
`[LJ-1.293]` quotes `[LJ-1.244]`: "as a DEFINITION the goal is stuck
(`ProbeLJ1244B.agda:75`, exit 42)". **That probe keeps `Graph` ABSTRACT**, at
`agents/tasks/LJ-1-244/ProbeLJ1244B.agda:45`, where `Graph` is a module
parameter. With `Graph` abstract NOTHING can produce `⟨ ambient γ (Graph ...) ⟩`,
so the exit 42 measures the telescope and not the instantiation. C-45 says
audit the instantiation, never the telescope, and the cited measurement does
the opposite. At the intended instantiation the "in" directions EXIST:
`LsetGraph-in` (`agents/tasks/LJ-1-238/GenSequence.agda:196`, exported at
`:225`), `ApproxAt-in` (`:184`) and `StepAt-in` (`:145`). `[LJ-1.244]` section
6 names all three and rules them out because they are absent from
`AmbientStep`'s TELESCOPE, which is true and beside the point once `Graph` is
instantiated. **So exit 42 is not evidence that `q'` is hard. MEASURED, by
reading `ProbeLJ1244B.agda:45` and `:75`.** The work is still real, and the
next paragraph prices it, but the record's one machine figure against `q'`
does not carry the weight it is given.

**The delivered class-carrier analogue is bigger than the three citations
suggest.** `[LJ-1.293]` cites three regions of `src/L/Condensation.lagda.md`.
The bridge is in fact THIRTY `Agree` modules, MEASURED by
`grep -c "^module .*Agree" src/L/Condensation.lagda.md`, spanning
`:2774` to `:7319`, which is **3,871 non-blank lines inside ` ```agda `
fences** of the file's 6,718. `[LJ-1.244]`'s word "chapter" is correct and, if
anything, low.

**What the port would cost, ONE number with its basis (DD8).** The class
commitment of the delivered code is CONCENTRATED, not diffuse: one module
application per file. `src/L/Condensation.lagda.md:73-74` is
`module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`, and the whole
7,319-line file mentions `isL` twice and `𝒮ʟ` twice. `src/L/Coding/Sequence.lagda.md:61-62`
is the same shape. **Basis: a delivered comparable.** `[LJ-1.224]` section 5
measured a carrier substitution of this exact kind at 8 changed lines out of
338 non-blank, and three generic ports already exist on record (`GenModel`,
`GenGraph`, `GenSequence`, per `[LJ-1.224]:251` and `[LJ-1.238]`). **So the
port is MECHANICAL per line and its price is set by VOLUME: about 3,900 lines
of delivered bridge to re-instantiate, against 157 lines for the one coding
chapter `[LJ-1.238]` ported in one dispatch.** That is roughly 25 times the
one delivered port comparable, so it is a chapter-scale block and not a
dispatch.

**P-l, answered plainly.** Everything in the paragraph above is a HYPOTHESIS
at the ambient carrier. I measured the class commitment and the volume; I did
NOT port a single `Agree` module, so the conversion rate is a projection.

**The widest unmeasured term, and the probe that measures it (DD8).**
Re-instantiate ONE delivered `Agree` module with the class as a parameter, and
diff it. `TagAgree` (`src/L/Condensation.lagda.md:6670`) is the smallest of
the thirty and it is one of the three the return already cites. That probe
prices the other twenty-nine. **Nobody has run it.**

**One reason to expect the ambient instance to be the EASY one.** The class
hypotheses that the generic form carries are `Cl-tr`, `Cl-Tow` and `Cl-Dee`
(`agents/tasks/LJ-1-184/ProbeLJ1184A.agda:88-90`), and at `Full` all three are
`tt*` (`:312-319`). Probe C is the same effect on the reading axis: the
statement that is FALSE at the class carrier for non-Δ₀ formulas is TRUE for
every formula at the ambient one. INFERRED, from those two sites, and it is a
reason to run the probe rather than a price.

## 6. DD4, WITH THE AXIS NAMED

**My axis: the port's L-against-ambient axis.** The same axis `[LJ-1.293]`
named, and I confirm it is the right one, because `amb` is the ambient half of
a cross that reads one formula at two carriers, so the carrier is the SUBJECT.
Not DD4's own AC-against-GCH axis, and not Devlin's Def-against-J axis, which
I use only in the last paragraph.

**On the L-against-ambient axis, the shared object grew today, and it is not
the negative.** `[LJ-1.293]` answered that the shared object is the REFUTATION,
one term for both carriers. That answer is correct and it is thin: a negative
is shared for free because it names no carrier.

**The generic objects I measured are the real DD4 answer.**

- `absFull` (`ProbeLJ1297C.agda:78-113`) is generic in the FORMULA and takes no
  class hypothesis. It is written once and it is the Δ₀-free companion of the
  delivered `abs₀`. It serves any class that is everything.
- `Supply` (`ProbeLJ1297D.agda:71-117`) is generic in the Def-step coding, and
  it turns `[LJ-1.238]`'s class-generic sequence coding into the ambient
  reading with six one-line transports. **The generic port paid off exactly
  here**: because `[LJ-1.238]` wrote `GenSequence` generic in the class, the
  ambient supply cost six lines instead of a coding chapter. That is DD4's rule
  producing a measured saving, and it is the strongest evidence in this report
  for writing the port generic.

**On Devlin's Def-against-J axis, `q'` stays per-tower**, and I confirm
`[LJ-1.244]` section 5 rather than extend it: `q'` names `LsetGraphAt`, which
runs to satisfaction syntax through `DefAt` (`GenSequence.agda:69`), and the J
tower's analogue is syntax-free op-graphs
(`dev/literature/devlin-II5.md:375`, row C2).

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `[LJ-1.293]`'s refutation is wrong on its own terms | **MEASURED FALSE.** Re-derived, `ProbeLJ1297A.agda`, exit 0 |
| `IntendedQ` is a different equation from `q` | **MEASURED FALSE.** `AmbientStep` accepts it in the `q` slot, `ProbeLJ1297B.agda:93-103`, exit 0 |
| the `refl` at `ProbeLJ1293A.agda:82-83` is a metavariable solution | **MEASURED FALSE.** `P184.Ambient` takes no class parameter, `ProbeLJ1184A.agda:321` |
| the `refl` proves the READING is the same | **MEASURED FALSE.** It compares carriers only; `A.ambient` is `⊨ᵛ` and `GenSequence` delivers at `⊨ᵐ` |
| the brief steered the verdict | **MEASURED FALSE.** The counter-branch was in the brief at `LJ-1.293.md:76-78`, and the verdict is a machine term |
| the `⊨ᵐ` to `⊨ᵛ` transport at the ambient carrier is undelivered | **MEASURED FALSE as of today.** `ProbeLJ1297C.agda`, exit 0 |
| the transport needs a Δ₀ or Σ₁ hypothesis at the FULL class | **MEASURED FALSE.** `absFull` takes neither, `ProbeLJ1297C.agda:78-113` |
| `AmbientStep`'s six readings are open at the ambient carrier | **MEASURED FALSE.** All six supplied, `ProbeLJ1297D.agda:95-117` |
| `[LJ-1.244]`'s exit 42 measures `q'` at the intended instantiation | **MEASURED FALSE.** `Graph` is abstract at `ProbeLJ1244B.agda:45` |
| `q` is refutable with `Graph` abstract | **MEASURED FALSE.** Confirmed with `[LJ-1.243]` section 1.3 and `[LJ-1.293]` section 1 |
| Devlin needs an equation between two codings | **MEASURED FALSE.** One formula `Φ` and its analogue `φ`, `dev/literature/devlin-II5.md:93-97` |
| the class-carrier analogue is the three regions the return cites | **MEASURED FALSE.** Thirty `Agree` modules, `src/L/Condensation.lagda.md:2774-7319` |
| I ported an `Agree` module to the ambient carrier | **MEASURED FALSE. I DID NOT.** The port price in section 5.2 is a projection, not a measurement |
| the Def-step trio is discharged by my probes | **MEASURED FALSE.** It stays a hypothesis in probes B and D |

## 8. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-293/lj-1.293-report.md`, read WHOLE, FIRST, as the brief
  orders. **Line read:** `:180`, "These seconds decide nothing; the term
  decides". TOOK the verdict, the four premises and the two obligations. That
  line is also why my correction in section 1 is a label and not a finding.
- `agents/tasks/LJ-1-293/ProbeLJ1293A.agda`, read WHOLE. **Line read:** `:133`,
  `q-false h = lower (subst (λ ψ → Case (tag₂ ψ)) h tt*)`. TOOK the term. My
  probe A is this file with the module name changed, and my probe B spends
  `q-false` on an `AmbientStep` application.
- `agents/tasks/LJ-1-244/ProbeLJ1244A.agda`, read `:85-110`. **Line read:**
  `:105-107`, the `q'` slot of the copied `AmbientStep`. TOOK the confirmation
  that `[LJ-1.244]`'s module is a COPY with `q` replaced, which is what
  `[LJ-1.293]` section 2 says.
- `agents/tasks/LJ-1-244/ProbeLJ1244B.agda`, read WHOLE. **Line read:** `:45`,
  `(Graph : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)`. TOOK the correction in
  section 5.2: the stuck goal at `:75` sits under an ABSTRACT `Graph`.
- `agents/tasks/LJ-1-244/lj-1.244-report.md`, read WHOLE. **Line read:**
  section 6's row, "the six readings produce `⟨ Graph ⟩` | MEASURED FALSE ...
  are not in `AmbientStep`'s telescope". TOOK the chapter price I re-examine.
- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read section 3 whole. **Line
  read:** `:227`, "Nothing reads `q` in the other direction. MEASURED". TOOK
  `q'`'s type and the one-direction reading, which probe D's `Left` module
  confirms is the only open slot.
- `agents/tasks/LJ-1-242/lj-1.242-report.md`, read `:1-30`. **Line read:**
  section 0, "The left side ... carries at least one constant. The right side,
  `embed φ₀`, carries none". TOOK the constant argument, which is the
  `φ₀`-independent half and which I did not re-measure.
- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`, read `:100-150`. **Line read:**
  `:103`, `base = Cnt.erase LH.levelHoodB refl`. TOOK the proof that `φ₀` is
  the BoundedSubset coding, which is what makes `q'` a two-coding bridge.
- `agents/tasks/LJ-1-224/lj-1.224-report.md`, read `:1-60` and the grep of its
  sections. **Line read:** section 0(c), "8 lines differ out of 338 non-blank,
  and all 8 are the carrier substitution". TOOK the only delivered comparable
  for a carrier-substitution port, and marked it TAKEN in section 5.2.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read `:1-75` and `:150-229`.
  **Line read:** `:224`, `open RecShape StepAt public renaming ( GraphAt to
  LsetGraphAt ...)`. TOOK the identity of `LsetGraphAt` and the six readings
  probe D supplies.
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read `:60-190` and `:285-363`.
  **Line read:** `:322-323`, `module R = ReadOff Lset 𝒟ₒ Lset-in Lset-out
  Full (λ {x} {y} → Full-tr {x} {y}) Full-Lset Full-Def`. TOOK the fact that
  `Ambient` takes NO class parameter, which is what makes the target's `refl`
  sound rather than a metavariable solution.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read WHOLE. **Line read:** `:112`,
  `(q : Graph {2} zero (suc zero) ≡ embed φ₀)`. TOOK the telescope my probes B
  and D apply.
- `archive/dev/TASKS-archived.md`. **NOT READ, and I say so rather than claim
  it.** `[LJ-1.293]` read `:60-110` and reported the retired route's ambient
  cross as SHAPE only, with the content not transferring. My four questions are
  about a term, a carrier and a price in the live tree, and no archived row can
  move any of them. INFERRED, from the target's own archive section.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115` and `:370-392`.

**Does Devlin need this equation? NO. The port introduced it. MEASURED, from
the digest.**

`:93-97` quotes `dev2.txt:1186-1194`: "By 2.7 there is a Σ₀ formula
Φ(z, v, γ) of LST such that (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)] and moreover,
if φ(z, v, γ) is the ℒ-analogue of Φ(z, v, γ), then (using 1.9.15) ...".
**ONE formula, and its ℒ-analogue.** Devlin's only bridge is 1.9.15, Σ₀
absoluteness, which moves ONE formula between a transitive carrier and the
ambient universe. He never asks two different formulas to be equal, and he
never asks two codings to agree.

**Row C1**, "level-hood formula, Σ₁-with-Σ₀-matrix, uniform Δ₁, witness in
carrier, PER-TOWER content" (`:374`). `amb` is clause (a)'s soundness half at
the ambient carrier, and I confirm `[LJ-1.293]`'s row.

**What the digest adds to the price, and this is new here.** Row C3 is "Σ₀
absoluteness of the matrix, 1.9.15 at transitive carriers, EITHER tower,
neither tower; general absoluteness" (`:376`). **My probe C is that row at the
ambient carrier**, and at that carrier it needs no Σ₀ restriction, because the
carrier is the universe. So the port's second obligation was Devlin's C3 all
along, it was priced as a gap by `[LJ-1.242]` and `[LJ-1.293]` because they
read it at the CLASS carrier, and it costs 20 lines at the ambient one.

**Why the phase pays what Devlin does not.** Devlin's Φ is a Σ₀ formula of
LST, written informally, with no constants and no coding. Bedrock's level-hood
certificate is machine-checked through a CODED satisfaction machine, so it has
constants, while the site needs a parameter-free formula for the elementarity
transfer. That is why there are two codings, and `q` and `q'` are the price of
the pair. INFERRED, from the absence in Devlin plus `ProbeLJ1241A.agda:103`.

**WHY NOT the other rows.** C2 is the bounded Def-step matrix, C4 the transfer
along elementarity, C5 and C6 bookkeeping and unions, D and G the well-order,
E the counting, F the cardinal chain, A and B extensionality and the collapse.
`q` and `q'` name none of them: they are C1's ambient half, with C3 as the
transport probe C now delivers.

## 10. WHAT I DID NOT SETTLE

- **The Def-step trio at the ambient carrier.** A hypothesis in probes B and D.
  `[LJ-1.224]` reports it delivered; I take that and mark it TAKEN.
- **The port of any `Agree` module.** Section 5.2's price is a projection with
  a named basis, and P-l binds it. The probe that would settle it is named
  there.
- **Whether `q'` is TRUE.** I did not attempt it. `[LJ-1.243]` and
  `[LJ-1.244]` both read it true; I neither confirm nor refute.
- **The constant-count argument** that refutes `q` for an ARBITRARY `φ₀`.
  Still INFERRED, as `[LJ-1.293]` section 1 left it. My work is at the
  phase's `φ₀`, where the machine term needs none of it.
- **`archive/dev/TASKS-archived.md`**, not read. Section 8 says why.

## 11. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. No invocation near 30 minutes; the longest was
40.32 s.

| file | exit | elaboration | reload | load at the run |
|---|---:|---:|---:|---|
| `ProbeLJ1297A.agda` | 0 | 4.01 s | 2.56 to 2.61 s | 6.98 / 6.33 / 5.89 |
| `ProbeLJ1297B.agda` | 0 | 40.32 s | 2.71 s | 5.44 / 5.78 / 5.75 |
| `ProbeLJ1297C.agda` | 0 | 1.56 s | not measured | 6.47 / 5.55 / 5.58 |
| `ProbeLJ1297D.agda` | 0 | 22.81 s | not measured | 4.12 / 4.87 / 5.30 |

Three users throughout. `ProbeLJ1297D.agda` failed once before this table, on
unsolved metavariables, because the transport's formula argument was left
implicit; I made it explicit and the file passed. That failure is recorded
because it is the only thing between the two runs.

## 12. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-297/`. `agents/tasks/LJ-1-293/` was
read and copied from, never written to. `agents/tasks/LJ-1-294/`,
`agents/tasks/LJ-1-295/`, `agents/tasks/LJ-1-296/` and `scripts/` were not
touched. No master edited, `src/Everything.lagda.md` not opened,
`dev/ledger.toml` and `dev/PLAN.md` not touched,
`src/L/Choice/Name.lagda.md` not opened. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.

**A script moved under me, as the brief warned.** `scripts/ledger.py` is gone;
it is now `scripts/measure/ledger.py`. I report the move and did not work
around it: no size figure in this report comes from the ledger. `scripts/`
now holds `dispatch/`, `gate/`, `measure/`, `ops/`, `site/`, `tests/`,
`git-hooks/`, `agents_tree.py` and `repo_root.py`.

**My files:** `agents/tasks/LJ-1-297/LJ-1.297.md` (the pinned brief),
`agents/tasks/LJ-1-297/lj-1.297-report.md`,
`agents/tasks/LJ-1-297/ProbeLJ1297A.agda`, `ProbeLJ1297B.agda`,
`ProbeLJ1297C.agda` and `ProbeLJ1297D.agda`.
