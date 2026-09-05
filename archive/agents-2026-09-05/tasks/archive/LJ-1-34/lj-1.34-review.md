# LJ-1.34 review: the DD25 adversarial review of a NO-GO

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. ASD-STE100.

## 1. THE VERDICT

**OVERTURN. The same theorem, the same hypotheses, checks at 0.0072
seconds per line, not 0.436. The factor is 61.**

`src/ProbeDD25D5.agda` is 198 lines. Two flat cold runs give 1.41 and
1.42 seconds of user time. The rate is 0.00715. The GO bar is 0.013. The
row is a GO. DD24's bar is 0.013193, so the row lands at **0.54 of the
bar**. `[LJ-1.5]`'s delivered block 1 landed at 0.60
(`_build/lj-1.5-report.md:8-13`).

I reproduced the return's own probe first. `src/ProbeLJ134.agda` costs
71.74 seconds of user time on this machine, against the return's 73.75
and 74.40. **The return's measurement is sound. Its conclusion is not.**

The certificate half needs a correction of a different kind. The return
reports TWO obstructions. **One of them is not real.** I built the cure
and measured it at 756 milliseconds. The other obstruction stands, but
`[LJ-1.2]` recorded it before this dispatch (`_build/lj-1.2-gate.md:8`,
`:60-63`), so it is not a finding of this one. It is the substrate, and
the substrate was always the price.

Three claims of the return do not survive:

1. **0.436 seconds per line.** The real figure is 0.0072. The cause is
   the shape, and the return named that shape and declined to measure it.
2. **"Two independent obstructions stand."** One stands.
3. **"the bounded satisfaction substrate ... 2.7 to 3.0k+
   (`_build/lj-1.2-gate.md:64-76`)".** The cited lines hold no price. The
   number prices a different object.

One claim of the return survives and decides the phase: **the Δ₀
certificate does not close, because the delivered leaves carry unbounded
quantifiers.** That is true, it is the whole remaining obligation, and
`src/ProbeDD25D2.agda` now states it as ONE premise.

## 2. THE GENERIC LEAF LAYER

BUILT, and it works. Then I found what it left behind, and killed that
too.

| probe | lines | cold user s | s per line |
|---|---:|---:|---:|
| `src/ProbeLJ134.agda`, the return's | 170 | 71.74 | 0.422 |
| `src/ProbeDD25D1.agda`, generic leaf layer | 219 | 29.89 | 0.136 |
| `src/ProbeDD25D3.agda`, hypotheses generic too | 219 | 30.23 | 0.138 |
| `src/ProbeDD25D4.agda`, story side generic | 224 | 4.84, 4.43 | 0.021 |
| `src/ProbeDD25D5.agda`, the deliverable shape | 198 | 1.41, 1.42 | **0.0072** |

Every row proves the SAME theorem. `step-out` and `step-in` carry the
return's hypotheses and the return's conclusion, and I copied their types
from `src/ProbeLJ134.agda:275-287` without a change of meaning. Section
2.4 gives the machine proof that the story is the same story.

The noise rule holds. D5's two runs differ by 0.01 seconds. D4's differ
by 0.41 seconds, which is under 0.5.

### 2.1 The layer alone: 71.74 to 29.89

`src/ProbeDD25D1.agda` makes the leaf body a variable ψ. The leaf
agreement, the body agreement and the step agreement never name the built
`DefBody`. The built body enters once, at the instantiation.

The cold profile:

| definition | ms |
|---|---:|
| `StepAgree.step-out`, the instantiation | 14,902 |
| `StepAgree.step-in`, the instantiation | 14,513 |
| the WHOLE generic layer, six definitions | 115 |
| miscellaneous, the import cone | 1,379 |
| total | 30,914 |

The return attributes 41.7 seconds to its leaf agreement and 31.1 to its
body agreement, which is 72.7 of its 74.0 seconds. **The generic layer
does the same work in 0.115 seconds.** The return's own candidate cure
works.

The residue is two conversion checks.

### 2.2 What the residue is

`src/ProbeDD25D2.agda` splits the conversion. Each entry below is an
identity, proved by `refl` or by `h`, and each carries no proof content
at all.

| identity | ms |
|---|---:|
| A1, the FORMULA identity, `StepAt ≡ ClauseD` | below the report threshold |
| A2, the CLAUSE satisfaction identity, out | 17 |
| A2, the CLAUSE satisfaction identity, in | 13 |
| A3, the BODY satisfaction identity | below the report threshold |
| A4, the LEAF satisfaction identity | 6,397 |

`src/ProbeDD25D3.agda` then writes the bound hypotheses through the
generic layer. Cold: 30.23 seconds. **No change.** The hypotheses are not
the cost.

### 2.3 The cause, in one sentence

**The cost is a satisfaction-level conversion between two SPELLINGS of
one formula.**

The formula-level identity is free. The same identity under `⟨ γ ⊨ - ⟩`
costs seconds. The return's 73 seconds are that conversion, performed
inside the type of every agreement lemma, because the story spells the
leaf `DefAtB` and the delivered machine spells it `DefAt`.

### 2.4 The kill: 29.89 to 4.84, then to 1.42

**The story is ours to write.** The delivered machine's spelling is
fixed. The story's spelling is not. So write the story once, in the
generic layer's vocabulary, and never convert.

`src/ProbeDD25D4.agda` does that, and proves at the formula level that
nothing changed:

```
story-is-story : StepStory.StepBndB v b f ≡ G.ClauseB (DefBody (suc zero)) v b f
story-is-story = refl
```

| definition | ms |
|---|---:|
| `story-is-story`, the formula identity, a diagnostic | 2,991 |
| `StepAgree.step-out`, the endpoint | 31 |
| `StepAgree.step-in`, the endpoint | 28 |
| the whole generic layer | 103 |
| miscellaneous, the import cone | 1,249 |
| total | 4,409 |

**The two endpoints fall from 29,415 milliseconds to 59.**

`src/ProbeDD25D5.agda` is the deliverable shape. It drops the second
spelling and the diagnostic that compares them. It is 198 lines and 1.42
seconds. A profiled run totals 1.522 seconds and puts 1.383 of them in
the import cone. **The file's own content is about 140 milliseconds.**

### 2.5 P-l was cited to avoid a measurement

The return wrote (`_build/lj-1.34-report.md:148-153`):

> One candidate is a generic leaf layer with the body abstract, the way
> `[LJ-1.33-R]` did the outer layer. The instantiation still names the
> built satisfaction, so P-l forbids pricing it by analogy. I did not
> measure it.

**P-l forbids pricing by analogy. It does not forbid measuring.** The
return used a law about estimates as a reason to skip an experiment. The
brief had asked for the opposite in plain words (`_build/briefs/LJ-1.34.md:86`):
"Measure it; do not argue it." The layer took me one file and one run,
and it typechecked first try. The unmeasured cure was the whole verdict.

I propose a law for `dev/LESSONS.md`, and the orchestrator assigns the
ID. **Measurement: 0.436 against 0.0072, a factor of 61, from a cure the
return named in its own section 6.**

> **A return that names a cure prices it or reports the wall that stops
> it.** A named and unpriced cure is not a caveat. It is an unmeasured
> term inside the verdict, and it decides the verdict. P-l forbids
> pricing a cure by analogy; it never forbids building the cure and
> measuring it.

A second law is available from the same numbers, and it is the sharper
one.

> **Never state a theorem whose type forces a satisfaction-level
> conversion between two spellings of one formula.** Prove the spelling
> identity ONCE at the formula level, then state everything in one
> spelling. Measured at this site: 59 milliseconds against 29,415, a
> factor of 499, for the identical theorem.

## 3. IS Δ₀ THE RIGHT TARGET?

**YES. The Σ₁ relaxation buys one binder at the root and nothing else.
This line of attack fails, and the brief was right.**

`Σ₁` is delivered, with two constructors and no third
(`src/FOL/LevyHierarchy.lagda.md:73-75`):

```
σ-Δ₀ : Δ₀ φ → Σ₁ φ
σ-∃  : Σ₁ φ → Σ₁ (∃̇ φ)
```

The only base is `σ-Δ₀`, and it demands `Δ₀`. **So "Σ₁ with a Σ₀ matrix"
and "Δ₀ on the matrix" are ONE target in this tree.** Devlin agrees. Step
C frees the top existential, then binds every quantifier of the Def step
by the concrete set `K(u)`, INSIDE the matrix
(`dev/literature/devlin-II5.md:246-255`).

`[LJ-1.5]` carries BOTH, not Σ₁ instead of Δ₀:

- `Clause.Δ₀-existBndAt : Δ₀ existBndAt`, a full Δ₀ witness for the
  matrix (`src/L/Condensation.lagda.md:190-194`).
- `Σ₁-cert = σ-∃ (σ-Δ₀ (Clause.Δ₀-existBndAt ...))`, built ON it
  (`:201-202`).

The consumer decides it. Three transfer lemmas exist and there is no
fourth:

- `abs₀ : Δ₀ φ → (δ) → (δ ⊨ᵐ φ) ≡ (map fst δ ⊨ᵛ φ)`, BOTH ways, demands
  `Δ₀` of the whole formula (`src/FOL/Absoluteness.lagda.md:122-123`).
- `σ₁-up`, upward only (`:182-183`).
- `π₁-down`, downward only (`:187-188`).

`EraseTransfer` takes `(d : Δ₀ φ)` and spends it at `AbsL.abs₀ d γ`
(`src/L/Condensation.lagda.md:216-217`, `:233`). `ClauseDecode`
instantiates it at the MATRIX (`:296-297`). The crossing is a round trip:
`[LJ-1.29]` step 2 goes up with `σ₁-up`, and step 4 comes DOWN with
`π₁-down` (`_build/lj-1.29-report.md:93-100`, `:113-121`). There is no
`σ₁-down`, and `∃̇ φ` has no Π₁ witness.

**So the highest-value finding you hoped for is not there. I looked for
it and it is not there.**

### 3.1 But obstruction 2 is not real, and its cure is five lines

The return names two obstructions. Only one survives.

`extAt y φ = ∀̇ (z ∈ y ⇒̇ φ) ∧̇ ∀̇ (φ ⇒̇ z ∈ y)`
(`src/L/Coding/Model.lagda.md:662-664`). The FIRST universal is a bounded
universal written unbounded. Its own hypothesis is the bound. The SECOND
needs a set that holds every satisfier, and the story already carries
one: the bound slot K.

So write the ext bounded, exactly as the delivered
`src/L/Condensation.lagda.md:132-140` writes its own clause. The
delivered block 1 never uses `extAt`. I grepped it: `DefAt`, `StepAt`,
`DefBody` and `StepBody` do not occur in that file at all.

```
extAtB y K φ = ∀̇∈ (var y) φ ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))
Δ₀-extAtB y K φ d = δ-∧ (δ-∀∈ d) (δ-∀∈ (δ-⇒ d δ-∈))
```

MEASURED. `src/ProbeDD25D2.agda` writes the WHOLE story clause with
`extAtB` at both levels, and closes its certificate:

```
StoryBB.Δ₀-clause : Δ₀ (DefBody (suc zero)) → Δ₀ ClauseBB
```

It checks in **756 milliseconds**. **ONE premise remains, and it is the
leaf content.** Every quantifier of the story's own shape is now bounded
and certified, including the outer ext, the three witness existentials,
the leaf ext, the two leaf existentials and `appAt`.

**So there is ONE obstruction, not two, and the machine now states it as
a single hypothesis.** The return's obstruction 2 is an artefact of
writing the story with the delivered `extAt`.

## 4. IS THE SUBSTRATE NEEDED, AND IS 2.7-3.0k REAL?

**The substrate is needed. The figure is not real as stated, and the
table that carries it double-counts.**

### 4.1 The citation does not resolve

The return cites `_build/lj-1.2-gate.md:64-76` three times for the
substrate price (`_build/lj-1.34-report.md:64`, `:157`, `:204`). I read
that file whole. **Lines 64 to 76 hold no price.** They hold the probe's
own line and second miss, and the heading of the DD4 section.

`[LJ-1.2]`'s only substrate price is a different number
(`_build/lj-1.2-gate.md:126-128`): "Its measured price is 5,047 lines
(T257 section 4.2). The alternative is the cone abstraction fork at 1.0
to 1.7 thousand lines (T51 section 5)."

### 4.2 Where 2.7-3.0k comes from, and what it prices

It first appears at `_build/lj-1.5-report.md:110-111`. There it prices
**"the clause-shaped residue"**, which is the whole remainder of route A
after block 1: the other eleven table clauses, plus iso-invariance, plus
the limit case, plus leg D. It is route A's 3.3k survey
(`_build/lj-1.12-report.md:20-49`) minus what block 1 delivered.

`[LJ-1.33]` narrowed the label to "eleven more clauses". `[LJ-1.34]`
renamed it "the bounded satisfaction substrate" and added a plus sign.
**The number never moved. Only the label moved.**

The project's own component rows for the substrate PROPER are smaller:

| component | band | class | source |
|---|---:|---|---|
| bounded code-set description and adequacy | 0.2-0.5k | ESTIMATED | `_build/lj-1.12-report.md:30` |
| bounded twelve-clause table and adequacy | 0.7-1.6k | ESTIMATED | `:31` |
| the same table, re-priced after a measurement | 0.7-1.9k | MEASURED anchor | `_build/lj-1.15-report.md:133-137` |

So the substrate proper is **0.9k to 2.4k**, and `[LJ-1.34]`'s figure is
1.3 to 3 times the project's own estimate for that object. DD8 asks an
estimate to name its basis. This one names a basis that belongs to a
different object.

### 4.3 The table double-counts

The return's section 6 lists both "the leaf agreement and body agreement,
110 lines at 0.66" and "the bounded satisfaction substrate, 2.7 to 3.0k".

My numbers delete the first row: the agreement is 59 milliseconds, not 73
seconds. And the eleven remaining table clauses are not a PREREQUISITE
for the substrate. **They ARE the substrate's table half.** `[LJ-1.5]`
delivered clause 1 of 12, and `[LJ-1.15]` measured it as the hardest one
(`_build/lj-1.15-report.md:133-137`). So the row appears twice in one
table.

### 4.4 What is genuinely needed

One thing, and the machine now names it:

```
Δ₀ (DefBody (suc zero))
```

`DefBody w = isCodeAt (suc zero) (sh3 w) ∧̇ (satGraphAt ... ∧̇ DefinesAt ...)`
(`src/L/Coding/Powerset.lagda.md:437-440`). Its three leaves carry
unbounded quantifiers, and the return's `file:line` evidence for that is
correct. A bounded restatement of those three leaves, with its agreement,
is the substrate's code-set half. That is Devlin's `K(u)`.

`[LJ-1.2]`'s NO-GO on this point stands, and nothing since has moved it.
`[LJ-1.15]` and `[LJ-1.5]` moved the TABLE half by delivering one clause
of twelve. Nobody has re-priced the code-set half since the survey.

## 5. DID THE BRIEF CAUSE IT?

**Partly. But the decisive defect is in the return, not in your brief.
This is not a second C-33.**

### 5.1 The Δ₀ demand was correct. Your line is right

You asked me to quote your line if it was your error. Here it is
(`_build/briefs/LJ-1.34.md:48-51`):

> **So the row still owes its Δ₀ half.** ... The crossing needs the story
> ABSOLUTE, which means a Δ₀ certificate, and that is what nobody has
> measured at this site.

**That is correct on the delivered code.** Section 3 gives the evidence:
`σ-Δ₀` is Σ₁'s only base, `abs₀` demands Δ₀ of the whole formula, and the
crossing's return leg is `π₁-down`. You did not impose an over-strict
target. You named the target the tree imposes.

### 5.2 One brief line did push the shape

This one (`_build/briefs/LJ-1.34.md:59-61`):

> **Use the CHEAP route** that `[LJ-1.33-R]` measured: the formula
> readings, and the delivered body rather than a re-typed one.

"The delivered body rather than a re-typed one" reads as an instruction
to put the built `DefBody` into the types. That is the exact move that
costs. The intent was cheapness and DD4, and the effect was the opposite.

**This is the C-33 pattern, at a smaller scale: the line names an ENTRY
POINT, not the OBLIGATION.** The obligation is "the decode must not force
a satisfaction-level conversion between two spellings". A brief that said
that would have produced the 1.42-second file.

### 5.3 But the brief also gave the licence, twice

- `:64-66`: "If you find a delivered reader I have not named that does
  this job better, use it and say so. That is a finding, not a
  deviation."
- `:86`: "Bounding `DefAt` may or may not have the same character.
  **Measure it; do not argue it.**"

The return had the licence, the slot and its own idea. It argued.
Section 2.5 states the law I propose for that.

## 6. WHAT THE NEXT BLOCK COSTS

On my numbers, and every MEASURED row below is mine from today.

| piece | lines | seconds | class |
|---|---:|---:|---|
| the generic leaf and step layer, written ONCE | 125 | 0.10 | MEASURED |
| the instantiation at `DefBody`, both directions | 32 | 0.06 | MEASURED |
| the witness template certificate | 13 | below threshold | MEASURED |
| the bounded ext and its certificate, template | 10 | in the row below | MEASURED |
| the story's Δ₀ certificate, given the leaf witness | 9 | 0.76 | MEASURED |
| the approximation and graph clause decodes | 2 more clauses | ~0.06 each | PROJECTED on the rows above |
| the bounded code-set description, the substrate's half | 0.2-0.5k | 1.6-4.0 | SURVEY, `_build/lj-1.12-report.md:30` |
| the other eleven table clauses | 0.7-1.9k | 5.6-15.2 | SURVEY, `_build/lj-1.15-report.md:133-137` |
| the bound-fact construction, the carrier facts row | unmeasured | unmeasured | OWED |

The seconds columns for the two survey rows use `[LJ-1.5]`'s delivered
0.0079 and my 0.0072. The basis is two delivered comparables at this
site, and I name it because DD8 asks for the basis and not a caliber.

**Leg D is no longer the widest unmeasured term. It is measured and it is
nearly free.** The widest unmeasured term is now the bound-fact
construction: the proof that the code, the value, the witnesses and the
satisfiers all lie inside K. Both the return's probe and mine take those
as hypotheses. `src/ProbeDD25D2.agda`'s `extAtB` shape adds one more of
them, because the bounded second conjunct needs every satisfier inside K.

**The next brief should gate the bound-fact construction, not leg D.**

### DD4

The split is now measured, and it is better than the return reports.

**Template: 148 lines of 189, and 78 percent.** The generic layer is 125
lines and is generic in the leaf body ψ. It carries the leaf agreement,
the body agreement, the witness agreement and both step directions. It
never mentions L's Def syntax. The witness template certificate is 13
lines and `extAtB` with `Δ₀-extAtB` is 10. Both close for ANY Δ₀ body.
The J tower instantiates all of it at its own leaf body, and pays the
same 0.10 seconds.

**Per tower: 41 lines.** The instantiation at `DefBody`, 32 lines, and
the story's own certificate, 9 lines. The count excludes the 28 lines of
header and imports.

The return says "The measured cost is neither half. It is the shared
machine's built tree." **That is now false.** The built tree costs 59
milliseconds when the story is spelled once.

## 7. WHAT I AM NOT SURE OF

1. **I priced ONE clause.** The approximation and graph clauses have
   different bodies. Their decodes should ride the same generic layer,
   but I did not build them. My "~0.06 each" is a projection on one
   measured comparable at the same site, not a measurement.
2. **The FULL row is not measured end to end.** I measured the decode
   with the story's ext spelled `extAt` (1.42 s), and the certificate
   with the story's ext spelled `extAtB` (0.76 s). I did NOT build the
   decode of the `extAtB` story against the machine. It is about 20 more
   lines and it needs one more bound fact. I expect it to be cheap for
   the reason in section 2.3, and **that expectation is a hypothesis, not
   a price.**
3. **The bound facts are hypotheses in every probe in this lineage**,
   mine included. `LeafBnd` and `OuterBnd` are the K(u) obligations
   written as assumptions. Nobody has built them. The return says the
   same at `_build/lj-1.34-report.md:245-247`, and it is right.
4. **The rate meter is weak here.** D5's 1.42 seconds is 1.38 seconds of
   import cone and 0.14 seconds of content. Adding lines would LOWER the
   rate without lowering the cost. DD24 measures cold seconds over
   in-fence lines, and at this size that meter mostly measures the import
   cone. A seconds-per-statement meter would have caught the return's
   real problem faster.
5. **I did not build any part of the substrate.** Its 0.9k to 2.4k rests
   on the project's own surveys, and the code-set half has not been
   re-priced since `[LJ-1.2]`.
6. **I did not find the mechanism** behind the satisfaction-level
   conversion cost. I measured it at four sites and localized it. I
   cannot say which part of Agda's conversion checker does the work.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, and the summary at
`:299-302`). Took the exact requirement: Σ₁ with a Σ₀ matrix, the
unbounded existential free at the top ONLY, and every quantifier of the
Def step bounded by `K(u)` inside the matrix. This is what refutes the
Σ₁ escape in section 3. The book asserts absoluteness where the formal
proof must prove a decode, so it cannot price any row here.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5
(`_build/lj-1.14-report.md:107-108`), and the LJ-1.34 brief rules out
re-checking it.

## 9. ARCHIVE USED

`_build/lj-1.34-report.md`, whole. `_build/briefs/LJ-1.34.md`, whole.

`_build/lj-1.2-gate.md`, whole. Took the verdict at `:8`, the clause
results at `:32-35`, the missing bounds at `:60-63`, the probe's miss at
`:64-68` which is the broken citation, the substrate definition at
`:87-89`, and the 5,047 price at `:126-128`.

`_build/lj-1.5-report.md`. Took the next-block list at `:96-108` and the
2.7-3.0k origin at `:110-111`.

`_build/lj-1.12-report.md`. Took the component bands at `:28-33`.

`_build/lj-1.15-report.md`. Took the table re-price at `:133-143`.

`_build/lj-1.29-report.md`. Took step 2 at `:93-100`, step 4 at
`:113-121` which is the downward leg, and the open point at `:351-354`.

`src/FOL/LevyHierarchy.lagda.md`: the Δ₀ data at `:47-57`, the Σ₁ data
at `:73-75`.

`src/FOL/Absoluteness.lagda.md`: `abs₀` at `:122-123`, `σ₁-up` at
`:182-185`, `π₁-down` at `:187-188`.

`src/FOL/Semantics.lagda.md`: the bounded quantifier readings at
`:102-103`.

`src/L/Condensation.lagda.md`: the bounded clause at `:132-141`, the atom
witnesses at `:142-156`, `Δ₀-existBndAt` at `:190-194`, `existCertAt` and
`Σ₁-cert` at `:196-202`, `EraseTransfer` at `:216-233`, `ClauseDecode`'s
instantiation at `:296-297`, `cert-transfer` at `:346-347`.

`src/L/Coding/Model.lagda.md`: `extAt` at `:662-664`, the readings at
`:666-678`.

`src/L/Coding/Powerset.lagda.md`: `DefBody` at `:437-440`, `DefAt` at
`:442-443`.

`src/L/Coding/Sequence.lagda.md`: `StepBody` at `:110-114`, `StepAt` at
`:116-117`.

`src/ProbeDD25D.agda:179-186`: the atom Δ₀ witnesses, copied.

`dev/LESSONS.md` is not archived and binds. P-l decided section 2. D-1,
D-10, C-12, C-22 and C-32 were followed. P-u: no placement anywhere, so
nothing needed certifying before a placement.

## 10. PROBES BUILT

All untracked, all thrown away per D-1. None committed.

| file | lines | what it measures |
|---|---:|---|
| `src/ProbeDD25D1.agda` | 219 | the generic leaf layer, the return's own cure |
| `src/ProbeDD25D2.agda` | 107 | the conversion split, and the bounded ext certificate |
| `src/ProbeDD25D3.agda` | 219 | the same, with generic hypothesis types |
| `src/ProbeDD25D4.agda` | 224 | the story spelled once, with the identity proved |
| `src/ProbeDD25D5.agda` | 198 | the deliverable shape, 0.0072 s per line |

I also re-ran the return's `src/ProbeLJ134.agda` cold, at 71.74 seconds,
to reproduce its figure before attacking it.

Every Agda run used `GHCRTS="-A64m -I0 -M8g"`, one process, on a quiet
machine. No heap exhaustion. The cap was never raised. Interfaces were
removed from `_build/2.8.0/agda/src/` before each cold run, never from
beside a source.
