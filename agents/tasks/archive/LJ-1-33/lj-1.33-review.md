# LJ-1.33 review: the DD25 attack on the leg D NO-GO

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. The review uses ASD-STE100.

## 1. THE VERDICT

**OVERTURN.** Leg D is not expensive. The return's two signatures, with the
return's hypotheses, against the DELIVERED `StepAt`, check in **1.32 seconds
over 122 lines. The rate is 0.0108, which is 0.82 of DD24's bar.** The
return measured 50.13 seconds and 0.334 for the same theorem.

The cut is **38x in seconds and 31x in rate**. The gate said GO at or below
0.013. The theorem passes that gate.

The 0.34 is real, and it is not a property of leg D. It is a property of one
proof shape. I built the other shape and measured it.

The evidence is `src/ProbeDD25CD.agda`. Its `step-out'` and `step-in'` carry
the same types as `src/ProbeLJ133.agda:171-173` and `:237-240`. Its
`BoundOK` is a copy of `src/ProbeLJ133.agda:123-126`.

**Read section 7 before you fund.** The target that both the return and I
measured is the brief's target. It is not yet the story that the crossing
needs.

## 2. THE SHARED MACHINE-READING LAYER

BUILT, and it costs 34 milliseconds.

### 2.1 Why the layer is possible

The story clause and the machine clause carry THE SAME body. They differ
only by three bounds. I proved this by `refl` in `src/ProbeDD25CE.agda`:

| fact | statement | file:line |
|---|---|---|
| 1 | the return's hand-written body IS the delivered `StepBody` | `src/ProbeDD25CE.agda:44-46` |
| 2 | the story clause IS one `extAt` over the bounded witness | `src/ProbeDD25CE.agda:62-64` |
| 3 | the delivered `StepAt` IS one `extAt` over the SAME body, unbounded | `src/ProbeDD25CE.agda:68-71` |

All three are `refl`. So leg D at the step clause is a bound-drop and a
bound-add. Nothing in it needs to read the machine's body.

### 2.2 The layer

`src/ProbeDD25CS.agda:53-102`, the module `Triple`. It is **37 lines**. It
takes the body as an ABSTRACT formula parameter `φ`. It names no built
formula anywhere. It gives `drop`, `add`, `toUnb` and `toWit`.

The profile of `src/ProbeDD25CD.agda`:

| definition | ms |
|---|---:|
| `Triple.add` | 15 |
| `Triple.drop` | 14 |
| `StepAgree.discharge` | 10 |
| miscellaneous, the import cone | 1,270 |
| total | 1,310 |

`step-out'` and `step-in'` do not appear. They cost nothing.

### 2.3 The 2x2, which separates the two causes

The return's shape has two independent defects. I measured each. Every cell
is a cold pair, one Agda process, at `GHCRTS="-A64m -I0 -M8g"`.

| route \ body | body written by hand | delivered body reused |
|---|---|---|
| **machine CONTENT projections** (`StepAt-out`, `StepAt-in`) | **50.13 s**, 150 lines, 0.334 (`src/ProbeLJ133.agda`, the return) | 13.34 s, 145 lines, 0.092 (`src/ProbeDD25CB.agda`) |
| **machine FORMULA readings** (`extAt-out`, `extAt-in`, `extAt-in-both`) | 30.00 s, 101 lines, 0.297 (`src/ProbeDD25CL.agda`) | **1.32 s**, 122 lines, 0.0108 (`src/ProbeDD25CD.agda`) |

Neither cure alone passes the gate. Together they pass it with room.

**Cause 1, the route.** `StepAt-out` returns `StepOf`, the machine's clean
content type (`src/L/Coding/Sequence.lagda.md:217-229`). To reach that
content, the decode must read the built body. `extAt-out` returns the raw
satisfaction of the body formula (`src/L/Coding/Model.lagda.md:667-678`).
It never reads the body. Both are delivered. The brief named only the
first.

**Cause 2, the copy.** The return writes the body out again at
`src/ProbeLJ133.agda:70-76`. That is the same formula as the delivered
`StepBody` at `src/L/Coding/Sequence.lagda.md:113-117`. Agda must then
prove the two equal inside every proof term that mentions both. In
`src/ProbeDD25CL.agda` that conversion is the whole cost: `step-out` 14,777
ms and `step-in` 14,396 ms, against 34 ms for the layer.

This is P-l exactly (`dev/LESSONS.md:2305`). Naming a built construction in
a type is what costs. It is P-t as well (`dev/LESSONS.md:2601`): the class
follows the formula.

### 2.4 The layer amortizes

`src/ProbeDD25CM.agda` holds SIX instantiations of the same agreement.

| probe | instantiations | lines | cold s | rate |
|---|---:|---:|---:|---:|
| `ProbeDD25CD` | 1 | 122 | 1.32 | 0.0108 |
| `ProbeDD25CM` | 6 | 317 | 1.72 | 0.0054 |

Five more clauses cost 0.40 seconds, so **0.08 seconds per clause**. The
rate FALLS as clauses arrive, because the 37-line layer is written once.

### 2.5 DD4

The layer is TEMPLATE, and this is measured rather than argued. `Triple`
takes the body as a parameter and mentions no tower. Both towers and every
clause use the same 37 lines. The per-clause instantiation is about 20
lines and 0.08 seconds.

The return predicted this in prose and declined to price it
(`_build/lj-1.33-report.md:156-162`, `:173-181`). The prediction is
correct. The J tower gets the expensive-looking half for free.

## 3. IS THE 0.34 SOUND?

The SECONDS are sound. The INFERENCE from them is not.

I re-ran both of the return's probes cold. I moved each probe's interface
out of `_build/2.8.0/agda/src/` before every run, per C-32. No interface
ever sat beside a source.

| probe | return's cold s | my cold s | delta |
|---|---:|---:|---:|
| `src/ProbeLJ133.agda` | 50.99, 50.90 | 50.22, 50.03 | 1.6 percent |
| `src/ProbeLJ133Ctrl.agda` | 1.11 | 1.21 | 0.10 s |

Both deltas are flat under the brief's noise rule. The line counts also
check: 150 and 61, by the return's own convention
(`_build/lj-1.33-report.md:65`).

So the return measured its file correctly. The defect is the step from
"this file costs 0.34 per line" to "leg D costs 0.34 per line". P-m says a
rate certifies a content class. A rate certifies a content class only when
the proof uses the cheapest delivered route. This proof did not.

One figure in the return is wrong in the other direction. Section 4 puts
the measured 0.34 "at or above P-n's concrete-carrier floor band, 0.22 to
0.297". `src/ProbeDD25CL.agda` sits at 0.297 inside that band and needs no
carrier at all. So the band does not diagnose this cost.

## 4. DID THE BRIEF CAUSE IT?

**YES, and it caused both halves.** I quote the brief.

**Cause 1.** The brief, `_build/briefs/LJ-1.33.md:42-43`:

> The machine side is delivered: `src/L/Coding/Sequence.lagda.md:217-229`
> and `:295-312`.

And `_build/briefs/LJ-1.33.md:55-58`:

> **one clause's decode against the delivered machine's projections** [...]
> **Use a DELIVERED machine projection**, not a synthetic stand-in, so the
> answer is about the real site.

`Sequence.lagda.md:217-229` is exactly `StepAt-out`, `StepAt-back` and
`StepAt-in`. Those are the CONTENT projections. They are the expensive
route. The cheap route is `extAt-out`, `extAt-in` and `extAt-in-both` at
`src/L/Coding/Model.lagda.md:667-678`. Those are delivered too. The brief
never named them, and it named no other file for the machine side.

An agent told to use the delivered projections, and given one file and one
line range, will use those projections. The return did.

**Cause 2.** The brief, `_build/briefs/LJ-1.33.md:59-60`:

> **`src/L/Condensation.lagda.md` is committed and green.** Build against
> it, and take its `Clause` shapes as the source rather than re-inventing
> them.

Block 1's `Clause` module writes every formula out by hand
(`src/L/Condensation.lagda.md:64-137`). That is correct there, because
those formulas are new bounded content with Δ₀ witnesses. The step body is
NOT new content. It is delivered. The instruction to copy the style copied
the hand-writing, and the hand-writing is worth 10x here.

This is the failure mode you named. The brief pinned the shape, and the
shape carried the whole cost.

## 5. IS LEG D NEEDED IN THIS FORM?

**Not in the return's form, and the brief chose that form.** I did not
re-open the crossing question that `[LJ-1.29]` settled.

`[LJ-1.28]` states leg D as a two-way decode between the bounded table's
clause and the delivered machine's clause, at variable slots
(`_build/lj-1.28-report.md:95-100`). The brief restated that and the return
built it. So far there is no defect.

The defect is deeper. `[LJ-1.29]` says the hypothesis at `M` must be an
ABSOLUTE formula, because the machine's clause is not absolute
(`_build/lj-1.29-report.md:148-157`). `[LJ-1.2]` found the step clause has
no Δ₀ witness at any carrier (`_build/lj-1.2-gate.md:14-16`, `:28-35`).

The return's `StepBnd` bounds the three OUTER existentials and keeps the
`DefAt` leaf unbounded (`src/ProbeLJ133.agda:80-96`). So `StepBnd` is not
Δ₀. It is not the story that the crossing needs. The return says this
itself, at `_build/lj-1.33-report.md:259-262`.

Two things follow, and they point the same way:

1. The 0.34 does not price the real leg D, because the target is a proxy.
2. My 0.0108 does not price the real leg D either, for the same reason.

So the NO-GO rests on a proxy, and the proxy is cheap. The evidence for
the NO-GO is gone. The real row is still unmeasured, by the return and by
me.

**One agreement at the graph level does not serve.** `[LJ-1.29]` fixes the
crossing on the shared story formula. I take that as ruled and I did not
test it.

## 6. WHAT THE NEXT BLOCK COSTS

On my numbers the block funds, with a wide margin.

| piece | lines | rate | seconds |
|---|---:|---:|---:|
| the clause-shaped residue, eleven more clauses | 2.7 to 3.0k | 0.008 to 0.010, MEASURED at block 1 | 22 to 30 |
| leg D, the story-to-machine agreement | 0.3 to 0.8k | 0.0108, MEASURED at `src/ProbeDD25CD.agda` | 3 to 9 |
| total | | | **25 to 39** |

The GCH side's budget is 99.6 to 147.7 seconds (`dev/ledger.toml:305`). The
block fits inside the low end.

**One best-effort number for leg D, per DD8: about 6 seconds.** The basis
is 0.55k lines at 0.0108 seconds per line, measured cold at
`src/ProbeDD25CD.agda`. That number returns to `[LJ-1.28]`'s original
5 seconds (`_build/lj-1.28-report.md:128-136`). The recon was right and the
probe shape was wrong.

At the six-clause rate of 0.0054 the row costs about 3 seconds. I do not
claim that figure, because I measured it on one repeated clause.

Marginal figures, for the record. The import cone alone costs 1.18 seconds
over 26 lines (`src/ProbeDD25CF.agda`). Above that floor the return's probe
costs 0.395 per content line. `ProbeDD25CD` costs 0.0015.

## 7. WHAT I AM NOT SURE OF

1. **The target, and it is the big one.** Section 5 shows that the measured
   clause is not the absolute story the crossing needs. Both figures, the
   return's and mine, price the same proxy. Do not book 0.0108 as leg D's
   rate. Book it as: the bound-drop half of leg D is free. **Send a brief
   that measures the certificate story against the delivered machine.**
2. **One clause.** I measured the step clause, which the return calls the
   binding clause. The approximation and graph clauses have different
   bodies. My layer is generic in the body, so I expect it to carry, but
   P-l forbids me to price them by analogy.
3. **The layer is fixed at three existentials.** A clause with two or four
   needs its own instance of about 37 lines. That is still template.
4. **The bound hypothesis is deferred.** `Bounds` is a hypothesis in my
   probe, exactly as `BoundOK` is in the return's. `discharge` derives mine
   from the return's, so the two are at parity (`src/ProbeDD25CD.agda:172-202`).
   The carrier-facts row still owes the bound construction.
5. **Cold discipline.** Dependencies were warm through
   `_build/2.8.0/agda/src/`. Only each probe's own interface was cold. That
   matches the return's protocol, so the comparison holds. It is not a
   whole-cone figure.
6. **`src/ProbeDD25CE.agda` costs 5.47 seconds** for three `refl` facts.
   The formula conversion is not free even at the formula level. It is
   cheap only when nobody puts it inside a proof term.

## 8. PROBES BUILT

All untracked, all thrown away per D-1. `scripts/check-probes.py` reports
clean.

| file | lines | what it measures |
|---|---:|---|
| `src/ProbeDD25CF.agda` | 26 | the import cone floor |
| `src/ProbeDD25CE.agda` | 43 | the three `refl` facts |
| `src/ProbeDD25CL.agda` | 101 | the layer, body written by hand |
| `src/ProbeDD25CS.agda` | 96 | the layer, delivered body reused |
| `src/ProbeDD25CD.agda` | 122 | the return's exact signatures, through the layer |
| `src/ProbeDD25CB.agda` | 145 | the return's route, delivered body reused |
| `src/ProbeDD25CM.agda` | 317 | six instantiations, for the slope |

## 9. ARCHIVE USED

`_build/lj-1.33-report.md`, whole. `_build/briefs/LJ-1.33.md`, whole.

`_build/lj-1.28-report.md`: leg D's statement at `:95-100`, the ride at
`:68-93`, the pricing at `:128-136`.

`_build/lj-1.29-report.md`: the absolute-formula requirement at `:148-157`,
the crossing verdict at `:8-16`.

`_build/lj-1.2-gate.md`: the step clause NO-GO at `:14-16` and `:28-35`.

`src/L/Coding/Sequence.lagda.md`: `StepBody` at `:113-117`, `StepAt` at
`:119-120`, `readBody` and `fill` at `:170-215`, the three step projections
at `:217-229`.

`src/L/Coding/Model.lagda.md`: `extAt` and its three readings at
`:662-678`, `appAt-adequate` at `:163-166`.

`src/L/Coding/Powerset.lagda.md`: `DefAt` at `:442-443`, `DefAt-out` at
`:662-666`.

`src/L/Condensation.lagda.md`: the `Clause` module at `:52-195`,
`ClauseDecode` at `:247-343`.

`dev/LESSONS.md`: P-l at `:2305`, P-m at `:2460`, P-n at `:2483`, P-t at
`:2601`, P-u at `:2908`, D-10 at `:1316`, C-32 at `:2947`.

`dev/ledger.toml`: the seconds budget at `:305`.
