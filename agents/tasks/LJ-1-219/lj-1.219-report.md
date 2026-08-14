# LJ-1.219 report: join GenModel to Powerset's body at the ambient class

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Written
incrementally (C-22). No master edited. No commit, no push. Every negative is
MEASURED or INFERRED, in those words.

## 0. LEAD

**The Model link composes. The joined pair does not typecheck. MEASURED.**

Exit 42 at `JoinAtAmbient.agda:142.32-42`. A second supplier leaks.

Every Model name the body uses before that line typechecks at the ambient
class: `extAt`, `tagAtL`, `extAt-out`, `extAt-in-both`, `tagAtL-adequate`.
The body advanced past the `:68` wall of `[LJ-1.216]`. MEASURED.

**The second supplier is `L.Coding.Recover`, names `keyOf` and `keyOf-fst`,
at `JoinAtAmbient.agda:142` and `:138`.** MEASURED. I name it and stop. I do
not port it.

**The join's written lines: 21 non-blank added, 6 deleted, 386 unchanged,
against the `[LJ-1.216]` file.** MEASURED by `linediff.py`. `[LJ-1.210]`'s 19
is Model's standalone instance. The join's 21 is the same instance content
plus six join-wiring lines. P-l: a comparable, not a price.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process. `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised. No run
passed 30 minutes. No heap exhaustion.

The machine is not quiet. Five sibling Agda processes ran beside me. Load sits
beside every figure. The first run was the warm-up and was discarded. No
verdict rests on seconds. The verdict rests on exit code 42 and a line number.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `JoinAtAmbient.agda` | the Powerset body joined to `LJ-1-210.GenModel`, both at the ambient class `M = Full`. Exit 42 at `:142` |

The file is new. None is deleted. It sits in `agents/tasks/LJ-1-219/`. It is a
probe. Nothing lands in `src/`.

## 3. THE JOIN

I copied `agents/tasks/LJ-1-216/GenPowersetAtAmbient.agda` to
`JoinAtAmbient.agda`. I made four changes.

One. I removed the `open import L.Coding.Model` block. I added
`import LJ-1-210.GenModel`.

Two. I added the six numeral operations at the ambient class. They are the same
definitions `[LJ-1-210]` used at `ProbeLJ1210C.agda:53-70`. `numeralF`,
`numeralF-fst`, `pairF`, `pairF-fst`, `sucF`, `sucF-fst`. All `tt*` or `refl`.

Three. I applied the generic module.

```
module AtFull = LJ-1-210.GenModel {ℓ} M (λ {x} {y} → M-trans {x} {y})
                  numeralF numeralF-fst pairF pairF-fst sucF sucF-fst

open AtFull using ( extAt; extAt-out; extAt-in; extAt-in-both; tagAtL
                  ; tagAtL-adequate; domAt; domAt-intro; domAt-out )
```

Four. I added `⁅_,_⁆` and `sucV` to the two imports the numeral operations
need.

The eta-expansion `(λ {x} {y} → M-trans {x} {y})` is the same cure
`[LJ-1.210]` section 6.2 and `[LJ-1.216]` section 3 measured. It is plumbing,
not mathematics.

**The body text is untouched.** The 386 unchanged lines are the body from
`envOne` to `DefAt-out`. The join changes only the supplier header.

## 4. THE FIRST FAILURE, AND WHAT IT MEASURES

The first run stopped at `:142` with `[UnequalTerms]`:

```
Lift Cubical.Data.Unit.Unit !=<
∥ Σ (FOL.ZFStructure.ZFStructure.S 𝒮ᵥ) (...) ∥₁
when checking that the expression lookup y γ has type
FOL.ZFStructure.ZFStructure.S L.Constructible.𝒮ʟ
```

Line 142 is `hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩`. The body's
`lookup y γ` has type `S`, the ambient carrier `𝒮ᵥ ↾ Full`. The delivered
`keyOf` expects the delivered carrier `𝒮ʟ`. The tower leaks in through that
supplier.

**What composes. MEASURED.** The names the body takes from the generic Model
typecheck at the ambient `S`. `envOneAt` (`:90-91`), `envOneAt-in`
(`:108-118`), `envOneAt-out` sub1 (`:122-132`). All use `extAt`, `tagAtL`,
`extAt-out`, `extAt-in-both`, `tagAtL-adequate` from `AtFull`. None fails.
Five names.

**What is INFERRED.** `extAt-in` first appears at `:143`, the body of
`hasKey`, one line past the error. The `domAt` trio (`domAt`, `domAt-intro`,
`domAt-out`) appears later, at `graphAt-holds` and `graphAt-unique`. Agda
stops at `:142` before it reaches them. Their composition at the ambient
class is INFERRED.

## 5. THE SECOND SUPPLIER THAT LEAKS

`L.Coding.Recover`. MEASURED at `JoinAtAmbient.agda:142` (`keyOf`) and `:138`
(`keyOf-fst`).

`src/L/Coding/Recover.lagda.md:84` opens `hPropStructure 𝒮ʟ`. So its
`keyOf : ℕ → S → S` (`:112`) and `keyOf-fst` (`:115`) produce values over the
delivered `𝒮ʟ` carrier. The body needs them over the ambient carrier.

`Recover` is itself a consumer of the delivered Model:
`src/L/Coding/Recover.lagda.md:69` imports `prʟ`, `prʟ-fst`, `closedAt` from
`L.Coding.Model`. So it is the next brick in `[LJ-1.213]`'s bottom-up order.
**I do not port it. One link per task.**

The other fixed suppliers the body imports are never reached. Their leak is
INFERRED, not measured. I do not price them (C-42).

## 6. DD4 NUMBERS

| number | lines | basis |
|---|---:|---|
| shared body | 389 | the generic Powerset body, `[LJ-1.213]`'s figure. The join touches no body line |
| plumbing | 21 | the join delta: 15 Model-instance lines plus 5 join wiring plus 1 rename |
| per-tower residual | 8 | `DefAt-stage`, `[LJ-1.213]`'s figure, unchanged |

The 21 plumbing lines split: 13 numeral-operation lines, 2 module-application
lines, 2 `open AtFull` lines, 1 import line, 2 import-adjustment lines, 1
module-rename line.

**Against `[LJ-1.210]`'s 19.** The 19 is the standalone ambient instance of
Model: `Full`, `Full-trans`, six numerals, the application. The join's 21
reuses the six numerals (13 lines) and the application (2 lines) and adds six
wiring lines. The two figures are consistent in kind. P-l forbids dividing one
by the other.

## 7. TIMINGS

All runs use `GHCRTS="-A64m -I0 -M8g"`.

| run | exit | seconds | load |
|---|---:|---:|---|
| 1 (warm-up, discarded) | 42 | 3 | 4.32 / 5.07 / 4.92 |
| 2 (kept) | 42 | 2 | 5.45 / 5.13 / 4.95 |
| 3 (kept) | 42 | 1 | 5.45 / 5.13 / 4.95 |
| 4 (kept) | 42 | 2 | 5.45 / 5.13 / 4.95 |

Three kept runs: 2, 1 and 2 seconds. Exit 42 each time. The seconds decide
nothing. Exit code 42 and line 142 decide.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the joined pair typechecks at the ambient class | **MEASURED FALSE.** Exit 42 at `JoinAtAmbient.agda:142` |
| the Model link composes | **MEASURED TRUE for five names.** `extAt`, `tagAtL`, `extAt-out`, `extAt-in-both`, `tagAtL-adequate` all typecheck before `:142` |
| `extAt-in` and the `domAt` trio compose | **INFERRED.** Agda stops at `:142` before it reaches them |
| a second supplier leaks | **MEASURED TRUE.** `L.Coding.Recover`, `keyOf`/`keyOf-fst`, `:142` and `:138` |
| the other fixed suppliers leak | **INFERRED.** Not reached (C-42) |
| the order is wrong | **MEASURED FALSE so far.** The Model link confirms `[LJ-1.213]`'s bottom-up reading for the first step |

## 9. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-216/lj-1.216-report.md`, read WHOLE. TOOK the `:68` wall,
  the leak naming, the eta-expansion cure. My probe is its direct successor.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE. TOOK the 389/12/8
  figures, the body, the bottom-up reading.
- `agents/tasks/LJ-1-213/GenPowersetBodyAtL.agda`, `DefAtStage.agda`, read.
  TOOK the body text and the 8-line corollary.
- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read WHOLE. TOOK the 19-line
  ambient instance and the eta-expansion cure (section 6.2).
- `agents/tasks/LJ-1-210/GenModel.agda`, `ProbeLJ1210C.agda`, read. TOOK the
  six numeral definitions at `ProbeLJ1210C.agda:53-70`.
- `src/L/Coding/Powerset.lagda.md:49-70`, `:128-129`, read. TOOK the fixed
  imports and the leak site.
- `src/L/Coding/Recover.lagda.md:57`, `:69`, `:84`, `:112-116`, read. TOOK the
  second leak's site.
- `archive/dev/TASKS-archived.md:1-40`, read for shape. The archived rows price
  the retired route. No figure transfers.

## 10. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:301-302` says the proof does not pin the
presentation. `:370-382` splits the steps into nine tower-neutral steps and
three per-tower steps.

The joined pair lands on the neutral side as mathematics. The Model names and
the Powerset body never name the tower in their text. `DefAt-stage` lands on
the per-tower side.

**But the table splits mathematics, not modules.** `L.Coding.Recover`'s `keyOf`
is tower-neutral as an idea and tower-fixed as an Agda term. Its type pins the
`𝒮ʟ` carrier. So the joined pair lands where Devlin puts it as mathematics and
does not land there as a module. The same conclusion as `[LJ-1.216]`.

## 11. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. The second-supplier branch
  fired. I name it and stop.
- C-42. I measure one site: `L.Coding.Recover` at `:142`. I do not price the
  chain.
- P-l. Model's 19 is a comparable. I measure the join's own 21.
- C-22. The report file existed before the first Agda run.
- C-36. The term I could not write is a typechecked joined pair. Section 4
  writes the compiler message.
- C-12. One process, `-M8g`, cap never raised. Load beside every figure.
- DD0, DD8. One number per claim. Line counts are non-blank lines.
- DD4. Section 6.
- DD23. No mathematical prose written. No master edited.
- I-5. No probe under `src/`. `check-probes.py` is clean.
