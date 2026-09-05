# LJ-1.216 report: the second instantiation of Powerset at the ambient class

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Written incrementally
(C-22). No master edited. No commit, no push. Every negative is MEASURED or
INFERRED, in those words.

## 0. LEAD

**The ambient instantiation does NOT typecheck. MEASURED.** Exit 42 at
`GenPowersetAtAmbient.agda:68`.

There is no written-line figure to set against `[LJ-1.210]`'s 19, because the
body does not reach a valid instantiation. The port does NOT serve both towers
today. **A supplier leaks the tower into the body. MEASURED.**

**The supplier is `L.Coding.Model`, at `GenPowersetAtAmbient.agda:68`**, the
delivered `src/L/Coding/Powerset.lagda.md:129`. The body declares `envOneAt`
over the ambient structure `S = 𝒮ᵥ ↾ Full`, but `tagAtL` and `extAt` from
`L.Coding.Model` produce formulas over the delivered `𝒮ʟ`. That supplier is
hard-wired to the L tower. **Naming it is the complete answer per the brief.**
I stop here.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process. `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised. No run
passed 30 minutes. No heap exhaustion.

The machine is NOT quiet. Sibling Agda processes ran beside me. Load sits beside
every absolute figure. The first run was the warm-up and was discarded. No
verdict rests on seconds. The verdict rests on exit code 42 and a line number.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `GenPowersetAtAmbient.agda` | the class-generic Powerset body with `M = Full`, `M-trans = Full-trans`. Exit 42 at `:68` |

The file is new. None is deleted. It sits in `agents/tasks/LJ-1-216/`. It is a
probe. Nothing lands in `src/`.

## 3. THE BUILD

I copied `agents/tasks/LJ-1-213/GenPowerset.agda` (the class-generic candidate)
to `GenPowersetAtAmbient.agda`. I set `M` to the ambient class:

```
M : V ℓ → hProp (ℓ-suc ℓ)
M _ = Unit* , isPropUnit*

M-trans : Transitive (𝒮ᵥ {ℓ}) M
M-trans {x} {y} _ _ = tt*
```

That is the same ambient class `[LJ-1.210]` used at
`ProbeLJ1210C.agda:47-50`. The generic candidate's 389 non-blank lines are
unchanged. The file has 392 non-blank lines, net +3: one import line added, two
header parameter lines removed, four `M`/`M-trans` lines added.

**First failure. MEASURED.** The first run stopped at `:62` with
`[UnsolvedConstraints]` on `module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M
M-trans`. The message is:

```
fst (y ∈ x) =< fst (_y_14 ∈ _x_13) (blocked on _x_13)
```

That is the SAME wall `[LJ-1.210]` hit at `ProbeLJ1210C.agda:72`. Its cure is one
eta-expansion. I applied it:

```
module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})
```

That is plumbing, not mathematics. MEASURED, confirmed at this site (P-l).

**Second failure. MEASURED.** The next run stopped at `:68` with exit 42,
`[UnequalTerms]`:

```
Formula (FOL.ZFStructure.ZFStructure.S L.Constructible.𝒮ʟ) _n_21
!=< Lift Cubical.Data.Unit.Unit of type Type (ℓ-suc ℓ)
when checking that the inferred type of an application
  Formula (FOL.ZFStructure.ZFStructure.S L.Constructible.𝒮ʟ) _n_21
matches the expected type
  Formula S n
```

Line 68 is `envOneAt e y = extAt e (tagAtL zero 0 (suc y))`. The body declares
`envOneAt` with return type `Formula S n`, where `S` is the ambient structure
`𝒮ᵥ ↾ Full`. But `extAt` and `tagAtL` come from `L.Coding.Model`, whose formulas
are over `𝒮ʟ`. The tower leaks in through that supplier.

## 4. THE SUPPLIER THAT LEAKS

`L.Coding.Model`, at `GenPowersetAtAmbient.agda:68`. The two names are `tagAtL`
and `extAt`, both on the same line. MEASURED.

`L.Coding.Model` is fixed at the class. Its `S` is `𝒮ʟ`. The body needs `S` to
be `𝒮ᵥ ↾ M`. The two do not meet. The next module to port is `L.Coding.Model`.

The other fixed suppliers the body imports — `L.Coding.CodeSet`, `L.Coding.Graph`,
`L.Coding.Table`, `L.Coding.Slot`, `L.Coding.Sound`, `L.Coding.Unique`,
`L.Coding.Sat`, `L.Coding.Bridge`, `L.Coding.Uniform`, `L.Coding.Recover` — are
never reached, because Agda stops at `:68`. Their leak is INFERRED, not measured.
I do not price them (C-42).

## 5. DD4 NUMBERS

The brief asks for three numbers at the ambient class. I can give only one
cleanly.

| number | at `isL` (LJ-1.213, MEASURED) | at the ambient class |
|---|---:|---|
| shared body | 389 non-blank lines, exit 0 | the SAME 389 lines as text, but NOT a working body. Exit 42 at `:68` |
| plumbing | 12 lines | not 12. It is the port of `L.Coding.Model`, which I do not measure |
| per-tower residual | 8 lines (`DefAt-stage`) | not 8. It is blocked at the first supplier |

**The shared body is the same set of 389 lines as text. MEASURED.** But it is not
a shared body in the DD4 sense: it typechecks at `isL` and does not typecheck at
the ambient class. The difference is not in the body's own text. It is in the
body's suppliers. The body is class-generic in its lines and class-fixed in its
imports.

## 6. TIMINGS

All runs use `GHCRTS="-A64m -I0 -M8g"`.

| run | file | exit | seconds | load |
|---|---|---:|---:|---|
| 1 | `GenPowersetAtAmbient.agda`, before eta-expansion | error | 2.13 | 5.74 / 4.41 / 4.35 |
| 2 | after eta-expansion | 42 | 1.39 | 5.74 / 4.41 / 4.35 |
| 3 | kept | 42 | 1.42 | 3.49 / 3.97 / 4.18 |
| 4 | kept | 42 | 1.37 | 3.49 / 3.97 / 4.18 |
| 5 | kept | 42 | 1.50 | 5.98 / 4.62 / 4.41 |

The three kept runs are 1.42, 1.37 and 1.50 seconds. Exit 42 each time. The
seconds decide nothing. Exit code 42 and line 68 decide.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the ambient instantiation typechecks | **MEASURED FALSE.** Exit 42 at `GenPowersetAtAmbient.agda:68` |
| the port serves both towers | **MEASURED FALSE at this site.** A supplier leaks the tower |
| a supplier leaks the tower into the body | **MEASURED TRUE.** `L.Coding.Model` at `:68` |
| the eta-expansion wall is only Model's | **MEASURED FALSE.** The same wall fires at the Powerset site, `:62`, and the same cure works |
| the other ten suppliers leak | **INFERRED.** Agda stops at `:68` before reaching them |

## 8. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE. TOOK the 389/12/8
  figures, the seven substitution sites, and the chain-gate reading.
- `agents/tasks/LJ-1-213/GenPowerset.agda`, `GenPowersetBodyAtL.agda`,
  `GenPowersetAtL.agda`, `DefAtStage.agda`, read WHOLE. My probe is a copy of the
  first, with the class fixed to `Full`.
- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read WHOLE. TOOK the 19-line
  ambient instance of Model (`ProbeLJ1210C.agda:47-73`) and the eta-expansion
  cure (section 6.2). P-l: a comparable is not a price.
- `agents/tasks/LJ-1-210/ProbeLJ1210C.agda`, read. TOOK the `Full` and
  `Full-trans` definitions at `:47-50`.
- `src/L/Coding/Powerset.lagda.md`, read at `:49-70` (the fixed imports), `:86-88`
  (the `𝒮ʟ` structure), `:128-129` (the leak site) and `:720-727` (`DefAt-stage`).
- `archive/dev/TASKS-archived.md:1-40`, read for shape only. The archived rows
  price the retired route. No figure transfers.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:370-382`. The table splits the twelve steps of
II.5 into nine tower-neutral (EITHER) steps and three per-tower steps.

`Powerset`'s BODY falls on the neutral side, as `[LJ-1.213]` said: its own text
never names the tower. `DefAt-stage` falls on the per-tower side: it spends
`LsetS` and `𝒟ₒ→isL`, the two facts that pin the L tower.

**But Devlin's table splits mathematics, not Agda modules.** The body's
SUPPLIERS pin the tower in their TYPES, not their text. `L.Coding.Model`'s
`tagAtL` and `extAt` are tower-neutral as ideas and tower-fixed as Agda terms.
So `Powerset` lands where Devlin puts it as mathematics, and does NOT land there
as a module. The split the table gives is necessary and not sufficient for a port.

## 10. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. The supplier-leak branch
  fired. I name it and stop.
- C-42. I measure ONE site: `L.Coding.Model` at `:68`. I do not price the chain.
- P-l. I do not copy Model's 19 lines onto Powerset. I measure the Powerset site.
- C-36. The term I could not write is a typechecked ambient Powerset. Section 3
  writes the compiler message.
- C-22. The report file existed before the first Agda run.
- DD4. Section 5. The shared body is the same 389 lines as text and is not a
  working shared body.
- DD23. No mathematical prose written. No master edited.
- I-5. No probe under `src/`. `check-probes.py` is clean.
- C-12. One process, `-M8g`, cap never raised. Load beside every figure.
