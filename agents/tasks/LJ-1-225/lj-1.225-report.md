# LJ-1.225 report: the port supplies the substrate, not the environment lift

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. No Agda ran. No
slot held. No master, brief or report edited. No commit, no push. Every
negative is MEASURED or INFERRED, in those words. Written incrementally
(C-22).

## 0. LEAD

**NO.**

The ported chain does not supply the environment lift. It supplies the coding
chain below the lift. The lift is six ambient readings. They live one module
above the port's scope.

## 1. THE FOUR HYPOTHESES

`theorem : ⟨ x ∈ˢ Lset κ ⟩` sits at `src/L/BoundedSubset.lagda.md:1621`. It
derives from `levelIn` and `cover`, stated at
`src/L/BoundedSubset.lagda.md:1555-1556`. `[LJ-1.178]` built both as functions
of four hypotheses. The four sit at
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:486-493`.

| hypothesis | what it says | state | file:line |
|---|---|---|---|
| `amb` | Devlin (a) at the AMBIENT carrier | **SUPPLIED** | def `ProbeLJ1178A.agda:190-191`; supply `ProbeLJ1184B.agda:155`; site `ProbeLJ1184C.agda:92-95` |
| `sl` | the stage believes every ordinal has a level | **NEITHER** (open) | `ProbeLJ1178A.agda:360-361` |
| `sc` | the stage believes every set lies in a level | **NEITHER** (open) | `ProbeLJ1178A.agda:405-406` |
| `s₁` | the level-hood formula is Σ₁ | **BUILT in shape** | `src/L/BoundedSubset.lagda.md:145-146`; 2-line gap `ProbeLJ1178A.agda:78-85` |

`amb` is SUPPLIED by `[LJ-1.184]` (C-38: something supplies it). `sl` and `sc`
are open and unpriced by this chain. BUILT is not SUPPLIED, so `s₁` does not
discharge. MEASURED.

## 2. QUESTION 2: NO

The environment lift is the six ambient readings.
`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:44-52` names them "THE RESIDUE". They
are the delivered objects of `L.Coding.Sequence` at the ambient carrier. The
six are `StepAt-out` (`src/L/Coding/Sequence.lagda.md:217`), `StepAt-back`
(`:221`), `ApproxAt-dom` (`:295`), `ApproxAt-value` (`:298`), `ApproxAt-step`
(`:303`), `Graph-out` (`:325`).

The port does not reach them. The green body
`agents/tasks/LJ-1-220/Probe.agda` ends at `DefAt-out` (`Probe.agda:566`).
`DefAt` is one ingredient of `StepAt-out`. The step readings sit in
`L.Coding.Sequence`. That module pins `𝒮ʟ` at `Sequence.lagda.md:59`. It is
not among `[LJ-1.220]`'s 17 modules or `[LJ-1.223]`'s 10 suppliers.

The port supplies the ingredients only. `DefAt-in` and `DefAt-out`
(`Probe.agda:549`, `:566`). The Model readings `domAt`, `appAt`, `extAt` from
`GenModel.agda`. It stops one layer short of the lift itself.

MEASURED FALSE: the port supplies the environment lift.

## 3. THE MISSING TERM

**The ambient step reading.** It is the carrier-generic port of
`L.Coding.Sequence`: `StepAt-out`, `StepAt-back`, `ApproxAt-dom`,
`ApproxAt-value`, `ApproxAt-step`, `Graph-out` at the ambient carrier. C-36:
this is the term the six dispatches did not write.

`Sequence.lagda.md` holds 157 non-blank in-fence lines. It pins `𝒮ʟ` at
`:59`. Its port is small and mechanical. It is not in the port's scope.
MEASURED.

## 4. THE 17-LINE SURFACE

`[LJ-1.200]` measured a 17-line class-naming surface on Model plus Powerset.
`[LJ-1.220]` measured the real surface: 22 parameters across 9 modules
(`CodeSet`, `Graph`, `Table`, `Slot`, `Sat`, `Sound`, `Unique`, `Bridge`,
`Uniform`). Both surfaces sit below the six readings. The 17 lines had
nothing behind them. The 22 parameters have the six readings still behind
them. MEASURED.

## 5. LITERATURE: IS THE RESIDUE ONE OF THE TWO OBJECTS?

The six readings are Devlin's C2 row. `dev/literature/devlin-II5.md:375`
marks it "bounded Def-step matrix", PER-TOWER content. The verdict at
`:387-389` says the per-tower content is exactly two objects: the level-hood
certificate (Step C) and the definable well-order (Steps D, G).

So the environment lift IS part of Step C, the level-hood certificate. The
port prices the coding substrate, the "coding analogue" of C2. It never
reaches the step matrix itself. Devlin said so: the C2 row marks it per-tower.

`sl` and `sc` are the C1 instantiation (`:374`), also part of Step C. The port
never targets them either. So both parts of `[LJ-1.7]`'s residue are the
level-hood certificate. Neither part is the well-order. MEASURED.

## 6. DD4 JUDGEMENT

The port is worth landing on DD4 alone, as a shared refactor. `[LJ-1.223]`'s
figure stands: 2,971 shared lines, about 200 plumbing, 0 per-tower residual in
the chain. It unblocks nothing for `[LJ-1.7]`. Two reasons. One: it stops one
module short of the six readings. Two: `sl` and `sc` stay open whatever the
port does. Land it as DD4, call it DD4, and do not call it a cure. One note:
the C2 row marks the coding per-tower, which bears on the word "shared". That
is `[LJ-1.223]`'s claim to defend. I do not re-price it.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the port supplies the environment lift | **MEASURED FALSE.** `Probe.agda` ends at `DefAt-out` `:566`; Sequence is not in scope |
| the environment lift is tower-neutral | **MEASURED FALSE.** `devlin-II5.md:375` marks C2 per-tower |
| the port discharges all of `[LJ-1.7]`'s residue | **MEASURED FALSE.** `sl` and `sc` are open; the six readings are missing |
| the 17-line surface was the real surface | **MEASURED FALSE.** 22 parameters across 9 modules |
| Sequence is in the port's 17-module scope | **MEASURED FALSE.** It is not in `[LJ-1.220]`'s list nor `[LJ-1.223]`'s 10 |

## 8. ARCHIVE USED (DD18)

- `dev/PLAN.md:36-70`, read WHOLE, first. TOOK the `[LJ-1.7]` row at `:49`
  and the ENVIRONMENT LIFT wording.
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read. TOOK the four hypotheses at
  `:486-493`, `amb` at `:190-191`, `sl` at `:360-361`, `sc` at `:405-406`,
  `s₁` at `:492`.
- `agents/tasks/LJ-1-178/lj-1.178-report.md`, read WHOLE. TOOK the four open
  rows and the states.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read. TOOK "THE RESIDUE" at
  `:44-52` and the `amb` supply at `:155`.
- `agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, read. TOOK the real-site
  discharge at `:92-95`.
- `agents/tasks/LJ-1-184/lj-1.184-report.md`, read. TOOK the residue table
  (section 5.2) and the SUPPLIED template.
- `agents/tasks/LJ-1-196/lj-1.196-report.md`, read WHOLE. TOOK the NO-GO, the
  use site at `Sequence.lagda.md:181`, and the environment-lift wording.
- `agents/tasks/LJ-1-200/LJ-1.200-report.md`, read WHOLE. TOOK the 17-line
  surface and the environment-lift naming.
- `agents/tasks/LJ-1-220/Probe.agda`, read WHOLE. TOOK the body end at
  `DefAt-out` `:566` and the 22 parameters.
- `agents/tasks/LJ-1-220/lj-1.220-report.md`, read WHOLE. TOOK the 22
  parameters and the 17-module census.
- `agents/tasks/LJ-1-223/lj-1.223-report.md`, read WHOLE. TOOK the 10
  suppliers, 2,971 shared, about 200 plumbing, 0 residual.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read. TOOK the Powerset body
  figures and `DefAt-stage`.
- `agents/tasks/LJ-1-219/lj-1.219-report.md`, read. TOOK the ambient join and
  the Recover leak.
- `src/L/Coding/Sequence.lagda.md`, read `:40-360`. TOOK `𝒮ʟ` at `:59`, the
  six readings at `:217`, `:221`, `:295`, `:298`, `:303`, `:325`.
- `src/L/BoundedSubset.lagda.md`, read `:900-920`, `:1545-1626`. TOOK
  `levelIn`/`cover` at `:1555-1556` and `theorem` at `:1621`.
- `src/L/Condensation.lagda.md`, read header `:28`, `:341-428`. TOOK
  `σL-transfer` and `ride-only` for shape only.
- `archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`: read
  for shape only. No figure transferred.

## 9. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:370-395`, read WHOLE. TOOK the C1 row at
  `:374`, the C2 row at `:375` (PER-TOWER content), and the verdict at
  `:387-389` (two per-tower objects: level-hood certificate, definable
  well-order).
- `dev/literature/devlin-II5.md:301-303`, read. It says the proof does not
  pin the presentation. It is about the level-hood formula, not the coding.
  Cited for completeness.

## 10. RULES ANSWERED

- D-10. This task IS D-10 on a whole phase. I priced the truth of the
  residue before its proof: the residue is the six ambient readings, not the
  coding chain.
- C-38 as extended. `amb` is discharged because `[LJ-1.184]` supplies it.
  The six readings are not supplied. `sl` and `sc` are not supplied.
- C-36. Section 3 names the term: the ambient step reading.
- C-22. This report existed as a skeleton before the first search closed.
- C-42. I measure one site: the six readings in `L.Coding.Sequence`. I do not
  price the rest of the tree.
- P-l. I take `[LJ-1.223]`'s figures. I give no new line figure.
- D-26. Section 5 rests on the C2 row's D-26 carrier column.
- C-32, C-39, C-40, DD0, DD2, DD4, DD8, DD24, I-5. One number per claim.
  The DD4 figure is taken, not re-derived.
