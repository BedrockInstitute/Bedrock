# LJ-1.213 report: the Powerset chain does not port at Model's rate

tier: pi (deepseek-subagent-mode). Written incrementally (C-22).
No master edited. No commit, no push.

## 0. LEAD

The chain does not port at Model's rate. The Powerset body port costs
**19 written lines and 21 removed lines on 391 non-blank lines**, with
**370 lines verbatim**. The per-line written cost is higher than Model.
The reason is fixed plumbing on a smaller module.

The body substitution claim holds. **Seven of the seven mechanical body
lines are substitutions.** The eighth L-specific piece is `DefAt-stage`.
That piece is **8 non-blank lines**. It is a corollary, not a chapter.

The full class-generic Powerset file does not typecheck. It stops at its
fixed supplier imports. That stop is measured, and it is the chain gate.

Every negative is marked MEASURED or INFERRED.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process. `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised.
No run passed 30 minutes. No heap exhaustion.

The machine is not quiet. Load sits beside every absolute figure.
The first run of a file was the warm-up and was discarded. Kept runs used
the existing interface cache. No verdict rests on seconds. Every verdict
rests on an exit code or a line count.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `GenPowerset.agda` | the class-generic candidate for Powerset. It has M and M-trans as module parameters. It does not typecheck. Exit 42 at `:63` |
| `GenPowersetMasterBody.agda` | the master fence extract without the DefAt-stage block |
| `GenPowersetBodyAtL.agda` | the transformed body, with M set to isL. It has no DefAt-stage. Exit 0 |
| `GenPowersetAtL.agda` | the transformed body plus DefAt-stage, with M set to isL. Exit 0 |
| `DefAtStage.agda` | the 8-line DefAt-stage definition alone, imported from the delivered Powerset. Exit 0 |
| `linediff.py` | counts non-blank added, deleted, and unchanged lines between two files |

All files are new. None is deleted. All sit in `agents/tasks/LJ-1-213/`.
`check-probes.py` is clean. `check-rule-ids.py` is clean.

## 3. THE TWO BUILDS

### 3.1 Powerset, class-generic

I compared the master fence extract without DefAt-stage to the generic
candidate. `linediff.py` reports:

| figure | non-blank lines |
|---|---:|
| added (written) | **19** |
| deleted (removed) | **21** |
| unchanged (verbatim) | **370** |
| changed sum | 40 |

The master body has 391 non-blank lines. The generic candidate has 389.

**Seven added lines are body substitutions. MEASURED.**
They sit at `GenPowerset.agda:104`, `:153`, `:242`, `:256`, `:355`, `:374`
and `:443`. Each replaces `isL-trans` or `isL` with `M-trans` or `M`.

**Twelve added lines are plumbing. MEASURED by diff.**
They are the pre-module imports, the M and M-trans telescope, and the three
import adjustments. The file lists them at `GenPowerset.agda:7-16`, `:23`,
`:55` and `:57`.

**The generic file does not typecheck. MEASURED.**
`agda agents/tasks/LJ-1-213/GenPowerset.agda` exits 42 at `:63`. The error is
an `UnequalTerms` between the delivered `𝒮ʟ` and `M`. The fixed supplier
modules import `𝒮ʟ`. They block the generic body until each supplier is
ported. This is the chain gate.

**The seven body substitutions are green at isL. MEASURED.**
`GenPowersetBodyAtL.agda` sets `M = isL` and `M-trans = isL-trans`, keeps the
same seven substitutions, and removes DefAt-stage. It exits 0.

### 3.2 DefAt-stage

The master block is `src/L/Coding/Powerset.lagda.md:720-727`. It has
**8 non-blank lines**. The brief calls it a 9-line span. The ninth raw line
is a trailing blank line.

`DefAtStage.agda:27-34` copies those 8 lines unchanged. It imports
`DefAt`, `DefAt-in` and `DefAt-out` from the delivered Powerset and the two
L facts `LsetS` and `𝒟ₒ→isL`. It exits 0.

**DefAt-stage is a corollary. MEASURED.**
The 8 lines only instantiate `DefAt-out` and `DefAt-in` at a stage. They
spend `LsetS` and `𝒟ₒ→isL`. They write no new body. The body they sit on
exists and typechecks at isL. No missing body appears.

## 4. TIMINGS

All runs use `GHCRTS="-A64m -I0 -M8g"`.

| file | cold seconds | cold load | kept warm seconds | kept load |
|---|---:|---:|---:|---:|
| `GenPowersetBodyAtL.agda` | 8.29 | 4.23 / 6.91 / 19.33 | 1.25, 1.25, 1.24 | 21.72 / 32.24 / 40.04 |
| `DefAtStage.agda` | 2.23 | 3.81 / 6.42 / 18.51 | 1.25, 1.23, 1.22 | 17.03 / 30.48 / 39.22 |
| `GenPowerset.agda` | 1.34, exit 42 | 5.61 / 20.12 / 33.51 | not kept | not kept |

The cold run was the first run after the interface was removed. Three kept
warm runs follow it. The seconds decide nothing. The exit codes and line
counts decide.

## 5. DD4 AND PLUMBING

For the Powerset site the shared class-generic body is **389 non-blank
lines**: 370 verbatim, 7 body substitutions, and 12 plumbing lines. The
per-tower residual is `DefAt-stage`, **8 non-blank lines**.

The plumbing paid at this module is **12 lines**, not 17. The 17-line
projection came from Model's fuller telescope. Powerset needs only M and
M-trans, so its telescope is smaller. The 12 lines are the flat telescope
and the three import adjustments.

The DD4 figure for the second tower is **INFERRED**. I did not build a
second instantiation. The measured fact is that the only L-specific content
in Powerset is the 8-line `DefAt-stage`. The second tower would need the
same 8-line corollary with its own two facts. That is an inference, not a
price.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the chain ports at Model's rate | **MEASURED FALSE at Powerset.** Model port-proper is 28 written over 1,288 lines, or 0.022 written per line. Powerset is 19 written over 391 lines, or 0.049 written per line. The factor is 2.2 |
| the generic Powerset file typechecks | **MEASURED FALSE.** Exit 42 at `GenPowerset.agda:63` |
| the seven body substitutions hold | **MEASURED TRUE.** `GenPowersetBodyAtL.agda` exits 0 |
| DefAt-stage is a chapter | **MEASURED FALSE.** It is 8 non-blank lines over an existing body. `DefAtStage.agda` exits 0 |
| the second tower's DD4 cost is measured | **INFERRED.** I measured only the L-specific residual, not a second instantiation |
| the 17-line plumbing estimate is exact | **MEASURED FALSE at this site.** The actual is 12 |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read WHOLE. TOOK the Model
  figures, the 17-module census, the 17-line plumbing projection, and the
  wall discipline. `GenModel.agda` is my calibration point.
- `agents/tasks/LJ-1-200/LJ-1.200-report.md`, read at the lead and sections
  1, 2, 5. TOOK the anchor counts and the `abs₀` correction.
- `src/L/Coding/Powerset.lagda.md` and `src/L/Coding/Model.lagda.md`, read at
  the class sites. The line numbers in section 3 come from these files.
- `archive/dev/TASKS-archived.md:1-60`, `:150-175`, `:220-250`, read for
  shape. The retired rows price old modules. No old figure transfers to the
  delivered `L.Coding.*` tree. The shape that transfers is small carrier-generic
  growth, which L3.32-T126 and T239 also show.

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:301-302` says the proof does not pin the
presentation. `dev/literature/devlin-II5.md:370-382` splits the steps into
nine tower-neutral steps and three per-tower steps.

`Powerset` falls on the neutral side. Its body never names the tower. It
names `M`, `M-trans`, and the shared operator `𝒟ₒ`. `DefAt-stage` falls on
the per-tower side. It spends `LsetS` and `𝒟ₒ→isL`, the two facts that pin
the L tower.

## 9. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. The rate broke. I report
  both figures and stop.
- P-l. I do not copy Model's rate onto Powerset. I measure the Powerset site.
- C-42. The negative covers the Powerset site only. I do not price the other
  16 modules.
- C-22. The report file existed before the first Agda run.
- C-36. The term I could not write is a typechecked generic Powerset. The
  fixed suppliers block it. Section 3.1 writes the compiler message.
- DD0, DD8. One number per claim. Line counts use the non-blank fence method.
- DD4. Section 5.
- DD23. No mathematical prose written. No master edited.
- I-5. No probe under `src/`. `check-probes.py` is clean.
