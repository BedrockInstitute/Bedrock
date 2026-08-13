# LJ-1.124: probe the bounded level-graph decode

tier: codex (default)

## STATUS

GO on the 150-line gate.

The two directions close in 147 non-comment lines of decode content.
The whole probe file has 176 non-comment lines. The extra 29 lines are
the import and module header.

No commit. No push. No master edited by me. The working tree carries
two non-probe edits that I did not make.

## 1. THE MEASUREMENT

The probe is `src/ProbeLJ1124A.agda`. It typechecks under
`GHCRTS=-M8g`.

The probe has these terms:

| direction | term | line |
|---|---:|---:|
| bounded step to machine step | `StepBridge.step-out` | `src/ProbeLJ1124A.agda:112` |
| machine step to bounded step | `StepBridge.step-in` | `src/ProbeLJ1124A.agda:116` |
| bounded approximation to machine approximation | `ApproxBridge.approx-out` | `src/ProbeLJ1124A.agda:167` |
| machine approximation to bounded approximation | `ApproxBridge.approx-in` | `src/ProbeLJ1124A.agda:171` |
| bounded graph to machine graph | `GraphBridge.graph-out` | `src/ProbeLJ1124A.agda:199` |
| machine graph to bounded graph | `GraphBridge.graph-in` | `src/ProbeLJ1124A.agda:204` |

The two graph directions close against `LsetGraphAt`. The delivered
`ride-only` and `ride-defines` then close against `Lset`
(`src/L/Condensation.lagda.md:419-428`).

## 2. LINES AND SECONDS

The decode content runs from the first `module StepBridge` to the end
of `module GraphBridge`. It has 147 non-comment, non-blank lines.

The whole probe file has 176 non-comment, non-blank lines. It has 210
total lines.

Cold user seconds, three runs, one Agda process:

| run | user seconds | load average |
|---:|---:|---:|
| 1 | 37.63 | 9.28 |
| 2 | 37.52 | 7.00 |
| 3 | 37.13 | 6.76 |

The mean is 37.43 seconds. The spread is 0.50 seconds.

The two directions are one module. The seconds above cover both
directions. The directions were not profiled separately.

## 3. WHAT WAS VERIFIED IN THE SOURCE

The brief says these facts. Each is MEASURED by `rg`.

1. `StepB`, `ApproxB` and `GraphB` are delivered at
   `src/L/Condensation.lagda.md:2389-2493`. Their Delta-0 witnesses
   are in the same range.
2. `graphBndAt` has no master decode. `rg -n 'graphBndAt' src/L`
   returns only the definition and the two Delta-0 lines in
   `src/L/Condensation.lagda.md:2489-2493`.
3. `ride-only` and `ride-defines` decode only the unbounded graph at
   `src/L/Condensation.lagda.md:419-428`.
4. `LevelHood` consumes `GraphB` at
   `src/L/BoundedSubset.lagda.md:74-111`. Nothing consumes `LevelHood`.

## 4. THE ASSEMBLY CLAIM

The claim of `[LJ-1.123]` section 2 holds. The probe closes the graph
decode from three delivered layers.

1. `StepBridge` uses a leaf agreement. The supplier is
   `LeafAgree.out` and `LeafAgree.back`
   (`src/L/Condensation.lagda.md:7020-7033`).
2. `ApproxBridge` uses the domain agreement. The supplier is
   `DomainAgree.out` and `DomainAgree.back`
   (`src/L/Condensation.lagda.md:6376-6385`).
3. `GraphBridge` uses the machine step and approximation decodes. The
   suppliers are `StepAt-out`, `StepAt-in`, `ApproxAt-dom`,
   `ApproxAt-value`, `ApproxAt-step` and `ApproxAt-in`
   (`src/L/Coding/Sequence.lagda.md:217-301`).

The final read and write against `Lset` use `ride-only` and
`ride-defines` (`src/L/Condensation.lagda.md:419-428`).

The probe states the leaf and bound facts as parameters. Their
suppliers are `LeafAgree`, `DomainAgree` and the `KFacts` fields
(`src/L/Condensation.lagda.md:5939-5975`).

## 5. THE RE-PRICED REMAINDER

The measured decode is 147 lines. That is 0.147 thousand lines. It
sits inside the `[LJ-1.123]` decode band of 0.10 to 0.25 thousand
lines.

The re-priced remainder is unchanged. It stays at about 0.6 thousand
in-fence lines, band 0.35 to 0.85 thousand lines.

## 6. GHCRTS

`env | grep GHCRTS` returned `GHCRTS=-M8g` at the start. I did not set
or raise the cap.

## 7. THE C-39 SECTION

Every prohibition was respected.

1. No master edited by me.
2. The probe is `src/ProbeLJ1124*.agda` only.
3. `src/Everything.lagda.md` was not opened.
4. `make check` was not run.
5. One Agda process ran at a time.
6. The heap cap was not raised.

The door worth naming is the same as `[LJ-1.123]` section 6. The
probe closes the graph decode. It does not build the chapter.

## 8. NEGATIVES AND THEIR STATUS

1. "The two directions close": MEASURED TRUE by the probe.
2. "The decode is tower-free": MEASURED TRUE on the statements. Every
   module states slots and site facts as parameters. It names no Def
   syntax and no concrete tower.
3. "The whole probe file is under 150 non-comment lines": MEASURED
   FALSE. It has 176 non-comment lines.
4. "The decode content is under 150 non-comment lines": MEASURED TRUE.
   It has 147 non-comment lines.

The negative in item 3 sets no verdict on the gate. The gate in the
brief is the decode content, not the import header.

## 9. DD4

The decode is tower-free.

`StepBridge`, `ApproxBridge` and `GraphBridge` are module-parameterized
in the leaf formulas, the slots and the environment. They name no
concrete `DefBodyB`, no concrete tower and no concrete carrier. The J
tower inherits the whole decode by instantiating its own leaf content
and site facts.

The final read and write against `Lset` use the shared `ride-only` and
`ride-defines`. Those are already tower-free.

## 10. GATES

Load averages beside every absolute figure are in section 2.

- `scripts/lint-agda.py --check src/ProbeLJ1124A.agda`: clean.
- `scripts/check-unbound-hyp.py src/ProbeLJ1124A.agda`: clean.
- `scripts/check-probes.py --check`: clean.
- `scripts/lint-prose.py --check`: run at the end on this report.
- `make check` not run.

## 11. ARCHIVE USED

- `_build/lj-1.123-report.md`, read WHOLE. Took the decode probe from
  section 3 and the assembly from section 2.
- `_build/lj-1.121-report.md`, read for the three facts.
- `src/ProbeLJ1121A.agda`, read WHOLE. Took the three fact statements.
- `_build/lj-1.12-report.md`, read for the inherited figure.
- `src/L/Condensation.lagda.md:2389-2493` and `:400-430`, read. Took
  the matrices and the unbounded decodes.
- `src/L/BoundedSubset.lagda.md:70-150`, read. Took `LevelHood`.
- `src/L/Coding/Sequence.lagda.md:217-301`, read. Took the machine step
  and approximation decodes.
- `src/L/Condensation.lagda.md:5939-5975`, read. Took `KFacts`.
- `src/L/Condensation.lagda.md:6366-6385` and `:6911-7033`, read. Took
  `DomainAgree` and `LeafAgree`.
- `dev/LESSONS.md` D-1, D-8, D-30, P-l, C-36, C-38, C-39, read WHOLE.

