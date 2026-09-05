# LJ-1.249 report: port `graph-assembly` to the class abstraction

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**STEP ZERO: exit code 0.** The archived probe is green today.
`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda` typechecks unported, 9.10 user
seconds, 10.06 real seconds, from its task directory with the include path set.

**THE PORT: IT PORTS.** `graph-assembly` typechecks at the `(M, M-trans)`
class abstraction. `agents/tasks/LJ-1-249/ProbeLJ1249.agda`, exit 0.

**So the chapter does NOT exist.** `[LJ-1.7]`'s gap is `StepAgree` and
`ApproxAgree` plus this port. This is the outcome the chain reached for. STOP.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run passed
20 minutes. No heap exhaustion.

| run | file | exit | user s | real s | load |
|---|---|---:|---:|---:|---|
| step zero, unported | `ProbeLJ152B.agda` | 0 | 9.10 | 10.06 | 5.05 / 5.64 / 4.89 |
| port, own module cold | `ProbeLJ1249.agda` | 0 | 1.67 | 1.82 | — |
| kept 1 | `ProbeLJ1249.agda` | 0 | 0.78 | 1.67 | 4.29 / 4.98 / 4.76 |
| kept 2 | `ProbeLJ1249.agda` | 0 | 0.79 | 0.89 | 4.11 / 4.93 / 4.74 |
| kept 3 | `ProbeLJ1249.agda` | 0 | 0.77 | 0.86 | 4.11 / 4.93 / 4.74 |

Step zero ran cold in its own module, deps warm. Its 9.10 s reads the heavy
`L.Condensation` / `L.BoundedSubset` / `L.Coding.Sequence` interface cone.
The port drops that cone, so its own cold-module run is 1.67 s. Mean of the
three kept warm runs: **0.78 user s**. The decision rests on exit codes, not
these seconds.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `agents/tasks/LJ-1-249/ProbeLJ1249.agda` | the class-generic port of `ProbeLJ152B`. Exit 0 |
| `agents/tasks/LJ-1-249/lj-1.249-report.md` | this report |

The port passes `scripts/lint-agda.py --check` and `scripts/lint-prose.py
--check`.

## 3. THE PORT, COUNTED

Caliber: non-blank lines. The file is a plain `.agda` file, so non-blank in
file equals non-blank in fence.

| block | non-blank code lines |
|---|---:|
| plumbing (telescope, imports, `GenModel`/`GenSequence` application, `Body` params) | 54 |
| BS templates (`extAtB`, `domB`, `StepB`, `ApproxB`, `GraphB`) | 47 |
| the assembly (`StepAgree`, `ApproxAgree`, `graph-assembly`) | 30 |
| **whole file** | **132 non-blank code, 165 non-blank, 194 physical** |

The 30-line assembly block is `ProbeLJ152B.agda:53-88` verbatim, with three
renames: `LH0.LH.G.S.stepBndAt → GB.S.stepBndAt`,
`LH0.LH.G.A.approxBndAt → GB.A.approxBndAt`,
`LH0.LH.G.graphBndAt → GB.graphBndAt`. The body of `graph-assembly` at
`ProbeLJ1249.agda:181-194` is the same `PT.rec` / `LsetGraph-in` body.

The 47-line BS templates are `src/L/Condensation.lagda.md:100-101`,
`:1746-1747`, `:2390-2425`, `:2465-2490` re-expressed at the generic carrier.
Their content is unchanged; the carrier swap is the whole change.

## 4. THE DD4 SPLIT, TESTED

**THE CLAIM HELD.** The assembly is carrier-generic. The port typechecks with
`graph-assembly` naming only `graphBndAt`, `LsetGraphAt`, `StepAt`,
`ApproxAt`, all of them instantiations of templates whose generic form exists.
MEASURED, exit 0.

The per-tower content enters as parameters and no more:

- the BS leaf `ψs : Formula S 13`, `ψa : Formula S 15` (the `DefBodyB`
  instantiations), at `ProbeLJ1249.agda:148-149`;
- the At leaf trio `DefAt` / `DefAt-in` / `DefAt-out`, at
  `ProbeLJ1249.agda:141-147`.

Both are constrained, not free: `ψs` and `ψa` determine
`GB.S.stepBndAt` / `GB.A.approxBndAt` / `GB.graphBndAt`, which occur in the
hypotheses `StepAgree` and `ApproxAgree`; `DefAt` occurs in the At formulas
`StepAt` / `ApproxAt` / `LsetGraphAt`. The concrete filling exists:
`ψs = DefBodyB {5} …`, `ψa = DefBodyB {7} …` from `LevelHood0`
(`src/L/BoundedSubset.lagda.md:840-849`), and the `DefAt` trio is supplied by
the ambient body (`agents/tasks/LJ-1-224/ProbeGraphSupply.agda:373, :531, :548`).
So the assembly is paid ONCE for both towers. The L-vs-ambient axis is
MEASURED. The L-vs-J axis stays INFERRED, the same caveat as
`agents/tasks/LJ-1-238/lj-1.238-report.md:113-118`: no `src/J/` exists and the
J tower's analogue is op-graphs, not satisfaction coding.

**No new hypothesis was introduced.** C-36: nothing had to be named that was
not already in the brief. The parameters are exactly the two per-tower leaves
the brief names (`DefBodyB`/`DefBody`), plus the delivered `DefAt` trio.

## 5. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the archived probe is red today | **MEASURED FALSE.** exit 0, section 0 |
| `graph-assembly` does not port to `(M, M-trans)` | **MEASURED FALSE.** `ProbeLJ1249.agda` exit 0 |
| the assembly spends `isL` | **MEASURED FALSE.** the body names no `isL`; `ProbeLJ1249.agda` imports `L.Constructible` only for `𝒟ₒ` |
| the assembly is paid once for both towers | **MEASURED TRUE** on the L-vs-ambient axis; **INFERRED** for L-vs-J, section 4 |
| the port needs a new hypothesis | **MEASURED FALSE.** only the two named per-tower leaves are parameters, section 4 |
| the port touches the Δ₀/Σ₁ gap | **MEASURED FALSE.** 0 references to `Δ₀`, `Σ₁`, `φP` in the port, section 7 |

## 6. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE. **Line read
  `:70`**, `graph-assembly`, the object ported.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read WHOLE. **Line read
  `:58`**, `matrix-decode`, the companion that closes `fst w ≡ Lset (fst γ)`.
- `agents/tasks/LJ-1-246/lj-1.246-report.md`, read WHOLE. **Line read `:204`**,
  the probe specification, passed through unchanged.
- `agents/tasks/LJ-1-244/lj-1.244-report.md`, read WHOLE. **Line read `:18`**,
  "`q'` does not build", the false chapter verdict this run overturns.
- `agents/tasks/LJ-1-244/ProbeLJ1244B.agda`, read WHOLE. **Line read `:68`**,
  the unconstrained `φ₀` parameter. My `ψs`/`ψa` are constrained; I did not
  repeat that shape.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read `:14-24` and the body.
  **Line read `:16`**, `(M-trans : Transitive (𝒮ᵥ {ℓ}) M)`, the abstraction
  re-pointed to.
- `src/L/Condensation.lagda.md`, read `:5433-5434` and the template blocks.
  **Line read `:5433`**, the comment naming `StepAgree`/`ApproxAgree`/
  `GraphAgree` as the gap.
- `agents/tasks/archive/LJ-1-52/lj-1.52-report.md`, read `:1-175`. **Line read
  `:63-64`**, the unbuilt content is `StepAgree` and `ApproxAgree`.
- `agents/tasks/LJ-1-238/lj-1.238-report.md`, read WHOLE. **Line read
  `:113-118`**, the ambient half marked INFERRED, which I carry.

## 7. LITERATURE USED (DD18)

I took the complexity-gap measurement from the brief and re-checked it.

- `src/L/Coding/Sequence.lagda.md`: `grep -c Δ₀` is **0**. The Sequence coding
  carries zero Δ₀ certificates. MEASURED.
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:194`: `crossOut : Σ₁ Cr.φP → …`.
  The crossing spends Σ₁. MEASURED.

**My port leaves that gap whole.** `ProbeLJ1249.agda` has 0 references to
`Δ₀`, `Σ₁`, `φP` or `Cr.`. The assembly transfers satisfaction, not complexity.
The certificates live in the leaves (`Δ₀-DefBodyB`, `Σ₁-levelHood`) and in the
per-tower leaf content `ψs`/`ψa`/`DefAt`, which this port parameterizes over
and does not build.

## 8. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. Step zero ran first. The
  branch that fired is **IT PORTS**. I report the lines and seconds and stop.
- D-10. The target is true: the assembly is generic, not a refutable
  telescope. `ψs` and `ψa` occur in the hypotheses they feed.
- P-l. 1.95 s is a comparable, not my price. My price is 1.67 s own-module
  cold, 0.78 s mean warm, MEASURED at this site.
- C-36. No term had to be named beyond the two per-tower leaves already in the
  brief.
- C-44. The brief's "the assembly is paid once" claim was unchecked. I checked
  it: exit 0.
- C-45. I audited the instantiation: `ψs`/`ψa`/`DefAt` are constrained, with a
  concrete filling, section 4.
- C-22. The report skeleton was written before the first run.
- C-12. One process, `-M8g`, cap never raised.
- DD4. Section 4: the assembly is carrier-generic, the leaves are the only
  per-tower content.
- DD8. One number per claim, each with its basis.
- DD18. Archive and literature sections above.
- I-5, R-34. No probe under `src/`. No heap wall.
