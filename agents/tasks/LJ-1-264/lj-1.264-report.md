# LJ-1.264 report: A5's row 1, the composition of two injections — builds, not dissolves

tier: pi (deepseek-subagent-mode). Probe task. No master edited. No commit,
no push. Written incrementally (C-22). ONE agda process at a time,
`GHCRTS="-A64m -I0 -M8g"`, cap never raised.

Every negative is marked **MEASURED** or **INFERRED**, in those words.

## 0. LEAD

**ROW 1 BUILDS. It does not dissolve. The composition of two injections is
160 lines at my site, exactly `[LJ-1.152]`'s figure, and it is needed: the
delivered `noinj²` clause of `InitialCore` still consumes it, and no
delivered route gives it.**

The composition survives through a site the two dissolutions did not touch.
`[LJ-1.247]` dissolved the column square, which was the composition's use in
the NON-INITIAL case. `[LJ-1.234]` closed the base at `ω`, where `noinj²` is
vacuous. **Neither dissolved `noinj²` itself.** `noinj²` is the square clause
of `Init` (`src/L/Ordinal/SquareLaw.lagda.md:705-707`), still a live
hypothesis of the delivered `InitialCore`, and its proof composes `sqβ ∘ f`
(`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:385-396`). That is a second site,
distinct from the column square, and the L-side composition is what supplies
it.

**Separation carries it, re-measured at my site.** My probe
`agents/tasks/LJ-1-264/ProbeLJ1264A.agda` is green, `--safe`, exit 0, one
`hasSeparationL` and zero `hasReplacementL` in code. Cold mean **2.79 s**
(three kept runs, load 5.8 to 6.2). The 160-line charge is re-derived, not
carried: `appC` 20 + `compFo` 41 + `Comp` 99.

**A5 stays 348.** Row 1 holds at 160, so 16 + 160 + 0 + 112 + 0 + 60 = 348.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **IT DISSOLVES.** Say so with evidence. A5 falls to 188. STOP.
- **IT BUILDS.** Report written lines against 160 and the seconds.
- **SEPARATION DOES NOT CARRY IT.** Say what does (C-36).
- **MATERIALLY OVER 160.** Report both figures.
- **A WALL.** One `agda` invocation past 20 minutes is a wall.

**VERDICT: IT BUILDS.** No other branch was reached. No wall, no heap
exhaustion.

## 2. THE DISSOLUTION QUESTION, ASKED AND ANSWERED

The question: does anything demand the composition as its own object, or
does a delivered route give it?

**ANSWER: something demands it. The `noinj²` clause. A delivered route gives
the other site and not this one.**

The composition object has TWO sites in the chain. Site A is the column
square, `pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))`
(`ProbeLJ1156A.agda:496-497`), the non-initial transfer. Site B is `noinj²`,
the square clause, whose proof is `h m = sqβ .fst (f m)` — the composite of
the given injection `f : ⟪α⟫ → ⟪β⟫ × ⟪β⟫` with the induction pairing
`sqβ : ⟪β⟫ × ⟪β⟫ → ⟪β⟫` (`ProbeLJ1156A.agda:385-396`).

- **Site A dissolved.** `[LJ-1.247]` measured that the delivered
  `via-col-square` builds `sq α` directly at every initial ordinal, so the
  non-initial successor step is gone.
- **Site B did not dissolve.** `noinj²` is still a hypothesis of the
  delivered `InitialCore` (`SquareLaw.lagda.md:705-707`), and it is the
  cardinality clause that makes `Init α` say "α is initial". Nothing
  delivered supplies it: the L-side composition (`compFo`/`Comp`/`appC`) is
  in NO delivered `src/` file. **MEASURED** by grep, zero hits.

The archived route confirms the same site B. Its `no-inj-down` composes
`comp m = k (comp₀ p e m)` (`archive/src/2026-08-09-rud-route/L/Ordinal/
SquareLaw.lagda.md:470-479`), the square-law pairing applied to the collapse.
The composition is the mechanism that turns an injection into a square into
an injection into a smaller ordinal, which is what the leastness refutation
consumes.

**Why the L-side form and not the 8-line metatheoretic one.** The metatheoretic
composite `sqβ ∘ f` costs eight lines in the ambient chain. Route A-prime
restates the chain over L-injections: `[LJ-1.136]` section 3.2 measured that
the leastness refutation is L-leastness, so the refuting injection must be an
L-element. A4's internal cardinal refutes L-codes, `InjCode F κ δ`
(`ProbeLJ1236A4.agda` S2), not metatheoretic functions. So the composite must
be an L-code, and that is row 1. **INFERRED** from the measured shapes; the
shapes themselves are measured.

## 3. THE MEASUREMENTS

**The probe.** `agents/tasks/LJ-1-264/ProbeLJ1264A.agda`. It is
`[LJ-1.152]`'s `ProbeLJ1152E.agda` re-sited, with its one broken dependency
fixed: `ProbeLJ1134A` now lives under `agents/tasks/LJ-1-134/`, so its
top-level module name no longer resolves, and I inlined the four pieces the
composition needs (`injAt`, `Extract`, `Small`, `Concrete`) instead of
importing them. **MEASURED**: the original file fails today with
`[FileNotFound] Failed to find source of module ProbeLJ1134A`.

**The lines, re-derived at my site** (non-blank non-comment, the caliber
`[LJ-1.152]` and `[LJ-1.176]` used):

| part of `ProbeLJ1264A.agda` | lines | class |
|---|---:|---|
| header and imports | 39 | header, paid once by a master |
| inlined `injAt` + `Extract` + `Small` + `Concrete` | 125 | A2's readback content, not A5's charge |
| **`appC` and its adequacy** | **20** | **the composition charge** |
| **`compFo` and `CompFo`** | **41** | **the composition charge** |
| `PairBound` | 38 | the bound; a master uses the shared `StageBound` (16) |
| **`Comp`, four conjuncts and readback** | **99** | **the composition charge** |
| `Witness` + `WitnessZero` | 16 | probe-only C-38 guard, does not ship |

**The composition charge is 20 + 41 + 99 = 160 lines.** It equals
`[LJ-1.152]`'s figure at its site, re-derived here rather than carried (P-l).

**The seconds, with load and run count.** Machine: 16 cores, 64 GB, macOS,
Agda 2.8.0. All runs cold (the interface was deleted before each), one agda
process, `GHCRTS="-A64m -I0 -M8g"`. No sibling agda process was running.
Warm-up discarded, three kept.

| run | cold seconds | exit | 1-minute load at start |
|---|---:|---:|---:|
| warm-up (discarded) | 3.76 | 0 | — |
| kept 1 | 2.78 | 0 | 6.17 |
| kept 2 | 2.76 | 0 | 6.17 |
| kept 3 | 2.82 | 0 | 5.84 |
| **cold mean** | **2.79** | 0 | 5.8 to 6.2 |

**No wall, no heap exhaustion, no postulate, no hole, no `trustMe`.**
`hasReplacementL` appears only in comments (four times). `hasSeparationL`
appears once in code, at `ProbeLJ1264A.agda:460` (its `K-spec` at `:464` is
the same call's second projection). **Separation carries it.**

## 4. TOWER ANSWER (DD4)

**Axis named: Def against J (Devlin's), not L against ambient.**

The composition's STATEMENT — the composite of two injections is an
injection — names no tower atom. Its L-internalization carries exactly two
tower-specific names: the separation field (`hasSeparationL`, one call) and
the stage-bound device (`stage`/`boundingOrd`/`LsetS`, inside `PairBound`,
38 lines, which a master replaces with the shared `StageBound`, 16).
`[LJ-1.152]` section 7 measured that these two are the only L-names, and that
both can be taken as module parameters, so the J tower re-instantiates the
whole 160 lines rather than rewriting them.

**On the Def-against-J axis the composition is tower-neutral in shape,
modulo two parameterized names.** On the L-against-ambient axis it is NOT
neutral: it is L content (`S`, `⟪_⟫`, `hasSeparationL`, `stage`). The DD4
question for this object lives on the first axis, and there it is shared.

## 5. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-247/lj-1.247-report.md`, read WHOLE.** TAKEN: A5 = 348
  and the column-square dissolution. One line: section 2, "the consumer never
  asks for an L-element; it asks for a metatheoretic injection".
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`, read WHOLE.** TAKEN: the
  160 split at `:214-224` (`appC` 20, `compFo` 41, `PairBound` 38, `Comp` 99)
  and the GO at 2.50 s.
- **`agents/tasks/LJ-1-234/lj-1.234-report.md` and `ProbeLJ1234A.agda`, read
  WHOLE.** TAKEN: the dissolution method and the 60-line base at `ω`.
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, read WHOLE.** TAKEN: the fork
  the other way — A2's range set needed replacement, separation did not carry
  it.
- **`src/L/Ordinal/SquareLaw.lagda.md:685-687, :705-707, :960-961`, read in
  the source.** TAKEN: the consumer's obligation `sq`, the live `noinj²`
  hypothesis, and the delivered order route.
- **`archive/dev/TASKS-archived.md:82`.** TAKEN: L3.32-T47 "Truncated square
  law at initial ordinals — DELIVERED".
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:470`.**
  TAKEN, SHAPE ONLY: `no-inj-down` composes `comp m = k (comp₀ p e m)`, the
  same site-B composition. **WHAT WOULD NOT TRANSFER: the line counts (P-l),
  and the whole internalization route, which the seven-block A-prime route
  replaced.**

## 6. LITERATURE USED (DD18)

- **`dev/literature/rudimentary-functions.md:68`.** TAKEN: the basis list
  gives `F2(x, y) = x × y` (the product) and `F9(x, y) = <x, y>` (the ordered
  pair) outright. **It requires only the injection (the product and the
  pairing), not a composition of two injections as its own object.** No basis
  function is a successor-step composition of injections; the composition is
  a construction of the route, not a requirement of the literature basis.
  **MEASURED**: zero hits in that file for any composition-of-injections
  basis entry.

## 7. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The composition does not dissolve.** `noinj²` is a live
  hypothesis at `SquareLaw.lagda.md:705-707`, and the L-side composition is
  in no delivered `src/` file (grep, zero hits).
- **MEASURED. The composition builds green.** `ProbeLJ1264A.agda`,
  `--safe`, exit 0.
- **MEASURED. The charge is 160 lines.** 20 + 41 + 99, re-derived at my site.
- **MEASURED. Separation carries it.** One `hasSeparationL` in code, zero
  `hasReplacementL` in code.
- **MEASURED. Cold mean 2.79 s.** Three kept runs at load 5.8 to 6.2.
- **MEASURED. The original `[LJ-1.152]` probe is stale today.** Its
  `ProbeLJ1134A` import fails with `[FileNotFound]`.
- **INFERRED. The composition is needed at site B (`noinj²`) specifically.**
  The site is measured (`ProbeLJ1156A:385-396`, archived `:470`); that the
  L-internalized chain consumes an L-code composite there is my judgement
  from the measured A4 shape.
- **INFERRED. Tower-neutral on the Def-against-J axis.** The two L-names are
  measured; that they are parameterizable is `[LJ-1.152]` section 7's
  reading, re-affirmed here.

## 8. WORKING TREE

Two files in `agents/tasks/LJ-1-264/`:

| file | state |
|---|---|
| `ProbeLJ1264A.agda` | green, `--safe`, exit 0, 378 non-blank non-comment lines whole, 160 charge, 2.79 s cold mean |
| `lj-1.264-report.md` | this file |

No master edited. No file under `src/` edited. No commit, no push, no
`git checkout .`/stash/reset/clean. No `make check`; the orchestrator runs
it. ONE agda process at a time, cap never raised.
