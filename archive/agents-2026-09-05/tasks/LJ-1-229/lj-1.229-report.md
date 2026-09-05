# LJ-1.229 report: A2's range set and `ranAt`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe only. No
master edited. No commit, no push.

The probe is `agents/tasks/LJ-1-229/ProbeLJ1229A.agda`. It is tracked, never
deleted. It typechecks green: `--safe`, exit 0.

Every negative is marked MEASURED (a machine result, or read at the cited
line) or INFERRED (my judgement). ASD-STE100 applies to this report.

## 0. LEAD: TWO NUMBERS

**A2's measured written lines: 186 non-comment code lines.** The standing is
170. A2 builds 16 lines over standing, which is 9.4 percent. That is not
material. The two range pieces are the whole overage. Section 1 and section 2.
The 186 counts definitions only, in the caliber of the 78-line core. It does
not count the import block, which the probe carries separately at 32 lines.

**The description plus adequacy: 27 non-comment code lines.** That is the
`injAt` row, `injAt` plus `injAt-out` plus `injAt-in`. A4 consumes those 27
lines and not the readback. The readback is 51 lines, `Extract` plus `Small`.
The 27-to-78 range closes at 27. The corrected A-prime sum is **1,521**, not
1,470 to 1,521. Section 3.

## 1. THE RANGE SET

**BUILT. MEASURED.** The range set C is produced by `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:277`) over the graph. Agda accepts it under
`--safe`.

The construction is section S3 of the probe. It has three parts.

1. `rangeGraph` (`ProbeLJ1229A.agda:152-153`). The graph F, read with the
   value first and the argument second, as `hasReplacementL` wants. It is
   `∃̇∈ (con F) (prAtL zero (suc (suc zero)) (suc zero))`.
2. `rangeGraph-adequate` (`ProbeLJ1229A.agda:155-175`). The two directions.
   Forward reads the pair out of the graph. Backward builds the witness with
   `prʟ` and `prʟ-fst`.
3. `Range` (`ProbeLJ1229A.agda:179-211`). It proves `funct`, the
   functionality `hasReplacementL` demands, from `domAt-in` and `svAt-out`.
   It then applies `hasReplacementL` once and takes the centre. The result is
   C with its specification `C-mem`.

**The range set is 45 non-comment code lines.** In the ledger caliber, which
counts comments, it is 53 non-blank lines.

**Replacement was needed. Separation does not carry it. INFERRED from the
shape.** The range collects the values of the graph. Those values have no
pre-existing superset. A separation would need a superset, and no superset
exists before the stage-bound argument that `hasReplacementL` makes. So
`hasReplacementL` is the right tool. It elaborated green at my site. MEASURED.

**The discharge is 20 non-comment code lines** (section S5,
`ProbeLJ1229A.agda:256-285`). It proves C satisfies `ranAt`. This is where
`[LJ-1.134]`'s "every value lies in C" hypothesis is supplied, not assumed
(C-38 as extended).

## 2. `ranAt`, MIRRORING `domAt`

**BUILT. MEASURED.** `ranAt` is the mirror of `domAt`
(`src/L/Coding/Model.lagda.md:278`). Section S4 of the probe
(`ProbeLJ1229A.agda:214-255`).

- `inRanAt` (`:217-218`): "there is an argument whose value is this".
- `inRanAt-adequate` (`:220-224`): the existential reading.
- `ranAt` (`:226-229`): "c is the range of f", the two implications under one
  quantifier, exactly the shape of `domAt`.
- `ranAt-out`, `ranAt-in`, `ranAt-intro` (`:231-255`): the two adequacy
  readings and the introduction, each the mirror of its `domAt` counterpart.

**`ranAt` is 31 non-comment code lines.** In the ledger caliber it is 34
non-blank lines.

The two adequacy readings are `ranAt-out` (a value of the graph lies in the
range) and `ranAt-in` (a member of the range is a value at some argument). The
second is truncated, exactly as `domAt-in` is.

## 3. DESCRIPTION PLUS ADEQUACY, APART FROM READBACK

The probe separates the pieces `[LJ-1.227]` could not split by reading.

| piece | lines | what it is |
|---|---:|---|
| S1 `injAt`, `injAt-out`, `injAt-in` | **27** | the description plus the adequacy conjuncts |
| S2 `Extract` | 29 | readback, first half: `toFun`, `toFun-inj` |
| S6 `Small` | 22 | readback, second half: the small index types |

**A4 consumes S1 and nothing else.** A4 states "g is an injective graph from
a to b". That needs `svAt`, `domAt`, `valuesInAt`, all delivered in
`L.Coding.Model`, and `injAt` with its two directions. It does not need the
readback, the range set, or `ranAt`. MEASURED by reading the pieces; INFERRED
that A4 needs only S1.

**The double-count is 27, one number.** The corrected A-prime sum is
1,548 minus 27, which is **1,521**. The 27-to-78 band is closed. The three
documents that carry the band can now carry one figure.

The core still measures 78: S1 plus S2 plus S6 is 27 plus 29 plus 22.

## 4. SECONDS, LOAD, RUN COUNT

**The whole probe: mean 1.64 s, upper bound 1.81 s.** Three kept runs, one
warm-up discarded.

| run | wall seconds | 1-minute load |
|---|---:|---|
| warm-up (discarded) | 1.61 | not recorded |
| first | 1.81 | 4.73 |
| second | 1.60 | 4.73 |
| third | 1.51 | 4.73 |

**Load: 4.73, one-minute average, before each kept run.** No sibling agda
process was running when I checked at the end. MEASURED by `ps`.

**The figure is not a cold-tree figure.** Only `Checking LJ-1-229.ProbeLJ1229A`
appeared. No `Checking L.Coding.Model` and no `Checking L.Axioms.Full`. The
probe re-checks only its own file against cached interfaces. The 254 s figure
for `hasReplacementL` (`agents/tasks/LJ-1-136/lj-1.136-report.md:1059`) is the
cold cost of the `L.Axioms.Full` master. That master is delivered and cached.
At my site, `hasReplacementL` is a black box from the interface, and the call
site costs about 1.6 s. P-l: 254 s is a comparable at another site, not my
price.

One agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no heap
exhaustion, no wall. C-12 honoured.

## 5. TOWER-NEUTRALITY (DD4)

**Both the range set and `ranAt` stayed tower-neutral. MEASURED.**

The new code names no `Lset`, no `stage`, no `sucV`, no numeral, no order. The
only `isL` appearances are the S-carrier equality lift
`Σ≡Prop (λ z → snd (isL z))`, one new line at `ProbeLJ1229A.agda:197` inside
`funct`. That lift is the generic level-hood-Ω lift the coding chain already
carries. It works for any tower whose carrier is a sigma over its level-hood
predicate. It is not a reach for an L stage.

`ranAt` itself names only `appAt`, the quantifiers and the atoms. It has no
tower content at all.

So A2 stays tower-neutral from its first line, as `[LJ-1.227]` section 8
ruled. The range set and `ranAt` add nothing per-tower.

## 6. ABORT CRITERION, HONOURED

The criterion was fixed before the run. D-1.

**BOTH RANGE PIECES BUILD.** Exit 0, `--safe`. The range set is 45 lines and
`ranAt` is 31 lines. A2 is measured at 186 non-comment lines against 170.

**The overage is 16 lines, 9.4 percent, not material.** I report both numbers
and let the orchestrator rule. The original band for A2 was 120 to 220
(`agents/tasks/LJ-1-134/lj-1.134-report.md:368`). 186 sits inside that band.

**Replacement was not a wall.** `hasReplacementL` over the graph elaborates.
Separation does not carry it, and the question is answered: replacement was
needed.

**No wall.** No single agda invocation ran past 20 minutes. The whole probe is
under 2 seconds.

**The double-count is split.** 27 description plus adequacy, 51 readback.

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`, whole.** TAKEN: the two
  deliverables at section 2 and section 7.1; the 27-to-78 floor and ceiling;
  the corrected 1,470 to 1,521.
- **`agents/tasks/LJ-1-134/lj-1.134-report.md`, whole.** TAKEN: the 78-line
  core at `:219-227`; the two unpriced range pieces at `:177-180`; the
  per-part table.
- **`agents/tasks/LJ-1-134/ProbeLJ1134A.agda`, whole.** TAKEN: S1, S2 and S6
  are copied from it unchanged. That is the starting file.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`**, the cited lines. TAKEN: the
  254 s `hasReplacementL` figure at `:1059`; the A4 consumption claim at
  `:359-368`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`**, the cited lines. TAKEN: the
  separation-carries-it question. The answer at my site is no.
- **`src/L/Axioms/Full.lagda.md:277` and `src/L/Coding/Model.lagda.md:278`.
  READ, never a report.** TAKEN: the exact `hasReplacementL` signature and the
  exact `domAt` shape that `ranAt` mirrors.
- **`archive/dev/TASKS-archived.md` and
  `archive/src/2026-08-09-rud-route/`.** READ for shape. `grep` for `ranAt`
  and `inRanAt` returns zero hits in the archive. The retired route holds the
  same `hasReplacementL` (`archive/src/2026-08-09-rud-route/L/Axioms/Full.lagda.md:277`)
  but no range set. What would NOT transfer: the rud route reached its trophy
  through the `L/Rud/*` closure machinery and never needed a coding-layer
  `ranAt`. There is no archive shape to copy. The natural shape, `ranAt`
  mirroring `domAt`, is what I wrote.

## 8. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  two objects. A2 is neither.
- **`dev/literature/devlin-II5.md:145-171`.** USED. The GCH chain is 5.5 and
  5.6. Devlin shows `𝒫(κ) ⊆ L_{κ⁺}` and `|L_{κ⁺}| = κ⁺`, so `|𝒫(κ)| ≤ κ⁺`.

**Devlin's proof does not need a range set at this point.** It takes the range
for granted. His cardinal comparison is subset containment and level size, not
an internalized injection. It never writes `⟪κ⟫ ↪ ⟪δ⟫`. The range set is
A-prime's own machinery, because A-prime states the square law through internal
injections. So Devlin gives no shape for the range set. That is the reason the
archive also holds none.

## 9. THE NEGATIVES, CLASSIFIED

- **MEASURED. The range set builds.** `--safe`, exit 0.
- **MEASURED. `ranAt` builds.** `--safe`, exit 0.
- **MEASURED. A2 is 186 non-comment lines against 170.** 16 over, 9.4
  percent.
- **MEASURED. The description plus adequacy is 27 lines.** The readback is 51.
- **MEASURED. The corrected A-prime sum is 1,521.** 1,548 minus 27.
- **MEASURED. The whole probe checks in 1.81 s upper bound.** Three kept runs,
  load 4.73.
- **MEASURED. The range set and `ranAt` stayed tower-neutral.**
- **INFERRED. A4 consumes only the 27 description-plus-adequacy lines.** The
  split is measured; that A4 needs only that half is my reading of A4's
  statement.
- **INFERRED. 186 is not material over 170.** It is a judgement. The original
  band was 120 to 220.

## 10. WORKING TREE, AS MY REPORT DESCRIBES IT

Two files added: `agents/tasks/LJ-1-229/ProbeLJ1229A.agda`, this probe, and
`agents/tasks/LJ-1-229/lj-1.229-report.md`, this report. No master edited. No
commit, no push. `scripts/lint-agda.py --check` and
`scripts/lint-prose.py --check` both exit 0.
