# LJ-1.224 report: is `[LJ-1.220]`'s exit 0 bought? All 22 parameters checked

tier: opus (deepseek-subagent-mode). The switch's ADVERSARIAL row. The target was
written by pi, so the critic is not the author. Written incrementally (C-22). No
master edited. No commit, no push. Every negative is MEASURED or INFERRED, in
those words.

## 0. LEAD

**22 of 22 parameters are FAITHFUL. The exit 0 SURVIVES. The review AGREES with
`[LJ-1.220]` on soundness.**

**But the width is wrong, and it is wrong in `[LJ-1.220]`'s favour.** Three
parameters are SUPPLYABLE, the class the orchestrator added mid-run. **The
corrected width is 8 modules and 19 names, not 9 and 22.** MEASURED by run 2.

- **(a) FAITHFUL: 22 of 22.** Every parameter's type is the delivered signature
  with one substitution only: the carrier `𝒮ʟ = 𝒮ᵥ ↾ isL`
  (`src/L/Constructible.lagda.md:411`) replaced by `𝒮ᵥ ↾ M` with `M` trivial.
  No hypothesis is missing. No `Σ` or `∥ ∥₁` moved. No implicit became explicit.
  No quantifier scope moved. MEASURED, row by row, in section 3.
- **(b) THE FIVE RECONSTRUCTIONS ARE SOUND, all five.** Each is
  character-for-character the delivered definition. The reduction the body
  needs, `fst (keyS A φ)` to `pr (# n) (fst (codeS A φ))`, holds in the
  DELIVERED code too, because `key {n} φ = pr (# n) VCode.⌜ mapFo f φ ⌝` at
  `src/L/Coding/InL.lagda.md:253`. **No reconstruction reduces more than the
  delivered name.** MEASURED, in section 4.
- **(c) THE BODY IS THE DELIVERED BODY.** 8 lines differ out of 338 non-blank,
  and all 8 are the carrier substitution. MEASURED, in section 5.
- **(d) SUPPLYABLE: 3 of 22.** Rows 7, 8 and 9. `GenGraph.agda` supplies them at
  the ambient class and the body still exits 0. **Two of the five
  reconstructions, `GraphWitAt` and `twelveAt`, are supplied by the same file
  and were never reconstructions either.** MEASURED by run 2.

**The exit 0 is not bought. The census that rests on it overstates the remaining
port by one module and three names.**

**One caveat, reported apart in section 6b:** the `tt*` in `codeS` and `keyS` is
free at the ambient class and is `codeL` and `keyL` at a real tower. **It is not
a hidden hypothesis**, because the class telescope `GenModel.agda:13-23` already
carries what derives it, **but the generic `CodeSet` port must carry that
induction as code, and no figure here prices it.** INFERRED.

## 1. MACHINE AND PROCESS DISCIPLINE

One Agda process at a time. `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised.
No run passed 20 minutes. No heap exhaustion. Two runs, both exit 0.

The machine is not quiet. Load sits beside every absolute figure.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `Probe.agda` | byte copy of `agents/tasks/LJ-1-220/Probe.agda`, module renamed only. The baseline. Exit 0 |
| `ProbeGraphSupply.agda` | the same file with rows 7, 8, 9 and the `GraphWitAt` and `twelveAt` reconstructions taken from `LJ-1-210.GenGraph` instead. 19 parameters. Exit 0 |
| `lj-1.224-report.md` | this report |

I did not edit `agents/tasks/LJ-1-220/Probe.agda`. I copied it first. Nothing
lands in `src/`. No master, brief or report of another agent was changed.

## 3. THE 22 PARAMETERS, one row each

**The test applied to every row: open the delivered signature at its
`file:line`, and accept only the carrier as a difference.** Where the delivered
name sits inside a module telescope, the probe hoists the telescope to explicit
arguments; I checked the telescope in every such case, because a dropped
telescope hypothesis is the defect that would buy the exit 0.

| # | name | delivered at `file:line` | verdict |
|---|---|---|---|
| 1 | `keyArityAtL` | `src/L/Coding/CodeSet.lagda.md:135` | FAITHFUL |
| 2 | `keyArityAtL-in` | `src/L/Coding/CodeSet.lagda.md:145` | FAITHFUL |
| 3 | `keyArityAtL-out` | `src/L/Coding/CodeSet.lagda.md:138` | FAITHFUL |
| 4 | `hasWitnessAt` | `src/L/Coding/CodeSet.lagda.md:240` | FAITHFUL |
| 5 | `witnessAt-in` | `src/L/Coding/CodeSet.lagda.md:365` | FAITHFUL, telescope `(A : S)` at `:286` hoisted |
| 6 | `witnessAt-out` | `src/L/Coding/CodeSet.lagda.md:375` | FAITHFUL, same telescope |
| 7 | `satGraphAt` | `src/L/Coding/Graph.lagda.md:204` | FAITHFUL, and **SUPPLYABLE** |
| 8 | `graphAt-in` | `src/L/Coding/Graph.lagda.md:210` | FAITHFUL, and **SUPPLYABLE** |
| 9 | `graphAt-out` | `src/L/Coding/Graph.lagda.md:215` | FAITHFUL, and **SUPPLYABLE** |
| 10 | `keyʟ` | `src/L/Coding/Table.lagda.md:82` | FAITHFUL |
| 11 | `Sat` | `src/L/Coding/Sat.lagda.md:142` | FAITHFUL, telescope `(B : S)` at `:139` hoisted |
| 12 | `slot` | `src/L/Coding/Table.lagda.md:106` | FAITHFUL, telescope `(B : S)` at `:85` hoisted |
| 13 | `satTable` | `src/L/Coding/Table.lagda.md:103` | FAITHFUL, same telescope |
| 14 | `total` | `src/L/Coding/Table.lagda.md:277` | FAITHFUL, same telescope |
| 15 | `inSlot` | `src/L/Coding/Table.lagda.md:287` | FAITHFUL, same telescope |
| 16 | `entry-in` | `src/L/Coding/Table.lagda.md:321` | FAITHFUL, same telescope |
| 17 | `slotClosed` | `src/L/Coding/Slot.lagda.md:262` | FAITHFUL, see the note below |
| 18 | `soundness` | `src/L/Coding/Sound.lagda.md:1099` | FAITHFUL, see the note below |
| 19 | `asConst` | `src/L/Coding/Bridge.lagda.md:124` | FAITHFUL, telescope `(B : S)` at `:116` hoisted |
| 20 | `defSet-Sat` | `src/L/Coding/Bridge.lagda.md:621` | FAITHFUL, see the note below |
| 21 | `keyBridge` | `src/L/Coding/Uniform.lagda.md:180` | FAITHFUL, telescope `(A : S)` at `:179` hoisted |
| 22 | `pinned` | `src/L/Coding/Unique.lagda.md:884` | FAITHFUL, see the note below |

**Row 17, `slotClosed`.** The delivered type is `⟨ δ ⊨ closedAt Ci ⟩` with
`δ = B ∷ satTable B φ ∷ Sl φ ∷ γ` at `src/L/Coding/Slot.lagda.md:112` and
`Ci = suc (suc zero)` at `:115`. `Sl` is not a separate slot operator: `Sl =
slot B` at `src/L/Coding/Slot.lagda.md:76-77`, and `slot` is Table's, imported
at `:42`. So the probe's `(B ∷ satTable B φ ∷ slot B φ ∷ γ)` is the delivered
`δ`. MEASURED.

**Row 18, `soundness`.** The delivered return type at
`src/L/Coding/Sound.lagda.md:1099-1105` is the 12-way product written out, NOT
`⟨ δ ⊨ twelveAt ... ⟩`. The probe's `Clauses` is that product, in the same order
and the same right-nesting. Its environment `δ = B ∷ satTable B φ ∷ slot B φ ∷
γ` is at `:357` and `Ci Ti Bi = 2, 1, 0` at `:360-362`. The enclosing telescope
is `module _ (B : S) {n : ℕ} (φ : Formula S n) {k : ℕ} (γ : S ^ k)` at `:354`,
which the probe hoists exactly. **No nested module adds a hypothesis between
`:354` and `:1099`.** MEASURED by listing every nested module in that span; all
are frames such as `Un`, `Bin` and `Atom`, and `soundness` sits at the outer
indent.

**Row 20, `defSet-Sat`.** This row needed the most work, because the delivered
statement and the probe's look different. Delivered at
`src/L/Coding/Bridge.lagda.md:621-623`:
`(⟪ fst B ⟫↪ m ∈ DB.defSet ψ) ≡ (envS B (λ _ → m) ∈ˢ Sat B (mapFo asConst ψ))`.
The probe writes the right side as
`envOne (⟪ fst A ⟫↪ m) ∈ fst (Sat A (mapFo (asConst A) ψ))`. **The two are the
same proposition, and the difference is two unfoldings.** First, `_↾_` defines
`_∈ˢ_ = λ a b → fst a ∈ˢ fst b` at `src/FOL/ZFStructure.lagda.md:149`, so `∈ˢ`
at this carrier IS membership on the first components. Second,
`envS g = env (λ i → fst (ix (g i))) , envSL g` at
`src/L/Coding/EnvSet.lagda.md:154` and `ix m = ⟪ fst B ⟫↪ m , ...` at `:122-123`,
so `fst (envS B (λ _ → m))` reduces to `env (λ _ → ⟪ fst B ⟫↪ m)`, which is the
probe's `envOne (⟪ fst A ⟫↪ m)` at `Probe.agda:90-91`. **FAITHFUL. MEASURED.**

**Row 22, `pinned`.** The delivered type at
`src/L/Coding/Unique.lagda.md:884` is `Closed → Total → Clauses → ∀ {m} (ψ) →
Pinned ψ`, four abbreviations inside `module Good {k : ℕ} (γ : S ^ k) (Ci Ti Bi
: Fin k)` at `:104`. Each unfolds to exactly what the probe writes:
`Closed = ⟨ γ ⊨ closedAt Ci ⟩` at `:111-112`; `Total = ⟨ γ ⊨ domAt Ti Ci ⟩` at
`:114-115`; `Clauses` at `:880-882` is the same 12-way product in the same
order, whose twelve components are defined at `:117-151`; and
`Pinned {m} ψ = (c y : S) → fst c ≡ fst (keyʟ ψ) → ⟨ fst c ∈ fst C ⟩ → ⟨ pr (fst
c) (fst y) ∈ fst T ⟩ → fst y ≡ fst (Sat B ψ)` at `:186-190`, with `B = lookup Bi
γ`, `C = lookup Ci γ`, `T = lookup Ti γ` in `Good`'s private block. The argument
ORDER is the delivered order: `ψ` before `c` and `y`. **FAITHFUL. MEASURED.**

**No row is WEAKENED. No row is STRONGER.** MEASURED, by the comparison above.

**One shape I hunted and did not find.** The brief warns that an opaque
parameter standing for a delivered definition WITH a reduction gives the body
its definitional steps free. **That defect cannot occur in this direction.** A
parameter is opaque to the body, so the body proves MORE, not less: a proof from
an abstract `keyʟ` still typechecks when the real `keyʟ` is substituted. The
danger is the opposite direction, a RECONSTRUCTION that reduces where the
delivered name does not, and that is section 4. **Rows 10, 11 and 12 are the
rows where a delivered transparent definition became an opaque parameter**
(`keyʟ` at `Table.lagda.md:83`, `Sat` at `Sat.lagda.md:143`, `slot` at
`Table.lagda.md:107`), and in all three the body never unfolds the name. This
makes the probe's result stronger than the delivered setting needs, not weaker.
MEASURED.

## 4. THE FIVE RECONSTRUCTIONS, each judged

**All five are SOUND. None reduces more than the delivered name.** This was the
brief's likeliest defect and it is not there.

| # | reconstruction | delivered at `file:line` | verdict |
|---|---|---|---|
| R1 | `codeS` | `src/L/Coding/CodeSet.lagda.md:297-298` | SOUND |
| R2 | `keyS` | `src/L/Coding/CodeSet.lagda.md:300-301` | SOUND |
| R3 | `Clauses` | `src/L/Coding/Sound.lagda.md:1099-1105` | SOUND |
| R4 | `twelveAt` | `src/L/Coding/Graph.lagda.md:94-101` | SOUND, and **SUPPLYABLE** |
| R5 | `GraphWitAt` | `src/L/Coding/Graph.lagda.md:141-146`, `:191-192` | SOUND, and **SUPPLYABLE** |

**R1 and R2 carry the whole risk, and they are clean.** The delivered
`codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ` has first component
`VCode.⌜ mapFo ι φ ⌝` with `ι = ⟪ fst A ⟫↪` at `CodeSet.lagda.md:288-289`. The
probe writes `codeS A φ = VCode.⌜ mapFo ⟪ fst A ⟫↪ φ ⌝ , tt*`. **The first
components are the same term; only the constructibility certificate becomes
`tt*`, which IS the carrier swap.**

The delivered `keyS φ = key ι ιL φ , keyL ι ιL φ`, and **`key {n} φ = pr (# n)
VCode.⌜ mapFo f φ ⌝` at `src/L/Coding/InL.lagda.md:253`**. So the delivered
`fst (keyS A φ)` ALREADY reduces to `pr (# n) (fst (codeS A φ))`. The probe
writes that reduction as its definition. **The body's definitional step is not
free in the probe and paid in the delivered code; it is free in both.**
MEASURED. **Neither `key` nor `keyS` is sealed:** `InL.lagda.md` has no `opaque`
or `abstract` at all, and `CodeSet.lagda.md`'s only `opaque` is at `:439`, after
both definitions.

**R3.** The probe's `Clauses` is the delivered `soundness` return type verbatim
(`Sound.lagda.md:1099-1105`) and the delivered `Good.Clauses`
(`Unique.lagda.md:880-882`) unfolded through its twelve abbreviations. Nothing
was made easier to produce. MEASURED.

**R4 and R5.** The probe's `twelveAt` is `Graph.lagda.md:94-101`
character-for-character. The probe's `GraphWitAt` is `GraphWitOn` at
`Graph.lagda.md:141-146` with `W := lookup B γ`, which is exactly
`GraphWitAt B x y γ = GraphWitOn (lookup B γ) x y γ` at `:191-192`, with
`Ci Ti Bi` expanded to `suc (suc zero)`, `suc zero`, `zero` per `:86-89`.
MEASURED.

**A note that strengthens `[LJ-1.220]` rather than weakening it.** The delivered
`satGraphAt` is itself `opaque` (`Graph.lagda.md:203`, sealed under P-t with a
2,459 ms measurement in the comment at `:194-202`). **So keeping it an opaque
parameter is not an approximation; it is the delivered behaviour.** The probe
made the right call there.

## 5. THE BODY IS THE DELIVERED BODY

**MEASURED, and this closes the brief's fourth abort branch.** I extracted every
in-fence line of `src/L/Coding/Powerset.lagda.md:120-700` and compared it with
`Probe.agda:90-94` plus `:200-596` dedented by two.

**338 non-blank lines on each side. 8 lines differ. Every one is the carrier.**

| delivered | probe | count |
|---|---|---:|
| `isL-trans` | `M-trans` | 5 |
| `snd (isL u)` | `snd (M u)` | 1 |
| `⟨ isL x ⟩` in `DefOK` | `⟨ M x ⟩` | 1 |
| `Good.pinned` | `pinned` | 1 |

The eighth is not a carrier swap but the parameterization itself: the delivered
body calls `Good.pinned` with the module applied, and the probe calls the
parameter with the same four arguments in the same order. **No line moved. No
proof step was rewritten. A rewritten body would prove nothing about the
delivered one, and this body was not rewritten.** MEASURED.

## 6. THE SUPPLY TEST, and the corrected width

The orchestrator added the SUPPLYABLE class mid-run, on `[LJ-1.223]`'s finding.
**I confirmed the premise before testing it:** `agents/tasks/LJ-1-210/GenGraph.agda`
exists, and `agents/tasks/LJ-1-210/lj-1.210-report.md:90` reads
"`GenGraph.agda` | **`L.Coding.Graph` with the class as a module parameter.**
Exit 0". MEASURED, by opening both.

`GenGraph.agda:14-24` takes the same class telescope as `GenModel.agda:13-23`,
plus `lem`. I instantiated it at the ambient class with the probe's own six
numeral operations, dropped rows 7, 8 and 9 from `module Body`, and deleted the
local `twelveAt` and `GraphWitAt`.

**Run 2 exits 0.** So all three rows are SUPPLYABLE, and so are two of the five
reconstructions. MEASURED.

| figure | `[LJ-1.220]` | corrected | basis |
|---|---:|---:|---|
| parameters | 22 | **19** | run 2 |
| home modules | 9 | **8** | `L.Coding.Graph` leaves |
| parameter block, non-blank | 58 | **53** | `Probe.agda:141-198`, `ProbeGraphSupply.agda:128-180` |
| reconstruction, non-blank | 28 | **13** | `codeS` 2, `keyS` 2, `Clauses` 9 |

The 8 remaining home modules are `L.Coding.CodeSet` (6 names),
`L.Coding.Table` (6), `L.Coding.Bridge` (2), and `L.Coding.Slot`,
`L.Coding.Sound`, `L.Coding.Unique`, `L.Coding.Sat`, `L.Coding.Uniform` (1
each). 6+6+2+5 = 19.

**THE SWEEP (C-42).** A refutation measures one site, so I swept for the shape.
**Only two generic ports exist on record: `GenModel.agda` and `GenGraph.agda`.**
No other of the 22 rows' home modules has a class-generic file anywhere under
`agents/tasks/`. **So exactly 3 rows are SUPPLYABLE, and the sweep is closed.**
MEASURED by directory listing.

**One caution I will not soften.** `GenGraph.agda` is a probe file, not a
delivered module in `src/`. Calling rows 7 to 9 SUPPLYABLE is consistent with
what `[LJ-1.220]` already did for `keyOf`, which it supplied from `GenModel.agda`
on the same footing. **The corrected width of 8 and 19 therefore prices the work
that REMAINS given that both generic files land.** It does not say the Graph
port is delivered.

## 6b. WHAT THE `tt*` HIDES, and it is not a bought exit 0

**This is the one place where the census is not the whole port price, and I
report it apart because it does NOT make the exit 0 false.**

The probe's `codeS` and `keyS` end in `tt*`. The delivered ones end in real
proofs: `codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ` and
`keyS φ = key ι ιL φ , keyL ι ιL φ` (`src/L/Coding/CodeSet.lagda.md:298`,
`:301`). **At the ambient class that obligation is trivial, and `[LJ-1.220]`
says so honestly.** MEASURED.

**But a second tower is not the ambient class.** At `isL` the obligation is
`codeL`, an induction over all twelve formula constructors
(`src/L/Coding/InL.lagda.md:138-147`), and `keyL φ = prL (numL _) (codeL f h φ)`
at `:256`.

**Is it a hidden 23rd hypothesis? MEASURED NO.** `codeL` is built from `tagL`,
`prL`, `numL` and the alphabet's own certificate. **Those are the pairing and
numeral closure operations `GenModel.agda:13-23` already takes in its class
telescope.** So a class-generic `CodeSet` DERIVES the certificate; it does not
need a new module-level parameter. The 19-name census is not understated.

**Is it free? INFERRED NO.** The generic `L.Coding.CodeSet` port must still
CARRY that induction as code. **I did not build it and I do not price it.** I
flag it because "the reconstruction is 13 lines" could be read as the whole cost
of `codeS` and `keyS` at the second tower, and it is not. **The 13 lines are
their cost at the AMBIENT class only.** INFERRED, in that word.

**Why I could not convert this to MEASURED.** The decisive test is to
instantiate `module Body` at `M := isL` and supply the 22 delivered names, which
would prove no parameter is stronger than delivered. **`𝒮ʟ = 𝒮ᵥ ↾ isL`
(`src/L/Constructible.lagda.md:411`) makes the carriers agree on the nose, and
`agents/tasks/LJ-1-210/ProbeLJ1210A.agda:59-99` shows GenModel at `isL` IS the
delivered Model by eight `refl` checks. So the test is sound in principle.** It
is blocked by exactly this `tt*`: the probe's reconstructions are written at the
trivial class and do not typecheck at `isL` without being made generic, **and
making them generic is the port, which the brief forbids.** I stopped there
rather than port. C-36: this is the term I could not write.

## 7. A SMALL COUNTING CORRECTION, not load-bearing

`[LJ-1.220]`'s section 6 gives the transparent reconstruction as 30 non-blank
code lines, split `Clauses` 10, `twelveAt` 8, `GraphWitAt` 8, `codeS` 2, `keyS`
2. **I recount 28: `Clauses` 9 (`Probe.agda:110-118`), `twelveAt` 8 (`:121-128`),
`GraphWitAt` 7 (`:133-139`), `codeS` 2 (`:101-102`), `keyS` 2 (`:104-105`).**
A 2-line overcount. It changes no verdict. MEASURED.

`[LJ-1.220]`'s 58-line parameter block reproduces exactly. MEASURED.

## 8. RUNS

All runs use `GHCRTS="-A64m -I0 -M8g"`. One process at a time. **Two runs.**

| run | file | exit | seconds | load at start |
|---|---|---:|---:|---|
| 1 | `Probe.agda`, the byte copy | 0 | 5.49 | 6.03 / 4.69 / 4.64 |
| 2 | `ProbeGraphSupply.agda`, 19 parameters | 0 | 5.79 | 5.72 / 4.98 / 4.76 |

**Exit 0 is MEASURED by the interface files**, not by a shell status: Agda writes
`.agdai` only on success, and both
`_build/2.8.0/agda/agents/tasks/LJ-1-224/Probe.agdai` and
`ProbeGraphSupply.agdai` exist.

The seconds decide nothing and the machine is not quiet. **The 5.49 s baseline is
not comparable with `[LJ-1.220]`'s 1.00 s to 1.10 s: those three runs were warm
on their own module, mine builds a new module name.** No run approached the
20-minute wall. No heap exhaustion.

**The run count is 2, not 22.** The brief allows one parameter per run, and I
budgeted for that. **I did not need it: the 22 comparisons are type reading, and
type reading is MEASURED without a run.** A run was needed only where a
judgement about the body's DEPENDENCE was at stake, and that arose once, for the
supply test.

## 9. DD4

**Maximize the code the two proofs share, and write it generic.**

The shared body does not move. **It is the same 338 non-blank lines at the
ambient class as at `𝒮ʟ`**, with 8 carrier substitutions, so DD4's whole point
holds: one body serves both towers.

**The three numbers, corrected:**

| number | `[LJ-1.220]` | corrected |
|---|---:|---:|
| shared body | 389 (`[LJ-1.213]`) | **unchanged.** My span measures 338; see the note |
| plumbing, the parameter block | 58 | **53** |
| per-tower residual | 9 modules, 22 names | **8 modules, 19 names** |

**The note on 389.** `[LJ-1.213]:60` and `:112` measure 391 for the master body
and 389 for the generic candidate. **I did not re-measure that figure, and my
338 is NOT a correction of it:** my span is `Powerset.lagda.md:120-700`, the
exact extent the probe reproduces, and `[LJ-1.213]`'s span is wider. **Two
figures over two spans are not a disagreement.** INFERRED that they are
consistent; I did not check `[LJ-1.213]`'s span.

**What the correction is worth.** The parameter block is an instrument, not
plumbing, exactly as `[LJ-1.220]` section 7 says. The number that matters to
DD4 is the per-tower residual, and **it falls by one module and three names.**

## 10. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| a parameter is WEAKENED against its delivered signature | **MEASURED FALSE**, all 22 rows compared at `file:line` |
| a parameter is STRONGER than its delivered signature | **MEASURED FALSE**, all 22 rows |
| a reconstruction reduces more than the delivered name | **MEASURED FALSE**, all five, `InL.lagda.md:253` is the key evidence |
| the probe's body differs from the delivered body | **MEASURED FALSE**, 8 lines, all carrier |
| the exit 0 is bought | **MEASURED FALSE** |
| the chain width is 9 modules and 22 names | **MEASURED FALSE.** 8 and 19, by run 2 |
| a fourth row is SUPPLYABLE | **MEASURED FALSE.** Only `GenModel` and `GenGraph` exist |
| `GenGraph.agda` is a delivered module in `src/` | **MEASURED FALSE.** It is a probe file |
| the reconstruction block is 30 lines | **MEASURED FALSE.** 28 |

## 11. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-220/lj-1.220-report.md`, read WHOLE. TOOK the 22-row table
  at `:86-107`, the three-name blind spot at `:159-161`, the 58-line block at
  `:114-115`, the 30-line reconstruction at `:170-172`. Its section 4 is the
  object of this review.
- `agents/tasks/LJ-1-220/Probe.agda`, read WHOLE, then COPIED before any edit.
  It is the evidence; the report is its account.
- `agents/tasks/LJ-1-210/GenGraph.agda`, read WHOLE. TOOK the class telescope at
  `:14-24` and the four exports at `:107`, `:120`, `:126`, `:131`.
- `agents/tasks/LJ-1-210/GenModel.agda:13-23`, read for the telescope shape, to
  instantiate `GenGraph` with the same arguments.
- `agents/tasks/LJ-1-210/lj-1.210-report.md:85-95`, read. TOOK the `GenGraph.agda`
  exit-0 record at `:90`, which is the orchestrator's premise, confirmed.
- `agents/tasks/LJ-1-213/lj-1.213-report.md:60`, `:112`, read. TOOK the 391 and
  389 body figures, and did NOT transfer them: see section 9.
- `src/L/Coding/{CodeSet,Graph,Table,Slot,Sound,Unique,Sat,Bridge,Uniform}.lagda.md`,
  read at every signature line in section 3 AND at every enclosing module
  telescope. **Read the source, never a report about it.**
- `src/L/Coding/InL.lagda.md:249-256`, read. This is the file that settles the
  reconstruction question, and no earlier report names it.
- `src/L/Coding/EnvSet.lagda.md:119-154`, `src/FOL/ZFStructure.lagda.md:143-152`,
  `src/L/Constructible.lagda.md:410-411`, read. They settle row 20 and the
  carrier swap.
- `src/L/Coding/Powerset.lagda.md:120-700`, extracted in full for the body diff.
- `archive/dev/TASKS-archived.md`, consulted for SHAPE only. No figure transfers.
  **I did not need it: this task compares live types against live types.**

`agents/tasks/LJ-1-221/lj-1.221-report.md` and `agents/tasks/LJ-1-219/` were in
the brief's ARCHIVE list. **WHY NOT: I did not read them.** The 22 comparisons
are settled by the delivered sources and `Probe.agda` alone, and reading another
agent's account of the same signatures would have risked taking a claim where a
source was available (C-40).

## 12. LITERATURE USED (DD18)

**Nothing in the literature governs whether an Agda parameter is faithful to a
delivered signature.** It is a question about two types in one file tree, and it
is settled by reading them. Said in one line, as the brief asks.

**On `dev/literature/devlin-II5.md:387-389` and the 9-module width.** WHY NOT
USED for the verdict: **it cannot bear on it.** The file says the per-tower
content is a small fixed number of objects; the width of 9, or 8, counts AGDA
MODULES that pin the carrier. **A mathematical step and an Agda module are not
the same unit**, and `[LJ-1.220]:249-258` already reached that conclusion for
the 12-row table at `:370-383`. **Two objects and eight modules do not conflict;
they do not compare.** Reading the width as evidence for or against Devlin would
be the error `[LJ-1.219]` recorded at `keyOf`: one mathematical step spread over
many modules. INFERRED, and I did not open a further source to press it.

## 13. RULES ANSWERED

- **D-1.** The abort criterion was fixed by the brief before the run. **Two
  branches fired together:** "ALL 22 FAITHFUL AND THE 5 SOUND", so the exit 0 is
  real; and the orchestrator's added SUPPLYABLE branch, which moves the width.
  **The width branch is not the WEAKENED branch:** the width is not a floor, it
  is an OVERCOUNT, and I say so in those words.
- **C-38 as extended.** 19 parameters remain undischarged hypotheses. Three were
  discharged by supply, not by port. **A hypothesis is discharged when something
  SUPPLIES it, and `GenGraph.agda` supplies three.**
- **C-42.** I measured one site and then SWEPT for the shape before pricing. The
  sweep found no fourth row. The count is reported before any cure.
- **C-40.** Every figure in this report traces to a line I opened. Where I did
  not open the span behind a figure, I say so: the 389.
- **C-36.** The term I could not write: **the instantiation of `module Body` at
  `M := isL` against the 22 delivered names.** Section 6b says why: the
  reconstructions carry `tt*`, and making them generic is the port. **No type
  comparison was blocked; only this one confirmation run was.**
- **P-l.** `[LJ-1.220]`'s seconds are a comparable, not a price. I report my own,
  with load, and say they are not comparable.
- **C-22.** The report file existed before the first Agda run.
- **C-12.** One process, `-M8g`, cap never raised, second slot only.
- **DD4.** Section 9, three numbers, corrected.
- **DD8.** One number per claim, each with its basis.
- **DD23.** No mathematical prose written. No master edited.
- **DD0, D-10, D-26, I-5, P-i, P-k, P-m, P-y, C-39.** No probe under `src/`; both
  probe files are in `agents/tasks/LJ-1-224/` and tracked.
