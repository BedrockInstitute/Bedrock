# LJ-1.217 report: A6 re-priced from the green interface, with a clock cap

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe task. No
master edited. No commit, no push. Written incrementally (C-22).

Every claim is marked **MEASURED** or **INFERRED**.

## 0. LEAD

**A6 = 446 LINES. The seven cells now sum, and the sum is still not a quotable
price.**

**MEASURED.** A6's open charge — building `ShiftAbs`/`Shiftω` INTO L — is
**296 lines**. A6's standing base is 150, so **A6 = 150 + 296 = 446**. The
charge is a green typecheck: `ProbeLJ1217A.agda`, exit 0, **mean 15.0 s over
three kept runs** (15.617 / 14.684 / 14.747), loads 5.13 to 5.59, under
`GHCRTS="-A64m -I0 -M8g"`, 30-minute clock cap never approached.

**The wall was fixed-shape.** `[LJ-1.215]`'s fixed-shape finding is now
MEASURED: the fibre `sv` conjunct walls at **1,810 s** under the same 30-minute
bound, and the fibre `ij` conjunct is a **type error** (exit 42, 4.78 s), while
the direct-equality shape of the same four conjuncts is green in 15 s.

**Do the seven cells sum?** Arithmetically YES: A1 40 + A2 170 + A3 45 +
A4 190 + A5 547 + A6 446 + A7 110 = **1,548**. **As a price, NO**: 555 of those
lines (A1, A2, A3, A4, A7) still rest on reading, and 47 of A6's 150 base does
too. I do not quote 1,548 as A-prime's total. `[LJ-1.176]`'s refusal stands,
and its reason moved: A6 is no longer the blocker; the reading residue is.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

Copied from the brief `agents/tasks/LJ-1-217/LJ-1.217.md`, fixed before the
first line of probe code:

- **PRICED.** A6 becomes ONE number with its basis named, and the seven cells
  are said to sum or not. STOP.
- **THE DIRECT SHAPE WORKS.** Report both prices, the fibre form and the
  direct form.
- **A REAL WALL SURVIVES THE CLOCK CAP.** Name the term and stop.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall. Interrupt
  it, report the ELAPSED SECONDS, and bisect. Every cut gets the SAME bound as
  its green control, and the control's elapsed time is reported BEFORE any cut
  is interpreted.

**VERDICT: THE DIRECT SHAPE WORKS.** The direct-equality shape of the four
conjuncts is green and fast. The fibre shape's `sv` is a wall that survives the
clock cap, and its `ij` is a type error. Both prices are in section 4.

**THE FIGURE TO STRIKE.** `[LJ-1.198]`'s「at least 6,400 to 1」ratio is VOID:
a non-completion has no duration. I do not carry it forward.

## 2. THE FIXED-SHAPE FINDING, AND THE DIRECT-EQUALITY SHAPE

**MEASURED. The direct-equality shape is GREEN and FAST.**
`ProbeLJ1217A.agda` is the full A6 build in six parts: the ambient shift
(Part 1), the three-case description `shiftFo` and its reading (Part 2),
`StageBound` (Part 3, shared), `Carve` with all four conjuncts `sv`/`ij`/`dm`/
`ran` plus the readback (Part 4), `ShiftGraph` (Part 5), and the C-38 guard
(Part 6). Warm-up exit 0 in 16.3 s; three kept runs in section 3.

**What changed against the fibre shape.** The fibre `pair-out` returned
`∥ Σ k ∈ ⟪ fst D ⟫. (↪k ≡ fst x) × (fst y ≡ ↪(sh k)) ∥`, so `sv` and `ij`
had to run `↪-inj` inline on a composite of two truncated witnesses. The
direct shape makes `out`/`G-out`/`pair-out` return the value equality
`fst y ≡ val D C sh x m` directly and pushes the two `↪-inj` uses into TWO
shared lemmas in `ShiftFo`: `val-cong` (value irrelevance across `fst u ≡
fst u'`, `ProbeLJ1217A.agda:334-337`) and `val-inj` (value injectivity via
`shInj`, `:339-343`). The four conjuncts compose these lemmas instead of
re-normalizing `↪-inj` on composite proofs.

**MEASURED. The original fibre probe had LATENT TYPE ERRORS the wall hid.**
`ProbeLJ1198A.agda` never went green, so its Parts 5 and 6 carried errors the
3.06 h wall never reached: `subst isL` at `:627` (needs `subst (λ x → ⟨ isL x
⟩)` and the non-sym direction of `sucʟ-fst`), and the C-38 guard's
`zero∈D`/`inG` at `:690`/`:695` (numeral `# 0` vs `numeralL 0`; `shift 0` vs
`numeralL 1`). I fixed all three in `ProbeLJ1217A.agda:627,690,695`. This
means `[LJ-1.198]`'s「the probes have no hole and no postulate — the wall is
elapsed elaboration, not an unfinished term」overclaimed: the file had type
errors the wall masked.

## 3. THE MEASUREMENTS

**Machine state.** 16 cores, macOS, Agda 2.8.0. ONE agda process of mine at a
time, always `GHCRTS="-A64m -I0 -M8g"`, cap never raised. The machine was NOT
quiet: a sibling ran `agda src/L/Condensation.lagda.md` at 99.6 percent CPU
throughout, and the one-minute load band over my runs is 3.93 to 7.78.

**All runs cold: the file's own interface was deleted before every run.**
Warm-up discarded, three kept.

| run | what it is | seconds | exit | load before → after |
|---|---|---:|---|---|
| warmup | `ProbeLJ1217A.agda` (direct shape, whole) | 16.349 | 0 | 4.60 → 5.45 |
| **kept 1** | the same | **15.617** | 0 | 5.13 → 5.59 |
| **kept 2** | the same | **14.684** | 0 | 5.59 → 5.56 |
| **kept 3** | the same | **14.747** | 0 | 5.56 → 5.49 |

**Direct-shape mean: 15.0 s** (15.617 + 14.684 + 14.747 = 45.048 / 3). Own
spread 0.93 s, 6.2 percent. Zero heap walls. Zero postulates, zero holes, zero
`trustMe`. `hasReplacementL` appears four times and all four are comments;
`hasSeparationL` appears once in code at `ProbeLJ1217A.agda:678`.

**The lines, by part.** Counted as non-blank non-comment lines, the same
caliber `[LJ-1.176]` applied by hand (the ledger cannot count a probe,
`scripts/ledger.py:13-15`).

| part of `ProbeLJ1217A.agda` | lines | what it is |
|---|---:|---|
| imports header | 5 | paid once by a master |
| Part 1 `Ambient` | 142 | **A6's base**, the ambient `ShiftAbs`+`Shiftω` |
| L-side imports + `sucV-#` + `val` | 43 (4 code) | imports + two shift helpers |
| Part 2 `shiftFo` + `ShiftFo` reading | 133 | the one-place three-case description and its reading |
| Part 3 `StageBound` | 16 | **SHARED**, no object owns it |
| Part 4 `Carve` (4 conjuncts + readback) | 115 | the graph, carved |
| Part 5 `ShiftGraph` | 44 | the L instantiation, the only site of `hasSeparationL` |
| Part 6 `Witness` | 14 | probe-only, does not ship |
| **whole file** | **512** | |

**THE CHARGE = Part 2 + Part 4 + Part 5 + the two helpers = 133 + 115 + 44 + 4
= 296 lines.** Part 1 is A6's base (already in the 150). Part 3 is shared.
Part 6 is probe-only. The two helpers (`sucV-#`, `val`, 2 lines each) are
shift-specific code the inclusion never needed, so they are charged.

## 4. THE CUTS, EACH WITH ITS BOUND AND ITS CONTROL'S ELAPSED TIME

**The control's elapsed time, stated BEFORE the cuts are interpreted: the green
direct-shape probe typechecks in 15.0 s mean (3 kept runs, section 3).** Every
cut below ran under the SAME bound as the control: **1,800 s (30 minutes)**.

| cut | content | bound | result | elapsed |
|---|---|---:|---|---:|
| `ProbeLJ1198F` | the fibre shape, `ij` conjunct alone | 1,800 s | **TYPE ERROR**, exit 42 | **4.78 s** |
| `ProbeLJ1198G` | the fibre shape, `sv` conjunct alone | 1,800 s | **WALL**, no completion, killed | **1,810 s** |
| `ProbeLJ1217A` | the direct shape, all four conjuncts + readback | 1,800 s | **GREEN**, exit 0 | **15.0 s mean** |

**The fibre `ij` is not a wall, it is a type error. MEASURED.**
`ProbeLJ1198F.agda:541` — `shInj (r .fst) (r' .fst)` uses `r .fst`, which is
the fibre element `k : ⟪ fst D ⟫`, where `sym (fst r)` at `:539` already forced
it to be a path. The correct term is `r .snd .fst`. **`[LJ-1.198]`'s「F is a
sixth unreported wall」is wrong: F never typechecked.**

**The fibre `sv` is a real wall that survives the clock cap. MEASURED.**
`ProbeLJ1198G.agda` ran 1,810 s under the 30-minute bound and did not finish.
Its `sv` puts `↪-inj {a = fst D}` on the composite `fst r ∙ sym (fst r')`,
where `fst r = k : ⟪ fst D ⟫` is misused as a path; Agda normalizes the deep-
monic presentation `⟪ fst D ⟫` to type the composite, and that is what does not
finish. **The wall's term is named: `↪-inj {a = fst D}` on a composite whose
endpoints are the mis-projected fibre element, at `ProbeLJ1198G.agda:541`.**

**The direct shape removes exactly that.** The direct `sv` composes
`val-cong` and the direct `ij` composes `val-inj`; neither re-normalizes
`↪-inj` on a composite of two truncated witnesses. Both are in the green file.

## 5. A6's PRICE, ONE NUMBER WITH ITS BASIS

**A6 = 446 lines. Basis: 150 standing base + 296 measured charge.**

| component | lines | class |
|---|---:|---|
| A6's standing base (`ShiftAbs`+`Shiftω` ambient + the theorem wrapper) | **150** | carried from `[LJ-1.175]`/`[LJ-1.136]`; 103 of it MEASURED by `[LJ-1.107]`, 47 reading |
| the open charge, NOW CLOSED: the L-side build | **296** | **MEASURED**, this task, a green 512-line file |
| **A6** | **446** | |

**The seven cells, as numbers: A1 40, A2 170, A3 45, A4 190, A5 547, A6 446,
A7 110. Their sum is 1,548.** I do NOT quote it as a price, for the same reason
`[LJ-1.176]` refused: A1, A2, A3, A4 and A7 (555 lines) rest on reading, only
100 of those carry a measured core, 47 of A6's 150 rests on reading, and A5's
547 carries two inferred rows. **The seven cells are now seven numbers — the
「A6 is not one number」blocker is cleared — but the total is arithmetic, not a
measured price.**

**Seconds against DD24, recorded, not argued.** Whole-file 15.0 s over 512
lines is 0.0293 s per line, 3.7× the 0.007913 bar. **The caliber differs**: the
bar counts non-blank in-fence lines of masters; this counts non-blank
non-comment lines of a `.agda` probe, and the file includes the 142-line
ambient base and the shared bound. Net of the ambient base and imports the
charge's own share is not separately timed (no import-baseline probe was run;
P-l forbids carrying `[LJ-1.176]`'s 1.29 s baseline). The DD24 bar is for the
whole GCH side at the end, and intermediate debt is allowed.

## 6. DD4

**The re-instantiation figure: 85 percent generic.** MEASURED by part, the
same method as `[LJ-1.176]`: the generic half of the charge is Part 2
(133) + Part 4 (115) + the two helpers (4) = 252 of 296 lines, 85.1 percent.
The L half is Part 5 (44 lines), the instantiation that supplies the bound,
the numerals and `hasSeparationL`. A grep for
`hasSeparationL|hasReplacementL|StageBound|stage|boundingOrd|Lset|LsetS|numeralL|ωʟ|∅ʟ|sucʟ|IsOrd`
over the charge returns 8 code lines, all in Part 5.

**The direct-equality shape is EQUALLY generic and BETTER factored.** Both
shapes keep the L-specificity in Part 5 alone, so the 85 percent is the same.
The difference: the fibre shape had the two `↪-inj` uses inline in `sv` and
`ij` (so a J re-instantiation rewrites each proof); the direct shape factors
them into two shared lemmas `val-cong`/`val-inj` inside `ShiftFo`, which a J
instantiation reuses whole. **The factoring costs six lines** (the two lemmas,
eight lines, replace the two-line `val-irrel`), and it is what buys 15 s against
1,810 s.

**The genericity cost at this cluster, answered.** `[LJ-1.176]` measured
genericity costing ONE line at its site (78 against 77, 81 percent
re-instantiating for J). I cannot measure the same one-line figure here: there
is no non-generic shift carve to diff against, and writing one would mean
hardcoding the L stage into `Carve`, which the shape deliberately does not.
**INFERRED: the parameterized form is the only form that prices A6, so the
cost of genericity is not separately visible.**

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-215/lj-1.215-report.md`, read WHOLE.** TAKEN: the four
  defects at section 3.2, the fixed-shape finding at section 3.4 and section 7,
  and the proposed law「a cut must never get a shorter bound than its control」.
  This brief is that report's next step, applied.
- **`agents/tasks/LJ-1-198/`, in full.** TAKEN: `ProbeLJ1198A.agda` (copied
  and rewritten into the direct shape), `ProbeLJ1198E.agda` (the green base),
  `ProbeLJ1198F.agda` and `ProbeLJ1198G.agda` (the two cuts I re-ran).
  `_build/2.8.0/agda/agents/tasks/LJ-1-198/` holds interfaces for A and E only.
- **`agents/tasks/LJ-1-176/`, read WHOLE.** TAKEN: the carve device
  (`ProbeLJ1176A.agda`), whose `pair-out` returned `fst x ≡ fst y` directly and
  cost 1.72 s; the 112-line object and the part table at section 3.1, which
  fixes my line-count caliber and the shared/probe-only split.
- **`agents/tasks/LJ-1-175/lj-1.175-report.md:38-53`.** TAKEN: A6's cell as
  「150 PLUS an open charge」and the 705 figure.
- **`agents/tasks/LJ-1-152/`, `LJ-1-154/`.** TAKEN: the separation carve shape
  and the 2,500-to-1 ratio (not used as a number; P-l).
- **`archive/dev/TASKS-archived.md`: SEARCHED, NOTHING TAKEN.** It holds no
  L-side carve of the shift. **`archive/src/2026-08-09-rud-route/`**: the shift
  shape is recorded but nothing transfers as a number (the retired tree is not
  this tree).

## 8. LITERATURE USED (DD18)

- **`dev/literature/devlin-errata.md:202-203`**:「BS = ReS0 + Cartesian product
  + full foundation + ω ∈ V」. **TAKEN: Devlin's base theory has NO
  replacement.** The shift needs no replacement axiom; it needs a Δ0
  separation, so it does not leave Devlin's setting.
- **`dev/literature/devlin-errata.md:180`**:「DS = S0 + Δ0 separation + Π1
  foundation + ω ∈ V + S(x) ∈ V」. **TAKEN: the shift's three cases are each a
  bounded condition, so the object is separation-shaped in Devlin's terms.**
- **`dev/literature/devlin-II5.md`, searched.** **TAKEN: it holds NO
  successor-absorption content.** Its only successor material is a
  formula-reading successor clause (`:392`, `:544`, `:546`, `:567`); nothing
  states or builds `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`.
- **Does Devlin BUILD A6's two objects or ASSUME them?** **INFERRED, and
  stated as inference.** Devlin does not state the successor absorption as
  such. Each of its three cases (numeral successor on ω, constant zero at the
  top, identity elsewhere) is a bounded formula, so the object is Δ0-definable
  in his BS — he would BUILD it, as he builds the analogous bounded pairing
  function (II.6.6). He neither states nor assumes the theorem itself.

## 9. WHAT `[LJ-1.8]` STILL NEEDS

**`dev/PLAN.md:50`'s blocker moved, and did not clear.**

1. **A6: CLOSED at 446** (150 base + 296 measured charge). The「not one
   number」cell is now one number.
2. **The seven cells now sum to 1,548, but the total is not a price.** The
   reading residue (555 lines across A1, A2, A3, A4, A7, plus 47 of A6's base,
   plus two inferred rows of A5) is unchanged. `[LJ-1.176]`'s refusal stands.
3. **The seconds are 15.0 s whole-file for A6's probe, 3.7× the DD24 bar on
   the whole-file caliber.** A6 is the first block whose L-side build exceeds
   the bar on the whole-file figure. No decision follows (DD24 judges the
   whole GCH side at the end).
4. **G8 (`levelIn`, `cover`) stays excluded, in writing.**
5. **The two open A5 rows (`pairω`, the column square) remain the widest
   unmeasured lines in the route**, and they are A5's, not A6's.

## 10. WORKING TREE, AS MY REPORT DESCRIBES IT

**New files, all in `agents/tasks/LJ-1-217/`, none deleted, none committed:**

| file | state |
|---|---|
| `ProbeLJ1217A.agda` | green, `--safe`, exit 0, 707 raw / 512 non-blank non-comment lines. THE DELIVERABLE |
| `lj-1.217-report.md` | this file |
| `runs/run_one.py` | the timing harness (records load, wall seconds, exit) |
| `runs/warmup.txt`, `runs/direct1-3.txt`, `runs/fibreF.txt`, `runs/fibreG.txt` | raw run logs |

**No master edited. No file under `src/` edited.** I committed nothing and
pushed nothing. No `git checkout .`, stash, reset or clean. No `make check`; the
orchestrator runs it. ONE agda process of mine at a time, cap never raised.
The sibling `agda src/L/Condensation.lagda.md` ran throughout; I did not touch
it.

**Checks run:** `scripts/lint-agda.py --check` on `ProbeLJ1217A.agda` (clean);
`scripts/lint-prose.py --check` on this report (clean at final write).

## 11. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The fibre `sv` conjunct is a wall.** `ProbeLJ1198G.agda`, 1,810
  s under a 1,800 s bound, no completion.
- **MEASURED. The fibre `ij` conjunct is a type error, not a wall.**
  `ProbeLJ1198F.agda`, exit 42, 4.78 s, at `:541`.
- **MEASURED. The direct-equality shape is green and fast.** 15.0 s mean, three
  kept runs, exit 0.
- **MEASURED. The original fibre probe carried latent type errors in Parts 5
  and 6.** `:627`, `:690`, `:695`.
- **MEASURED. The shift's L-side charge is 296 lines.**
- **MEASURED. The shift needs no `hasReplacementL`.** Four occurrences, all
  comments; one `hasSeparationL` in code at `:678`.
- **MEASURED. 85 percent of the charge re-instantiates for J.**
- **INFERRED. Devlin would build the shift by Δ0 definability.** He does not
  state it; section 8.
- **INFERRED. The cost of genericity at this cluster is not separately
  visible.** No non-generic shift carve exists to diff against.
