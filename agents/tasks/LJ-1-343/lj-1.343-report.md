# LJ-1.343 report: repair the two vacuous telescopes in `src/L/Condensation.lagda.md`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row.
Written incrementally (C-22). Every negative is MEASURED or INFERRED, in those
words.

## 0. LEAD

**THE REPAIR LANDS AND THE CHAPTER IS GREEN. `agda src/L/Condensation.lagda.md`
exits 0 in 133.96 s, against an empty-file floor of 2.37 s.**

**The load-bearing premise HOLDS, and I measured it before I edited anything.**
`hz` is in scope at all three call sites, and its type is the SET membership the
repair needs, with no transport. `agents/tasks/LJ-1-343/ProbeScope343.agda`,
exit 0 in 2.32 s.

**Every consumer is checked, not read.** `DefinesAgree` has ONE consumer inside
`src/`, and `LeafAgree` has ZERO. The five masters that import the chapter all
typecheck against the repaired interface.

| item | verdict | basis |
|---|---|---|
| the repair lands green | **YES** | `agda src/L/Condensation.lagda.md`, exit 0, 133.96 s |
| `hz` in scope at `:6811`, `:6820`, `:6826`, the brief's PRE-repair numbers | **YES, MEASURED** | `ProbeScope343.agda:60-105`, exit 0 |
| `hz` needs a transport | **MEASURED FALSE** | the identity function typechecks both ways |
| a consumer breaks | **MEASURED FALSE** | `ConsumerCheck343.agda`, all five, exit 0 |
| the repaired statement is also false | **MEASURED FALSE** | both are TERMS at `ProbeTies341.agda:254-266` and `:288-294`, and the chapter now elaborates them |
| the brief's「two frozen copies」count | **MEASURED FALSE, it is larger** | 38 files carry the old shape; section 5 |

**Runs.** Four Agda invocations, longest 133.96 s. **No wall**; nothing came
near 30 minutes. One process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. I ran the slot count before every invocation and it returned 0 each
time.

## 1. THE PREMISE UNDER TEST, and it HOLDS

The brief named this premise as the one most likely to be wrong, and said
`[LJ-1.341]` read it from two line numbers and landed no repair. **It has two
halves, and `[LJ-1.341]` tested only the first.**

**HALF 1, the binding. TRUE, MEASURED by reading.** `DefinesAgree.fwd` at
`src/L/Condensation.lagda.md:6807` is `fwd z (hz , hx) = ...`, and
`DefinesAgree.bwd` at `:6822` is `bwd z (hz , hx) = ...`. Both `go` blocks sit
in the `where` clause of those clauses, so `hz` is in scope at all three call
sites. (Line numbers are POST-repair; pre-repair they were `:6798` and `:6813`,
as the brief says.)

**HALF 2, the TYPE, which nobody had tested.** `hz` is the first conjunct of
`bodyB` (`:6799`) and `bodyM` (`:6803`), so its type is the SATISFACTION type
`⟨ (z ∷ γ) ⊨ (var zero ∈̇ var (suc w)) ⟩`. The repaired hypothesis wants the SET
type `⟨ fst z ∈ fst (lookup w γ) ⟩`. **If those were two types, the repair would
need a transport at each site and the five-line estimate would be wrong.**

**THEY ARE ONE TYPE. MEASURED.**
`agents/tasks/LJ-1-343/ProbeScope343.agda:60-68` passes `hz` through the
identity function in BOTH directions, and Agda accepts both. The unfolding chain
is `src/FOL/Semantics.lagda.md:92`,
`γ ⊨ (t ∈̇ u) = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ`, then `:87`, `⟦ var i ⟧ γ = lookup i γ`.
**exit 0 in 2.32 s.**

**AND THE THREE CALL SITES FEED FROM `hz` ALONE.**
`ProbeScope343.agda:78-105` restates the two repaired parameters at the
chapter's own shape and feeds both from a clause that destructures the body
formula. **Nothing but `hz` is passed. MEASURED.**

**SO THE REPAIR COSTS ONE ARGUMENT AT EACH OF THREE SITES**, and the brief's
estimate stands. **The premise the brief flagged is the one premise of it that
did not need correcting.**

## 2. THE DIFF

**20 insertions, 7 deletions, ONE file.** `git diff --stat` gives
`src/L/Condensation.lagda.md | 27 +++++----`. **9 of the 20 insertions are the
comment DD23 requires** (section 6), so the code change is **4 telescope lines
rewritten into 8, and 3 call sites edited in place**.

**CHANGE 1, `DefinesAgree`'s telescope, `:6781-6784` before the edit.** One
hypothesis added to each of two parameters.

    (envK : (E z : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
           → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
           → ⟨ fst E ∈ fst (lookup K γ) ⟩)
    (pairK : (E z w' : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
            → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
            → ⟨ fst w' ∈ fst (lookup K γ) ⟩)

**The new hypothesis binds `z` by the CARRIER slot `w`, never by the bound slot
`K`.** That is what makes the countermodel impossible: `z := lookup K γ` now
needs `lookup K γ ∈ lookup w γ`, which the refutation cannot supply.

**CHANGE 2, the three call sites, now `:6819`, `:6828` and `:6834`.**

| site | before | after |
|---|---|---|
| `fwd`, `EA` module argument | `(λ w' hw → pairK E z w' hw)` | `(λ w' hw → pairK E z w' hz hw)` |
| `bwd`, the `envK` application | `envK E z hE` | `envK E z hz hE` |
| `bwd`, `EA` module argument | `(λ w' hw → pairK E z w' hw)` | `(λ w' hw → pairK E z w' hz hw)` |

**Nothing else in either body changed.** The bound hypothesis is about `z`,
which is FIXED at each site, and never about `w'`, which is the quantified
variable, so the lambdas keep their shape.

**CHANGE 3, `LeafAgree`'s telescope, `:7183-7186` before the edit.** The same
repair at this site's index form. `LeafAgree` passes these two straight through
to `DA` at `:7220-7222`, so their types must match `DefinesAgree`'s after the
substitution `w := suc (suc (suc w))`, `K := suc (suc (suc K))`.

    (envK : (E z : S) → ⟨ fst z ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
           → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
           → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    (defPairK : (E z w' : S) → ⟨ fst z ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
               → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
               → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)

**I DID NOT TIDY, RENAME OR RESTRUCTURE.** No other line of the chapter moved.

**THE SHAPE IS THE SIBLING TIE'S.** `satK` at `:7200-7202` carries the same
carrier membership, as the conjunct `var zero ∈̇ var (suc (suc (suc (suc w))))`
inside its formula. **Section 1 measured that this conjunct and the new
hypothesis are the SAME TYPE**, so the two repaired ties now say in a hypothesis
exactly what the tie beside them says in its formula.

## 3. THE CHECK TIME, WITH THE EMPTY ARM (C-53 as the brief extends it)

| run | file | exit | seconds |
|---|---|---:|---:|
| 1 | `agents/tasks/LJ-1-343/ProbeScope343.agda` | **0** | **2.32** |
| 2 | `src/L/Condensation.lagda.md`, repaired | **0** | **133.96** |
| 3 | `agents/tasks/LJ-1-343/FloorEmpty343.agda` | **0** | **2.37** |
| 4 | `agents/tasks/LJ-1-343/ConsumerCheck343.agda`, all five consumers | **0** | **32.89** |

**THE EMPTY-FILE FLOOR IS 2.37 s.** `FloorEmpty343.agda` copies the chapter's
import block VERBATIM from `src/L/Condensation.lagda.md:6-68` and **defines
nothing**. So process start plus the load of every interface the chapter imports
is 2.37 s, and **the chapter's own content is 131.59 s**.

**WHAT I DID NOT MEASURE, and it matters.** **I ran NO same-session baseline of
the unrepaired chapter.** So I claim **NO DELTA**: I cannot say the repair costs
0 s rather than 2 s. **INFERRED**, from the brief's standing figure of about
132 s and my 133.96, that the repair adds nothing a reader would notice. **A
baseline would have cost a second 132 s run and a 7,600-line frozen copy of the
old chapter in this task directory, which the brief forbids in spirit.**

**THE BRIEF'S TWO TIMING FIGURES, TRACED.** **The 71.4 percent does not trace.**
`grep -rn "71.4" dev/` returns exactly two hits: `dev/ledger.toml:1882`, which
says「the top 11 DEFINITIONS carry 71.4 percent of the 172,518 ms」of the
CARRIED SEQUENCE, a different measurement about a different object; and a URL in
`dev/literature/geology.md:170`. **No line of `dev/` says this chapter is 71.4
percent of the GCH wing's seconds. MEASURED.** The seconds figures `dev/` does
carry for this chapter are **137.0** (`dev/ledger.toml:2451` and `:2467`).
**My 133.96 sits between the brief's 132 and the ledger's 137**, so nothing
operational turns on it, but the percentage should not be re-quoted.

## 4. EVERY CONSUMER, CHECKED

**INSIDE THE CHAPTER.** `DefinesAgree` has **exactly ONE consumer**, `module DA`
at `src/L/Condensation.lagda.md:7220`. `LeafAgree` has **ZERO**: `grep -rn
"LeafAgree" src/` returns its own declaration and two comment lines and nothing
else. **`[LJ-1.338]`'s measurement was right and the abort criterion did not
fire. MEASURED, re-run today.**

**OUTSIDE THE CHAPTER.** `grep -rn "L.Condensation" src/` gives FIVE masters
that import it, plus `src/Everything.lagda.md:378`.

| consumer | names it imports | can it break? |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:29-32` | `DefBodyB`, `Δ₀-DefBodyB`, `module GraphB` | **NO** |
| `src/L/Coding/EnvSupply.lagda.md:47` | `envSetB`, `module EnvSet` | **NO** |
| `src/L/Condensation/LowerAgree.lagda.md:33-36` | `envHypB2` and twelve modules | **NO** |
| `src/L/Condensation/UpperAgree.lagda.md:33` | the same list | **NO** |
| `src/L/Condensation/TwelveAgree.lagda.md:31` | `succU`, `keyU`, `module SatGraphB` | **NO** |

**NO `using` LIST NAMES `DefinesAgree`, `LeafAgree`, `envK`, `pairK` OR
`defPairK`. MEASURED, by reading all five.** An `using` clause hides everything
it does not name, so a break is structurally impossible.

**AND I RAN THEM ANYWAY, because C-45 is the law of this episode: a reading of a
telescope is not a check of it.** `agents/tasks/LJ-1-343/ConsumerCheck343.agda`
imports all five in ONE process. **exit 0 in 32.89 s, all five re-elaborated
against the repaired interface**, and the log names each one
(`L.BoundedSubset`, `L.Coding.EnvSupply`, `L.Condensation.LowerAgree`,
`L.Condensation.UpperAgree`, `L.Condensation.TwelveAgree`).

**`src/Everything.lagda.md` is the orchestrator's**, per the brief and
`AGENTS.md`. It names none of the changed modules (MEASURED, `grep`), and its
re-check of `L.Condensation` now reads a fresh interface.

## 5. THE FROZEN COPIES MY CHANGE MAKES STALE, and the brief UNDERCOUNTS

**THE BRIEF NAMES TWO. THE SWEEP FINDS 38 FILES. MEASURED**, by
`grep -rl` for the unbounded `envK` signature over `agents/`, `src/` and
`archive/`.

| bucket | files |
|---:|---|
| under `src/` | **0** |
| live, under `agents/tasks/` | **23** |
| frozen, under `agents/tasks/archive/` or `archive/` | **15** |

**ONE OF THE BRIEF'S TWO IS MEASURED FALSE.**
`agents/tasks/LJ-1-306/GenAgree.agda` **does NOT copy `DefinesAgree` or
`LeafAgree` at all**: `grep -c "DefinesAgree\|LeafAgree"` on it returns **0**.
Its `envK` parameters are the arity-numeral ties of a different family (the
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` shape). **My change does not touch it.**

**THE OTHER ONE IS CORRECT.** `agents/tasks/LJ-1-336/GenDirty.agda` copies both
modules verbatim, and its own line map at `:1069-1072` records the copy:
`DefinesAgree: :6778-6834 -> this file :594-650` and
`LeafAgree: :7107-7243 -> :907-1043`. **Stale at `:597-600`, `:627`, `:636`,
`:642` and `:983-986`.**

**THE LIVE 23, SO THE NEXT PORT WAVE KNOWS.** Three classes.

- **WHOLE-CHAPTER COPIES, stale at the same two regions.**
  `LJ-1-145/ProbeLJ1145C.agda`, `LJ-1-204/ProbeMinusArNum.agda` and
  `ProbeMinusBound.agda`, `LJ-1-209/ProbePlain.agda`, `ProbeSeal.agda` and
  `ProbeTrivial.agda`, `LJ-1-214/ProbeDelete.agda`, `ProbeMinusArNum.agda` and
  `ProbePlain.agda`, `LJ-1-266/CondensationControl.lagda.md`,
  `CondensationEnv.lagda.md`, `CondensationFact.lagda.md` and
  `CondensationStep6.lagda.md`, `LJ-1-275/CondControlToday.lagda.md`,
  `LJ-1-322/CondProbe.lagda.md`, `LJ-1-336/ControlA.agda` and `ControlB.agda`,
  `LJ-1-336/GenDirty.agda`. **18 files.**
- **TIE RESTATEMENTS, which quote the chapter's type verbatim as their own
  parameter.** `LJ-1-338/ProbeLeaf338.agda:346` and `:349`,
  `LJ-1-338/ControlB338.agda` and `ControlC338.agda` at the same two lines.
  **3 files.** **These are the ones `[LJ-1.341]` proved vacuous**, so their exit
  0 established nothing and their staleness is the point rather than a loss.
- **THE REFUTATION ITSELF, which is NOT stale.**
  `LJ-1-341/ProbeTies341.agda:202` and the brief `LJ-1-341/LJ-1.341.md:22`
  state the old type **on purpose, as the thing they refute**. **My change makes
  them HISTORY, not wrong. 2 files.**

**I UPDATED NONE OF THEM**, as the brief orders. They are frozen probe records.

**AND `[LJ-1.338]`'s RESIDUE FIGURE MOVES AS `[LJ-1.341]` SAID.** Its residue
drops from 51 lines and six ties to 43 and four, because residues 5 and 6 priced
a false statement. **I did not re-measure the four survivors.**

## 6. THE COMMENTS I CHANGED (DD23)

**NO EXISTING COMMENT DESCRIBED THE OLD TELESCOPE.** MEASURED, by reading the
comment blocks that bracket both modules: `:7096-7106` above `LeafAgree`
describes what the module composes and names its port source, and `:7119-7121`
describes the `witK` pass-through. **Neither mentions `envK` or `defPairK`.**
`DefinesAgree` carried no comment header at all. **So nothing was made wrong,
and I deleted nothing.**

**I ADDED TWO COMMENTS, 9 lines, and here is why each is not tidying.**

- **Six lines above `DefinesAgree`'s two repaired parameters.** They say that
  `z` is bound by the carrier slot, that without the hypothesis both types are
  EMPTY by a membership cycle that `regularityV` refutes, that the bound is not
  in the formula because `tagAtL-adequate` and `envOneAt-out` make each premise a
  bare set equation, and that the sibling tie `satK` carries the same bound.
  **Without them a reader restores the unbounded form, because the unbounded
  form is the one that reads naturally and the chapter gives no other warning.**
- **Three lines above `LeafAgree`'s two.** They name the repair, say it is
  `DefinesAgree`'s at this site's index form, and say the two are handed
  straight through.

**Both carry the task code `[LJ-1.343]`, which is the chapter's own convention**
(`:7119` carries `[LJ-1.153]`, `:7104` carries `[LJ-1.62]`).

## 7. C-45, AND WHY THE GREEN HERE IS NOT THE GREEN `[LJ-1.338]` HAD

**`[LJ-1.338]`'s `module Leaf` took both false hypotheses as PARAMETERS**, so
its exit 0 said only「if these types were inhabited, the module would build」.
**They were not inhabited, so it established nothing.** That is C-45 exactly.

**THIS GREEN IS DIFFERENT IN ONE RESPECT AND THE SAME IN ANOTHER, and saying
which is the honest part of this return.**

- **DIFFERENT:** the repaired types are INHABITABLE, and `[LJ-1.341]` built
  inhabitants (`ProbeTies341.agda:254-266` and `:288-294`) from fields the
  `KFacts` record already carries. **So the telescope can now be met.**
- **THE SAME:** **this chapter run still does not INSTANTIATE them.** `LeafAgree`
  has zero consumers, so nothing in `src/` supplies the two ties, and my exit 0
  is again an exit 0 of a module with parameters. **The repair removes the
  vacuity; it does not by itself supply the ties.** MEASURED, by the zero
  consumer count in section 4.
- **THE ONE GAP `[LJ-1.341]` NAMED IS STILL OPEN.** `KFacts` (`:6076-6112`)
  carries no SINGLETON closure and `envOne v` is a singleton, so the repaired
  `envK` needs two lines from `BoundOver.pr∈λ` at `src/L/Coding/Bound.lagda.md:69`
  and `trans∈λ` at `:93`. **My task did not add that field**, because adding a
  `KFacts` field is a telescope change at every one of the record's sites and the
  brief scopes me to five lines. **It is the next task's first line.**

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**THE REPAIR'S TEXT IS CLASS-FREE. CONFIRMED, by reading both new hypothesis
types.** They name `fst`, `∈` and `lookup` and a slot index. **No L-side name, no
ambient-side name, no concrete carrier.** So the same two lines serve either
carrier, which is what DD4 asks, and this is `KFacts.carrierK`'s own shape
(`:6109-6110`).

**BUT `[LJ-1.341]`'s CLOSURE CLAIM IS MEASURED FALSE TODAY.** Its section 9
says「`L.Condensation` is in neither trophy closure」. **`ledger.py
--trophy-files` puts `src/L/Condensation.lagda.md` in `gch_only` at 6,718
lines.** So on DD4's own axis **the repair lands entirely on the GCH side, not
on the shared side.** The three `src/L/Condensation/*Agree` masters are `shared`
and AMBIGUOUS; the chapter itself is not.

**THE CLOSURE TODAY**, from `ledger.py --reuse`, run after the repair:

    AC closure   73 masters  17,186 lines
    GCH closure  48 masters   8,878 lines
    SHARED       43 masters   7,585 lines
    share of the union: 41.0% of 18,479

**AND THE GCH FIGURE UNDERSTATES, as the brief says.** `dev/ledger.toml:206-213`
records the bound as a construction rather than an estimate: `[LJ-1.326]` built
the two terms the proof owes and re-ran the closure with each, so the
understatement is **about 1,028 GCH lines and 36 shared**. **The share is read
beside the SHARED row, never alone.**

**WHAT THE REPAIR MOVES ON THE AXIS: 4 code lines, all GCH-side.** Nothing moves
to shared and nothing leaves it. **DD4 is neutral here by structure, and the
useful statement is the class-free one:** when the tie supply is finally
written, it is written once.

## 9. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `hz` is unavailable at the call sites | **MEASURED FALSE.** In scope at all three |
| `hz` needs a transport to the set type | **MEASURED FALSE.** `ProbeScope343.agda:60-68`, the identity both ways |
| the repair costs more than five lines | **MEASURED FALSE.** 4 code lines and 3 call sites |
| the repaired chapter fails to typecheck | **MEASURED FALSE.** exit 0, 133.96 s |
| a consumer of the chapter breaks | **MEASURED FALSE.** All five, exit 0, and no `using` list names the changed modules |
| `LeafAgree` has a consumer in `src/` | **MEASURED FALSE.** Re-measured today, zero |
| `DefinesAgree` has more than one consumer | **MEASURED FALSE.** Exactly one, `:7220` |
| a comment described the old telescope | **MEASURED FALSE.** I read both bracketing blocks; neither mentions the two ties |
| the brief's two frozen copies are the whole set | **MEASURED FALSE.** 38 files carry the old shape |
| `LJ-1-306/GenAgree.agda` is made stale | **MEASURED FALSE.** It copies neither module |
| the repair moved to the shared side of DD4 | **MEASURED FALSE.** The chapter is `gch_only` |
| `[LJ-1.341]`'s「neither trophy closure」stands | **MEASURED FALSE.** `gch_only`, 6,718 lines |
| the brief's 71.4 percent traces to `dev/` | **MEASURED FALSE.** The only `dev/` hit is a different measurement |
| a run hit a wall or exhausted the heap | **MEASURED FALSE.** Longest 133.96 s, cap never raised |
| the chapter's cost changed | **INFERRED, no delta claimed.** I ran no same-session baseline |
| the repair supplies the two ties | **INFERRED FALSE.** It removes vacuity only; `KFacts` still lacks the singleton closure |
| the four surviving residues are affected | **INFERRED FALSE.** I did not re-price them |
| I ran `make check` | **MEASURED FALSE.** The orchestrator runs it |

## 10. THE GATES

    .venv/bin/python scripts/gate/lint-prose.py  --check src/L/Condensation.lagda.md   exit 0
    .venv/bin/python scripts/gate/lint-agda.py   --check src/L/Condensation.lagda.md   exit 0
    .venv/bin/python scripts/site/weave-i18n.py  --check src/L/Condensation.lagda.md   exit 0
    .venv/bin/python scripts/gate/lint-prose.py  --check agents/tasks/LJ-1-343/lj-1.343-report.md   exit 0
    .venv/bin/python scripts/gate/lint-agda.py   --check <my three probes>             exit 0
    .venv/bin/python scripts/gate/check-probes.py                                      exit 0, clean

`git status --short` shows one modified file, `src/L/Condensation.lagda.md`, and
four new files, all inside `agents/tasks/LJ-1-343/`.

## 11. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read WHOLE.** **Line read:**
  `:162-168`,「THE NEW HYPOTHESIS IS FREE AT BOTH CALL SITES, AND THIS IS THE
  LOAD-BEARING CHECK ... MEASURED, by reading」. **TOOK** the corrected
  statement of section 4 and the three call-site line numbers. **CORRECTED its
  basis, not its verdict:**「by reading」covered the binding and not the type.
  I ran the type. **CORRECTED one claim outright:** section 9's「`L.Condensation`
  is in neither trophy closure」is false; it is `gch_only`.
- **`agents/tasks/LJ-1-341/ControlA341.agda`, read WHOLE.** **Line read:**
  `:54-59`, `leaf-defPairK-false`, the chapter's own type stated VERBATIM and
  discharged into `⊥`. **TOOK** it as the proof that both index forms fall, so
  that I repaired `LeafAgree` as well as `DefinesAgree` rather than only the
  module the countermodel names first.
- **`agents/tasks/LJ-1-341/ProbeTies341.agda`, read `:230-300`.** **Line read:**
  `:288-294`, `envK-bounded`. **TOOK** the exact position of the new hypothesis
  in the argument order, before the satisfaction premise, so the chapter's
  telescope and the sibling's term agree.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`, read the residue table.**
  **Line read:** `:194`,「`envK` (`:7183-7184`) ... its entry `z` carries NO
  hypothesis, so the tie climbs from an unbounded set」. **TOOK** its zero-consumer
  measurement for `LeafAgree` as the claim to re-run. **CONFIRMED it**, which is
  why the「a consumer breaks」abort criterion did not fire.
- **`agents/tasks/LJ-1-338/ProbeLeaf338.agda`, read `:290-315`.** **Line read:**
  `:305`, `satK z h = carrierK fL z (fst h)`. **TOOK** it as the first evidence
  that the satisfaction conjunct and the set membership are one type, which is
  what `ProbeScope343.agda` then measured directly rather than inferred.
- **`agents/tasks/LJ-1-336/GenDirty.agda`, read `:1069-1072`.** **Line read:**
  `:1070`,「`DefinesAgree`: `:6778-6834` -> this file `:594-650`」. **TOOK** the
  line map, which is how section 5 names the stale regions exactly instead of
  naming the file.
- **`archive/dev/TASKS-archived.md`, read the shared-kit rows.** **TOOK SHAPE
  ONLY:** the retired route also carried hypotheses whose quantifier was wider
  than the proof needed. **WHAT WOULD NOT TRANSFER:** every figure. That route
  had a different carrier and no `KFacts` record, so no residue count or check
  time from it prices anything here.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:240-256`.**

**THE ONE LINE THE BRIEF ASKS FOR: YES, the repair puts the binder back where
Devlin has it, but in a different PLACE in the sentence.** `:245-250` records
that 2.2 to 2.4 write `D(v, u) = "v = Def(u)"` as Σ₁ and **「then bind every
unbounded quantifier by the concrete set K(u), the finite sequences over the
formula set, the variables and the members of u」**. **In Devlin the bound is
inside the FORMULA, so no variable escapes.** Our telescope moved the bound out
of the formula and into a hypothesis, and `z` lost its binder on the way. **The
repair restores the binder as a HYPOTHESIS rather than as a conjunct.**

**THAT DIFFERENCE IS REAL AND IT IS NOT A DEFECT.** The digest's own closing
line at `:254-256` says the argument「does not require them to have any
particular shape, only that some bounded description with a bound inside the
carrier exists」. **A hypothesis and a conjunct are two shapes of one bound**,
and the chapter already uses both: `satK` (`:7200-7202`) binds by its formula,
`KFacts.carrierK` (`:6109-6110`) binds by a hypothesis. **INFERRED**, by
comparison; the digest states Devlin's binding and says nothing about our
telescope.

**WHY NOT the rest of the digest.** `:243-244` is the `[LJ-1.12]` Δ₀ question,
answered and not reopened here. `:258` onward is Step D, the hull with least
witnesses, which no tie of `LeafAgree` reaches. The cardinality half of 5.5 and
5.6 is a different step, and C-46 forbids using Devlin's tower axis as DD4's.

## 13. WHAT I DID NOT SETTLE

- **The two ties are still unsupplied.** The repair makes them meetable; nothing
  in `src/` meets them. `KFacts` still lacks the singleton closure, two lines
  from `src/L/Coding/Bound.lagda.md:69` and `:93`.
- **No same-session timing baseline**, so no delta on the chapter's cost.
- **The four surviving residues** of `[LJ-1.338]`, `witK`, `graphWitK` and the
  two arity-numeral facts. Untouched, not re-priced, truth not tested.
- **The 38 stale copies.** Named, never edited.
- **`make check`.** Not run. The orchestrator runs it.

## 14. PROHIBITIONS, ANSWERED

I wrote to `src/L/Condensation.lagda.md` and to `agents/tasks/LJ-1-343/` and
nowhere else. I did not open `dev/PLAN.md`, `dev/LESSONS.md` or `AGENTS.md` for
writing, and I edited no other task directory: `LJ-1-341/`, `LJ-1-338/` and
`LJ-1-336/` were read and counted only. I did not touch
`src/Everything.lagda.md`. No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`. One agda process at a time under
`GHCRTS="-A64m -I0 -M8g"`, the cap never raised, and the slot count run before
every invocation. No em dash in any language.
