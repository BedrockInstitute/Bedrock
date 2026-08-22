# LJ-1.534 report: the frame the honest forms want, and whether it is satisfiable

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-534/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`.

TARGET: one term `honest-frame-inhabited` in
`agents/tasks/LJ-1-534/Probe534.agda`. Nothing lands in `src/`. I did not
edit `src/`. I did not replace `TFacts`. I did not rebuild the 59-row census.
I did not postulate.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work and starts no
collection. No Boundary clause is in conflict.

## VERDICT

**GO, AND THE FRAME ALSO NAMES THE ONE HYPOTHESIS THAT CANNOT JOIN IT.**

1. **The collected frame is INHABITED at `KValue`'s frame.**
   `honest-frame-inhabited` (`agents/tasks/LJ-1-534/Probe534.agda:183-192`)
   typechecks, exit 0, median **2.30 s** over three forced rechecks
   (`runs/full-t1.time`, `runs/full-t2.time`, `runs/full-t3.time`), and the
   final run is `runs/final.time`, 2.28 s. The program's witness meter agrees:
   `/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-534
   --brief agents/tasks/LJ-1-534/LJ-1.534.md`, exit 0, **0 UNRESOLVED of 1**,
   `probe_red=False` (`runs/witness-1.out`). `.venv/bin/python` is absent in
   this worktree, as `[LJ-1.499]`, `[LJ-1.504]` and `[LJ-1.507]` also found.
   I added no dependency.

2. **NO TWO HYPOTHESES OF THE COLLECTED FRAME CONFLICT.** All eight hold at
   once, in one value.

3. **ONE HYPOTHESIS THAT IS NOT IN THE FRAME CANNOT BE ADDED TO IT**, and the
   refutation is machine-checked: `arNum-uniform-conflicts`
   (`Probe534.agda:251-271`) derives `⊥` from the collected frame plus the
   uniform arity-numeral hypothesis, using only conjuncts 3 and 5. That
   hypothesis is what `SupplyEnv.someEnv` needs and what `someEnvDef` refuses
   to give. Section "THE ONE HYPOTHESIS THAT CANNOT JOIN" below.

4. **THE FRAME CANNOT BE A RECORD, AND THAT IS MEASURED, NOT CITED.** Four
   runs of the same eight hypotheses as a `record` each exhausted the 8 GB
   heap. The waller is ONE conjunct, `sucK`. Section "W3" below.

## THE COLLECTED FRAME

`HonestFrame` (`agents/tasks/LJ-1-534/Probe534.agda:102-120`). It is a
PRODUCT and not a record, for the reason section W3 measures. It is indexed
by `TFacts`'s own two slot names and its own vector: `A K : Fin (5 + n)` and
`γ : Vec S (11 + n)`, with `Kslot K γ = lookup (suc⁶ K) γ`
(`Probe534.agda:70-71`), which is how every `TFacts` field reads `K`
(`src/L/Condensation/TwelveAgree.lagda.md:129-133`).

    HonestFrame A K γ =
        isTransV (fst (Kslot K γ))
      × ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
      × ⟨ # 0 ∈ fst (Kslot K γ) ⟩
      × ((a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ sucV a ∈ fst (Kslot K γ) ⟩)
      × ((a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
           → ⟨ pr a b ∈ fst (Kslot K γ) ⟩)
      × ((m : ℕ) (h : Fin m → V ℓ)
           → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
           → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩)
      × (lookup zero γ ≡ lookup (suc⁶ A) γ)
      × ((ar : S) (m : ℕ) → fst ar ≡ # m
           → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
           → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩)

| # | conjunct | the honest forms that take it, at `src/L/Coding/EnvSupply.lagda.md` | disposition |
|---|---|---|---|
| 1 | `Ktr` | `module Fact`'s own second parameter, `:450` | **supplied by `[LJ-1.495]`'s shift.** `KFacts.arityK` (`src/L/Condensation.lagda.md:6114-6115`) is the same statement at `S`, and `module AtLevel` already fixes the term for a level, `:755-756` |
| 2 | `TK`, the VALUE TABLE slot | `valK` `:462`, `valK-un` `:471`, `subK₁-and` `:497`, `subK₀-and` `:508`, `subK₁-imp` `:519`, `subK₀-imp` `:530`, `subK-neg` `:541`, `subK-un` `:552`, `subK-allin` `:563`. NINE forms | **NEW** |
| 3 | `numK0` | `EnvClosure` `:673` | **supplied by `[LJ-1.495]`'s shift.** `KFacts.numK0` (`Condensation.lagda.md:6094`) plus `numeralL-fst` |
| 4 | `sucK` | `EnvClosure` `:674` | **NEW.** `KFacts` has no successor field, and `TFacts` keeps `sucK` a telescope hypothesis on purpose (`TwelveAgree.lagda.md:340-341`) |
| 5 | `pairK`, at `V ℓ` | `EnvClosure` `:675` | **supplied by `[LJ-1.495]`'s shift.** `KFacts.pairK` (`Condensation.lagda.md:6110-6111`) plus `prʟ-fst`; the lift is `Probe534.agda:171-181` |
| 6 | `finSetK` | `EnvClosure` `:676-677` | **NEW** |
| 7 | `carrier≡`, the carrier slot pin | `envK-gen` `:278`, `envInK-gen` `:352` | **NEW** |
| 8 | `envSetK`, PINNED to `B₀` | `envSetK` `:140-143` | **NEW**, and it is a WEAKENING: the record field is generic in `B` (`TwelveAgree.lagda.md:306-310`) |

**THE COUNT OF NEW IS FOUR PLUS ONE WEAKENING: `TK`, `sucK`, `finSetK`, the
carrier pin, and `envSetK` at `B₀` only.** Three of the eight are already
paid by the shift `[LJ-1.495]` delivered.

**`envConsK` IS NOT A NINTH.** `ConsK` takes it as a module hypothesis
(`:627-629`), and `EnvClosure` (`:672-700`) builds it from conjuncts 3, 4, 5
and 6. So the three `consK-*` forms cost the frame nothing beyond what is
already listed.

**THE OUTER TELESCOPE COSTS ONE MORE, AND IT IS NOT NEW EITHER.** `module
SupplyEnv` takes eight parameters (`:107-111`). Seven of them ARE `KValue`'s
telescope, term for term (`src/L/Condensation.lagda.md:7380-7383`). The
eighth is `ω∈γ : ⟨ ω ∈ sucV gam ⟩` (`:111`), and `[LJ-1.491]` already carried
an ω gate into this frame; `[LJ-1.495]` took its telescope with `ω∈γ` in it
(`agents/tasks/LJ-1-495/Probe495.agda:91`), in the stronger form
`⟨ ω ∈ gam ⟩`. **This task takes the chapter's own weaker form.**

### The witness

`honest-frame-inhabited : HonestFrame {n = 9} KV.iA KV.iK γ₆`
(`Probe534.agda:183-192`). The frame vector is

    γ₆ = B₀ ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ KV.Kenv     (Probe534.agda:169)

which is `KValue.Kenv` under the six conses `[LJ-1.495]` left free
(`agents/tasks/LJ-1-495/Probe495.agda:166-169`). **Slot zero is the rows' own
carrier slot** (`envK-mem`'s `bi` is `suc⁶ zero` over a six-deep cons, which
is `lookup zero γ'`, `TwelveAgree.lagda.md:186-191`), so it takes `B₀` and
conjunct 7 is `refl`. **Slot one is the value table**, so it takes a member of
the level and conjunct 2 is `KFacts.numK0`. The other four conses are read by
no conjunct.

The eight terms, in order:

| # | term | from |
|---|---|---|
| 1 | `layer-trans (Lset-layer lam)` | `src/L/Constructible.lagda.md:183`, `:246` |
| 2 | `KFacts.numK0` of `KValue.facts` | `src/L/Condensation.lagda.md:7411` |
| 3 | the same, transported by `numeralL-fst 0` | |
| 4 | `SupplyEnv.sucK` | `src/L/Coding/EnvSupply.lagda.md:204` |
| 5 | `pairK-V`, built from `KFacts.pairK` | `Probe534.agda:171-181` |
| 6 | `SupplyMerge.finSetK` | `src/L/Coding/EnvSupply.lagda.md:906` |
| 7 | `refl` | |
| 8 | `SupplyEnv.envSetK` | `src/L/Coding/EnvSupply.lagda.md:140` |

**NOTHING IN THE WITNESS IS NEW MATHEMATICS.** Every conjunct is a term the
tree already holds. That is the result: the four NEW hypotheses are new to
`TFacts`, not to `src/`.

### What the frame does NOT collect, and why

A second group of extras binds a ROW's own variable and not a slot of the
frame: `zK` and `aK` (`valV` `:595`, `wKfact` `:615`), `zK` and `bK` (`valW`
`:605`), `eK` and `tK` (`tmValK` `:576-577`), `xK` (`consK-forall` `:634`,
`consK-allin` `:649`), `yaK` (`consK-exist` `:662`).

`TwelveAgree.lagda.md:356-358` already rules this group:

> are the rows' binders; the facts are derivations, not hypotheses

**A UNIFORM VERSION OF ANY OF THEM WOULD SAY EVERY VALUE OF `S` LIES IN `K`,
AND WOULD BE FALSE.** They belong at the call site. They are correctly absent
from a collected frame, and the mathematician does not have to price them.

**ONE EXTRA IS NEITHER A SLOT FACT NOR A BINDER MEMBERSHIP.**
`consK-forall` `:632-633` and `consK-allin` `:647-648` take `g : Fin k → V ℓ`
and `fst z ≡ env g`: the row's `z` IS an environment. The tree never derives
this from the satisfaction, because `consAtL-adequate`
(`src/L/Coding/Model.lagda.md:1487-1491`) takes the same two as inputs.
**The consumer owes it, and no frame can pay it.**

## THE ONE HYPOTHESIS THAT CANNOT JOIN

**`someEnv` IS THE ONE FIELD WHOSE HONEST FORM ASKS FOR SOMETHING THE RECORD
FIELD REFUSES TO GIVE.**

- `SupplyEnv.someEnv` (`src/L/Coding/EnvSupply.lagda.md:417-424`) takes a
  numeral arity at `:418`.
- The field it would fill is `someEnv : someEnvDef {n} K γ'`
  (`TwelveAgree.lagda.md:289`), and `someEnvDef`
  (`src/L/Condensation/LowerAgree.lagda.md:52-58`) binds `ar` with
  `⟨ fst ar ∈ K ⟩` and nothing else.

So filling that field asks for the arity hypothesis UNIFORMLY over `K`. That
is `ArNumUniform` (`Probe534.agda:246-249`).

**IT IS REFUTED BY THE COLLECTED FRAME'S OWN CONJUNCTS 3 AND 5.**
`arNum-uniform-conflicts` (`Probe534.agda:251-271`) takes any
`HonestFrame A K γ` and any `ArNumUniform K γ` and returns `⊥`. The witness is
`prʟ (numeralL 0) (numeralL 0)`: conjunct 5 puts it in `K` from conjunct 3
twice, and a self-pair is not an ordinal, so it is not a numeral
(`pr-self-not-numeral`, `Probe534.agda:226-228`).

**THIS IS `[LJ-1.507]`'s REFUTATION, RE-MEASURED AND WIDENED.**
`[LJ-1.507]` refuted `someEnvDef-gap` at `[LJ-1.504]`'s frame with
`KValue.facts` in hand (`agents/tasks/LJ-1-507/lj-1.507-report.md:24-31`:
"**NO-GO, STATED. THE GAP IS NOT UNPAID. IT IS FALSE.**"). **The statement in
this file needs no frame at all**, only two conjuncts of the collected frame,
so it holds at EVERY site the collected frame holds. I did not import that
probe; the three library steps and `pr-self-not-ord` are rebuilt here
(`Probe534.agda:200-228`), because a measured cure does not transfer by
analogy (`AGENTS.md:45`).

**WHAT THIS MEANS FOR THE RECORD.** The honest forms can all be used at one
frame. **Fifty-eight of the fifty-nine fields have no obstruction from the
frame.** `someEnv` is the one that cannot be reached from it, and the reason
is not the frame: it is that `someEnvDef`'s own type is too weak to call its
supplier. **So the record does not need SPLITTING. `someEnvDef` needs its
arity hypothesis, or `someEnv` needs a different supplier.** That is a
statement about one type and not about the design.

## D-10, BEFORE ANY AGDA

The brief ordered this first.

**I did not read `[LJ-1.512]`'s census. It is not in this tree**:
`agents/tasks/LJ-1-512/` holds `LJ-1.512.md` and nothing else. Every line
above and below is re-derived from `src/`.

The walk produced the two telescopes and the eight extras of the section
above. Three findings came out of it before any Agda ran, and all three held:

1. **Seven of `SupplyEnv`'s eight parameters are `KValue`'s telescope.** So
   the outer frame was never in doubt; only the extras were.
2. **`TFacts` has no slot for the carrier `B₀`, and nine forms need one.**
   `envK-gen` and `envInK-gen` take `lookup bi γ ≡ B₀`, and the five `envK-*`
   plus four `envInK-*` all go through them. The rows read their carrier at
   `lookup zero γ'`, and `KValue`'s own `iA` slot holds the same value, so
   the pin is `refl` at this frame and free.
3. **The `TK` extra is nine forms and one slot.** It is the largest single
   group and it is one conjunct.

**AND THE PREDICTION I MADE BEFORE THE AGDA: the frame is inhabited, and
`someEnv` is the one form that cannot be reached from it.** Both held.

## W3

The brief named the witness as the widest unmeasured term and gave no
estimate. **The measured answer is 2.30 s for the whole file and the witness
is eight one-line terms. The estimate the brief would not invent is now a
number: the witness was never the cost. THE STATEMENT WAS.**

### FOUR WALLS, AND WHAT THEY MEASURED

**Run 0 is a WALL. Reported, not rerun.** `runs/w3-0.time`:
`agda: Heap exhausted; Current maximum heap size is 8589934592 bytes
(8192 MB)`, after `real 132.91` s. The file is kept verbatim at
`runs/W3.agda.wall.txt`. **I did not rerun that file.** Every run below is a
different file and a controlled change.

| run | file | what it holds | result |
|---|---|---|---|
| 0 | `runs/W3.agda.wall.txt` | the frame as a RECORD, plus `module SE = SupplyEnv …` and `module SM = SupplyMerge …` inside the eight-parameter frame, plus the witness | **WALL**, 132.91 s (`runs/w3-0.time`) |
| 1 | `runs/W3b.agda` | the same, with both module APPLICATIONS replaced by qualified applications | **WALL**, 116.63 s (`runs/w3-1.time`) |
| 2 | `runs/R.agda` | the RECORD ALONE. No frame, no witness | **WALL**, 104.43 s (`runs/r-0.time`) |
| 3 | `runs/I.agda` | the same imports, no type at all | green, **1.04 s** (`runs/i-0.time`) |
| 4 | `runs/F.agda` | eight ONE-field records, one per conjunct | **WALL**, 100.26 s (`runs/f-0.time`) |
| 5 | `runs/T.agda` | the eight conjuncts as a PRODUCT, token for token | green, **1.14 s** (`runs/t-0.time`) |
| 6 | `runs/G.agda` | conjuncts 1, 2, 3 as one-field records | green, **1.04 s** (`runs/g-0.time`) |
| 7 | `runs/H.agda` | conjunct 4, `sucK`, ALONE as a one-field record | **WALL**, 101.38 s (`runs/h-0.time`) |
| 8 | `runs/J.agda` | conjuncts 5, 6, 7, 8 as one-field records, no `sucK` | green, **1.21 s** (`runs/j-0.time`) |

**RUN 1 IS THE ONE THAT KILLED MY FIRST GUESS.** I read the wall as
`[LJ-1.62]`'s module-telescope cost and removed both module applications.
It walled again. The module applications were not the cost and I say so
rather than leave the guess standing.

**THE ANSWER IS P-x, AND IT IS RE-MEASURED HERE AND NOT TRANSFERRED.**
`dev/LESSONS.md:3630` and `TwelveAgree.lagda.md:126-128` both name it. Runs 6,
7 and 8 measure it at THIS site:

- **Seven of the eight conjuncts are free as record fields.** 1.04 s and
  1.21 s, both equal to the no-type baseline of 1.04 s.
- **`sucK` alone walls at 8 GB.** 101.38 s.
- **The same eight conjuncts as a product cost 0.10 s over the baseline.**

`archive/dev/LJ-dispatch-index.md:234` says the same of `[LJ-1.158]`'s site,
and this task confirms it at its own site rather than citing it.

**SO THE COLLECTED FRAME IS A PRODUCT.** The brief allowed "one record or
telescope" and the measurement chose. **A `TFacts` replacement that puts
`sucK` in a field would not typecheck at 8 GB**, which is why
`TwelveAgree.lagda.md:340-341` keeps it a telescope hypothesis today. Any
projection-of-honest-forms design must keep it there.

**NO HEAP EVENT IN THE DELIVERED FILE.** `Probe534.agda` is 273 lines, three
forced rechecks at 2.31, 2.30 and 2.30 s.

## FOR THE NEXT BRIEF

1. **The frame is satisfiable, so the projection design is not blocked.** The
   mathematician can rule on replacing `TFacts` with a projection of the
   honest forms. Four hypotheses are NEW to the record and all four have
   terms in `src/` at `KValue`'s frame.
2. **`sucK` MUST STAY OUT OF ANY RECORD FIELD.** Measured here, 8 GB, run 7.
3. **`someEnvDef` IS THE ONE TYPE TO FIX**, not the record. It binds `ar` too
   weakly to call its own supplier, and the uniform repair is refuted.
4. **THE CONSUMER STILL OWES `fst z ≡ env g`** at the two `consK-*` forall
   sites. No frame can pay it and `consAtL-adequate` will not derive it.
5. **The `envSetK` field is generic in `B` and the honest form is not.**
   Either the field is pinned to the carrier slot, or a second supplier is
   owed for a general `B`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` **READ AND USED.** `:234`:

  > | LJ-1.158 | Collapse the Agree telescopes into one record | WING 2.06x TO 1.60x, HALF THE GAP | TwelveAgree behaved BETTER, not worse: DeadCode by 138x. sucK is the only waller |

  It named `sucK` as the waller at `[LJ-1.158]`'s site. I did not transfer it:
  runs 6, 7 and 8 re-measure it here (`AGENTS.md:45`).
- `archive/dev/JOURNAL-archived.md` **not read.** The wall was settled by
  measurement in this worktree, and a journal carries no line I could check.
- `archive/dev/JOURNAL.md` **not read**, for the same reason.
- `archive/dev/DECISIONS-archived.md` **declined.** It resolves a bare `D<n>`
  series, and no `D<n>` code appears in this brief or in this task.
- `archive/dev/PLAN-archived.md` **declined.** This task changes no plan row
  and quotes no plan number.

## LITERATURE USED

**NO HIT USED.** This task is a satisfiability measurement over types that
already exist in `src/`. It states no new mathematics and takes no definition
from a source.

- `dev/literature/devlin-II5.md` **not read.** It is Devlin's II.5, and the
  collected frame quotes no Devlin statement.
- `dev/literature/digest.md` **not read**, for the same reason.
- `dev/literature/truncation-and-selection.md` **declined.** The `∥_∥₁` in
  `ArNumUniform` is copied from `someEnvDef`'s own type
  (`src/L/Condensation/LowerAgree.lagda.md:53`) and is not a design choice
  this task made.
- `dev/literature/terms-2026-08.md` **declined.** I added no term and no
  `dev/glossary.toml` entry.
- `dev/literature/geology.md` **declined.** No stage-geology statement is
  used.

## FILES

Written, all under `agents/tasks/LJ-1-534/`:

- `Probe534.agda`, 273 lines, the deliverable.
- `lj-1.534-report.md`, this file.
- `runs/`: nine Agda files and the `.out` and `.time` of every run.
  `W3.agda` is run 0's file and `W3.agda.wall.txt` is a byte copy of it, kept
  so the walling text survives even if the `.agda` is ever touched. The other
  eight are `W3b.agda`, `R.agda`, `I.agda`, `F.agda`, `T.agda`, `G.agda`,
  `H.agda` and `J.agda`. **Four of them wall at 8 GB and are meant to**:
  `W3.agda`, `R.agda`, `F.agda` and `H.agda`. Nothing typechecks them, because
  `make typecheck` reads only `src/Everything.lagda.md` (`Makefile:26`, `:50`).

No `review-of-*.md` is written. The obligation is delivered and the verdict is
GO, so there is no stop to state.
