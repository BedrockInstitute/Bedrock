# LJ-1.553 report: ONE MEMBERSHIP BUYS NINE FIELDS, NOT THIRTEEN AND NOT SEVEN

slot: `coder`. I wrote this file early as a skeleton and I filled it as the
runs landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-553/`. Agda ran under the caliber that the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **No heap event, no WALL.**

TARGET: one term `graph-in-K-discharges` in `agents/tasks/LJ-1-553/Probe553.agda`.
The brief asks for the `TFacts` fields that ask for a membership in `K`,
collected at `KValue`'s frame under ONE supplied membership. Nothing lands in
`src/`. I did not build a `TFacts` value. I did not collect the 38 or the 37
again. I did not trim the telescope. I did not edit `src/`. I postulated
nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection and it does not start phase 3. No Boundary clause is in
conflict.

## VERDICT

**GO, AND THE COUNT IS 9 OF THE 13.**

1. **The brief gives two possible answers to D-10, thirteen or seven. Both are
   wrong.** The count is **NINE**: the seven `subK-*` fields, PLUS `valK` and
   `valK-un`. Section `D-10` gives the reading at `file:line`.

2. **`graph-in-K-discharges` typechecks** (`Probe553.agda:354-361`, top-level
   alias at `:364`), `--safe` at `:1`, exit 0, no hole, no postulate, no
   `TERMINATING`, no warning on any run (`runs/full-0.out`). It typechecked on
   its first full run (`runs/try-1.time`, 3.56 s). Nothing was weakened.

3. It PASSes the program's witness meter:
   `/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-553
   --brief agents/tasks/LJ-1-553/LJ-1.553.md`, exit 0, 3.94 s,
   **0 UNRESOLVED of 1**, `probe_red=False` (`runs/witness-0.out`).
   `.venv/bin/python` is absent in this worktree, as `[LJ-1.512]`,
   `[LJ-1.545]` and `[LJ-1.551]` all found. I added no dependency.
   `/opt/homebrew/bin/python3.11 scripts/gate/check-probes.py --check` is clean
   (`runs/check-probes.out`, 6315 tracked files, no probe outside
   `agents/tasks/`). `check-fences.py`, `check-rule-ids.py`, `lint-agda.py` and
   `lint-prose.py` are also clean (`runs/check-fences.out`,
   `runs/check-rule-ids.out`, `runs/lint-agda.out`, `runs/lint-prose.out`).

4. **W3 IS GO AND IT RAN FIRST, ALONE.** The supplied membership is inhabited
   at `KValue`'s frame at TWO instantiations, one of them the carrier stage
   itself (`Probe553.agda:88-132`, top-level alias `:134`). The `[LJ-1.71]` failure that the brief
   warns about does not happen here. Section `W3` says why the guard is weaker
   at this site than it was at `[LJ-1.551]`, because the graph slot is a FREE
   cell.

5. **THE COVERED COUNT GOES FROM 37 TO 46 OF 59, NOT TO 51.** The brief says a
   GO takes it from 38 to 51. Two corrections apply. `[LJ-1.551]` measured the
   clean set at 37, not 38 (`agents/tasks/LJ-1-551/lj-1.551-report.md:23`). And
   this task adds 9, not 13. 37 + 9 = 46.

6. **THE NINE-FIELD OBLIGATION FILE COSTS 695,418,880 B AND 3.17 s, WHICH IS
   8.10 PERCENT OF THE 8 GiB CAP.** `[LJ-1.551]`'s 37-field obligation, re-run on THIS pane for
   comparison, costs 1,069,957,120 B and 4.75 s. Section `THE PRICE`.

I did not write `review-of-graph-in-K.md`. The obligation is inhabited, so the
verdict on the obligation is GO. The correction in `D-10` is a correction of a
count. It is not a stop on the target.

**A NOTE ON THE RATIO BAR.** My write scope is one raw `.agda` probe and two
`.md` files. A raw `.agda` file carries no ` ```agda ` fence, so the in-fence
divisor is 0 and the bar cannot fire on this return, as my role section states.

## 0. THE PREDECESSORS, TAKEN FROM THEIR REPORTS

Audit F1 (`dev/pod/audit-2026-08-20.md`) says a module hypothesis taken from a
predecessor is the type that the predecessor DELIVERED, read from its report
and its probe. I opened both for both.

- **`[LJ-1.551]` is GO** (`agents/tasks/LJ-1-551/lj-1.551-report.md:23`, which
  reads `**GO, AND THE COUNT IS 37, NOT 38.**`). I take its FRAME from
  `agents/tasks/LJ-1-551/Probe551.agda:337-338` and I re-state it in my own
  file rather than importing its probe. I do NOT take its 37 fields: the brief
  forbids collecting them again.
- **`[LJ-1.508]` is the source of the hypothesis shape.** Its report
  (`agents/tasks/LJ-1-508/lj-1.508-report.md:361`) reads
  `grep -rnE "fst \(lookup T γ'?\) ∈ fst \(lookup .*K" src/`. COUNT: **0**.`
  So the membership is stated NOWHERE in `src/`. That is why this task supplies
  it and inhabits it, and claims it nowhere else.

Neither is a NO-GO on a statement that I inhabit here, so no stop is owed on
that account.

## D-10, BEFORE ANY AGDA: THE COUNT IS NINE

The brief offers two answers: one membership discharges all thirteen, or it
discharges only the seven that state the graph slot character for character.
**I read all thirteen at first hand and the answer is neither.**

**THE TEST IS NOT "IS IT THE SAME KIND OF ASK". IT IS "IS IT THE SAME
PROPOSITION AT THE RECORD'S FRAME".** `[LJ-1.551]` grouped the thirteen by
kind and that grouping is correct. A group by kind does not settle
reachability, because a membership at a binder that the FIELD ITSELF
quantifies over is a different proposition for each instance.

### THE NINE THAT ONE MEMBERSHIP REACHES

The supplied hypothesis is one proposition:

```
⟨ fst (lookup (suc zero) γ') ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
```

**THE SEVEN `subK-*` FIELDS.** Each honest form goes through
`SupplyEnv.Fact.subK-gen` (`src/L/Coding/EnvSupply.lagda.md:481-487`) or
`subKSucc-gen` (`:489-495`), whose hypothesis is
`⟨ fst (lookup T γ) ∈ fst K ⟩`. At the record's frame the `T` index of each
field strips the field's own prefix cells and lands on `lookup (suc zero) γ'`,
because `lookup (suc i) (x ∷ xs)` reduces to `lookup i xs`. The seven and their
`T` index, against the prefix length of each field's environment:

| field | record line | prefix cells | `T` index | lands on |
|---|---:|---:|---:|---|
| `subK₁-and` | `:265` | 7 | 8 | `lookup (suc zero) γ'` |
| `subK₀-and` | `:271` | 7 | 8 | `lookup (suc zero) γ'` |
| `subK₁-imp` | `:277` | 8 | 9 | `lookup (suc zero) γ'` |
| `subK₀-imp` | `:283` | 8 | 9 | `lookup (suc zero) γ'` |
| `subK-neg` | `:290` | 6 | 7 | `lookup (suc zero) γ'` |
| `subK-un` | `:311` | 6 | 7 | `lookup (suc zero) γ'` |
| `subK-allin` | `:326` | 7 | 8 | `lookup (suc zero) γ'` |

All lines are `src/L/Condensation/TwelveAgree.lagda.md`.

**AND TWO MORE, WHICH THE BRIEF PUTS OUTSIDE THE SEVEN.** The honest forms of
`valK` (`src/L/Coding/EnvSupply.lagda.md:462`) and `valK-un` (`:471`) read
`(C T : S) → ⟨ fst T ∈ fst K ⟩`, with `T` a FRESH binder of the honest form.
The brief calls this "a fresh binder" and treats it as a different ask.
**It is not, because the honest form's `T` is an argument that the DISCHARGE
chooses.** The record's `valK` (`src/L/Condensation/TwelveAgree.lagda.md:173-176`)
carries the premise

```
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
```

at `:175`, and the honest form's matching premise is `⟨ pr (fst c) (fst yc) ∈ fst T ⟩`
(`src/L/Coding/EnvSupply.lagda.md:466`, one line above the conclusion). So `T`
is FORCED to `lookup (suc zero) γ'`, and `⟨ fst T ∈ fst K ⟩` becomes the same
proposition as the seven. `valK-un` is the same at `:179` against `:475`.
**So the count is nine and not seven.**

### THE FOUR THAT IT DOES NOT REACH, AND WHY NO MEMBERSHIP CAN

`valV`, `valW`, `wKfact` and `consK-exist` ask for a membership at a binder
that the RECORD FIELD ITSELF quantifies over. The binder is universally
quantified in the field's own type, so a single supplied membership names a
different set and cannot fill it.

| field | record line | the field's own binders | the honest form asks | honest line |
|---|---:|---|---|---:|
| `valV` | `:244` | `(E yc b a ar c z v w : S)` | `⟨ fst z ∈ fst K ⟩` and `⟨ fst a ∈ fst K ⟩` | `:595` |
| `valW` | `:250` | `(E yc b a ar c z v w : S)` | `⟨ fst z ∈ fst K ⟩` and `⟨ fst b ∈ fst K ⟩` | `:605` |
| `wKfact` | `:256` | `(E ya yc b a ar c z w : S)` | `⟨ fst z ∈ fst K ⟩` and `⟨ fst a ∈ fst K ⟩` | `:615` |
| `consK-exist` | `:317` | `(ya yc a ar c E z x e' : S)` | `⟨ fst ya ∈ fst K ⟩` | `:662` |

Record lines are `src/L/Condensation/TwelveAgree.lagda.md`. Honest lines are
`src/L/Coding/EnvSupply.lagda.md`.

**THE FIELD'S OWN HYPOTHESIS DOES NOT CONSTRAIN THOSE BINDERS EITHER.** The
three `tmValAt` fields give only `⟨ γ ⊨ tmValAt t e v ⟩`, and
`SupplyEnv.Fact.tmValK` (`src/L/Coding/EnvSupply.lagda.md:575-593`) needs
`eK` and `tK` in ADDITION to it: `varCase` consumes `eK` at `:588` and
`conCase` consumes `tK` at `:591-592`. `consK-exist`
(`src/L/Coding/EnvSupply.lagda.md:661-667`) is `Ktr (h .snd) yaK`, so it
consumes `yaK`. **I did not weaken any of the four and I did not build them.**
The brief says a field that needs a different membership is not one of the
thirteen: I name them and I leave them.

## W3, THE WIDEST UNMEASURED TERM

**GO. THE MEMBERSHIP IS INHABITED AT `KValue`'s FRAME, AT TWO INSTANTIATIONS.**

**AND THE GUARD IS WEAKER HERE THAN IT WAS AT `[LJ-1.551]`. I SAY SO RATHER
THAN CLAIM A STRONG PASS.** `[LJ-1.71]`'s `tagEq` was uninhabited because its
slot was PINNED (`archive/dev/LJ-dispatch-index.md:135`). The graph slot is
`lookup (suc zero) γ'`, which at this frame is the FREE cell `g1`
(`agents/tasks/LJ-1-551/Probe551.agda:337-338`). A free cell can be
instantiated, so a single witness proves only that the hypothesis is not
absurd. I give two, and the second is the one that carries weight.

- **(a) `g1 := numeralL 0`** (`Probe553.agda:116-117`), discharged by
  `KValue.facts .numK0`. This is the cheap witness. It proves non-vacuity and
  nothing more.
- **(b) `g1 := SE.B₀ = LsetS gam ordγ`, THE CARRIER STAGE ITSELF**
  (`Probe553.agda:124-126`), discharged from `SupplyEnv.B₀∈σ`
  (`src/L/Coding/EnvSupply.lagda.md:127`) and `SupplyEnv.σ∈λ` (`:121`) through
  `Lset-mono` (`src/L/Constructible.lagda.md:355`). A value graph over the
  carrier is a set at that scale, so this witness sits at a set the graph slot
  could hold.

`membership-inhabited` (`Probe553.agda:129-132`, top-level alias `:134`) is ONE
value with the two witnesses at one frame.

W3 alone, three forced rechecks with the interface deleted before each
(`runs/w3-0.time` to `runs/w3-2.time`; the file at that run is
`runs/Probe553.w3-only.agda.txt`, 119 lines): **2.47 to 2.52 s, median peak RSS
685,637,632 B, 7.98 percent of the 8 GiB cap.** Exit 0 on the first run. The
brief estimated about 20 lines and under 30 seconds. It was 119 lines, most of
them the import header that the file needs anyway, and 2.5 seconds.

**SO THE TASK WAS NOT REFUTED BEFORE A FIELD WAS TOUCHED.**

## THE OBLIGATION

`NineOfThirteen` (`Probe553.agda:157-209`) states the nine fields ONCE at a
generic `K` and a generic `γ'`, at `TFacts`'s own indices (W2). `Discharge`
(`:231-293`) fills them from `SupplyEnv.Fact`. `Frame` (`:333-361`)
instantiates at `n = 9` against `KValue`'s `Fin 14`.

**EVERY FIELD TYPE IS COPIED VERBATIM OUT OF THE MASTER**, extracted with `sed`
and not retyped, from `src/L/Condensation/TwelveAgree.lagda.md:173-180`,
`:265-288`, `:290-295`, `:311-316` and `:326-331`.

**`statement-matches` (`Probe553.agda:305-315`) is Agda's word that the nine
types ARE `TFacts`'s own.** Every field is read off a `TFacts` value by
projection, with no coercion, no `subst` and no re-association. **It is not
part of the obligation and the obligation never calls it.** It is
`[LJ-1.545]`'s device at nine fields.

**EVERY ONE OF THE NINE IS ONE APPLICATION AND NOTHING ELSE.** Seven are
`F.subK-gen` or `F.subKSucc-gen`; two are `F.valK` and `F.valK-un`. **No
`subst` was added at any field, and no field was weakened.** The slot arguments
make the supplied membership fit DEFINITIONALLY, because
`lookup (suc i) (x ∷ xs)` reduces to `lookup i xs`.

### THE ONE THING THAT RESISTED: `Ktr` IS NOT THE RECORD'S `transK`

**`SupplyEnv.Fact` needs transitivity over `V ℓ` and the record supplies it
over `S`, and the second cannot produce the first.**

- `Fact` takes `(K : S) (Ktr : isTransV (fst K))`
  (`src/L/Coding/EnvSupply.lagda.md:450`), and `isTransV`
  (`src/L/Constructible.lagda.md:83-84`) quantifies over `𝒮ᵥ`, that is over
  `V ℓ`.
- The record's `transK` (`src/L/Condensation/TwelveAgree.lagda.md:262-264`)
  reads `(x a : S) → ...`, that is over constructible sets only.
- `prK`, which every one of the nine goes through
  (`src/L/Coding/EnvSupply.lagda.md:452-459`), applies `Ktr` at the
  intermediate `⁅ x , y ⁆` (`:455`), and that intermediate carries no `isL`
  witness. So the `S` form cannot be lifted.

**THIS DID NOT COST THE OBLIGATION A SECOND HYPOTHESIS, BECAUSE THE FRAME PAYS
IT FROM THE TREE.** `Ktr‡` (`Probe553.agda:349-352`) is
`layer-trans (Lset-layer lam)`, because `lookup (suc^6 iK) γ‡` reduces to
`LsetS lam ordλ` (`src/L/Condensation.lagda.md:7389-7390` with `iK = suc zero`
at `:7397`), whose `fst` is `Lset lam`. **If that stops being definitional,
this file stops checking.** So the frame telescope is `KValue`'s seven, then
`ω∈σ`, then the five free cells, then ONE membership, and nothing else.

**`ω∈σ` IS IN THE TELESCOPE AND THE NINE NEVER CONSUME IT.** It is there only
because the frame is `[LJ-1.551]`'s, whose cell 0 is `SE.B₀`. A later task
that wants only these nine can drop `SupplyEnv` and the cell 0 pin.

## HOW MANY THE ONE MEMBERSHIP BOUGHT

**NINE.** By name, with the record line of each:

| # | field | `TwelveAgree.lagda.md` | filled by |
|---:|---|---:|---|
| 1 | `valK` | `:173` | `Fact.valK` `EnvSupply.lagda.md:462` |
| 2 | `valK-un` | `:177` | `Fact.valK-un` `:471` |
| 3 | `subK₁-and` | `:265` | `Fact.subK-gen` `:481` |
| 4 | `subK₀-and` | `:271` | `Fact.subK-gen` `:481` |
| 5 | `subK₁-imp` | `:277` | `Fact.subK-gen` `:481` |
| 6 | `subK₀-imp` | `:283` | `Fact.subK-gen` `:481` |
| 7 | `subK-neg` | `:290` | `Fact.subK-gen` `:481` |
| 8 | `subK-un` | `:311` | `Fact.subKSucc-gen` `:489` |
| 9 | `subK-allin` | `:326` | `Fact.subKSucc-gen` `:489` |

**THE ONES IT DID NOT REACH, OF THE THIRTEEN: FOUR.** `valV` (`:244`), `valW`
(`:250`), `wKfact` (`:256`) and `consK-exist` (`:317`). Section `D-10` gives
the reason and the honest line of each. **They are not one debt. They are three
term-value debts and one `ya` debt, all at binders the field quantifies over.**

**THE STANDING TOTAL.** `[LJ-1.551]` collected 37. This task adds 9. **46 of
the 59 fields now have a collected form.** The remaining 13 are: the 4 above,
the 3 of the next section, `envSetK`, and the 5 with no supplier at all
(`codesK`, `codesK-un`, `t0eq`, `t1eq`, `t0K`), which `[LJ-1.512]` measured and
I did not re-open. 4 + 3 + 1 + 5 = 13.

## THE REMAINING THREE

`[LJ-1.551]` says three of the sixteen are NOT memberships in `K`. I read all
three at first hand.

1. **`consK-forall`** (`src/L/Condensation/TwelveAgree.lagda.md:322-325`). The
   honest form (`src/L/Coding/EnvSupply.lagda.md:631-641`) asks for an
   ENVIRONMENT WITNESS, `{k : ℕ} (g : Fin k → V ℓ)` with `fst z ≡ env g`
   (`:633`), plus two `K` memberships, because it must rebuild `e'` as
   `env (cons x g)` before transitivity applies.
2. **`consK-allin`** (`:332-335`). The honest form
   (`src/L/Coding/EnvSupply.lagda.md:646-657`) asks for the same environment
   witness at a one-cell-deeper environment (`:648`), so it is the same
   construction and not the same instance.
3. **`someEnv`** (`:289`, whose type is `someEnvDef {n} K γ'` at
   `src/L/Condensation/LowerAgree.lagda.md:52-59`). `someEnvDef` ALREADY
   carries its three `K` memberships, so the honest form
   (`src/L/Coding/EnvSupply.lagda.md:417-424`) asks for one thing more: the
   truncated numeral arity `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` (`:418`), which is
   the hypothesis that the nine clean env rows already carry and pay.

**I DID NOT BUILD ANY OF THE THREE.**

## THE PRICE

Every row is a WHOLE-FILE total on ONE pane, which is what `[LJ-1.551]`'s band
finding demands (its report, section `THE ONE MEASUREMENT I CANNOT EXPLAIN`).
No row is a baseline subtraction. Three forced rechecks per row, with the
interface deleted before each. The cap is 8 GiB, 8,589,934,592 B.

| fields | file | seconds | peak RSS (median) | of the cap | runs |
|---:|---|---|---:|---:|---|
| n/a | W3 alone, NOT a baseline | 2.47 to 2.52 | 685,637,632 B | 7.98 % | `runs/w3-0..2.time` |
| **9** | **this obligation alone** | **3.16 to 3.21** | **695,418,880 B** | **8.10 %** | `runs/obl-0..2.time` |
| 9 | the DELIVERED file | 3.57 to 3.59 | 733,364,224 B | 8.54 % | `runs/full-0..2.time` |
| 37 | `[LJ-1.551]`'s obligation, HERE | 4.73 to 4.77 | 1,069,957,120 B | 12.46 % | `runs/rerun551-obl-0..2.time` |

**THE PANE IS COMPARABLE TO `[LJ-1.551]`'s.** I copied its
`runs/Probe551.obligation-only.agda.txt`, renamed only the module line, and ran
it here (`runs/Probe553.rerun551-obl.agda.txt`). It gives 1,069,957,120 B
against the 1,067,859,968 B that `[LJ-1.551]` reports, a difference of
2,097,152 B, **0.20 percent**. So its curve stands and my row joins it.

**THE SENTENCE THE NEXT BRIEF NEEDS, ABOUT NUMBERS I MEASURED MYSELF: THE
NINE-FIELD OBLIGATION COSTS 65.0 PERCENT OF WHAT THE 37-FIELD OBLIGATION COSTS
ON THE SAME PANE, AND 66.7 PERCENT OF ITS TIME.** Both figures are ratios of
whole-file totals, which is the only form `[LJ-1.551]` says is safe here.

**I GIVE NO PER-FIELD RATE, AND THE REASON IS A MEASUREMENT AND NOT CAUTION.**
A per-field rate needs a baseline, and I have none. **The 685,637,632 B row is
NOT a baseline**: that file carries the full import header AND the W3 term, so
subtracting it from the obligation row measures "nine fields minus one W3 term"
and not "nine fields". The two obligation files are not nested either: mine and
`[LJ-1.551]`'s share no field. `[LJ-1.551]` measured a reproducible 136 MB band
in whole-file peak RSS whose cause it could not isolate, and it warns that a
subtraction can be wrong by a whole band. **So a rate computed here would be
invented. I do not give one.**

**THE REASON THE NINE ARE CHEAP IS VISIBLE IN THE FILE.** Each is one
application of one `EnvSupply.Fact` form, and seven of the nine are the SAME
form at different indices. The elaborator sees `subK-gen` once.

**AGAINST THE BRIEF'S ESTIMATE.** The brief estimated about 180 lines with a
45-line obligation and under 10 seconds of Agda. Delivered: **364 lines**, of
which `NineOfThirteen` is `:157-209` (53 lines) and `Discharge` is `:231-293`
(63 lines); **3.2 s** for the obligation-only file and **3.6 s** for the
delivered one. The line estimate was low because the nine field types are
copied verbatim and are 53 lines by themselves. The time estimate was high.

**NO HEAP EVENT AT ANY AGDA RUN OF THIS TASK.** The highest row is 12.46
percent of the cap and it is not mine.

## W2 AND W4, ANSWERED

**W2.** `NineOfThirteen` (`Probe553.agda:157-209`) states the nine ONCE at a
generic `K` and a generic `γ'`. `Discharge` (`:231-293`) fills them ONCE at the
same generic carrier. `Frame` (`:333-361`) instantiates at `n = 9` in exactly
one place (`:359-361`). **No block in this file is written twice, and nothing
is stated in a fixed form that could have been stated generically.** No
deadline pushed me toward the fixed form, so there is no conflict to report.
DD4's core constraint is at `archive/dev/DD-archived.md:22`.

**W4.** Nothing is retired by this task and nothing moves to `archive/`, so
`dev/ARCHIVE.md` gains no row. The clause's second half asks me to price the
ideal form written fresh today against the chapter I have. **For these nine the
ideal form written fresh today is `SupplyEnv.Fact` with the graph slot as a
MODULE PARAMETER rather than a per-field hypothesis.** The measurement is in
the file: nine fields, one supplied membership, zero `subst`, one application
each. `Fact` already takes `K` and `Ktr` as module parameters
(`src/L/Coding/EnvSupply.lagda.md:450`); it does NOT take the graph slot, so it
repeats the same hypothesis in nine signatures. **I propose no move**, because
a module redesign is the mathematician's call under AD3, and because C-42
(`dev/LESSONS.md:3752`) says I must count the sites before I price a cure. I
counted nine and I priced nothing.

## WHAT THE NEXT BRIEF NEEDS

1. **THE SIXTEEN ARE FOUR PROBLEMS, NOT THREE AND NOT SIXTEEN.** One supplied
   membership (9 fields), a membership at a term binder (`valV`, `valW`,
   `wKfact`), a membership at a value binder (`consK-exist`), an environment
   witness (`consK-forall`, `consK-allin`), and one already-paid truncation
   (`someEnv`). `[LJ-1.551]` said three. The split of its largest group is the
   correction this task measured.
2. **THE THREE `tmValAt` FIELDS ARE ONE DEBT AND IT IS NOT A MEMBERSHIP.**
   `valV`, `valW` and `wKfact` all go through
   `SupplyEnv.Fact.tmValK` (`src/L/Coding/EnvSupply.lagda.md:575-593`) and all
   three need `eK` and `tK` at binders the field quantifies over. **A brief
   that wants them must first say what constrains those binders.** That is a
   mathematical question and it is not mine.
3. **THE NINE ARE CHEAP AND THEY ARE DONE.** The whole obligation file is
   695,418,880 B and 3.17 s, which is 8.10 percent of the cap and 65.0 percent
   of what `[LJ-1.551]`'s 37 cost on the same pane. Nothing in the remaining
   front is expensive because of these nine.
4. **`Ktr` IS THE `V`-LEVEL TRANSITIVITY AND THE RECORD'S `transK` IS NOT IT.**
   Any task that consumes `SupplyEnv.Fact` from inside a `TFacts` telescope
   must pay `isTransV` from the tree, as this file does at `Probe553.agda:352`.
   A brief that assumes `transK` is enough will not typecheck.
5. **A GREEN COLLECTION STILL DOES NOT PREDICT A GREEN APPLICATION.**
   `archive/dev/LJ-dispatch-index.md:137` records a union frame that checked
   green while the APPLICATION heap-walled at the 8 GB cap. **I measured a
   value being BUILT. I did not apply it to anything, and I claim nothing about
   applying it.**
6. **THE GRAPH SLOT IS STILL UNCONSTRAINED IN `src/`.** `[LJ-1.508]` measured
   zero statements about it (`agents/tasks/LJ-1-508/lj-1.508-report.md:361`)
   and this task did not add one to `src/`. The membership is a HYPOTHESIS
   here. Somebody must still prove it at the real frame, where the graph slot
   is not free.

## THE WORKING TREE

Files I created, all inside my write scope:

- `agents/tasks/LJ-1-553/Probe553.agda` (364 lines)
- `agents/tasks/LJ-1-553/lj-1.553-report.md` (this file)
- `agents/tasks/LJ-1-553/runs/` (the `.out` and `.time` pairs for every run
  named above, plus the file variants below)

I did not create `agents/tasks/LJ-1-553/review-of-graph-in-K.md`. I did not
touch `src/`. I did not commit and I did not push.

Agda wrote interface files under `_build/2.8.0/agda/`, which
`dev/build-manifest.toml:117-120` declares `class = "toolchain"`, so no new
lifecycle declaration is owed.

**ONE RUN IN `runs/` IS RED AND I NAME IT.** `runs/try-0.out` is exit 42,
`[NotInScope] pr`: I wrote the nine field types before I added the `V.Coding`
import that `pr` needs. `runs/try-1.out` is the same file with the import
added, exit 0, and it is the first full run of the obligation. Every other run
in `runs/` is exit 0. `runs/final.out` is a last forced recheck of the
delivered file after the report was written, exit 0, 3.54 s.

Every file variant I measured is kept beside its runs, so a critic can re-run
any row of the price table. The delivered file is byte-identical to
`runs/Probe553.delivered.agda.txt` (`diff -q`, checked after the last run).

| file | what it is |
|---|---|
| `runs/Probe553.w3-only.agda.txt` | the file at the W3 runs, 119 lines |
| `runs/Probe553.obligation-only.agda.txt` | the obligation without W3 or `statement-matches`, 290 lines |
| `runs/Probe553.delivered.agda.txt` | the delivered file, 364 lines |
| `runs/Probe553.rerun551-obl.agda.txt` | `[LJ-1.551]`'s obligation-only file, module line renamed |

I read `agents/tasks/LJ-1-551/` and `agents/tasks/LJ-1-508/` and wrote nothing
in either.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.** `:135` reads

  > `| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |`

  This is why W3 ran first and alone, and it is why my W3 section says the
  guard is WEAKER at this site: `[LJ-1.71]`'s slot was pinned and mine is free.
  `:137` reads

  > `| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |`

  which is item 5 of `WHAT THE NEXT BRIEF NEEDS`. `:142` reads

  > `| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |`

  I read it and did NOT act on it: I trimmed no telescope. It is cited only to
  say so, and it is the brief's premise 10.
- **`archive/dev/JOURNAL.md`: NOT READ, declined.** `grep -c` for `TFacts`,
  `KFacts`, `EnvSupply` and `subK` returns 0, 0, 0 and 0 over its 1378 lines.
  It carries nothing about this record.
- **`archive/dev/JOURNAL-archived.md`: NOT READ, declined.** The same four
  counts over its 4280 lines are 0, 0, 0 and 0.
- **`archive/dev/ORCHESTRATION.md`: NOT READ, declined.** The same four counts
  over its 604 lines are 0, 0, 0 and 0. It is the archived operating document
  and this task changes no rule.
- **`dev/ARCHIVE.md`: NOT USED, declined.** The same four counts over its 299
  lines are 0. This task retires no module, so W4 has no row to write there.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: NOT USED, declined.** It is
  the dossier on when a truncation can be untruncated. **Not one of my nine
  fields carries a truncation**: the truncated numeral arity
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` appears in the env rows that `[LJ-1.551]`
  collected and in `someEnv`, which I did not build.
- **`dev/literature/devlin-II5.md`: NOT USED, declined.** It is the
  Condensation Lemma and the GCH in L. It treats transitivity as a property of
  the COLLAPSE image. My transitivity is `isTransV (Lset lam)`, a tree fact
  from `src/L/Constructible.lagda.md:183`, and no source bears on whether
  `lookup (suc^6 iK) γ‡` reduces.
- **`dev/literature/terms-2026-08.md`: NOT USED, declined.** It is the
  terminology dossier for the owner's naming ruling. I added no glossary entry
  and I named no new term.
- **`dev/literature/digest.md`: NOT USED, declined.** It pins the orthodox form
  of the rud route, which is `[LJ-2]` territory. This task touches no rud
  construction.
- **`dev/literature/geology.md`: NOT USED, declined.** It is the set-theoretic
  geology dossier. This task states no ground-model question.
