# [LJ-1.508] report: valK asks about slot one, and slot one has no facts

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-508/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `valK-family` in `agents/tasks/LJ-1-508/Probe508.agda`. The
type is the two `TFacts` fields `valK`
(`src/L/Condensation/TwelveAgree.lagda.md:173-176`) and `valK-un` (`:177-180`),
at `KValue`'s frame under `[LJ-1.495]`'s six-fold shift, under ONE named frame
hypothesis about slot ONE. Nothing lands in `src/`. I did not build a `TFacts`
value. I did not build `valV`, `valW` or `wKfact`. I did not postulate. I did
not use a `TFacts` field as a hypothesis.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It does not start
that collection and it does not start phase 3. No Boundary clause is in
conflict.

## VERDICT

**GO, AND THE BARE FORM IS ALSO REFUTED. Both results, exit 0.**

1. **W3 is NO-GO. `arityK` alone does not close `valK`.** Measured, exit 42,
   and Agda's error names the missing input exactly. Section 2.
2. **The bare field is FALSE at `KValue`'s own frame, with the FULL `KFacts`
   value supplied.** Machine-checked counterexample,
   `agents/tasks/LJ-1-508/Probe508.agda:324-329`. Section 3.
3. **The obligation is delivered under the weakest hypothesis**, and which
   hypothesis is weakest is MEASURED and not argued.
   `valK-family` at `Probe508.agda:216-221`, top-level alias at `:331`.
   Section 4.

`valK-family` PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-508 --brief
agents/tasks/LJ-1-508/LJ-1.508.md`, exit 0, 2.46 s, 0 UNRESOLVED of 1,
`probe_red=False`, `runs/witness-final.out`). `.venv/bin/python` is absent in
this worktree. I added no dependency.

I did not write `review-of-valK-family.md`. The obligation is inhabited.

**A GO here pays two field positions and names ONE hypothesis for 22
declarations, not 23.** Section 5 gives the corrected count.

## 0. THE PREDECESSORS, AND ONE THE BRIEF DID NOT NAME

Audit F1: a predecessor taken as a hypothesis is the REPORT, and the type is
the one that predecessor delivered (`dev/pod/audit-2026-08-20.md:34`).

`[LJ-1.495]` is **GO** (`agents/tasks/LJ-1-495/lj-1.495-report.md:71`). Quote
at `:71`:

> **GO.** `twice` typechecks

`[LJ-1.500]` is **GO** (`agents/tasks/LJ-1-500/lj-1.500-report.md:145`). Quote
at `:145`:

> **GO.** `codesK-family` typechecks (`Probe500.agda:365-372`, with the

`[LJ-1.506]` is **GO** (`agents/tasks/LJ-1-506/lj-1.506-report.md:5`). Its
counterexample is at slot two and it says its own result does not settle this
question (`:236-239`).

**THE ARCHIVE CARRIES A FOURTH PREDECESSOR AT THIS EXACT SITE, AND THE BRIEF
DID NOT NAME IT.** `archive/dev/LJ-dispatch-index.md:227` reads:

> | LJ-1.151 | Probe the one term two dispatches named and nobody ran | GO AT 21 LINES, AND valK IS FALSE | The band tightens on 9 of 25, not all 25. The wall stayed out: the two halves are separable |

**So `valK` HAS been asked about before, and the brief's premise 3 is too
strong.** The brief says `[LJ-1.506]` "NAMED THIS AS UNASKED". What
`[LJ-1.506]` actually wrote is narrower and correct: "**Nobody has asked where
those come from either**" (`agents/tasks/LJ-1-506/lj-1.506-report.md:237`),
about the SOURCE of the field. It did not claim the field had never been
refuted. **I state the difference rather than repeat the stronger claim.**

**WHAT THE OLDER WORK MEASURED, AND WHY IT IS NOT THIS RESULT.**

`[LJ-1.151]` measured the field FALSE when `yc` occurred in NO premise
(`agents/tasks/LJ-1-151/lj-1.151-report.md:23-25`). Quote at `:23`:

> **The frame's `valK`, AS STATED, is REFUTABLE. MEASURED, exit 0, at

`[LJ-1.153]` re-ran that refutation as one of its 36 repairs
(`agents/tasks/LJ-1-153/ProbeLJ1153A.agda:90-96`, `absurd` at `:95-96`). Its
counterexample is the same idea as mine: take `yc` to be the `K` slot itself
and close with `∈-irrefl`.

**THE FIELD WAS THEN REPAIRED, AND TODAY IT CARRIES THE GRAPH ENTRY.**
`src/L/Condensation/TwelveAgree.lagda.md:175` is the premise the repair added:

> `           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩`

`agents/tasks/LJ-1-275/CondControlToday.lagda.md:2739-2746` records the whole
transaction in the tree's own words. Quote at `:2743`:

> `-- at [LJ-1.151]).  The repaired `valK` takes the graph entry as a`

**SO MY REFUTATION IS NOT THEIRS, AND I SAY SO PLAINLY.** Their counterexample
leaves `yc` free of every premise. **Mine SATISFIES the graph-entry premise:**
slot one really does hold `pr c yc` (`Probe508.agda:303-309`). C-42 says a
refutation measures the site it names; the site moved when the field was
repaired, so the repaired field needed its own measurement and now has one.

**`[LJ-1.151]` ALSO BUILT A CURE, AT A CONCRETE LEVEL, AND I DID NOT REUSE
IT.** `Slots.frame-valK` (`agents/tasks/LJ-1-151/ProbeLJ1151A.agda:103-112`)
takes the graph slot's MEMBERSHIP `TK` (`:101`) plus a PIN
`Kis : lookup K γ' ≡ levelK α o` (`:100`), and runs through `isTransV` of the
concrete level (`:55`), not through `KFacts`. `[LJ-1.245]` measured that its
match claim rests on that pin. Quote at
`agents/tasks/LJ-1-245/lj-1.245-report.md:333`:

> | the `LJ-1.151` report's match claim is unconditional | **MEASURED FALSE.** It rests on `Kis`, section 2.6 |

**Nothing in `Probe508.agda` pins anything.** `arityK` comes from `KValue`'s
own `KFacts` value through the six-fold shift, `K` stays the frame's slot, and
the hypothesis I take is strictly weaker than `TK`. Section 4.3 measures that.

## 1. D-10, BEFORE ANY AGDA

D-10 says price the truth of a recorded target before pricing its proof. The
brief asked one question first: does `arityK` or `carrierK`, alone, close
`valK`?

**`arityK` ALONE: NO.** `arityK` is at `src/L/Condensation.lagda.md:6114-6115`:

> `      arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩`

It is transitivity. It consumes an `N` that is ALREADY a member of `K`. The
frame's three premises name exactly three sets: slot two (the code set), slot
one (the value set), and the two Kuratowski layers of `pr c yc` that the shape
equation implies. **Not one of the three is stated to be a member of `K`.** So
`arityK` has no starting point, and the chain stops before its first step.
Section 2 is the machine's version of this paragraph.

**`carrierK` ALONE: NO, AND FOR A REASON THAT IS ARITHMETIC.** `carrierK` is
at `src/L/Condensation.lagda.md:6112-6113`:

> `      carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩`

It is about slot `A`. At `KValue`'s frame under the six-fold shift, `A` is
`suc⁶ iA`, which is **position 6** of `γ'`, because `iA = zero` in `Kenv`
(`src/L/Condensation.lagda.md:7395`) and the six conses shift it by six.
**Slot one is position 1.** Positions 1 and 6 are different slots, so
`carrierK` does not reach the value set.

**THE ANSWER THE BRIEF ASKED FOR, IN THE BRIEF'S OWN WORDS.** The brief wrote:
"If slot one being a member of `K` is what is needed, say so." **It is nearly
what is needed, and the exact answer is weaker than that.** What is needed is
that slot one's MEMBERS are in `K`. Membership of the slot implies it in one
`arityK` step (`Probe508.agda:162-163`) and is strictly stronger
(`Probe508.agda:237-243`). Section 6 states the hypothesis as a type.

**`carrierK` IS THE RIGHT SHAPE AT THE WRONG SLOT, AND THAT IS THE USEFUL
FACT.** `carrierK`'s type IS the hypothesis I take, with the carrier slot
replaced by slot one. So the record already speaks this dialect; it has simply
never said the sentence about slot one.

**ONE MORE THING THE FRAME ALREADY HAS.** `TFacts` does state `transK`
(`src/L/Condensation/TwelveAgree.lagda.md:262`), which `AbstractFrame` turns
into `arityK` with the binder roles swapped (`:350-353`). **So the transitivity
half of this field is NOT a debt at any frame that carries a `TFacts`.** The
whole debt is the slot-one half.

## 2. W3: valK-from-arityK, obligation omitted

**NO-GO. MEASURED, exit 42.**

The W3-only file held ONE module and ONE definition and was 63 lines. It is
kept verbatim at `agents/tasks/LJ-1-508/runs/Probe508.w3-only.agda.txt`.

```agda
valK-from-arityK : (k : ℕ) (c ar a b yc : S)
                 → ⟨ fst c ∈ fst (lookup Cs γ) ⟩
                 → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
                 → ⟨ pr (fst c) (fst yc) ∈ fst (lookup Vs γ) ⟩
                 → ⟨ fst yc ∈ fst (lookup K γ) ⟩
```

`runs/Probe508.w3-only.agda.txt:56-64`.

**I WROTE THE LAST STEP TWICE, AND THE SECOND WRITING IS THE ONE THAT
INFORMS.** The first attempt left the step a hole. Agda answered
`[UnsolvedInteractionMetas]` and named a source position and nothing else
(`runs/w3-0.out`). **That is not evidence about the mathematics.** I then
offered the frame's OWN slot-one premise at that step, so the mismatch would
have to name both sides. It does (`runs/w3-1.out`, `runs/w3-r0.out` to
`w3-r2.out`), and the last line of the error is the whole finding:

> `when checking that the expression pr∈ has type`
> `⟨ fst (prʟ c yc) ∈ fst (lookup K γ) ⟩`

**SO THE MISSING INPUT IS NAMED BY THE MACHINE AND NOT BY ME: the PAIR must be
in `K`.** The frame puts the pair in slot one. Nothing carries it from slot one
into `K`. That is one implication, and it is exactly the hypothesis section 6
states.

**WHAT W3 BOUGHT.** The brief said a GO at W3 would make the field cost nothing
beyond `[LJ-1.495]`'s shift, and that the other twenty two declarations might
fall the same way. **W3 is NO-GO, so that saving does not exist.** What the
NO-GO buys instead is the shape of the debt: it is ONE implication about ONE
slot, and section 5 counts how many declarations share it.

Three forced rechecks of the W3-only file, interface deleted each time
(`_build/2.8.0/agda/agents/tasks/LJ-1-508/Probe508.agdai`), same caliber, one
Agda process, exit 42 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-r0.out` / `w3-r0.time` | 2.32 | 571949056 |
| `runs/w3-r1.out` / `w3-r1.time` | 2.31 | 571981824 |
| `runs/w3-r2.out` / `w3-r2.time` | 2.32 | 571932672 |

Median wall **2.32 s**. Median peak RSS **571949056 bytes**. No heap event.

The brief's W3 estimate was about 20 lines and under 30 seconds. Measured, the
term is 9 lines (`runs/Probe508.w3-only.agda.txt:56-64`) and the file is 63
lines. Wall is 2.32 s. **Nothing is funded against `[LJ-1.500]`'s 3.16 s, and
the brief was right to forbid it: that measured a decoder and this measures a
closure.** Nothing is funded against the estimate either.

## 3. THE BARE FORM IS FALSE, AND THIS MEASURES IT

`valK-bare-is-false` (`Probe508.agda:324-329`), exit 0.

**The statement refuted is `BareValK`** (`Probe508.agda:312-322`): the field
verbatim at `KValue`'s frame, universally quantified over the six cons slots,
**with the full `KFacts` value `facts` supplied**
(`src/L/Condensation.lagda.md:7411`). So nothing here turns on a missing fact
block.

**THE COUNTEREXAMPLE IS DELIBERATELY KIND TO THE CODE HALF.**

- `goodCode = prʟ (numeralL 0) (prʟ (numeralL 0) (prʟ (numeralL 0) (numeralL 0)))`
  (`Probe508.agda:277-280`). It is a well formed four-part binary code and its
  arity component is the numeral 0. **So `[LJ-1.506]`'s refutation is not being
  re-run here**, and no reader can answer this by pinning the code set.
- `good-shape` (`:294-301`) gives the field's shape equation at `k = 0`.
- `codeSlot = sucʟ goodCode` (`:286-287`) and `code∈` (`:290-292`) satisfy the
  code membership.
- `valSlot = sucʟ (prʟ goodCode badVal)` (`:286`, `:288`) and `pair∈` (`:303-309`)
  satisfy the graph entry. **This is the premise `[LJ-1.151]`'s and
  `[LJ-1.153]`'s counterexamples did not have to satisfy**, and it is why this
  measurement is a new one.
- `badVal = LsetS lam ordλ` (`:284`), the bound itself. `lookup (suc⁶ iK) γ'`
  reduces to it, so the conclusion is `Lset lam ∈ Lset lam` and `∈-irrefl`
  (`src/V/Hierarchy.lagda.md:155`) closes it.

**EVERY PREMISE OF THE FIELD IS SATISFIED AND THE CONCLUSION IS ABSURD.** So
the field is not short of a proof. It is short of an input, and the input is
about slot one.

## 4. THE OBLIGATION

**GO.** `valK-family : ValPair {n = 9} iK γ'` (`Probe508.agda:216-221`), with
the top-level alias the witness reads at `:331`.

### 4.1 What it is

`ValPair` (`:103-115`) states the two field types ONCE, at `TFacts`'s own
generic shape `K : Fin (5 + n)` over `γ' : S ^ (11 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:129-131`), character for character
the record's own two fields. Nothing is weakened. The obligation instantiates
it at `n = 9` against `KValue`'s `Fin 14`, the frame `[LJ-1.495]` measured
(`agents/tasks/LJ-1-495/lj-1.495-report.md:55-60`).

The term is `Val.sndK` (`Probe508.agda:151-157`): two `arityK` steps down the
Kuratowski pair, after the hypothesis puts the pair into `K`. It spends
`ChainZ`'s public pair pieces (`src/L/Condensation.lagda.md:2820-2917`) and
re-derives none of them: `Z.y∈pairʟxy`, `Z.ysingl∈prxy` and `Z.prʟxy∈z`.

**THE ROUTE IS THE ONE THE ARCHIVE ALREADY MEASURED.**
`archive/dev/LJ-dispatch-index.md:175` reads:

> | LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |

`[LJ-1.99]` needed four steps because it started from a pair membership plus a
separate `z ∈ K`. **This needs two**, because the hypothesis delivers the pair
into `K` directly and the first two of those four steps are what it replaces.

### 4.2 ONE TERM SERVES BOTH FIELDS, AND THAT IS MEASURED, NOT ASSERTED

`valK` and `valK-un` differ ONLY in the shape equation
(`src/L/Condensation/TwelveAgree.lagda.md:174` against `:178`). **The term
reads neither the shape equation nor the code membership.** Both are bound and
dropped in the record's two clauses (`Probe508.agda:217-221`), and the same
`R.sndK` call fills both.

**COUNT of the field's four premises that the term uses: 1 of 4.** It uses the
graph entry. It ignores `k`, the code membership, and the shape equation.

**THIS IS A FINDING ABOUT THE RECORD AND NOT ABOUT MY TERM.** The code half of
`valK`'s type is inert under this hypothesis. Whether the record wants to keep
premises that no proof of the field consumes is the mathematician's call, not
mine, and section 8 hands it over.

### 4.3 WHICH HYPOTHESIS IS WEAKEST, MEASURED

Three candidates were live. I compared them by machine.

| candidate | type | verdict |
|---|---|---|
| slot one IS in `K` | `⟨ fst E ∈ fst (lookup K γ) ⟩` | sufficient, STRICTLY STRONGER |
| slot one's MEMBERS are in `K` | `SubK E`, `Probe508.agda:146-147` | sufficient, and this is what the obligation takes |
| the pair's second component is in `K` | the conclusion itself | not a frame fact |

`memberSubK` (`:162-163`) turns the first into the second in ONE `arityK` step.

**THE CONVERSE IS FALSE AT THIS FRAME, AND I MEASURED IT RATHER THAN ARGUING
IT.** `subK-is-strictly-weaker` (`Probe508.agda:237-243`), exit 0: take `E` to
be the bound itself. `SubK E` then holds by identity (`subK-K`, `:167-168`)
and `E ∈ K` is refuted by `∈-irrefl`. **So the two are not interchangeable and
`SubK` is the weaker one.**

I took the weaker one. The brief said a hypothesis that pins slot one to a
particular set would be refused; `SubK` names no set at all.

### 4.4 TWO THINGS THIS TASK DID NOT PAY FOR

**`arityK` AT THIS FRAME COSTS ONE LINE, NOT 66, AND I RE-MEASURED IT RATHER
THAN CITING IT.** `[LJ-1.500]` measured that the six-fold shift is definitional
on `arityK` (`agents/tasks/LJ-1-500/Probe500.agda:334-341`), and its report
told the next brief so (`lj-1.500-report.md:405-408`). AGENTS.md:45 says a
measured cure does not transfer by analogy. **So `arityK'`
(`Probe508.agda:190-197`) states the shifted type and has the body
`f .arityK`, and it typechecks here.** COUNT of lines: 8. COUNT of lines
`[LJ-1.500]`'s `six` costs: 66. **This file contains no `KFactsCons`.**

**THE CODE SLOT COSTS NOTHING HERE.** `[LJ-1.500]` had to assume `C∈K` and
`arNumC`. This field needs neither, because the term never looks at the code.

## 5. C-42: THE SWEEP, AND A CORRECTION TO THE COUNT

C-42 says a refutation measures ONE site and never measures how far the shape
extends, so the count comes before any cure is priced.

**COUNT of declarations in `src/` that bind `valK` or `valK-un`: 23.** That
reproduces `[LJ-1.506]`'s count exactly (`lj-1.506-report.md:152-153`): 19
`valK` and 4 `valK-un`. Method: `grep -rnE "(^|[^A-Za-z0-9-])valK(-un)?[[:space:]]*:" src/`.

| file | valK | valK-un |
|---|---:|---:|
| `src/L/Condensation.lagda.md` | 15 | 0 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 1 | 1 |
| `src/L/Condensation/UpperAgree.lagda.md` | 1 | 1 |
| `src/L/Condensation/LowerAgree.lagda.md` | 1 | 1 |
| `src/L/Coding/EnvSupply.lagda.md` | 1 | 1 |

**THE CORRECTION: 22 OF THE 23 SHARE THIS SHAPE, NOT 23.** I classified all 23
by reading each declaration and the nine lines after it.

- **22 carry the graph-entry premise** `⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩`
  and conclude `yc ∈ K`. These are the declarations this task pays.
- **1 does NOT.** `src/L/Condensation.lagda.md:4219-4225` is named `valK` but
  its premise is `tmValAt` and its conclusion is about `v`. **It is a member of
  the `valV` family under the `valK` name.** Section 6 says why the hypothesis
  does not reach it.

**MEASURED, AND IT IS THE HEADLINE OF THE SWEEP: `src/` CONTAINS ZERO
STATEMENTS THAT THE GRAPH SLOT IS IN `K`.** Method:
`grep -rnE "fst \(lookup T γ'?\) ∈ fst \(lookup .*K" src/`. COUNT: **0**. So
the hypothesis is not merely unproved at the frame. **It is unstated anywhere
in the tree**, and `[LJ-1.151]`'s `TK` lives only in a probe
(`agents/tasks/LJ-1-151/ProbeLJ1151A.agda:101`).

**INSIDE `TFacts`, SLOT ONE IS MENTIONED TWICE AND CONSTRAINED NEVER.**
`grep -n "lookup (suc zero) γ'" src/L/Condensation/TwelveAgree.lagda.md`
returns exactly two lines, `:175` and `:179`, and both are the `valK` and
`valK-un` premise. **COUNT of `TFacts` fields that state a property of slot
one: 0.**

**ONE ARITHMETIC I DID NOT SETTLE.** The brief says `TFacts` has 59 field
positions. Counting field declarations my way over the record body
(`src/L/Condensation/TwelveAgree.lagda.md:132-336`, pattern
`^    <name> :`) I get **55**. I do not know which convention gives 59 and I
did not spend the task finding out. **I report my number and my method, and I
do not overwrite the brief's.**

**WHAT THE SWEEP MEANS FOR THE PRICE.** The 22 declarations are module
hypotheses and record fields, not definitions. They do not each carry a
separate debt. **They carry ONE debt, at the slot, and paying it once at the
frame pays all 22.** I price nothing further.

## 6. WHAT SLOT ONE MUST SATISFY

**THE HYPOTHESIS, AS A TYPE.** At `KValue`'s frame, with
`γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv : S ^ 20`:

```agda
valSub : (x : S)
       → ⟨ fst x ∈ fst (lookup (suc zero) γ') ⟩
       → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK)))))) γ') ⟩
```

`Probe508.agda:201-205`. Generically it is `Val.SubK E` (`:146-147`) at any
set `E`, and the obligation instantiates it at `E = lookup (suc zero) γ'`.

**IN WORDS: every member of the value set is a member of `K`.** It says
nothing about WHICH set slot one holds, so it pre-empts nothing that
`[LJ-1.505]` owns.

**IS IT DERIVABLE FROM `KFacts` AT THE SHIFTED INDICES? NO.** Measured three
ways in this file:

1. `arityK` cannot start (section 1, and section 2 is the machine's version).
2. `carrierK` is about position 6 and slot one is position 1 (section 1).
3. The bare field is FALSE with the whole `KFacts` value supplied
   (`Probe508.agda:324-329`). **That settles it: no field of `KFacts`, in any
   combination, closes `valK`**, because a derivation from `facts` would
   contradict the refutation.

**ONE CONDITIONAL, HANDED TO `[LJ-1.505]` AND PINNING NOTHING.**
`valSub-from-carrier` (`Probe508.agda:252-263`), exit 0: **IF** slot one and
the carrier slot hold the same set, `carrierK` supplies `valSub` with no new
frame entry at all. I did not assume the antecedent anywhere. `[LJ-1.505]` owns
whether it is true.

**DOES IT ALSO COVER `valV`, `valW` AND `wKfact`? NO, AND I MEASURED WHY.**
The brief said those three "read the same slot". **They do not read a slot at
all.**

- All three take a satisfaction premise `tmValAt t e v`
  (`src/L/Condensation/TwelveAgree.lagda.md:244-249`, `:250-255`, `:256-261`).
- `tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v))`
  (`src/L/Coding/Model.lagda.md:1702`).
- `appAt f x y` is adequate to `pr x y ∈ f` (`src/L/Coding/Model.lagda.md:161`
  and `:166-175`).
- In all three fields the `e` argument points at a BOUND VARIABLE of the field
  (`z`, at position 2 of the field's own extended environment), not at a slot
  of `γ'`.

**SO THE SHAPE TRANSFERS AND THE SITE DOES NOT.** The mathematics is the same
sentence: a Kuratowski pair lies in a set, therefore its second component lies
in `K`. **That is why `Val.sndK` is stated at a bare `E : S` and not at a slot**
(`Probe508.agda:151-153`): the term is already general enough for all three.
**What is missing for them is a different input**, namely that the bound
environment's members are in `K`, and the record has fields in that business
already (`envInK-mem` at `:218`, `envInK-neg` at `:225`, `envInK-top` at
`:232`, `envInK-imp` at `:239`). **I did not build the three and I did not
price them.** The same reading applies to
`src/L/Condensation.lagda.md:4219-4225`, the declaration named `valK` that is
really of this family.

## 7. PRICES

One Agda process per run, `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on
the pane by the program and untouched. Three forced rechecks per stage, by
deleting `_build/2.8.0/agda/agents/tasks/LJ-1-508/Probe508.agdai` before every
run. Every run printed `Checking`.

| stage | lines | exit | median wall | median peak RSS | runs |
|---|---:|---:|---:|---:|---|
| W3 alone | 63 | 42 | **2.32 s** | **571949056 B** | `runs/w3-r0` to `w3-r2` (2.32, 2.31, 2.32) |
| full file | 331 | 0 | **2.86 s** | **687194112 B** | `runs/final-r0` to `final-r2` (2.86, 2.86, 2.81) |

**NO HEAP EVENT. NO WALL. No warning in any green run.**

**THE EARLIER RUNS IN `runs/` ARE EARLIER FILE STATES, AND I NAME THEM SO
NOTHING IS QUOTED OUT OF PLACE.**

- `runs/w3-0` is the first W3 attempt, with the last step a hole. Exit 42,
  `[UnsolvedInteractionMetas]`, and it names no type. It is superseded.
- `runs/w3-1` is the second W3 attempt and is the same file the `w3-r*` runs
  measured.
- `runs/full-0` is the first full-file attempt. It failed `[NotInScope]` on
  `_^_`, exit 42, because the file did not yet open the absoluteness module.
  That is a missing import and not a mathematical event.
- `runs/full-1` is the file at 275 lines, before `Val` was generalized to a
  bare `E`. 2.84 s.
- `runs/full-2` is the file after that generalization. 2.90 s.
- `runs/full-3` and `runs/full-r0` to `full-r2` are the file at 304 and 311
  lines, before the predecessor citations were added to the header comment.
- `runs/witness-0` metered the 275-line state, 0 UNRESOLVED of 1.

**Only `runs/final-r0` to `final-r2` and `runs/witness-final` measure the file
that stands.**

**AGAINST THE ESTIMATE.** The brief priced the probe at about 170 lines, of
which the obligation was about 45, and W3 at about 20 lines and under 30
seconds. **Measured: the file is 331 lines**, the obligation term is 6 lines
(`Probe508.agda:216-221`), the generic term it calls is 7 lines (`:151-157`),
and the refutation plus its data is 53 lines (`:277-329`). **W3 cost 2.32 s,
not 30.** The file is over the estimate because the brief funded a term and I
also built two refutations and one conditional. **Nothing is funded against a
comparable. I report the numbers I measured.**

**THE RATIO BAR DOES NOT FIRE.** The bar is 0.0123 seconds per in-fence line,
and its divisor is the in-fence line count of this task's write scope. A raw
`.agda` probe carries no ` ```agda ` fence, so this scope counts 0 in-fence
lines and the bar cannot fire. Nothing lands in `src/`.

## 8. W2, W4 AND THE LAWS

**W2 (DD4): write the mathematics once at a generic carrier and instantiate
it.** Answered, and the answer is measured.

| piece | where | instantiated at |
|---|---|---|
| `ValPair` | `Probe508.agda:103-115` | `n = 9`, `:216` |
| `Val.SubK` | `:146-147` | `E = lookup (suc zero) γ'`, `:201` |
| `Val.sndK` | `:151-157` | `m = 20`, `:211-212`, called at `:219` and `:221` |

`Val.sndK` takes its set as a BARE `S` and not as a slot. **That is W2 doing
real work and not a formality:** section 6 shows the same term is what
`valV`, `valW` and `wKfact` need, and it will not have to be written again for
them. **I RE-DERIVED NOTHING THAT `src/` ALREADY HAS.** `ChainZ` owns the pair
pieces and this file opens it. It writes no `pairing-ax` and no
`pair-singleton`. It contains no `KFactsCons`.

No band. No site is named as a fixed form. There is no conflict with W2.

**W4 (DD13) does not fire.** No module was retired. Nothing was deleted. There
is no `dev/ARCHIVE.md` row to write.

**P-l did not fire.** The types name `Fin`, `lookup`, `pr`, `prʟ`, `pairʟ` and
six `suc`s on an index. The one stage value that appears, `LsetS lam ordλ`
(`Probe508.agda:284`), is in a REFUTATION's data and not in the obligation's
type, and it is reached through `KValue`'s own opaque binding.

**D-26 did not fire.** This is a closure fact, not a well-founded key.

**C-22 was followed.** The report was written as a skeleton before the full
probe existed and was filled as each run landed.

**C-42 is section 5.** The count came before any cure was priced, and it
corrected the brief's 23 to 22.

**D-10 is section 1.** The cheapest possible answer was priced first, before
any Agda, and then measured.

## 9. WHAT THE NEXT BRIEF NEEDS

1. **The frame entry to add is ONE implication about slot one**, and its type
   is in section 6. It is not 22 debts. It is one, at the slot, and it pays all
   22 declarations of the pair-in-the-graph shape.
2. **The record already speaks this dialect.** `carrierK`
   (`src/L/Condensation.lagda.md:6112-6113`) is the same sentence about the
   carrier slot. So the entry is a 60th field of the same kind, or slot one
   stops being free. **That is a record decision and it is not a coder's
   call.**
3. **THE LITERATURE SAYS EVERY SOURCE DETERMINES ITS BOUND RATHER THAN
   ASSUMING FACTS ABOUT IT.** `dev/literature/level-formula-slot-roles.md:58`
   is the section head, and `:60-61` reads: Devlin's `∃w` carries the conjunct
   `K(w,u)`, "which says `w = K(u)`", so the witness is unique. **`[LJ-1.506]`
   repaired the CODE slot exactly that way**, with an equation naming the set
   (`agents/tasks/LJ-1-506/lj-1.506-report.md:16-18`). **The same option is
   open for slot one and it would give `valSub` rather than assume it.** I did
   not take it, because it names a set and the brief reserved that for
   `[LJ-1.505]`.
4. **`[LJ-1.505]` gets one conditional for free.** If its answer is that slot
   one is the carrier slot, `valSub-from-carrier`
   (`Probe508.agda:252-263`) is already green and the field costs nothing more.
5. **A question about the field's TYPE, for the mathematician.** Under this
   hypothesis the field uses 1 of its 4 premises (section 4.2). The code
   membership and the shape equation are inert. **Whether they stay is a
   design question**, and dropping them would make `valK` and `valK-un`
   literally one field.
6. **`valV`, `valW` and `wKfact` are NOT covered**, and section 6 says exactly
   why and exactly what they need instead. **The term is already written for
   them.** The input is not.

## 10. THE WORKING TREE

`git status --porcelain` returns one line: `?? agents/tasks/LJ-1-508/`.

**NOTHING LANDS IN `src/`.** Nothing is committed and nothing is pushed. The
directory holds the brief, this report, `Probe508.agda` and `runs/`.

Individual gates run clean on the new files: `check-probes.py --check` reports
"clean (5175 tracked files, no probe outside agents/tasks/ and no generated
file)"; `lint-agda.py`, `lint-prose.py` and `check-glossary.py` each return 0
when called with the new paths as arguments. **I called them with explicit
paths on purpose.** `lint-prose.py` and `check-glossary.py` discover their
inputs through `git ls-files`, so an untracked file is skipped silently.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, and it changed this report.** It
  is where I found `[LJ-1.151]`, which the brief did not name. Quote at
  `archive/dev/LJ-dispatch-index.md:227`:

  > | LJ-1.151 | Probe the one term two dispatches named and nobody ran | GO AT 21 LINES, AND valK IS FALSE | The band tightens on 9 of 25, not all 25. The wall stayed out: the two halves are separable |

  Quote at `archive/dev/LJ-dispatch-index.md:175`:

  > | LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |

  The first row sent me to `agents/tasks/LJ-1-151/` and to `[LJ-1.153]`'s
  probe before I wrote the refutation, and it is why section 0 separates the
  old field from the repaired one. The second row is the archive's record of
  the route the obligation takes.
- **`archive/dev/JOURNAL.md`: not read, declined.** I searched it for `valK`,
  `graph slot`, `slot one` and `value set`. COUNT of hits: 0. The dispatch
  index carried this period at a higher density.
- **`archive/dev/JOURNAL-archived.md`: not read, declined.** Same four search
  terms. COUNT of hits: 0.
- **`dev/ARCHIVE.md`: not used.** Same four search terms. COUNT of hits: 0.
  W4 does not fire in this task, so there was no retirement row to write or to
  read.
- **`archive/dev/DECISIONS-archived.md`: declined.** 61 lines, and it resolves
  bare `D<n>` codes. This task cites no `D<n>`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`: READ, and it is the right
  file for this task.** It is the corpus's own record of what a slot may be
  asked to carry. Quote at
  `dev/literature/level-formula-slot-roles.md:58`:

  > ### 2.3 The bound is DETERMINED, not chosen

  Quote at `dev/literature/level-formula-slot-roles.md:35`:

  > ### 2.1 The free pair is the VALUE and the ORDINAL, in every source

  **Section 2.3 is what I carried into section 9 item 3**: no source leaves its
  bound undetermined, so a frame that assumes facts about a free slot is doing
  something the sources do not do, and naming the set is the sourced
  alternative. **Section 2.1 I did NOT use as evidence about slot one**: its
  VALUE is a free variable of a level-hood formula, and slot one here holds a
  set of code-value pairs. Those are different objects and I did not treat the
  agreement of rows 3 to 9 as saying anything about this slot.
- **`dev/literature/devlin-II5.md`: not used, declined.** I searched it for
  `K(u)`, `code set`, `graph` and `arity`. Devlin's `K(u)` bound is not
  discussed there; the file is the condensation and definable-hull chain.
  `dev/literature/level-formula-slot-roles.md:60-61` carries Devlin's `K(u)`
  clause instead, and that is the file I cite.
- **`dev/literature/truncation-and-selection.md`: not used, declined, and the
  reason is a fact about this field.** `Probe508.agda` contains no `∥_∥₁` and
  no `PT` call. **`valK` and `valK-un` are the only two of `TFacts`'s code
  fields that carry NO truncation**: `codesK` and `codesK-un` end in
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
  (`src/L/Condensation/TwelveAgree.lagda.md:167`, `:172`) and these two end in
  a bare membership (`:176`, `:180`). So the whole selection question that
  `[LJ-1.500]` and `[LJ-1.506]` had to answer does not arise here.
- **`dev/literature/digest.md`: not read, declined.** It is a route-level
  digest, and this task chose no route: the brief named the field and the
  frame, and the archive named the route.
- **`dev/literature/geology.md`: not read, declined.** Fine structure and the
  geology of `L`. This task did not reach fine structure.
