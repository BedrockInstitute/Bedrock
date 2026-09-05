# LJ-1.500 report: the two code readers, and where the numeral comes from

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-500/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `codesK-family` in
`agents/tasks/LJ-1-500/Probe500.agda`. The type is the two `TFacts`
fields `codesK` (`src/L/Condensation/TwelveAgree.lagda.md:162-167`) and
`codesK-un` (`:168-172`), at `KValue`'s frame under `[LJ-1.495]`'s
six-fold shift. Nothing lands in `src/`. I did not build a `TFacts`
value. I did not fill `someEnv`. I did not touch `EnvSet`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## PREDECESSORS, READ FIRST

Audit F1: a predecessor taken as a hypothesis is the REPORT, and the
type is the one that predecessor delivered
(`dev/pod/audit-2026-08-20.md:34`).

`[LJ-1.495]` is **GO** (`agents/tasks/LJ-1-495/lj-1.495-report.md:71`).
Quote at `:71`:

> **GO.** `twice` typechecks

It delivered `Shared26`, which is 26 of `TFacts`'s 59 fields
(`agents/tasks/LJ-1-495/Probe495.agda:166-199`). **`Shared26` does NOT
carry `arityK`**, and `[LJ-1.495]` says so at
`agents/tasks/LJ-1-495/lj-1.495-report.md:216-218`: `arityK` is one of
the three `KFacts` fields the shift carries and that task discarded. So
I could not take `arityK` from the delivered type. I took the same
INPUT that task took, a `KFacts` at `KValue`'s indices
(`Probe495.agda:168`), and applied `KFactsCons` six times myself
(`Probe500.agda:267-332`). That is a re-derivation of the shift, not a
re-opening of its verdict.

`[LJ-1.493]` is **GO** (`agents/tasks/LJ-1-493/lj-1.493-report.md:74`).
It measured that `codesK` APPLIES at the real frame, that `c∈` is the
`:3505` binder and that `shEq` computes from `shD`
(`:74-76`). **That is the other direction from this task.** I supply
the field; that task consumed it. I did not reuse its `someEnv`
inlining and I did not import its probe.

`[LJ-1.483]` reported the domain of `codesK` empty at its own frame
(`agents/tasks/LJ-1-483/lj-1.483-report.md:93`). I did not repeat its
dummy-`C` pad. `C` stays a free variable of the frame here, exactly as
`[LJ-1.493]` measured it must.

`[LJ-1.496]` (premise 8) says the `PropAgree` chain binds no stage
(`agents/tasks/LJ-1-496/lj-1.496-report.md:78`). **I did not need it.**
A decoder binds no stage either: nothing in `Probe500.agda` names a
stage value.

## WHERE THE NUMERAL COMES FROM

**AT THIS FRAME, NOTHING SUPPLIES IT.**

`codesK` returns four things. Three are memberships. The fourth is
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
(`src/L/Condensation/TwelveAgree.lagda.md:167`). The inputs at the frame
are these, and no others:

1. `c∈ : ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩`, the code's
   membership in the `C` slot (`:162`).
2. `shEq : fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))`, the
   decomposition (`:163`).
3. `arityK`, from `KFacts` (`src/L/Condensation.lagda.md:6114`), which
   is `TFacts`'s `transK` (`TwelveAgree.lagda.md:262`) with the binder
   roles swapped (`:347-353`).
4. `C∈K`, the code set's membership, which this task states as a
   hypothesis because the `C` slot is a free variable of `TFacts`'s
   environment.

**None of the four constrains `ar`.** `arityK` is transitivity: it puts
things INTO `K` and says nothing about their shape. `shEq` puts `ar` in
the head position of a Kuratowski pair and says nothing about what `ar`
is. `k` is a metalevel numeral in the SECOND component, not the first.
So the fourth conjunct is not derivable from this frame, and I did not
fabricate it.

**THE TREE ALREADY NAMES THE SOURCE, and it is one chapter away.**
`src/L/Condensation/TwelveAgree.lagda.md:303-306` states it in the
comment above `envSetK`:

> the arity at every consuming site IS a numeral: `codesK` gives the
> code's shape, `arityNumAtL` (L.Coding.CodeSet) says its arity
> component is a numeral, and `pr-inj` closes both into
> `fst ar ≡ # n`.

The three named parts, at `file:line`:

| part | home | what it gives |
|---|---|---|
| `arityNumAtL` | `src/L/Coding/CodeSet.lagda.md:185-187` | the object-language conjunct: the slot's first component is in `ωʟ` |
| `arityNumAtL-out` | `src/L/Coding/CodeSet.lagda.md:189-199` | reads it back as `∥ Σ[ m ∈ ℕ ] Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# m) (fst z)) ∥₁` |
| `pr-inj` | `src/V/Coding.lagda.md:178-179` | closes that against `shEq` into `fst ar ≡ # m` |

**THAT CHAIN IS BUILT AND IT TYPECHECKS AT THIS FRAME.** W3
(`Probe500.agda:78-84`) is exactly those three steps, and it is GO. So
the field is short by ONE input and not by a proof.

**THE MISSING INPUT, WRITTEN OUT.** It is the statement that the `C`
slot really holds codes:

```agda
arNumC : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
```

`Probe500.agda:226-228`. It is a property of the `C` SLOT, never of
`K`, and it enters only when an instantiation pins `C` to a real code
set. `TFacts` does not state it today. **Counted at
`src/L/Condensation/TwelveAgree.lagda.md:132-332`: COUNT of `TFacts`
fields that say anything about the `C` slot beyond a bare membership:
0.**

**A PREDECESSOR ALREADY REFUTED THE FIELD-LEVEL VERSION OF THIS AT A
NEIGHBOURING SITE, AND I DO NOT EXTEND IT.** `[LJ-1.347]` measured the
arity-numeral conjunct FALSE at `wCodesK`
(`src/L/Condensation.lagda.md:7239-7245`), with a countermodel whose
`ar` is `sglS (numeralL 1)`, a singleton and not a numeral
(`agents/tasks/LJ-1-347/lj-1.347-report.md:115-120`). Quote at
`agents/tasks/LJ-1-347/lj-1.347-report.md:8`:

> **FALSE.** `[LJ-1.344]`'s INFERRED verdict is now **MEASURED**.

**`wCodesK` IS NOT `codesK`.** Its premise is two-level, `c ∈ w'` with
`w' ∈ K` (`src/L/Condensation.lagda.md:7239-7240`); `codesK`'s premise
is one-level, `c ∈ C` with `C` a slot. C-42 says a refutation measures
the site it names and never how far the shape extends, and AGENTS.md:45
says a measured cure does not transfer by analogy. **So I do NOT claim
`[LJ-1.347]` refutes `codesK`.** I claim only what I measured: the
frame does not supply the conjunct, and `arNumC` is therefore a
mandatory input rather than a convenience. Whether the same countermodel
lands at `codesK`'s one-level premise is UNMEASURED by this task, and
section 5 names the probe that would settle it.

## VERDICT

**GO.** `codesK-family` typechecks (`Probe500.agda:365-372`, with the
top-level alias at `:374`, exit 0, median **3.16 s** on three forced
rechecks of the full file) and PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-500
--brief agents/tasks/LJ-1-500/LJ-1.500.md`, exit 0, 2.57 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-3.out`).
`.venv/bin/python` is absent in this worktree. I added no dependency.

W3 is GO: `ar-is-numeral` typechecks alone (exit 0, median **1.34 s**
on three forced rechecks of the W3-only file). **It is GO, and that is
the answer that matters: the truncation FORMS. It is the INPUT that is
missing, not the derivation.**

I did not write `review-of-codesK-family.md`. The verdict is GO.

A GO pays two of `TFacts`'s 59 fields and names the numeral's source
for the family that shares it. It does not land the readers in `src/`.
It does not inhabit the other 31 unpaid fields. It does not build a
`TFacts` value. It does not fill `someEnv`. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not
claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

Four generic pieces, each written once:

| piece | where | instantiated at |
|---|---|---|
| `CodesPair` | `Probe500.agda:92-105` | `n = 9`, `Probe500.agda:365` |
| `Split.prK-split` | `:124-130` | `m = 20`, through `Mem`, `:359-361` |
| `Mem` | `:145-215` | `m = 20`, `:359-361` |
| `Num` | `:225-250` | `m = 20`, `:363` |

`CodesPair` states the two field types ONCE at `TFacts`'s own generic
shape, `K : Fin (5 + n)` over `γ' : S ^ (11 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:129-131`). The obligation
instantiates it at `n = 9` against `KValue`'s `Fin 14`, which is the
frame `[LJ-1.495]` measured (`lj-1.495-report.md:56-60`). I did not
copy a field type twice.

**I RE-DERIVED NOTHING THAT `src/` ALREADY HAS.** `ChainZ`
(`src/L/Condensation.lagda.md:2820-2917`) already owns the four
Kuratowski pair pieces, and they are public. `prK-split`
(`Probe500.agda:124-130`) opens `ChainZ` and calls `Z.x∈pairʟxx`,
`Z.xsingl∈prxy`, `Z.y∈pairʟxy` and `Z.ysingl∈prxy`. It writes no
`pairing-ax`, no `inl∈⁅,⁆` and no `pair-singleton`. `[LJ-1.347]` records that both are public
(`agents/tasks/LJ-1-347/lj-1.347-report.md:124`) and that five earlier
probes each re-wrote four lines of that access (`:126-127`).
`src/L/Condensation.lagda.md:2812-2819` is the chain's own comment: it
says the chain is generic, one field plus the pair encoding. This probe
spends the public copy.

**ONE COPY SERVES BOTH READERS, AND THAT IS MEASURED.** `read`
(`:160-171`) is the shared core: head of the pair, tail of the pair,
no numeral. `codesK-mem` calls `prK-split` three times; `codesK-un-mem`
calls it twice. `ar-is-numeral` (`:78-84`) is ONE term and both
`codesK-num` and `codesK-un-num` call it. Neither reader's numeral half
looks inside the tail, which is why one copy is enough.

No band. No site is named as a fixed form. There is no conflict with
W2.

W4 does not fire: no module was retired.

P-l did not fire: the types name `Fin`, `lookup`, `pr` and six `suc`s
on an index. They name no transparent stage presentation.

D-26 did not fire: this is a decoder, not a well-founded key.

## 2. W3: ar-is-numeral, obligation omitted

**GO.**

The brief named the numeral truncation as the widest unmeasured term,
because it rides with every reader and no dispatch had named its source.
The W3-only file held ONE definition, `ar-is-numeral`, and was 63 lines.

```agda
ar-is-numeral : {m : ℕ} (γ : S ^ m) (c ar rest : S)
              → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
              → fst c ≡ pr (fst ar) (fst rest)
              → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

`Probe500.agda:78-81`. It is `arityNumAtL-out` at the code consed on
slot zero, then `pr-inj` against the decomposition, then `PT.map`.

**THE TRUNCATION NEVER HAS TO BE ESCAPED.** The conclusion is itself
truncated, so `PT.map` is enough and no `PT.rec` motive obligation
appears. That is the first question of the tree's own selection digest
(`dev/literature/truncation-and-selection.md:289`).

**`rest` IS A PARAMETER AND THE TERM DOES NOT LOOK AT IT.** That is why
one copy covers both readers and, on the type alone, would cover the
nine env fields that carry the same conjunct.

First landing of the W3-only file: 1.49 s, peak RSS 337494016 bytes,
exit 0, printed `Checking`. `runs/w3-0.out` / `w3-0.time`. **It landed
green on the first attempt.**

Three forced rechecks of the W3-only file, interface deleted each time
(`_build/2.8.0/agda/agents/tasks/LJ-1-500/Probe500.agdai`), same
caliber, one Agda process, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.34 | 337477632 |
| `runs/w3-2.out` / `w3-2.time` | 1.34 | 337477632 |
| `runs/w3-3.out` / `w3-3.time` | 1.35 | 337494016 |

Median wall **1.34 s**. Median peak RSS **337477632 bytes**. No heap
event.

The brief's W3 estimate was about 25 lines and under 40 seconds.
Measured, the term is 7 lines (`:78-84`) and the W3-only file is 63
lines. Wall is 1.34 s. Nothing is funded against the estimate. Nothing
is funded against `[LJ-1.493]`'s 4.53 s, and the brief was right to
forbid that: this reads an arity and that built an environment.

**WHAT A NO-GO WOULD HAVE SAID, AND WHAT THE GO SAYS INSTEAD.** The
brief said a NO-GO at W3 would say ten fields share one missing input.
W3 is GO, so the finding is narrower and better: the DERIVATION is
built and cheap, and what the ten fields share is one missing
HYPOTHESIS about the `C` slot. Section 4 counts the sites.

## 3. The obligation

**GO.** `codesK-family` (`Probe500.agda:365-372`) rebuilds `KValue`'s
telescope (`:259-265`), takes a `KFacts` at `iA iK i0 ... i11 Kenv`,
applies `KFactsCons` six times (`:267-332`), reads `arityK` off the
result (`:361`), and fills `CodesPair {n = 9}` from `Mem` and `Num`.
The top-level name the witness reads is the alias at `:374`.

**BUILT IN THE ORDER THE BRIEF SET.** `codesK` first
(`Mem.codesK-mem`, `:175-195`, plus `Num.codesK-num`, `:230-239`),
`codesK-un` second (`Mem.codesK-un-mem`, `:198-215`, plus
`Num.codesK-un-num`, `:241-250`).

**IS `codesK-un` THE FIRST MINUS ONE COMPONENT? YES, AND EXACTLY ONE.**
Measured by reading the two bodies. `codesK-mem` splits the pair three
times: `ar` from the tail (`:192`), the tag from the inner pair
(`:193`), then `a` from `b` (`:194`). `codesK-un-mem` splits twice:
`ar` from the tail (`:213`), then the tag from `a` (`:214`). The third
`prK-split` is the whole difference. The two numeral halves differ by
one term inside `inner1eq`: `prʟ-fst a b` against `refl`
(`:237` against `:248`). **COUNT of structural differences: 1 in the
memberships, 1 in the numeral. Nothing else differs.**

**THE THREE MEMBERSHIPS ARE DELIVERED SEPARATELY, AND THE NUMERAL IS
NOT IN THEIR TELESCOPE.** The brief asked for three of four honestly if
nothing supplied the fourth. `module Mem` (`:145-150`) has four
parameters, `C`, `K`, `γ`, `arityK` and `C∈K`. **`arNumC` is not one of
them.** It lives in `module Num` (`:225-228`), which has no `arityK`
and no `C∈K`. The split is deliberate: a module telescope is prepended
to the stored type of every definition inside it
(`src/L/Condensation/TwelveAgree.lagda.md:116-119`), so keeping the
numeral out of `Mem` is what makes "three of four with no numeral
input" a checkable claim rather than a sentence.

**I DID NOT ASSUME `[LJ-1.499]`'s ROUTE.** `Probe500.agda` does not
import `L.Coding.EnvSet` and does not name `EnvSet`, `Generic`,
`envSetAt` or `envOverAt`. I never wanted them. A decoder takes an
EQUATION apart with `pr-inj` and climbs a pair with `arityK`; it reads
no satisfaction except the one conjunct `arityNumAtL`, and that conjunct
is about the code, not about an environment. **The mathematician split
the two families correctly**, and this task confirms the split from its
own side.

**MEASURED SIDE-FINDING: THE SIX-FOLD SHIFT IS DEFINITIONAL ON
`arityK`.** `arityK-direct` (`:334-341`) has the shifted type and the
body `f .arityK`, with no `KFactsCons` at all. It typechecks.
`lookup (suc^6 iK)` over the six conses reduces to `lookup iK Kenv`, so
the field projects straight through. The obligation still goes through
`six`, which is the route `[LJ-1.495]` delivered and the route the brief
named. **What this buys the next brief: a later reader or env field
that needs only `arityK` at this frame can take it for one line instead
of 66.** COUNT of lines `six` costs: 66 (`:267-332`). COUNT of lines
`arityK-direct` costs: 8 (`:334-341`).

First landing of the full file, in its final shape: 3.32 s, peak RSS
715751424 bytes, exit 0, printed `Checking`. `runs/full-5.out` /
`full-5.time`.

Three forced rechecks of the full file, interface deleted each time,
same caliber, one Agda process, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-6.out` / `full-6.time` | 3.15 | 715784192 |
| `runs/full-7.out` / `full-7.time` | 3.17 | 715784192 |
| `runs/full-8.out` / `full-8.time` | 3.16 | 715784192 |

Median wall **3.16 s**. Median peak RSS **715784192 bytes**. No heap
event.

**THE EARLIER RUNS IN `runs/` ARE EARLIER FILE STATES, and I name them
so nothing is quoted out of place.** `runs/full-0` is the file before
`arityK-direct`, 2.87 s. `runs/full-1` to `runs/full-4` are the file
with `arityK-direct` and before the `Mem` and `Num` split, median 3.04 s.
`runs/witness-1` and `runs/witness-2` metered those two states, both 0
UNRESOLVED of 1. **Only `runs/full-6` to `full-8` and `runs/witness-3`
measure the file that stands.**

The brief's estimate was about 180 lines in the probe, of which the
obligation was about 60, comparables of SHAPE. Measured, the file is
374 lines. The obligation term itself is 8 lines (`:365-372`); the two
generic reader modules it calls are 71 and 26 lines; `six` is 66 lines.
Nothing is funded against the estimate. Nothing is funded against
`[LJ-1.493]`'s 4.53 s.

**THE SHAPE THAT RESISTED WAS NOTHING IN THE MATHEMATICS.** The W3 file
and the full file each landed green on the FIRST attempt, exit 0, with
no `NotInScope` and no unsolved metavariable. The only structural
decision that cost a rewrite was mine and not Agda's: the first full
file put `arNumC` in one module with `arityK` and `C∈K`, which made the
"three of four" claim unverifiable from the stored type. I split it
into `Mem` and `Num` and rechecked. That cost 0.12 s of median wall
(3.04 s against 3.16 s) and it is what makes section 3's claim
checkable.

**WHAT I HAD TO WEAKEN: nothing in the field types.** `CodesPair`'s two
fields are `TFacts`'s two fields, character for character at the record's
own indices. **WHAT I HAD TO ADD: two telescope hypotheses**, `C∈K` and
`arNumC`. Both are named at `file:line` above. `C∈K` is unavoidable
because the `C` slot is free; `arNumC` is unavoidable for the reason
`## WHERE THE NUMERAL COMES FROM` gives. **WHAT I COULD NOT CLOSE:
whether `arNumC` is merely absent or actually refutable at `codesK`'s
one-level premise.** Section 5 names the probe.

## 4. C-42: the sweep, before anyone prices a cure

C-42 says a refutation measures the site it names and never how far the
shape extends, so the next action is the sweep and the COUNT.
`[LJ-1.347]`'s refutation is at `wCodesK`. Here is the count of the
shape across the live tree.

COUNT of occurrences of `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` in `src/`:
**87**, in 5 files.

| file | count |
|---|---|
| `src/L/Condensation.lagda.md` | 50 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 11 |
| `src/L/Coding/EnvSupply.lagda.md` | 10 |
| `src/L/Condensation/LowerAgree.lagda.md` | 8 |
| `src/L/Condensation/UpperAgree.lagda.md` | 8 |

COUNT of untruncated `fst ar ≡ # n` in a FIELD or PARAMETER type in
`src/`: **3**. They are `envSetK`
(`src/L/Condensation/TwelveAgree.lagda.md:306`), `genEq`
(`src/L/Coding/EnvSupply.lagda.md:133`) and `envSetK`
(`src/L/Coding/EnvSupply.lagda.md:140`).

**INSIDE `TFacts` ITSELF, counted at
`src/L/Condensation/TwelveAgree.lagda.md:132-332`:**

| role | fields | count |
|---|---|---|
| PRODUCES the truncation | `codesK` (`:167`), `codesK-un` (`:172`) | **2** |
| CONSUMES it as a hypothesis | `envK-mem` (`:187`), `envK-neg` (`:193`), `envK-top` (`:199`), `envK-imp` (`:205`), `envK-allin` (`:211`), `envInK-mem` (`:218`), `envInK-neg` (`:225`), `envInK-top` (`:232`), `envInK-imp` (`:239`) | **9** |
| CONSUMES it untruncated | `envSetK` (`:306`) | **1** |

**The brief said the same truncation appears in nine other fields of
this record. MEASURED: exactly 9 consume it truncated, and 1 more
consumes it untruncated, so the number to carry forward is 10 and not
9.**

**THE TWO PRODUCERS ARE THE ONLY PRODUCERS, and they feed twelve rows.**
`TFacts.codesK` and `TFacts.codesK-un` are passed straight into `LFacts`
and `UFacts` (`src/L/Condensation/TwelveAgree.lagda.md:421-422` and
`:462-463`). Counted at the call sites, `codesK` serves 7 rows,
`k = 0,1,2,3,4` in `src/L/Condensation/LowerAgree.lagda.md:258,265,272,278,284`
and `k = 10,11` in `src/L/Condensation/UpperAgree.lagda.md:283,290`;
`codesK-un` serves 5 rows, `k = 5` in
`src/L/Condensation/LowerAgree.lagda.md:290` and `k = 6,7,8,9` in
`src/L/Condensation/UpperAgree.lagda.md:256,262,267,275`. **COUNT of
rows fed: 12. COUNT of producing fields: 2.**

**WHAT THE SWEEP MEANS FOR THE PRICE.** The nine consumers already
RECEIVE the truncation; they do not prove it. The one untruncated
consumer receives it untruncated. So `arNumC` is not nine or ten
separate debts. **It is ONE debt, at the two producers, and paying it
once pays the whole family.** I price nothing further.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **`arNumC` is the whole remaining question for this family, and it
   is one question and not ten.** Its shape is at `Probe500.agda:226-228`.
   The decision is whether it becomes a 60th `TFacts` field, or whether
   `C` stops being a free slot and gets pinned to the code set.
2. **The probe that would settle whether it is merely absent or
   actually FALSE at `codesK`'s premise.** Take
   `[LJ-1.347]`'s countermodel (`agents/tasks/LJ-1-347/lj-1.347-report.md:115-120`),
   put `sglS cS` in the `C` slot rather than in `w'`, and try to inhabit
   the fourth conjunct. **WARN THE NEXT CODER**: `[LJ-1.347]` measured
   that the non-numeral half of that countermodel walls an 8 GB heap
   when it is written as a PATTERN MATCH CASE SPLIT on the numeral
   index, 1.73 s against exhausted (`lj-1.347-report.md:36-37`), and
   that the library ELIMINATOR does the same split in 1.64 s
   (`:39`, `Elim347.agda`). **That is a measured cure at its own site
   and AGENTS.md:45 says re-measure it here.** It is not free, but it is
   named.
3. **`arityK` at this frame costs one line, not 66** (`:334-341`). Any
   later brief in this family should say so, so nobody pays `six` twice.
4. **`C∈K` was needed and nothing in `TFacts` states it either.** It is
   the second free-slot fact this task had to assume. I do not know
   whether the instantiation gets it for free; I did not measure that.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.** Three rows, and they
  are why `## WHERE THE NUMERAL COMES FROM` cites a refutation rather
  than only an absence. Quote at `archive/dev/LJ-dispatch-index.md:400`:

  > | LJ-1.347 | Settle the arity-numeral conjunct | FALSE. THE WALL IS THE CASE SPLIT. DD25 [LJ-1.352] SPLIT | Verdict upheld; its count and its repair reading are overturned. Law C-58 |

  Quote at `archive/dev/LJ-dispatch-index.md:401`:

  > | LJ-1.350 | Probe ONE third-shape tie before funding 28 | 8 INSERTIONS, 7 SHARED. 280 BECOMES 43, A FLOOR | Shapedness is NOT the bound; arityNumAtL is, and it is DELIVERED with both directions |

  Quote at `archive/dev/LJ-dispatch-index.md:433`:

  > | LJ-1.379 | Measure the BACK direction at the chain | SUPPLIED, 62 LINES. THE FLOOR BECOMES A PRICE AT ABOUT 113 | arityNumAtL's IN direction pays, and the upstream debt LJ-1.360 feared is GONE |

  The `[LJ-1.350]` row is what sent me to `arityNumAtL` before I wrote
  any Agda: it says the bound is `arityNumAtL` and that BOTH directions
  are delivered. W3 spends the OUT direction and it is GO, which agrees
  with that row.
- `archive/dev/JOURNAL-archived.md`: **not read.** Searched for
  `codesK`, `arityNum`, `ChainZ` and `KFactsCons`. COUNT of hits: 0.
- `dev/ARCHIVE.md`: **not used.** Searched for the same four terms.
  COUNT of hits: 0. W4 does not fire in this task, so there was no
  retirement row to write or to read.
- `archive/dev/JOURNAL.md`: **not read.** Searched for the same four
  terms. COUNT of hits: 0.
- `archive/dev/DECISIONS-archived.md`: **declined.** 61 lines, and it
  resolves bare `D<n>` codes. This task cites no `D<n>`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ**, and it settled
  a real question in W3. Quote at
  `dev/literature/truncation-and-selection.md:289`:

  > 1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to

  The reader's conclusion is itself `∥ - ∥₁`, so the first question
  answers yes and `PT.map` is enough. No `2-Constant` obligation
  appears, and none of this file's harder sections is reached. Quote at
  `dev/literature/truncation-and-selection.md:146`:

  > **The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`

  That constraint does not bind here, because nothing is selected out of
  the truncation.
- `dev/literature/devlin-II5.md`: **not used.** Searched it for
  `K(u)`, `code set` and `arity`. The hits are about
  Sigma-1-elementarity and the definable hull, which is
  `src/L/Condensation`'s upstream story and not this field. This task
  supplies a decoder inside an already-fixed coding; no source-level
  reading is in question.
- `dev/literature/digest.md`: **not read.** It is a route-level digest,
  and this task chose no route: the brief named the field and the frame.
- `dev/literature/glossary-review-2026-08.md`: **declined.** I added no
  `dev/glossary.toml` entry and I coined no term. The Boundary forbids
  me to add one anyway.
- `dev/literature/terms-2026-08.md`: **declined**, for the same reason.
  No naming question arose. Every name in `Probe500.agda` is either the
  tree's own (`codesK`, `codesK-un`, `arityK`, `prK-split` after
  `ChainZ`'s vocabulary) or a plain compound of them.
