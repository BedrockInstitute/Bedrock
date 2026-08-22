# LJ-1.539 report: the subK family collected, and the slot-one fact it really wants

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-539/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. **No heap event.**

TARGET: one term `subK-frame-inhabited` in
`agents/tasks/LJ-1-539/Probe539.agda`, the extra hypotheses the `subK`
forms take collected as ONE telescope, with a witness at `KValue`'s
frame. Nothing lands in `src/`. I did not build a `TFacts` value. I did
not collect the `valV`, `valW`, `wKfact`, `consK-*` or `envSetK` fields.
I did not fill `someEnv`. I did not edit `src/`. I did not rebuild
`subK-gen`, `subKSucc-gen` or their seven delivered instantiations. I
postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## VERDICT

**GO. SEVEN COLLECT, AND THEY WANT A WEAKER FACT THAN ANYBODY ASKED FOR.**

`subK-frame-inhabited` typechecks
(`agents/tasks/LJ-1-539/Probe539.agda:368-376`, top-level alias at
`:379`), exit 0, **3.49 s and 749,125,632 B peak RSS**
(`runs/full-1.time`; three runs at 3.83 s, 3.49 s and 3.51 s all report
that same byte figure, and a fourth after the comment corrections
reports 3.92 s and 749,109,248 B, `runs/final.time`, which is 16,384 B
apart and is the measurement's own granularity). Beside `[LJ-1.538]`'s
**722,698,240 B**
(`agents/tasks/LJ-1-538/lj-1.538-report.md:26`) that is
**+26,427,392 B, or +3.7 percent**, for a family of seven against a
family of nine. The caliber caps the heap at 8 GiB, so the run sits at
about **8.7 percent of the cap**.

It PASSes the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-539
--brief agents/tasks/LJ-1-539/LJ-1.539.md`, exit 0, 2.76 s,
**0 UNRESOLVED of 1**, `probe_red=False`, `runs/witness-final.out`).
`.venv/bin/python` is absent in this worktree, as it was for
`[LJ-1.538]` (`agents/tasks/LJ-1-538/lj-1.538-report.md:34-36`) and
`[LJ-1.499]`. I added no dependency.

I did not write `review-of-subK-frame.md`. The obligation is inhabited,
so the verdict on the obligation is GO.

**TWO RESULTS, AND THE SECOND IS THE ONE THAT MATTERS.**

1. **The family is SEVEN, not six.** The brief counts six. `EnvSupply`'s
   own comment counts seven (`src/L/Coding/EnvSupply.lagda.md:480`:
   `-- GROUP 3: the seven subK-* fields.`), and `[LJ-1.509]`'s report
   already corrected the count
   (`agents/tasks/LJ-1-509/lj-1.509-report.md:212-217`). The seventh is
   `subK-allin` (`src/L/Condensation/TwelveAgree.lagda.md:326-331`). It
   is in the family, it reads `T` out of the same cell, and one
   hypothesis pays it too. **I collected all seven**, because splitting
   the family would have cost a second dispatch for one field.
2. **THE SEVEN DO NOT WANT A MEMBERSHIP. THEY WANT `[LJ-1.508]`'s
   `valSub`, WHICH `[LJ-1.508]` MEASURED TO BE STRICTLY WEAKER.**
   `[LJ-1.509]` delivered the family's argument through `subK-gen`,
   which takes `TK : T ∈ K`. That is more than the family needs. W3
   below measures it: `subK-gen` spends `TK` in exactly ONE place, and a
   SUBSET fact at slot one does that one job. The obligation therefore
   takes `valSub`, and `Seven.sub-from-member` (`Probe539.agda:327-330`)
   shows `TK` buys `valSub` in one `arity` step, so this telescope
   covers `[LJ-1.509]`'s.

**AND THE FRAME IS NARROWER THAN `[LJ-1.538]`'s.** That task carried
`ω∈σ : ⟨ ω ∈ sucV gam ⟩` (`src/L/Coding/EnvSupply.lagda.md:111`),
`SupplyEnv`'s eighth parameter, because the nine env forms live inside
`SupplyEnv`. **The seven `subK` forms live in `module Fact`
(`src/L/Coding/EnvSupply.lagda.md:450`), which `SupplyEnv` does not
enclose, so this file never opens `SupplyEnv` and carries no `ω∈σ`.**
This frame is `KValue`'s seven parameters word for word, plus the
slot-one fact. **It also pins NO cell**: `[LJ-1.538]` had to fix cell 0
to `SupplyEnv.B₀` (`agents/tasks/LJ-1-538/Probe538.agda:177-178`); all
six cells stay free here.

## PREDECESSORS, READ FIRST

Audit F1 is the measurement behind the rule that a predecessor taken as a
hypothesis is its REPORT and never the brief. Its heading at
`dev/pod/audit-2026-08-20.md:34` reads `### F1 / F2. LJ-1.398 GO is hollow`.
I opened each report below and each probe I took a type from.

- **`[LJ-1.538]` is GO.** `agents/tasks/LJ-1-538/lj-1.538-report.md:26`
  reads:
  `` `:250`), exit 0, **3.56 s cold and 722,698,240 B peak RSS** ``
  I took its METHOD (one family at a time, state the block once at
  `TFacts`'s own shape and instantiate at `KValue`'s frame) and its
  NUMBER, which is the figure this report prices against. I did not
  import its probe and I did not reuse its frame: its frame carries
  `ω∈σ` and pins cell 0, and neither is needed here.
- **`[LJ-1.509]` is GO.** `agents/tasks/LJ-1-509/lj-1.509-report.md:56`
  reads: `**GO.** `subK-and` typechecks`. I took three things from it:
  that `T` is `γ'` position 1 for every field of the family; that the
  count is seven (`:212-217`); and its `arityK`-to-`isTransV` bridge
  (`:180-184`), which I re-wrote at this site rather than importing.
  **I did NOT take its `TK` hypothesis**, and W3 says why.
- **`[LJ-1.508]` is GO.** `agents/tasks/LJ-1-508/lj-1.508-report.md:23`
  reads: `**GO, AND THE BARE FORM IS ALSO REFUTED. Both results, exit 0.**`
  I took the TYPE
  of its module hypothesis `valSub`
  (`agents/tasks/LJ-1-508/Probe508.agda:201-205`) and its measurement
  that the subset form is strictly weaker than the membership
  (`Probe508.agda:237-243`, and `lj-1.508-report.md:307-310`).
  **`valSub` is a MODULE HYPOTHESIS there and it is a module hypothesis
  here.** No `TFacts` field states it: the cell `lookup (suc zero) γ'`
  occurs in exactly two field types, `valK`
  (`src/L/Condensation/TwelveAgree.lagda.md:175`) and `valK-un`
  (`:179`), and in both it is the CONTAINER, which is `[LJ-1.509]`'s
  count at `agents/tasks/LJ-1-509/lj-1.509-report.md:101-105`. **So this
  task moves the debt and does not pay it.**
- **`[LJ-1.530]` is GO.** `agents/tasks/LJ-1-530/lj-1.530-report.md:3`
  reads: `**VERDICT: GO.** The obligation is written and it typechecks.`
  I read `dK` (`Probe530.agda:131-156`) and `zK` (`:169-183`) and did
  NOT use either. W3 says why.

## D-10, BEFORE ANY AGDA

The brief ordered it first: list what `subK-gen` and `subKSucc-gen`
actually use, and say which telescope entries are dead weight. Counted at
the cited lines, before any Agda ran.

### What the two generics consume

`subK-gen` (`src/L/Coding/EnvSupply.lagda.md:481-487`) has a three-step
body and spends exactly three things:

1. `subValAt-adequate` (`src/L/Coding/Model.lagda.md:821-824`), which
   turns the satisfaction into
   `pr (pr (fst ar) (fst a)) (fst y) ∈ fst (lookup T γ)`.
2. `Ktr`, the second parameter of `module Fact`
   (`src/L/Coding/EnvSupply.lagda.md:450`), applied ONCE, to promote that
   pair out of slot `T` and into `K`. **This is the ONLY place `TK` is
   read.**
3. `Fact.prK` (`:452-459`), which splits the Kuratowski pair and itself
   spends `Ktr` three more times.

`subKSucc-gen` (`:489-495`) is the same three steps with
`subValSuccAt-adequate` (`src/L/Coding/Model.lagda.md:1409-1412`) and a
key whose arity component is a successor.

**INSIDE `Fact` THERE IS NO DEAD WEIGHT.** Its telescope is
`(K : S) (Ktr : isTransV (fst K))` and both are consumed on every one of
the seven paths.

**THE ONE FINDING THAT MADE W3 ANSWERABLE IS STEP 2.** A hypothesis that
is read once, for one job, can be replaced by anything that does that
job. `TK` does the promotion by transitivity. A subset fact at slot one
does the promotion directly.

### Dead weight in the FRAME telescope

At `KValue`'s frame the telescope is `KValue`'s seven parameters. Traced
at their own lines:

| entry | stated at | what the seven do with it |
|---|---|---|
| `lam` | `src/L/Condensation.lagda.md:7380` | **CONSUMED.** `Kenv` slot 1 is `LsetS lam ordλ` (`:7390`) and `facts .arityK` is `B.trans∈λ` (`:7425`), which is `T-trans lam` (`src/L/Coding/Bound.lagda.md:93-94`) |
| `ordλ` | `:7380` | **CARRIED, NEVER ELIMINATED.** It sits in the `snd` of `LsetS lam ordλ`, because `LsetS β oβ = Lset β , isL-Lset β oβ` (`src/L/Axioms/Basic.lagda.md:161`), and all seven read the slot by `fst` |
| `succλ` | `:7381` | **NOT ON THE PATH.** `arityK` reaches `Bound` only through `trans∈λ`, which names neither `succλ` nor `∅∈λ`. Both are spent by `facts`'s numeral fields (`B.num∈λ`, `:7416-7419`), which no `subK` field touches |
| `∅∈λ` | `:7382` | **NOT ON THE PATH**, same trace |
| `gam` | `:7383` | **CARRIED.** `Kenv` slot 0 is `LsetS gam ordγ` (`:7390`), the CARRIER slot `iA`, which no `subK` field names |
| `ordγ` | `:7383` | **CARRIED**, same slot |
| `γ∈λ` | `:7383` | **NOT ON THE PATH.** Spent by `carrierK` alone (`:7424`) |

**SO THE FRAME CARRIES SEVEN AND THE SEVEN FIELDS CONSUME ONE**, `lam`,
plus the `ordλ` that spelling the slot requires. Five entries are pure
statement cost. They cannot be dropped without dropping `KValue`, and
they cost a parameter and no elaboration: `facts .arityK` is one
projection out of a record `src/` has already checked. **This is the
same shape `[LJ-1.538]` found for `ordλ` at its own site**
(`agents/tasks/LJ-1-538/lj-1.538-report.md:81-94`), re-traced here
rather than carried over, as `AGENTS.md:45` requires.

**AND ONE ENTRY THAT `[LJ-1.538]` PAID FOR IS ABSENT HERE.** That task's
eighth parameter `ω∈σ` (`src/L/Coding/EnvSupply.lagda.md:111`) is
`SupplyEnv`'s. The seven `subK` forms are in `module Fact` (`:450`),
which is a SIBLING of `SupplyEnv` and not inside it, so this file never
opens `SupplyEnv`. **The subK family's frame is one hypothesis narrower
than the env family's, and that is a size result, not an accident.**

## W3, THE WIDEST UNMEASURED TERM

The brief named it: `subK-gen`'s `TK` argument, at the frame, from
`valSub` or `dK` or `zK` or none. Written FIRST, typechecked ALONE, and
the file at that run is kept verbatim at
`runs/Probe539.w3-only.agda.txt`.

**GO, AND IT IS THE LOAD-BEARING HALF OF THIS RETURN.**

`W3.subK-from-sub` (`Probe539.agda:97-107`) is `subK-gen`'s conclusion
with `valSub` in place of `TK`, generic in the environment length, the
environment and all four indices, exactly as `src/` states `subK-gen`.
Exit 0 on the first submission.

| run | real | max RSS | exit | evidence |
|---|---|---|---|---|
| W3 only, forced recheck | 2.60 s | 685,785,088 B | 0 | `runs/w3-0.time` |
| W3 only, forced recheck | 2.28 s | 685,768,704 B | 0 | `runs/w3-1.time` |
| W3 only, forced recheck | 2.27 s | 685,785,088 B | 0 | `runs/w3-2.time` |

**THE W3 IMPORT BLOCK IS NOT THE FINAL ONE**, so these three numbers are
this term's own and are NOT comparable with the table below:
`L.Condensation.TwelveAgree` was added afterwards, for
`statement-matches`. The controlled pair in `## THE SIX, AND WHAT THEY
COST` is stated-against-inhabited, both on the final block. The brief
estimated about 20 lines and under 40 seconds; the term plus its
packaging is 46 code lines (`:76-138`, both generics) and the run is
2.27 s.

### The three candidates, and what each one gives

**`valSub` FITS, and it is the answer.**
`[LJ-1.508]`'s slot-one hypothesis (`agents/tasks/LJ-1-508/Probe508.agda:201-205`)
says every member of slot one is a member of K. The adequacy puts the
Kuratowski pair INTO slot one, so `valSub` puts it into K in one step,
and `Fact.prK` splits it. **`Ktr` is still needed, for `prK` alone**, and
it comes from `arityK` at no cost. The price of the weaker hypothesis is
the packaging: `valSub` quantifies over `S` and the adequacy pins a raw
`V ℓ`, so `prʟ` and `prʟ-fst` (`src/L/Coding/Model.lagda.md:329`) close
the gap. That is the whole of `W3.keyPair` (`Probe539.agda:84-85`) and
`W3.keyEq` (`:87-92`), eight lines, and one `sucʟ`/`sucʟ-fst`
(`src/L/Axioms/Numerals.lagda.md:104`, `:152`) more for the successor
sibling `W3.keyPairS` (`:114-116`) and `W3.keyEqS` (`:118-126`).

**`valSub` DOES NOT GIVE `TK`, AND IT DOES NOT NEED TO.** `[LJ-1.508]`
refuted that converse at this frame
(`agents/tasks/LJ-1-508/Probe508.agda:237-243`, `subK-is-strictly-weaker`,
exit 0). **So the brief's framing, that the six want one membership and
the question is which delivered fact supplies it, has a better answer
than any of the three: the family does not want the membership.**

**`dK` DOES NOT FIT, AND ITS FRAME IS NOT AVAILABLE.** `dK`
(`agents/tasks/LJ-1-530/Probe530.agda:131-139`) concludes
`⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩` from `⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩`.
Two reasons, both checkable:
1. **The conclusion is the wrong statement.** The family needs
   `fst y ∈ K`, not `𝒟ₒ (fst y) ∈ K`.
2. **The frame is unavailable.** `dK` takes five hypotheses ahead of its
   pair (`Probe530.agda:133-137`): `fst (lookup K γ) ≡ Lset α` for a
   LIMIT `α`, `IsOrd` of a domain bound, that bound in K, plus
   `Domain (lookup f γ)` and `Values (lookup f γ)`
   (`src/L/Hierarchy.lagda.md:117-119`, `:124-125`). **`TFacts` states
   neither `Domain` nor `Values` about any slot: `grep -c` over
   `src/L/Condensation/TwelveAgree.lagda.md` gives 0 for each.** Slot one
   at this frame is a free cell, and nothing makes it a recorded
   function.

**`zK` DOES NOT FIT EITHER, FOR THE SAME TWO REASONS.** `zK`
(`Probe530.agda:169-178`) concludes `fst x ∈ K` from
`fst x ∈ 𝒟ₒ (fst w)`, under `dK`'s five hypotheses plus the limit. The
family's `y` is the right component of a pair in slot one, not a member
of the definable powerset of anything, and the five hypotheses are the
same five that `TFacts` does not state.

**WHAT THE THREE HAVE IN COMMON IS THE COUNT.** `valSub` is ONE
hypothesis and no side condition. `dK` and `zK` are five plus a limit
plus a slot that must hold a recorded function. **`valSub` wins on shape
and on price, and it is also the weaker of the two that are about slot
one at all.**

## THE SIX, AND WHAT THEY COST

**They are SEVEN.** The heading is the brief's and is kept unchanged;
the count is `EnvSupply`'s (`src/L/Coding/EnvSupply.lagda.md:480`) and
`[LJ-1.509]`'s (`agents/tasks/LJ-1-509/lj-1.509-report.md:212-217`).

### The collected telescope as a type

These are the parameters of `module Frame`
(`agents/tasks/LJ-1-539/Probe539.agda:357-362`), so the projected name
`Frame.subK-frame-inhabited` IS "telescope, then the free cells, then the
slot-one fact, then the witness", and the top-level alias at `:379`
carries it unchanged.

```
module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where
```

then, per term, the six free cells and the one slot-one fact:

```
subK-frame-inhabited : (c1 c2 c3 c4 c5 c6 : S)
  → ( (x : S)
    → ⟨ fst x ∈ fst (lookup (suc zero) (γ★ c1 c2 c3 c4 c5 c6)) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                      (γ★ c1 c2 c3 c4 c5 c6)) ⟩ )
  → SubKSeven {9} iK (γ★ c1 c2 c3 c4 c5 c6)
```

### Every hypothesis, at its `file:line`, and where it comes from

| # | hypothesis | stated at | where it comes from |
|---|---|---|---|
| 1 | `lam : V ℓ` | `src/L/Condensation.lagda.md:7380` | supplied by `KValue`. The one entry the seven consume |
| 2 | `ordλ : IsOrd lam` | `:7380` | supplied by `KValue`. Carried, never eliminated (D-10 above) |
| 3 | `succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩` | `:7381` | supplied by `KValue`. Not on the seven's path |
| 4 | `∅∈λ : ⟨ ∅ ∈ lam ⟩` | `:7382` | supplied by `KValue`. Not on the seven's path |
| 5 | `gam : V ℓ` | `:7383` | supplied by `KValue`. Carrier slot only |
| 6 | `ordγ : IsOrd gam` | `:7383` | supplied by `KValue`. Carrier slot only |
| 7 | `γ∈λ : ⟨ gam ∈ lam ⟩` | `:7383` | supplied by `KValue`. Spent by `carrierK` alone (`:7424`) |
| 8 | `c1 c2 c3 c4 c5 c6 : S` | `agents/tasks/LJ-1-539/Probe539.agda:368` | **NEW, and all six FREE.** The cells `[LJ-1.495]`'s six-fold shift conses on. The seven pin none of them |
| 9 | `valSub` | `agents/tasks/LJ-1-539/Probe539.agda:369-372` | **supplied by a predecessor's TYPE, and owed as a TERM.** It is `[LJ-1.508]`'s module hypothesis (`agents/tasks/LJ-1-508/Probe508.agda:201-205`). Nothing in the tree inhabits it |
| - | `arityK` | `src/L/Condensation.lagda.md:6114-6115` | **NOT a telescope entry.** `KValue.facts .arityK` (`:7425`) is a real term and it is passed at the shifted index with no conversion (`Probe539.agda:375-376`) |

**`ω∈σ` IS NOT IN THIS LIST, AND `[LJ-1.538]` HAD TO CARRY IT.** That is
the one structural difference between the two collected frames.

### What each of the seven costs: ONE application, and nothing else

No field needed a second step, a `subst`, or a weakening. The `valSub`
argument is passed UNCHANGED to all seven, at seven different prefix
lengths, because `lookup (suc^k) (prefix ++ γ')` reduces to
`lookup (suc zero) γ'` definitionally. **If that reduction ever stopped
being definitional this file would stop checking**, so the claim is
measured and not argued.

| field | stated at | prefix | index quadruple | supplier |
|---|---|---|---|---|
| `subK₁-and` | `src/L/Condensation/TwelveAgree.lagda.md:265` | 7 cells | 8, 5, 4, 1 | `W3.subK-from-sub` (`Probe539.agda:97`) |
| `subK₀-and` | `:271` | 7 cells | 8, 5, 3, 0 | `W3.subK-from-sub` |
| `subK₁-imp` | `:277` | 8 cells | 9, 6, 5, 2 | `W3.subK-from-sub` |
| `subK₀-imp` | `:283` | 8 cells | 9, 6, 4, 1 | `W3.subK-from-sub` |
| `subK-neg` | `:290` | 6 cells | 7, 4, 3, 1 | `W3.subK-from-sub` |
| `subK-un` | `:311` | 6 cells | 7, 4, 3, 1 | `W3.subKSucc-from-sub` (`Probe539.agda:128`) |
| `subK-allin` | `:326` | 7 cells | 8, 5, 3, 1 | `W3.subKSucc-from-sub` |

The index quadruples are the ones `EnvSupply`'s own delivered
instantiations already use (`src/L/Coding/EnvSupply.lagda.md:506`, `:517`,
`:528`, `:539`, `:550`, `:561`, `:572`). **This file changed the
environment TAIL from `Vec S 2` to `γ'` and kept every numeral.** It did
not rebuild `subK-gen`, `subKSucc-gen` or any of the seven.

**AND `SubKSeven` IS THE RECORD'S OWN BLOCK, BY AGDA AND NOT BY MY
READING.** `statement-matches` (`Probe539.agda:213-225`) reads all seven
off a `TFacts` value by projection, with no coercion, no `subst` and no
re-association. The obligation never calls it, so no `TFacts` field
proves a `TFacts` field.

### THE PEAK RSS, BESIDE 538's 722,698,240 B

Every run below deletes `_build/2.8.0/agda/agents/tasks/LJ-1-539/Probe539.agdai`
first, so the probe re-elaborates while the `src/` interfaces stay warm.
That is `[LJ-1.538]`'s "cold" protocol, and the figures are stable to the
byte across repeats. ONE Agda process at a time, `GHCRTS="-A64m -I0 -M8g"`,
set by the program and untouched.

| what | real | max RSS | exit | evidence |
|---|---|---|---|---|
| the seven STATED, no witness | 3.11 s | 706,002,944 B | 0 | `runs/stated-0.time` |
| the same, repeat | 3.18 s | 706,002,944 B | 0 | `runs/stated-1.time` |
| the same, repeat | 3.11 s | 706,002,944 B | 0 | `runs/stated-2.time` |
| the seven STATED AND INHABITED | 3.83 s | 749,125,632 B | 0 | `runs/full-0.time` |
| the same, repeat | 3.49 s | 749,125,632 B | 0 | `runs/full-1.time` |
| the same, repeat | 3.51 s | 749,125,632 B | 0 | `runs/full-2.time` |
| the same, after two comment corrections | 3.92 s | 749,109,248 B | 0 | `runs/final.time` |
| **the seven witnesses alone** | **+0.72 s** | **+43,122,688 B (41.1 MiB)** | | `runs/full-0.time` less `runs/stated-0.time` |

The stated-only file is kept verbatim at
`runs/Probe539.stated-only.agda.txt`. Both members of the pair carry the
FINAL import block, so the difference is the witnesses and nothing else.

**THREE MORE RUNS ARE IN `runs/` AND THEY ARE NOT COMPARABLES.** They are
the incremental build log that C-22 produced, each on a partial file, and
two of them predate the `L.Condensation.TwelveAgree` import:
`runs/succ-0.time` (both engine terms alone, 2.34 s, 664,813,568 B),
`runs/rec-0.time` (engine plus the record, 2.62 s, 699,662,336 B) and
`runs/seven-0.time` (all but the frame, 3.42 s, 736,362,496 B). Exit 0
on each. **Nothing in this report is funded against them.**
`runs/witness-0.out` is the witness meter before the two comment
corrections and `runs/witness-final.out` is after; both PASS.

**THE TWO FAMILIES NOW GIVE TWO POINTS, AND THE COST PER FIELD IS FLAT.**

| family | fields | witnesses cost | per field | full-file peak RSS |
|---|---|---|---|---|
| env (`[LJ-1.538]`) | 9 | 60,063,744 B, +0.73 s | 6.37 MiB | 722,698,240 B |
| subK (this task) | 7 | 43,122,688 B, +0.72 s | 6.16 MiB | 749,125,632 B |

**Sixteen fields collect for about 103 MiB of witness, in two files.**
`[LJ-1.534]` is reported to have hit a heap wall four times trying
sixteen at one frame. I cannot check that record: `grep -c 'LJ-1-534'`
over the tracked `dev/pod/transitions/2026-08.jsonl` in this worktree
gives 0 and the file ends at seq 158, task `LJ-1.399`,
`2026-08-19T13:31:57Z`. **`[LJ-1.538]` reported the same gap**
(`agents/tasks/LJ-1-538/lj-1.538-report.md:44-53`), and no
`agents/tasks/LJ-1-534/` directory exists here. I repeat the wall as the
brief's claim and not as a measurement of mine. **What I CAN say is that
the two collected families together are 103 MiB of witness on a 8 GiB
cap, so the count of collected fields is not what walls.**

## LAWS

**D-10.** Fired, and it is the section above. The two generics were read
at `file:line` and the single use of `TK` was found BEFORE any Agda ran.
That reading is what turned W3 from "which of three supplies the
membership" into "does the family want a membership at all".

**C-22.** Followed. The report was written as a skeleton with ten
`PENDING` sections before the first Agda run, and each section was filled
as its run landed.

**C-42.** A refutation is in this neighbourhood and it is
`[LJ-1.508]`'s `subK-is-strictly-weaker`
(`agents/tasks/LJ-1-508/Probe508.agda:237-243`): the subset form does not
give the membership, at this frame. C-42 asks for the sweep of the shape
before the cure. **This task IS part of that sweep**: it asks, of the
seven fields that `[LJ-1.509]` funded against the membership, how many
actually need it. The count is **0 of 7**. The TWO other `TFacts`
positions that read slot one, `valK` and `valK-un`
(`src/L/Condensation/TwelveAgree.lagda.md:175`, `:179`), were already
swept by `[LJ-1.508]` and take `valSub` too, and `[LJ-1.509]` counted
that pair at `agents/tasks/LJ-1-509/lj-1.509-report.md:101-105`.
**The full sweep of "reads slot one" over `TFacts` is therefore NINE
positions, all nine served by `valSub`, and none of them needs `TK`.**

**P-l did not fire.** The stated types name `Fin`, `lookup`, `subValAt`,
`subValSuccAt` and numeral chains. `sucV` occurs in a stated type in two
places: `Probe539.agda:120-121`, which is `subValSuccAt-adequate`'s own
right-hand side (`src/L/Coding/Model.lagda.md:1411`) with `sucV` applied
to a bound variable, and `Probe539.agda:359`, which is `KValue`'s own
telescope entry copied verbatim from `src/L/Condensation.lagda.md:7381`.
Neither is a transparent stage presentation inside a statement, which is
the shape P-l names. `sucʟ` is `opaque`
(`src/L/Axioms/Numerals.lagda.md:97-105`, read at source), which is the
guard `[LJ-1.509]` names at `agents/tasks/LJ-1-509/lj-1.509-report.md:258`. No stage is unfolded.

**D-26 did not fire.** These are memberships under a satisfaction
hypothesis. There is no well-founded key and no tower ordering.

**W2.** Answered. The family is stated ONCE, in `SubKSeven`
(`Probe539.agda:160-211`), generic in `K : Fin (5 + n)` and
`γ' : S ^ (11 + n)`, and instantiated once at `n = 9` against `KValue`'s
`Fin 14` (`:373`). The two engine terms
(`W3.subK-from-sub`, `W3.subKSucc-from-sub`) are generic in the
environment length, the environment and all four indices, so seven
prefixes of three different lengths share one body each. The packaging
lives once, in `W3.keyEq` and `W3.keyEqS`, and no field repeats it. No
site is written in a fixed form. There is no conflict with W2.

**W4 did not fire.** No module was retired. `dev/ARCHIVE.md` gets no row
from this task.

**THE RATIO BAR CANNOT FIRE ON THIS TASK.** The write scope is one raw
`.agda` probe, one report and one `runs/` directory. A raw `.agda` file
carries no ` ```agda ` fence, so the in-fence line count of this task's
write scope is 0 and the bar's divisor is 0. In-fence `agda` lines under
`src/` written by this task: **0**. Nothing landed in `src/`.

## ESTIMATE AGAINST ACTUAL

The brief estimated about 150 lines in the probe, of which the obligation
about 45, on a SHAPE comparable from `[LJ-1.538]`.

**Actual: 379 lines in the probe, of which 133 are comment and 33 are
blank, so 213 are code.** The obligation's own chain is `module Seven`
(`:256-325`, 59 code lines) plus `module Frame` (`:357-377`, 16) plus the
top-level alias (`:379`, 1): **76 code lines against about 45
estimated.**

The overrun is the count and the statement, not the argument. The
estimate was written for SIX fields and the family is SEVEN, which is one
sixth more of everything. Of the 76, **42 are the seven field
applications** and each is six lines of index numerals; the module
telescopes and `Ktr` are the other 34. The rest of the file is 45 code
lines of record statement (`SubKSeven`, `:160-211`), 46 of engine
(`:76-138`, both generics plus the packaging), 13 of `statement-matches`,
4 of `sub-from-member` and 28 of imports. **Neither
`statement-matches` nor `sub-from-member` was required by the brief.**

Comparables are of SHAPE and nothing may be funded against them.

## WHAT THE NEXT BRIEF NEEDS

1. **THE SLOT-ONE DEBT IS ONE STATEMENT, IT IS WEAKER THAN
   `[LJ-1.509]` THOUGHT, AND IT NOW COVERS NINE `TFacts` POSITIONS.**
   `valSub : (x : S) → x ∈ slot one → x ∈ K`
   (`agents/tasks/LJ-1-508/Probe508.agda:201-205`) discharges the seven
   `subK` fields (this task) and `valK` and `valK-un` (`[LJ-1.508]`).
   **Nothing in the tree inhabits it.** It belongs to whatever task fixes
   what occupies `γ'` position 1. **A brief that asks for `TK` instead is
   asking for strictly more than any consumer needs**, and
   `[LJ-1.508]` measured that the extra is real
   (`Probe508.agda:237-243`).
2. **SEVEN COLLECT FOR 41 MiB AND 0.72 s. WITH `[LJ-1.538]`'s NINE THE
   COST PER FIELD IS FLAT, 6.16 MiB AGAINST 6.37 MiB.** Two points, two
   different families, two different generics. **The remaining fields can
   now be priced by extrapolation instead of by guess: about 6.3 MiB of
   witness per collected field.** `AGENTS.md:45` still forbids
   transferring the figure to a family with a different shape, and
   point 5 names the one that has a different shape.
3. **`TFacts`'s 59 FIELDS ARE NOW 16 COLLECTED, 26 SHIFTED AND 17
   NEITHER.** Counted by field declaration over
   `src/L/Condensation/TwelveAgree.lagda.md:133-335`: **59 fields**, the
   same total `[LJ-1.538]` reported. 26 are the shared block
   `[LJ-1.495]` SHIFTS (`:133-161`), which is a different operation from
   collecting. 9 are `[LJ-1.538]`'s env forms (`:186-243`). 7 are this
   task's `subK` family (`:265-288`, `:290-295`, `:311-316`, `:326-331`).
   **17 are neither shifted nor collected**, and points 5 and 6 name
   them.
4. **THE SIX CELLS OF THE SHIFT ARE STILL FREE, AND THE TWO COLLECTED
   FAMILIES DISAGREE ABOUT CELL 0.** `[LJ-1.538]` had to pin cell 0 to
   `SupplyEnv.B₀` (`agents/tasks/LJ-1-538/Probe538.agda:177-178`); this
   task pins nothing. The two frames are compatible, because a pinned
   cell is an instance of a free one, but **a brief that merges the two
   families into one frame pays `[LJ-1.538]`'s `ω∈σ` and its pinned cell
   0 for the subK half, which does not want either.** Collect first,
   merge last.
5. **`valV`, `valW` AND `wKfact` ARE STILL THE NEXT SUSPECT AND STILL
   UNMEASURED.** `[LJ-1.538]` point 5 named them and this task did not
   touch them. Their types prepend NINE slots to `γ'`
   (`src/L/Condensation/TwelveAgree.lagda.md:244-249`, `:250`, `:256`)
   and name `tmValAt`, and their generic is `Fact.tmValK`
   (`src/L/Coding/EnvSupply.lagda.md:575-592`), which is a case split and
   not a three-step chain. **`Fact.valV` and `Fact.valW`
   (`:594-612`) take TWO memberships each, `zK` and `aK` or `bK`, not
   one.** A brief that takes them should expect two slot facts, not one,
   and a number unlike this task's.
6. **`consK-exist`, `consK-forall` AND `consK-allin` ARE THE OTHER
   UNMEASURED BLOCK** (`src/L/Condensation/TwelveAgree.lagda.md:317-325`,
   `:332-335`). Their generic is `Fact.ConsK`
   (`src/L/Coding/EnvSupply.lagda.md:626`), a MODULE and not a function,
   so its telescope is the thing a brief must price first. I did not open
   it.
7. **THE TRANSITIONS RECORD IN A WORKTREE IS STILL THREE DAYS BEHIND.**
   `[LJ-1.538]` point 8 reported it and it is unchanged: the tracked copy
   here ends at seq 158, `LJ-1.399`, `2026-08-19T13:31:57Z`. A brief that
   cites `dev/pod/transitions/2026-08.jsonl` for a recent event hands the
   worker an unverifiable premise. This is a program observation, not a
   mathematical one.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ.** `:175` reads:
  `| LJ-1.99 | Does transitivity of K close entryK? | YES, MEASURED GREEN | Four arityK steps close entryK; arSubK is one step. The rows supply every tie; EnvSet's own telescope does not |`
  This is the campaign's own earliest record that `arityK` is the tie for
  this shape, and that a SUBSET step ("arSubK is one step") is the cheap
  one. It agrees with what this task measured. `:345` reads:
  `| LJ-1.287 | Cure sucV-in, EnvSupply's 99.2 pc | 480.25 s TO 4.10 s FOR THREE LINES | 438 s was an IDENTITY function: depth is free, the MIXED spelling of the level costs. Three diagnoses refuted |`
  I read this row BEFORE writing the successor packaging, because that
  packaging is a mixed spelling of a successor (`sucʟ` against `sucV`,
  `Probe539.agda:118-126`). The row says depth is free and mixing is what
  costs. **The mixing here is two `≡` steps on a bound variable, not on a
  level, and the measured cost of the whole successor sibling is inside
  the 41 MiB the seven witnesses cost together.** I did not carry the
  row's number: `AGENTS.md:45`.
- **`archive/dev/JOURNAL.md`. DECLINED.** `grep -ci` gives 0 for each of
  `subK`, `subVal`, `valSub`, `TFacts` and `EnvSupply`. It carries
  nothing about this front. Not read.
- **`archive/dev/JOURNAL-archived.md`. DECLINED.** The same five counts,
  0 each. Not read.
- **`dev/ARCHIVE.md`. DECLINED.** The same five counts, 0 each. W4 did
  not fire on this task, so there was no row to write and no retirement
  to check. Not used.
- **`archive/dev/ORCHESTRATION.md`. DECLINED.** The same five counts, 0
  each. It is the archived operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`, and it binds nothing here. Not
  read.

## LITERATURE USED

**NO HIT, and each candidate is declined in writing.** This task is a
record collection and two module instantiations inside the tree. It
states no new mathematics, so no source stands behind it. The Boundary
also freezes mathematical prose until both trophies land
(`AGENTS.md:69`).

- **`dev/literature/truncation-and-selection.md`. DECLINED.** `grep -ci`
  gives 0 for each of `subK`, `subVal`, `valSub`, `TFacts` and
  `EnvSupply`. Not read.
- **`dev/literature/devlin-II5.md`. DECLINED.** The same five counts, 0
  each. The `K(u)` bound it stands behind is already landed as `KValue`,
  and this task adds nothing to it. Not read.
- **`dev/literature/digest.md`. DECLINED.** The same five counts, 0 each.
  Not read.
- **`dev/literature/geology.md`. DECLINED.** The same five counts, 0
  each. Not read.
- **`dev/literature/glossary-review-2026-08.md`. DECLINED.** The same
  five counts, 0 each. No term of this task went to the naming pipeline:
  every name in the probe is the tree's own, or `[LJ-1.508]`'s and
  `[LJ-1.509]`'s. Not read.
