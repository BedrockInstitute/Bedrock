# LJ-1.325 report: re-price PLAN 0.0 against the restated trophy

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Recon. It lands
nothing. Written incrementally (C-22).

**I RAN NO AGDA.** A sibling task measures check times. Every mark below comes
from reading source text, from `git`, or from `ledger.py`, which runs no Agda.
Each negative carries **MEASURED** or **INFERRED**, in those words.

## HEADLINE

**THE RESTATED TROPHY COSTS MORE, BY ABOUT 600 LINES. And that is about 800
lines LESS than the ruling's own survey said, because the machinery the ruling
priced as new is DELIVERED.**

Basis: `32,473 + 470 + 186 + 40` for the terms `dev/PLAN.md:76-83` already
carries, plus about 25 lines for the coded delivery and about 600 lines for the
reverse bound. The 32,473 is MEASURED by `ledger.py --brief` at HEAD. The 25 is
a DELIVERED COMPARABLE. The 600 is a SURVEY.

**One term is UNPRICED and I say so rather than dress a survey as a price.** The
coded delivery has a second half that no delivered site measures: the legs of
the final chain that carry no object-language description yet. Section 1.1 names
it and names the probe.

**No delivered chapter dies.** MEASURED: `src/L/Absorption.lagda.md` and
`src/L/InjChain.lagda.md` left the GCH import closure, and no `src/` master
except the catalog imports either. But they are the two chapters that BUILD
coded injections, so the restatement makes them more necessary, not less. It
repoints them from statement-side supply to proof-side supply. DD13 does not
open.

## 1. THE TWO DEBTS

### 1.0 The finding that moves both prices

`InjCode F a b` is a four-part product at `src/L/Cardinal.lagda.md:223-228`:
`svAt`, then `domAt`, then `injAt`, then a range clause.

**Three delivered modules already build an L-set and prove exactly those four
facts about it, under the heading「THE FOUR CONJUNCTS」.** MEASURED, by reading
the module text.

| delivered site | the L-set | the four facts | what it is |
|---|---|---|---|
| `src/L/Absorption.lagda.md:410-498` | `G`, by separation, `:411` | `sv :452`, `ij :466`, `dm :480`, `ran :494` | the shift graph, A6's `absorbs` |
| `src/L/InjChain.lagda.md:337-422` | `K`, by separation, `:338` | `svK :380`, `ijK :391`, `dmK :402`, `ranK :420` | the COMPOSITE of two coded injections |
| `src/L/InjChain.lagda.md:478-547` | `G`, by separation, `:479` | `sv :518`, `ij :525`, `dm :532`, `ran :544` | the INCLUSION, `OrdIncl` at `:604` |

Each fact has the type of the matching `InjCode` conjunct, word for word, at the
same argument spellings. Each module is opened `public` at its L instantiation
(`src/L/Absorption.lagda.md:604-605`, `src/L/InjChain.lagda.md:598` and `:607`),
so the four names are reachable from outside today.

**So `InjL` is inhabitable from delivered material.** The delivered code throws
the coded witness away at the last step: `absorbs` at
`src/L/Absorption.lagda.md:615-618` returns only the `Small` readback, and
`OrdIncl` exports only `incl` and `incl-inj`.

**The ruling priced debt 1 against the wrong comparable.**
`agents/tasks/LJ-1-323/lj-1.323-ruling.md:253-257` names「the delivered coding
readback half of `src/L/Coding/Injection.lagda.md`」. MEASURED, by reading that
file whole: every module in it runs CODE to AMBIENT. It takes `F : S` with the
satisfaction facts as hypotheses and returns ambient data. It builds no
`InjCode` witness. The modules that run AMBIENT to CODE are the two above, and
the ruling did not read them.

**Delivered comparables, MEASURED in the pinned caliber** (non-blank lines
inside the ` ```agda ` fence):

| span | lines | what it costs |
|---|---:|---|
| `src/L/Absorption.lagda.md:228-376`, `ShiftFo` | 130 | describe one ambient map by a formula |
| `src/L/Absorption.lagda.md:385-530`, `Carve` | 127 | carve it and prove the four conjuncts |
| `src/L/InjChain.lagda.md:445-607`, the inclusion | 133 | description, carve, L instantiation |
| `src/L/InjChain.lagda.md:314-433`, `Comp` | 103 | compose two coded injections |
| `src/L/InjChain.lagda.md:75-98`, `StageBound` | 17 | the bound, generic, one device for every row |

### 1.1 Debt 1: the final injection, delivered CODED

**The ruling's price: about 800 naive lines. My re-derivation: about 25 priced
lines plus ONE unpriced term.**

**THE WIDEST UNMEASURED TERM.** It is NOT「the interning of one delivered
ambient injection」, which the ruling names at `:258-260`. That term is
MEASURED and it is delivered three times over (section 1.0).

**The widest unmeasured term is the SQUARE LAW leg.** The final injection is a
chain. Its inclusion legs are carved (`OrdIncl`). Its shift leg is carved
(`ShiftGraph`). Its composition is carved (`Comp`). **Its pairing leg is
AMBIENT and has no object-language description.** MEASURED: `pairω` at
`src/L/InjChain.lagda.md:175-185` and `squareω` at `:184` return bare ambient
functions, and `src/L/Ordinal/SquareLaw.lagda.md` names no formula. So the leg
that carries the counting cannot enter `Comp`, because `Comp` demands the four
conjuncts of BOTH arguments.

**THE SMALLEST DECISIVE MINIATURE.** Two probes, and the first is tiny.

**Probe A, the adapter, about 10 lines.** Instantiate `L.InjChain.OrdIncl` at a
delivered ordinal pair and form the tuple `(sv , dm , ij , ran)` at the type
`InjCode G D C`. Run: one `agda` invocation on a probe file in
`agents/tasks/<TASK>/`, importing `L.Cardinal` and `L.InjChain`.
**GO:** the tuple typechecks, so `InjL` is inhabitable from delivered code and
debt 1's adapter half costs about 25 lines.
**NO-GO:** the conjunct types do not fit, by a level, a spelling or an argument
order. Then the adapter is a rewrite of three modules' exports and debt 1
returns to the ruling's survey band.

**Probe B, the square leg, about 40 lines.** Write the object-language
description of `pairω`, the pairing on ω, and carve its graph by the `Carve`
pattern. `pairω` is the SMALLEST site: it is delivered in about 10 ambient lines
at `src/L/InjChain.lagda.md:175-185`, it needs no square law above ω, and its
value map is arithmetic rather than case-defined.
**GO:** the description lands inside the `ShiftFo` band, so each remaining leg
costs about 130 lines of description plus about 127 of carve, and debt 1's
unpriced half becomes about 260 lines per uncarved leg.
**NO-GO:** the pairing has no bounded description at ω. Then every counting leg
must be re-derived internally, as Devlin does, and debt 1 exceeds the ruling's
800 rather than falling under it.

**WHAT THE ESTIMATE BECOMES ON NO-GO.** Probe A NO-GO returns debt 1 to about
800 lines, the ruling's survey. Probe B NO-GO puts no number on it at all, and
the next action is a route recon and not a build.

### 1.2 Debt 2: the reverse bound `InjL δ (𝒫 κ)`

**The ruling's price: about 600 naive lines. My re-derivation lands at the same
number by a different road, so the number stands and its GATE changes.** P-l
says a comparable elsewhere is a hypothesis. Two independent surveys agreeing is
still two surveys, so this stays a survey.

**What is delivered, and the ruling did not count it.**

1. **L's own order, AS AN L-SET.** `orderL : S` at
   `src/L/Choice/Order.lagda.md:693`, with both adequacy directions,
   `orderL-fill` at `:696` and `orderL-rep` at `:700`.
2. **The pattern for describing an order-minimal choice in the object
   language.** `Pick a rel` at `src/L/Choice/Transversal.lagda.md:194-238`
   describes「z is in a member x of a, and nothing in x precedes z」, with `rel`
   as a constant, and `transversalSet` carves it by separation at `:281`. That
   whole module is 137 lines, MEASURED.
3. **The coded inclusion and the coded composition**, from section 1.0.

**What is MEASURED absent.**

1. **No Cantor.** `grep -rni "cantor" src/` returns zero hits. MEASURED, my own
   grep at HEAD. This confirms the ruling's claim (C-44).
2. **No order-type predicate.** `grep -rni "otp|orderType|isWellOrderAt|woCode"`
   over `src/` returns zero relevant hits. MEASURED.
3. **No internal well-ordering of a power set.** The delivered choice is the
   transversal form, `hasChoiceL` at `src/L/Choice/Transversal.lagda.md:382`.
   MEASURED: nothing derives a well-ordering theorem inside L from it.

**THE WIDEST UNMEASURED TERM.** It is the ORDER-TYPE PREDICATE in the object
language: a formula that says「W codes a well-order whose order type is α」,
with its adequacy in both directions. Every other part of the reverse bound
reduces to a delivered device.

The reason it dominates: the classical route maps each α below κ⁺ to a subset of
κ that codes a well-order of type α. The RELATION「W has order type α」is
single-valued from W to α and many-valued from α to W. So the cheap object is a
coded SURJECTION from a subset of `𝒫 κ` onto δ, and `InjCode` demands an
INJECTION out of δ. Turning the one into the other needs a canonical choice of W
per α. Item 1 and item 2 above supply the choice device. **The order-type
predicate itself has no delivered part.** INFERRED, from the two greps and from
reading `src/L/Coding/Powerset.lagda.md`'s exported surface.

**THE SMALLEST DECISIVE MINIATURE, and it also gates debt 1.**

**Build `InjL κ (𝒫 κ)` from delivered code.** Every member of an ordinal κ is a
subset of κ, by κ's own transitivity. So the map is the inclusion, and
`L.InjChain.InclGraph D C sub` is exactly its graph, with
`D = κ`, `C = 𝒫 κ`, and `sub` supplied by the model's power-set specification.
Form the tuple at the type `InjCode G κ (𝒫 κ)`.

Size: about 10 lines. Run: one `agda` invocation on a probe file that imports
`L.Cardinal`, `L.InjChain` and `L.GCH`.

**GO:** the reverse bound holds one cardinal step too low, from delivered code,
in about 10 lines. Then debt 2's whole remaining content is the lift from κ to
δ, which is the order-type predicate and nothing else, and the 600 stands as the
price of that one object.
**NO-GO:** `𝒫 κ`'s membership does not read as「subset of κ」at the coded face,
or the four conjuncts do not fit `InjCode`. Then the reverse bound has no
delivered starting point at all, debt 2 is not 600, and the next action is to
price an internal re-derivation of the whole leg.

**WHAT THE ESTIMATE BECOMES ON NO-GO.** It becomes UNPRICED. A NO-GO here means
the coded face has no delivered inhabitant, and both new debts lose their basis
at once. That is why one miniature gates both.

### 1.3 The ruling's own miniature, checked

The ruling names「the decisive miniature is interning `absorbs` at its smallest
site」(`agents/tasks/LJ-1-323/lj-1.323-ruling.md:258-260`).

**I REPLACE IT.** It measures a term that is already measured. `absorbs` at
`src/L/Absorption.lagda.md:615-618` is built by `ShiftGraph`, which opens
`Carve` public, and `Carve` proves the four conjuncts at `:452`, `:466`, `:480`
and `:494`. Interning `absorbs` is therefore the tuple formation of probe A, not
a build. The ruling's miniature would return GO and would teach nothing about
the term that actually dominates.

## 2. THE RE-PRICED SECTION 0.0 BLOCK

### 2.1 Does the restatement kill any of the 470's steps

**NO. MEASURED, by re-reading the 23-step chain table at
`agents/tasks/LJ-1-310/lj-1.310-report.md:93-119`.**

No step of the 23 produces an ambient injection. The chain runs from `φ₀` to
`Graph*`, and every step is a formula manipulation, a satisfaction transport or
an `Agree` module. Step 22, the reading transport between `⊨ᵐ` and the ambient
reading, is the only step that names the ambient at all, and it supplies `amb`
for `module Whole` rather than an injection for the trophy's conclusion.

So the 470 does not fall. **The restatement raises the chain's value**, because
the conclusion is now internal and the chain is what makes internal satisfaction
available. INFERRED, not MEASURED: no term was built.

`[LJ-1.310]`'s about 175 hand-written lines outside the 470 stay outside the 470
and stay outside the endpoint figure, exactly as before.

### 2.2 The `sq` obligation does not leave the price

`sq` left the STATEMENT. It did not leave the PROOF.

MEASURED: `grep -rn "SqShape" src/` returns ZERO hits at HEAD. The two consumers
spell their own `sq` parameters and they are DATA, not truncations:
`src/L/StageCardinal.lagda.md:17-19` and `src/L/BoundedSubset.lagda.md:1388-1390`.

So `[LJ-1.305]`'s untruncation problem MOVES from the statement to those two
consumers. It does not dissolve. `[LJ-1.301]`'s 186-line descent stays in the
price. `[LJ-1.294]`'s limit-ordinal lemma stays owed, because `Init`'s
successor-closed component is a hypothesis of `via-col-square` and the use site
did not change (INFERRED, from `dev/PLAN.md:384-396`; I did not re-read
`SquareLaw`).

### 2.3 The block, re-derived

| | old, `dev/PLAN.md:76-83` | new | basis |
|---|---:|---:|---|
| standing today | 32,488 | **32,473** | `ledger.py --brief`, MEASURED at HEAD |
| of which the GCH wing | 14,099 over 16 masters | not re-measured | I did not run the wing split |
| `q'`'s hand-written part | 470 | **470** | unchanged, section 2.1 |
| `[LJ-1.8]`'s descent | 186 | **186** | unchanged, section 2.2 |
| `[LJ-1.304]`'s two add-ons | 40 | **40** | unchanged, INFERRED as before |
| the coded delivery, priced half | not present | **about 25** | DELIVERED COMPARABLE, section 1.0 |
| the reverse bound | not present | **about 600** | SURVEY, section 1.2 |
| **BEST SINGLE FIGURE** | **about 33,200** | **about 33,800** | |

**THE NET: about plus 600 lines.**

**THE FIGURE IS STILL A FLOOR, and it now has FIVE named omissions rather than
four.** The four `dev/PLAN.md:91-93` and `:48` already carry: the composite's
term, the truncation, A4's master, and A5's 348 with A6's 399. The fifth is
debt 1's unpriced half, section 1.1.

### 2.4 What the restatement DELETED from the price

**About 15 lines and nothing else.** MEASURED: the fence of
`src/L/GCH.lagda.md` fell from 73 lines to 58, and standing fell by the same 15.
The brief expected about 18.

`SqShape`, `AbsorbsShape` and `absorbsL` left the statement file. **They did not
leave the project.** `absorbsL` was a named alias of `absorbs`, which stands
unchanged at `src/L/Absorption.lagda.md:615`. `AbsorbsShape` was that
function's type written out, and `src/L/Absorption.lagda.md:610` says so in its
own comment. `SqShape` was a type with no `src/` consumer, MEASURED.

So the deletion is a text deletion. **No obligation was discharged by it.**

### 2.5 What it ADDED

The two debts, at about 25 priced lines plus one unpriced term, and about 600.

### 2.6 The residues in section 0.0, checked for truth (D-10)

| residue in section 0.0 | still true |
|---|---|
| `:106-109` the composite's term is unwritten | **YES**, MEASURED by `[LJ-1.310]` section 2 and unaffected by the restatement |
| `:110-111` the truncation is unknown | **YES**, and section 2.2 says where it moved |
| `:112-113` the cardinal face at κ is a statement-level fork | **NO. IT IS CLOSED.** `[LJ-1.323]` ruled the coded face on meaning. `dev/PLAN.md:410-431` is spent |
| `:114-115` two INFERRED add-ons | **YES**, unchanged |
| `:353-357` one hypothesis blocks the proof, `sq : SqShape` | **NO, AS STATED.** `sq` is not a hypothesis of the statement any more. Three things now block: the square lemma, the coded delivery, the reverse bound |
| `:303-309` the DD4 figure is the statement's and understates | **YES**, and section 3 says by how much it moved |

## 3. THE DD4 CLOSURE NUMBERS

MEASURED at HEAD `ffb0811` by `.venv/bin/python scripts/measure/ledger.py --reuse`.
The old row is MEASURED at `d7aa570`, the parent commit, by a replication of
`reuse_report` that reads `git show <rev>:<path>` in place of `git show
HEAD:<path>`. The replication reproduces `ledger.py` at HEAD digit for digit on
all seven figures, so it is calibrated. It runs no Agda.

| figure | old, at `d7aa570` | new, at HEAD | move |
|---|---:|---:|---|
| AC closure, masters | 73 | 73 | 0 |
| AC closure, lines | 17,197 | 17,197 | 0 |
| GCH closure, masters | 51 | 48 | minus 3 |
| GCH closure, lines | 9,967 | 8,889 | minus 1,078 |
| SHARED, masters | 44 | 43 | minus 1 |
| SHARED, lines | 7,632 | 7,596 | minus 36 |
| share of the union | 39.1% of 19,532 | 41.1% of 18,490 | plus 2.0 points |
| standing | 32,488 | 32,473 | minus 15 |

**WHICH WAY THE SHARE MOVED, AND WHY.** It ROSE, 39.1 to 41.1 percent. **Read
the rows and not the share.** SHARED FELL, 44 masters to 43 and 7,632 lines to
7,596. The share rose because the denominator fell faster: the GCH side lost
1,078 lines and the intersection lost only 36.

Three masters left the GCH closure, MEASURED: `src/L/Absorption.lagda.md`,
`src/L/InjChain.lagda.md` and `src/L/Axioms/Infinity.lagda.md`. Nothing entered.
`src/L/Axioms/Infinity.lagda.md` is the one that left SHARED. It stays in the AC
closure and it is AC-only again.

**AND THE UNDERSTATEMENT GREW.** `dev/ledger.toml:204` says the closure is read
from a statement whose proof is not wired, so it understates. The restatement
removed two chapters that the PROOF still needs, `Absorption` and `InjChain`,
and section 1.0 shows the proof needs them MORE than before. **So the
understatement grew by about 1,027 lines**, being the two chapters' size at
`d7aa570`, and 41.1 percent is a lower floor than 39.1 percent was.

**NAME THE AXIS (C-46).** DD4's own axis, AC closure against GCH closure, fixed
in code at `scripts/measure/ledger.py:50`. Both figures above are on it. This is
the first measurement of that axis against the restated statement.

## 4. THE FALSE WORDS IN dev/ledger.toml

I edited nothing. These are the exact words.

1. **`dev/ledger.toml:204`, `gch_root_why`.** Three clauses are now false.
   - 「`absorbs` is SUPPLIED since `[LJ-1.286]`」. **FALSE.** `absorbs` is not
     mentioned by the statement at all. MEASURED: `grep "absorbsL\|AbsorbsShape"
     src/` finds one comment and no code.
   - 「`sq` alone remains an unsupplied Pi-parameter」. **FALSE.** The statement
     has no Pi-parameter beyond `lem` and `zf`. MEASURED: `grep "SqShape" src/`
     returns zero hits.
   - 「landed 2026-08-15 by `[LJ-1.280]`」. **STALE, not false.** The file was
     replaced on 2026-08-16 by `[LJ-1.323]`.
   The clause「the closure is the statement's and it understates」stays TRUE and
   understates by more, per section 3.

2. **`dev/ledger.toml:183-186`, the comment block.** 「it carries ONE unsupplied
   hypothesis rather than two: `sq : SqShape` at src/L/GCH.lagda.md:80」 is
   **FALSE**, and 「`absorbs` is now SUPPLIED, by L.Absorption through the named
   alias `absorbsL` at src/L/GCH.lagda.md:57-63」 is **FALSE**. The first line reference reaches past the end of a 70-line file; the second
   names lines that now hold other text.

3. **`dev/ledger.toml:191-198`, the share block.** 「the share FELL when the
   proof got stronger, 41.1 to 39.1 percent」 is **OVERTAKEN**. The share is
   41.1 percent again. 「SHARED went UP, 43 masters and 7,596 lines to 44 and
   7,632, because L.Axioms.Infinity was AC-only and is now shared」 is
   **REVERSED**: `L.Axioms.Infinity` is AC-only again. The block's REASONING
   survives and is worth keeping: the ratio is driven by the denominator, and
   the restatement is a second instance of the same lesson pointing the other
   way.

4. **One defect in `src/`, reported and not edited.**
   `src/L/Absorption.lagda.md:610` reads「(`AbsorbsShape`,
   src/L/GCH.lagda.md:49-53)」. The name and the line range are both dead.

## 5. DATED RECORDS THAT QUOTE THE OLD STATEMENT

Listed at `file:line`. **I edited none of them.** A record is never rewritten.

**Live screens, which the orchestrator may correct.**

| locator | what it says that is now false |
|---|---|
| `dev/PLAN.md:72` | 「the function object `SqShape` needs」. The statement needs no function object |
| `dev/PLAN.md:303-309` | the DD4 block, at the 2026-08-15 figures and the `sq`/`absorbs` reading |
| `dev/PLAN.md:306` | 「`src/L/GCH.lagda.md:66-76`」. The range runs past the end of a 70-line file |
| `dev/PLAN.md:344-351` | 「A7 states `SqShape` and `AbsorbsShape` as hypotheses」 |
| `dev/PLAN.md:353-357` | 「ONE remains: `sq : SqShape` at `src/L/GCH.lagda.md:80`」 |
| `dev/PLAN.md:410-431` | the cardinal-face fork, listed as WAITING ON THE OWNER. `[LJ-1.323]` closed it |
| `dev/ledger.toml:183-198` and `:204` | section 4 above |
| `dev/LESSONS.md:4024` | 「`src/L/GCH.lagda.md` as a STATEMENT with `sq` still an unsupplied Pi-parameter」 |
| `dev/LESSONS.md:4028-4029` | 「41.1 percent shared when it first printed, 39.1 percent today」 |

**Frozen task-index rows, which nobody rewrites (C-41).** `dev/PLAN.md:1174`
(LJ-1.280), `:1192` and `:1193` (LJ-1.299 and LJ-1.300), `:1198` (LJ-1.305), and
`:1239` (LJ-1.8). The last one is the LIVE goal row and it does need the
orchestrator: 「sq : SqShape, and LJ-1.286 measured that the delivered square
law CANNOT supply it」 describes a superseded statement.

**MEASURED, not INFERRED:** the list is the full result of
`grep -rn "SqShape|AbsorbsShape|absorbsL|GCHStatement|L/GCH" dev/` at HEAD. I
did not read `dev/JOURNAL.md` for prose that names the old statement without
those tokens, so the list is complete for the tokens and INCOMPLETE for prose.

## 6. DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**NAME THE AXIS (C-46).** DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. Section 3 reports the four numbers on that axis,
old and new, and says the share rose while SHARED fell.

**The finding that bears on DD4.** `L.InjChain.Comp`, `L.InjChain.Carve` and
`L.Absorption.Carve` are all written GENERIC: their own comments say the bound,
the subset witness and the separation field are PARAMETERS, so no line names an
L axiom or an L stage (`src/L/InjChain.lagda.md:463-467`,
`src/L/Absorption.lagda.md:379-382`). `StageBound` is one device for every row
(`src/L/InjChain.lagda.md:65-73`). **So the coded-injection layer is already
written the way DD4 asks**, and debt 1's adapter spends that genericity rather
than duplicating it.

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-323/lj-1.323-ruling.md`, READ WHOLE. Line read `:253-260`:
  the coded-delivery estimate and its named miniature. TOOK: the two debts and
  their surveys, as hypotheses (P-l). **REFUTED AT THAT LINE:** the comparable
  it names runs code to ambient, and the delivered ambient-to-code sites are
  elsewhere.
- `agents/tasks/LJ-1-310/lj-1.310-report.md`, READ `:1-190`. Line read `:93-119`,
  the 23-step chain table. TOOK: the step-by-step check that no step is dead
  under the new statement, section 2.1.
- `agents/tasks/LJ-1-321/lj-1.321-report.md`, READ `:1-55`. Line read `:29`:
  「THE TREE OWES THE CROSSING, NOT A MAP」. TOOK: independent support that the
  ambient-to-code crossing is the project's real term, from a different site.
- `agents/tasks/LJ-1-324/lj-1.324-report.md`, READ `:1-50`. Line read `:5-6`:
  the transplant is CIRCULAR. TOOK: the confirmation that `CanonInj` is not a
  supplier for either new debt.
- `archive/dev/STATUS-archived.md`, line read `:1`, the header. TOOK, SHAPE
  ONLY: the retired route kept a per-goal status screen and re-priced it under
  the route. **WHAT DOES NOT TRANSFER:** its prices ride the rud route, which
  `dev/PLAN.md:787` records as retired, so no figure in it is a comparable here.
- `archive/dev/TASKS-archived.md`, line read `:53` (T18, GCH scope gate, NO-GO).
  TOOK, SHAPE ONLY: the retired route also gated GCH scope before funding it.
  **WHAT DOES NOT TRANSFER:** its endpoint band, 28,258 naive top, is already
  overtaken by standing at 32,473, as `dev/PLAN.md:95-97` records.

## 8. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`. IT BEARS ON THE REVERSE
  BOUND, and in the direction that makes it cheaper.** READ `:72-90` and
  `:285-310`. Line read `:75-77`: a cardinal inequality is a truncated
  existence, HoTT Book 10.2.7. TOOK: the reverse bound is `∥ Σ ∥₁`, so no
  untruncation is owed at the statement, and the checklist's item 4 at `:297-300`,
  `leastOf` over a well-order with a propositional payload, is exactly the
  device `Pick` and both `Carve` sites already spend. **So the one-line answer:
  the literature says the reverse bound needs a CHOICE, not a MAP, and the
  project already owns the choice device as an L-set.**
- **`dev/literature/level-formula-slot-roles.md`. IT DOES NOT BEAR.** READ
  `:19-40`, the table and law 2.1. **WHY NOT:** it binds the level-hood
  formula's free slots, which is `[LJ-1.7]`'s object. Nothing in it names a
  cardinal, an injection or a power set.
- **`dev/literature/devlin-II5.md`.** READ `:145-175`. Line read `:159-161`:
  5.6's proof is 𝒫(κ) ⊆ L_{κ⁺} and then 1.1(vii), and「The result follows at
  once」. TOOK: Devlin proves only the FORWARD bound explicitly. The reverse
  bound is the step he leaves to the reader, which is why the tree has no lemma
  for it. **WHY NOT re-fetched:** the digest landed 2026-08-15 with mechanical
  label checks and I take only statement-level facts.
- Jech 13.20, HoTT Book 10.2.7: through the two digests, at the locators they
  carry. **WHY NOT re-fetched:** same reason.

## 9. WHAT I DID NOT SETTLE, AND WHAT NEEDS A TYPECHECK

I name these rather than guess (the brief's rule).

1. **That `InjCode G D C` accepts `(sv , dm , ij , ran)`.** I read the types and
   they match word for word. INFERRED, never MEASURED. Probe A settles it in
   about 10 lines.
2. **That `𝒫 κ` accepts the inclusion's subset witness.** INFERRED from the
   model's power-set specification, which I did not read. The debt 2 miniature
   settles it.
3. **The GCH wing's line split, 14,099 over 16 masters.** I did not re-run the
   wing split, so `dev/PLAN.md:79` is unchecked by me.
4. **The wing's check-cost ratio.** `check-ratio.py` runs Agda and this task may
   not. The restatement removed 15 lines from a 3-second master, so the effect
   is INFERRED negligible and it is not measured.

## 10. PROHIBITIONS, ANSWERED

- **No Agda ran.** Zero invocations. `ledger.py --brief` and `--reuse` run no
  Agda, and my replication script uses `git show` only.
- **Writes:** `agents/tasks/LJ-1-325/lj-1.325-report.md` only. Nothing in
  `dev/`, nothing in `src/`, no other task directory.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- The replication script sits in the session scratchpad, outside the repository.
