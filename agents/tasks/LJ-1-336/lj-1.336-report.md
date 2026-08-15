# LJ-1.336 report: wave 2 of the generic port, the dirty seven

tier: opus (in-harness-subagent-mode). Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**SEVEN OF SEVEN PORTED, AND THE CHANGED-LINE COUNT IS 0 OF 838.**

`agents/tasks/LJ-1-336/GenDirty.agda`, exit 0, cold 31 s, reload 2 s.
It ports all seven dirty modules: `DomainAgree`, `WitnessAgree`,
`KeyAgree`, `EnvOneAgree`, `DefinesAgree`, `SatGraphAgree` and
`LeafAgree`, with the 17 supporting blocks their closure needs and wave 1
did not port. **The copy is 791 non-blank lines from
`src/L/Condensation.lagda.md` and 47 from `src/L/Coding/`, and 0 of the
838 changed.** MEASURED three ways, section 3.

**ONE SCAFFOLD SERVED, and it grew by 9 lines.** My hand-written code is
54 non-blank lines against wave 1's 45: 48 of scaffold and 6 of module
wrapper for the gap. **No second scaffold was needed.** MEASURED FALSE,
the abort branch「the scaffold does not stretch」.

**THE ONE-DEBT CLAIM IS MEASURED FALSE AT THE SECOND SITE, and this is
the report's main finding.** `[LJ-1.302]` priced the seven's ambient ties
at about 100 lines because「the ties are ONE debt, not sixteen」
(`agents/tasks/LJ-1-302/lj-1.302-report.md:191`). **The second module's
tie supply costs 42 non-blank lines, reuses ZERO lines of the first
module's shared closure block, and needs a DIFFERENT supplier with three
hypotheses the first module never took.** MEASURED, section 4. **There
are at least TWO debts, not one: a DOWNWARD one and an UPWARD one.**

**The chapter itself already separates them, and I found that after the
measurement, not before.** `module KValue` at
`src/L/Condensation.lagda.md:7264-7318` exists to discharge the upward
ties at the L class. **Its telescope is `(lam) (ordλ) (succλ) (∅∈λ)`, the
same four hypotheses my ambient probe needed**, and it costs 50 non-blank
lines. MEASURED, by reading `:7264-7266` and `:7261`.

**THE NEGATIVE CONTROL IS TWO FILES AND BOTH ARE RED AT THE RIGHT
POINT.** Section 5.

**ONE STRUCTURAL LIMIT, MEASURED AND NOT ANTICIPATED BY THE BRIEF.** The
port's re-stated `satGraphAt` does NOT convert with the committed one,
because both are `opaque` and two seals never convert. `DefBody` inherits
the failure. **No external consumer is harmed, MEASURED**, but a
replacement landing must know it. Section 6.

## 1. THE CLOSURE, RE-DERIVED (C-44)

`agents/tasks/LJ-1-336/closure336.py` parses `src/L/Condensation.lagda.md`
into top-level blocks from the text, then computes the name-dependency
closure of the seven dirty modules.

**The parser agrees with wave 1 at every block.** It finds 229 blocks.
Wave 1's `agents/tasks/LJ-1-306/closure.json` records 216 spans. **All
216 start lines agree, and none disagrees.** MEASURED, by the cross-check
the script prints. The 13 extra blocks my parser sees are top-level
`open` lines, which wave 1 did not name.

**The seven's closure is 137 blocks.** Wave 1 already ported 113 of them.
7 are the seven. **17 blocks are new work.** MEASURED.

| block | span | non-blank |
|---|---|---:|
| `keyArBS` | `:1474-1479` | 5 |
| `Δ₀-arTagPairBS` | `:1504-1510` | 6 |
| `Δ₀-arTagBS` | `:1521-1525` | 4 |
| `Δ₀-binShapeBS` | `:1533-1537` | 4 |
| `Δ₀-unShapeBS` | `:1543-1547` | 4 |
| `Δ₀-bothSameB` | `:1553-1557` | 4 |
| `Δ₀-oneSameB` | `:1561-1563` | 2 |
| `Δ₀-oneSuccB` | `:1570-1574` | 4 |
| `Δ₀-succSndB` | `:1581-1585` | 4 |
| `Δ₀-closedBS` | `:1599-1610` | 11 |
| `hasWitnessBS` | `:1712-1723` | 11 |
| `isCodeBS` | `:1733-1739` | 6 |
| `Δ₀-domB` | `:1754-1758` | 4 |
| `envOneBndS` | `:1763-1767` | 4 |
| `DefinesBS` | `:1773-1779` | 6 |
| `SatGraphB` | `:2230-2332` | 98 |
| `DefBodyB` | `:2335-2351` | 16 |

The seven themselves:

| module | span | non-blank | port lines |
|---|---|---:|---|
| `DomainAgree` | `:6510-6540` | 27 | `:398-428` |
| `WitnessAgree` | `:6576-6657` | 79 | |
| `KeyAgree` | `:6699-6747` | 46 | |
| `EnvOneAgree` | `:6748-6777` | 23 | |
| `DefinesAgree` | `:6778-6834` | 49 | |
| `SatGraphAgree` | `:6844-7097` | 246 | `:652-905` |
| `LeafAgree` | `:7107-7243` | 128 | `:907-1043` |

`agents/tasks/LJ-1-336/manifest336.json` records every block's source
range and its range in the port.

**One correction to `[LJ-1.302]`'s span table (C-44).** That report gives
`DomainAgree` as `:6510-6547` with 34 lines, `WitnessAgree` as
`:6576-6669` with 90, `DefinesAgree` as `:6778-6843` with 58, and
`SatGraphAgree` as `:6844-7106` with 255. **Those spans carry the
separator comment that follows each module.** Cut at the module's own last
code line, the figures are 27, 79, 49 and 246. **The seven's own text is
598 non-blank lines, not 634.** MEASURED, by my parser, which agrees with
wave 1's span map at every one of its 216 entries.

**`KValue` is NOT in the closure and is NOT ported.** No consumer among
the seven reaches it. MEASURED, by the closure computation. Section 4 says
why the block matters anyway.

## 2. THE DIRT, NAMED AT `file:line`

「Dirty」means the module names committed deliveries in its types. The
chapter's import list at `src/L/Condensation.lagda.md:55-57` names them
exactly: `L.Coding.CodeSet` gives `hasWitnessAt` and `keyArityAtL`;
`L.Coding.Graph` gives `satGraphAt` and `twelveAt`; `L.Coding.Powerset`
gives `isCodeAt`, `DefBody`, `DefinesAt` and `envOneAt`.

**All eight are pure syntax over `GenModel` primitives, so all eight
restate by COPYING, like wave 1's `Shape` cure.** MEASURED, by reading
each definition:

| name | home | body reaches |
|---|---|---|
| `keyArityAtL` | `src/L/Coding/CodeSet.lagda.md:135-136` | `tagAtL` |
| `hasWitnessAt` | `src/L/Coding/CodeSet.lagda.md:240-242` | `closedAt`, `shapedAt` |
| `envOneAt` | `src/L/Coding/Powerset.lagda.md:128-129` | `extAt`, `tagAtL` |
| `DefinesAt` | `src/L/Coding/Powerset.lagda.md:217-220` | `extAt`, `envOneAt` |
| `isCodeAt` | `src/L/Coding/Powerset.lagda.md:297-298` | `keyArityAtL`, `hasWitnessAt` |
| `DefBody` | `src/L/Coding/Powerset.lagda.md:437-440` | `isCodeAt`, `satGraphAt`, `DefinesAt` |
| `twelveAt` | `src/L/Coding/Graph.lagda.md:94-101` | the twelve `*ClauseAt` |
| `satGraphAt` | `src/L/Coding/Graph.lagda.md:203-205` | `closedAt`, `domAt`, `appAt`, `twelveAt` |

`shapedAt` is the ninth, and wave 1 already re-stated it at
`agents/tasks/LJ-1-306/GenAgree.agda:108-109`. **`GenModel` delivers every
other name in the right column.** MEASURED, by
`agents/tasks/LJ-1-336/dirt336.py` against
`agents/tasks/LJ-1-210/GenModel.agda`.

**The gap costs 47 copied lines and 6 hand-written wrapper lines.** The
three wrappers are `module CodeSetGap`, `module GraphGap` and
`module PowersetGap`, each with its `open ... public`. They keep each
source module's own private helpers private, exactly as `src/L/Coding/`
does. `[LJ-1.298]` projected this group at「`keyArityAtL` 1,
`hasWitnessAt` 3, `twelveAt` 11, `satGraphAt` about 16, the
`DefBody`/`envOneAt`/`DefinesAt`/`isCodeAt` group about 12」, which is
about 43 of HAND-WRITTEN code. **The true figure is 47 lines of COPIED
code plus 6 of wrapper, so the projection was close on volume and wrong on
kind.** MEASURED.

## 3. THE PORT, AND THE ZERO

`agents/tasks/LJ-1-336/GenDirty.agda`, exit 0.

| quantity | value |
|---|---:|
| modules ported | **7 of 7 dirty** |
| supporting blocks new to wave 2 | 17 |
| copied non-blank lines, chapter | 791 |
| copied non-blank lines, `src/L/Coding/` | 47 |
| **changed lines** | **0 of 838** |
| hand-written code | **54** (48 scaffold, 6 gap wrapper) |
| port total non-blank | 956 (861 code, 95 comment) |
| cold elaboration | **31 s** |
| reload | 2 s |

**Method 1, the per-block exact-run search.** All 24 copied blocks appear
in the port as contiguous ordered runs. 0 missing.

**Method 2, the whole-sequence diff `[LJ-1.308]` used.** I concatenated the
24 spans in manifest order and aligned the result against the whole port
with `difflib.SequenceMatcher`, `autojunk=False`. **0 delete lines and 0
replace hunks.** The expected text is an exact ordered sub-sequence of the
port. A run search can report zero because it cannot see a change; an
alignment cannot.

**Method 3, the gap restatement against `src/L/Coding/`.** Every one of the
47 source lines appears in the port's head, line for line, indent
stripped. **47 of 47.** MEASURED, by
`agents/tasks/LJ-1-336/verify336.py`.

**THE SCAFFOLD, AND WHY IT GREW BY 9.** Wave 1's scaffold is 45 lines and
applies `GenModel`. Mine is 48 and applies WAVE 1, not `GenModel`:

```agda
module W1 = LJ-1-306.GenAgree {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open W1
open W1.GM
open W1.GM.ToL using ( Δ₀-liftFo )
open W1.KFactsNS
open W1.KFactsNS.KFacts
```

That shape costs three lines more than wave 1's, and it buys the 113
already-ported blocks at zero copy cost and at zero re-elaboration cost:
the cold 31 s prices MY 838 lines only, with wave 1's interface cached.
**A second `GenModel` application does NOT work: `open W1` already brings
`GM` into scope and Agda refuses the ambiguity.** MEASURED, at the first
run, exit 42, `AmbiguousModule GM.AbsL`.

**The `opaque` seal survived the port without a special case.** The copied
`opaque unfolding satGraphAt` at chapter `:7069-7070` names the port's own
sealed restatement and Agda accepts it. MEASURED, by the green run.

## 4. THE SECOND MODULE'S TIE SUPPLY, AND THE ONE-DEBT CLAIM

**THE BRIEF NAMED THIS AS THE PREMISE MOST LIKELY TO BE WRONG. IT IS
WRONG.**

`[LJ-1.302]` supplied `DomainAgree`'s two ties at the ambient carrier in
51 non-blank lines, of which about 20 are a shared closure block, and
concluded:「The ties are ONE debt, not sixteen」and「about 20 of shared
closure block plus about 10 per module」
(`agents/tasks/LJ-1-302/lj-1.302-report.md:191` and `:205-209`).

**I measured the second site. `agents/tasks/LJ-1-336/ProbeTies336.agda`,
exit 0, 9 s, supplies `EnvOneAgree`'s three ties at the ambient carrier
in 42 non-blank lines.**

**The three findings, all MEASURED.**

1. **The first module's shared block serves NONE of the second module's
   ties.** `agents/tasks/LJ-1-336/ProbeTiesNoShare336.agda` is the same
   supply with `LJ-1-302.ProbeLJ1302B` NOT IMPORTED AT ALL. **Exit 0,
   9 s.** So the reuse is 0 lines, not「about 20 written once」.
2. **The second module needs a different supplier.** `numK` and `pairK`
   are UPWARD facts: the bound CONTAINS the numerals, and it contains the
   tagged pair built over its own members. The first module's block
   (`x∈pair`, `y∈pair`, `pair∈pr`, `Ltr`, `Lset-mono`, at
   `agents/tasks/LJ-1-302/ProbeLJ1302B.agda:92-108`) proves only DOWNWARD
   facts: a member of a member lands in the bound. **No downward lemma
   proves an upward fact.** My supply uses `L.Coding.Bound`'s `Bound`
   instead, at `src/L/Coding/Bound.lagda.md:130-145`.
3. **The new supplier takes three hypotheses the first module never
   took**: `ordλ : IsOrd lam`, `succλ` and `∅∈λ`. `[LJ-1.302]`'s `Supply`
   takes only `beta∈λ` and `gam∈λ`
   (`agents/tasks/LJ-1-302/ProbeLJ1302B.agda:81-82`).

**THE CHAPTER ALREADY KNEW.** `module KValue` at
`src/L/Condensation.lagda.md:7264-7318` is the block that builds the one
`KFacts` value, and `KFacts` is where `LeafAgree` gets `numK0` and `numK1`
(`:7201`, `:7209`). **`KValue`'s telescope is
`(lam : V ℓ) (ordλ : IsOrd lam) (succλ) (∅∈λ)` at `:7264-7266`, the same
four my ambient probe needed, and it imports `module Bound` at `:7261`,
the same supplier.** It costs 50 non-blank lines at the L class alone.
MEASURED, by reading. **I reached `Bound` from the tie types, before I
read `KValue`.**

**HOW WIDE IS THE UPWARD DEBT.** The upward numeral tie
`⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩` appears in the telescope of
`KeyAgree` (`:6701`), `EnvOneAgree` (`:6750`) and `DefinesAgree`
(`:6780`), and in wave 1's own clean `TagAgree` (`:6672`). `LeafAgree`
takes it through the `KFacts` record instead. MEASURED, by grep over
`:6510-7243`. **So the upward debt reaches at least four of the thirty
modules and is not confined to the seven.**

**THE RE-PRICE (DD8).** Two sites are now measured: 51 lines and 42 lines,
with 0 lines shared between them. **The seven's ambient tie supply is
INFERRED at 250 to 350 lines, not about 100.** Basis: two measured sites,
a measured zero for the sharing between them, and the seven's tie columns
in `[LJ-1.302]`'s table at `:183-189`. **This is an INFERENCE from two
sites and P-l binds me as it binds the source: five sites stay
unmeasured.** What is MEASURED is that the「ONE debt」premise under the
about-100 figure is false.

## 5. THE NEGATIVE CONTROL

**Two controls, and both are red at the point of the break.** Each is the
green port with ONE line changed, and `diff` shows one line each.

**CONTROL A, LOCALITY.** `agents/tasks/LJ-1-336/ControlA.agda` flips one
projection inside the copied `DomainAgree.out`, at port line 410:
`( λ hx → h x .fst` becomes `( λ hx → h x .snd`. **Exit 42 in 3 s, and
Agda refuses at `ControlA.agda:411.12-66`, the continuation of that same
expression, with `UnequalTerms`.** MEASURED.

**CONTROL B, NON-VACUITY.** `agents/tasks/LJ-1-336/ControlB.agda` changes
the RE-STATED `isCodeAt` at port line 147, from `keyArityAtL c 1` to
`keyArityAtL c 0`. This is the check that matters: the gap restatement is
hand-placed, so a port that only parsed would swallow it. **Exit 42 in
21 s, and Agda refuses at `ControlB.agda:1019.30-32` with
`0 != 1 of type ℕ`, INSIDE the copied `LeafAgree` proof** (`LeafAgree`
occupies port `:907-1043`). **So the seven's copied proofs genuinely
constrain the gap restatement.** MEASURED.

## 6. SERVING, AND THE ONE STRUCTURAL LIMIT

**C-40 is the lesson wave 1 was corrected on, so I started from the
consumers.** MEASURED, by grep over `src`:

| consumer | reach | site |
|---|---|---|
| `L.BoundedSubset` | `DefBodyB`, `Δ₀-DefBodyB` | `:30`, `:82`, `:90`, `:115`, `:124` |
| `L.Condensation.TwelveAgree` | `module SatGraphB`, `SatGraphB.twelveB` | `:31`, `:529`, `:534` |

**The seven `Agree` modules have ZERO external code reaches.** The two
`SatGraphAgree` hits in `src/L/Condensation/TwelveAgree.lagda.md:514` and
`:524` are COMMENT lines. MEASURED. **But `DefBodyB` and `SatGraphB` are
in WAVE 2's copy set, not wave 1's, so wave 2 moves two externally
consumed blocks into the generic port.**

`agents/tasks/LJ-1-336/ProbeServe336.agda`, **exit 0, 10 s, 18 checks, all
green**: 6 refls for the re-stated gap names against the committed
`L.Coding.*` deliveries; 8 refls for the externally consumed and the new
bounded blocks, original against generic, including `DefBodyB`,
`SatGraphB.twelveB` and `SatGraphB.satGraphB`, which are the names the two
consumers actually write; then ONE telescope, copied verbatim from
`src/L/Condensation.lagda.md:6748-6752`, applied to BOTH module
declarations, and the generic module's `out` and `back` given at the
ORIGINAL module's type.

**THE LIMIT, MEASURED.** `agents/tasks/LJ-1-336/ProbeSeal336.agda` states
the two refls a naive replacement would need and **fails, exit 42, 3 s**:

```text
Fam.satGraphAt B x y != satGraphAt B x y
```

**Two `opaque` declarations never convert, whatever their bodies say.**
`src/L/Coding/Graph.lagda.md:194-202` records why the seal exists: open,
one coercion cost 2,459 ms. **The seal cannot be avoided by taking
`satGraphAt` as a module parameter, because
`src/L/Condensation.lagda.md:7069-7070` writes
`opaque unfolding satGraphAt`, and nothing can unfold a parameter.**
INFERRED from the two measured facts, and it is the reason wave 1's
pattern needed a nested `opaque` block here.

**Does the limit block a replacement landing? NO, MEASURED.** No file
outside `src/L/Coding/Graph.lagda.md` and `src/L/Condensation.lagda.md`
names `satGraphAt` in a type that also reaches the seven: the other
consumers are `L.Choice.Adequate:477`, `L.Choice.Internal:517` and
`L.Coding.Powerset:358`, and each reaches the COMMITTED `satGraphAt`
directly, never through the chapter. `DefBody` has zero reaches outside
`L.Coding.Powerset` and the chapter. MEASURED, by grep.

## 7. DD4, WITH THE AXIS NAMED (C-46)

**MY AXIS IS THE PORT'S L-AGAINST-AMBIENT AXIS, AND IT IS NOT DD4'S OWN
AXIS.** C-46 asks for the qualifier and `[LJ-1.308]` marked wave 1 down
for leaving it out, so I say it first. DD4's own axis is AC-against-GCH,
fixed in code at `scripts/measure/ledger.py:50`.

**On DD4's own axis this port is NEUTRAL BY STRUCTURE, and I re-derived
it today.** I re-ran `agents/tasks/LJ-1-308/closure_check.py`:

| closure | masters | `L.Condensation` inside |
|---|---:|---|
| AC | 73 | **no** |
| GCH | **48** | **no** |
| shared | **43** | n/a |

`scripts/measure/ledger.py --reuse` prints the same 73, 48 and 43.
`L.BoundedSubset` and the three `L.Condensation.*` consumers sit outside
both closures too. MEASURED.

**A C-44 correction to `[LJ-1.308]`.** That report gives GCH 51 and shared
44, measured on 2026-08-15. **Today it is GCH 48 and shared 43**, because
`src/L/GCH.lagda.md` was RESTATED. The conclusion does not move; the
figures do. MEASURED, by running both instruments today.

**On the L-against-ambient axis the port is DD4's own work, and wave 2
extends the paid instance to the whole chapter.** Wave 1 made 4,738 lines
serve two carriers for 45. Wave 2 adds 838 more for 54. **Together the
`Agree` family is 5,576 copied lines serving two carriers for 99 lines of
hand-written code.** MEASURED, by the two reports' own counts on the same
caliber.

**What the J tower pays to re-instantiate the seven: 2 lines**, the module
application, exactly as `agents/tasks/LJ-1-336/ProbeTies336.agda:52-56`
does it. **What it does NOT get for free is the tie supply, and section 4
re-prices that upward.**

**P-h holds here.** The definability walk stays module-parameterized. The
class parameter IS the module parameter, and wave 2 adds no
function-parameterized walk. MEASURED, by the port's shape.

**C-55 is respected.** Nothing in this port folds a telescope into a
record. `KFacts` arrives from wave 1 unchanged, as the chapter wrote it,
and the seven keep their parameter-form telescopes. The brief ordered
this and the port obeys it.

**And the port buys no seconds, as the brief predicted.** 31 s cold for
838 lines is 0.037 s per line, against wave 1's 0.031. **The port's value
is lines and genericity, not seconds.** MEASURED.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| a copied non-blank line changed | **MEASURED FALSE.** 0 delete, 0 replace, whole-sequence diff, `verify336.py` |
| a copied block was reordered | **MEASURED FALSE.** The expected text is an ordered sub-sequence |
| a re-stated gap line differs from its `src/L/Coding/` source | **MEASURED FALSE.** 47 of 47 identical |
| the seven need a second scaffold | **MEASURED FALSE.** One scaffold, 48 lines, plus 6 wrapper lines |
| a second `GenModel` application works beside wave 1's | **MEASURED FALSE.** `AmbiguousModule GM.AbsL`, exit 42 |
| a module of the seven will not port | **MEASURED FALSE.** All seven, exit 0 |
| the gap names need hand-written mathematics | **MEASURED FALSE.** All eight are syntax over `GenModel` primitives |
| the ties are ONE debt | **MEASURED FALSE** at the second site. 0 lines shared, a different supplier, three new hypotheses |
| the second module's tie supply costs about 10 lines | **MEASURED FALSE.** 42 non-blank lines |
| the first module's shared block is needed by the second | **MEASURED FALSE.** `ProbeTiesNoShare336.agda`, exit 0, no import |
| the remaining five modules' supplies cost the same as these two | **INFERRED.** Two sites measured, five not. P-l binds |
| the port typechecks vacuously | **MEASURED FALSE.** Control B, `0 != 1 of type ℕ` inside `LeafAgree` |
| a break in a copied line goes unnoticed | **MEASURED FALSE.** Control A, red at the same expression |
| the port's `satGraphAt` converts with the committed one | **MEASURED FALSE.** `ProbeSeal336.agda`, exit 42 |
| the seal blocks a replacement landing | **MEASURED FALSE.** No external consumer reaches the seven's types |
| `DefBodyB` or `SatGraphB.twelveB` differ, original against generic | **MEASURED FALSE.** `ProbeServe336.agda`, exit 0 |
| the seven have an external code consumer | **MEASURED FALSE.** Two hits, both comments, `TwelveAgree:514` and `:524` |
| `L.Condensation` is in a trophy closure | **MEASURED FALSE.** AC 73, GCH 48, neither contains it |
| `[LJ-1.308]`'s GCH figure of 51 still holds | **MEASURED FALSE.** It is 48 today, after `GCH.lagda.md` was restated |
| `[LJ-1.302]`'s seven-module span total of 634 is on the module caliber | **MEASURED FALSE.** 598; the spans carried separator comments |
| the port wins seconds | **MEASURED FALSE.** 0.037 s per line, above wave 1's 0.031 |
| a run hit a wall | **MEASURED FALSE.** The longest was 34 s |
| a probe under `src/` was written | **MEASURED FALSE.** `check-probes.py` clean; all files sit in `agents/tasks/LJ-1-336/` |
| a sibling task directory was edited | **MEASURED FALSE.** `git status` shows my directory only |
| `KValue` was ported | **MEASURED FALSE.** No consumer among the seven reaches it |
| the whole chapter typechecks with wave 1 and wave 2 landed | **INFERRED.** Neither wave has landed and I ran no whole-chapter check |

## 9. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-306/lj-1.306-report.md`, read WHOLE, FIRST, as SCOPE
  orders. **Line read:** `:22-27`,「Zero copied lines changed ... The
  changed-line count is 0 of 4,738 copied non-blank lines」. TOOK the
  method, the manifest discipline and the zero as the bar to match.
- `agents/tasks/LJ-1-306/GenAgree.agda`, read `:1-120` and grepped.
  **Line read:** `:62-65`, the `module GM =` application and the two
  opens. TOOK the scaffold; CHANGED it to apply wave 1 instead of
  `GenModel`, because `open W1` makes a second `GM` ambiguous, MEASURED.
- `agents/tasks/LJ-1-306/manifest.json` and `closure.json`, read WHOLE.
  **Line read:** the `[6670, 6698, "TagAgree"]` row. TOOK the exact set
  wave 1 ported, which fixes my 17.
- `agents/tasks/LJ-1-308/lj-1.308-report.md`, read WHOLE. **Line read:**
  `:37`,「Ten of twelve row fields went unchecked. This is C-40 exactly」.
  TOOK the instruction to start a serving probe from the consumers, and
  section 6 does.
- `agents/tasks/LJ-1-308/verify_zero.py` and `closure_check.py`, read
  WHOLE and RE-RAN the second. **Line read:** the
  `SequenceMatcher(None, expected, port, autojunk=False)` call. TOOK the
  stronger zero method and the closure instrument; my `verify336.py` is
  that method at wave 2's spans.
- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE. **Line read:**
  `:191`,「The ties are ONE debt, not sixteen」. TOOK it as the claim to
  test; REFUTED it at the second site, section 4.
- `agents/tasks/LJ-1-302/ProbeLJ1302B.agda`, read WHOLE and IMPORTED
  unchanged. **Line read:** `:92-108`, the shared closure block. TOOK the
  ambient supply shape; MEASURED that the block serves none of the second
  module's ties.
- `agents/tasks/LJ-1-307/lj-1.307-report.md`, read `:1-45`. **Line read:**
  the family-as-one-shape finding, about fifteen things and thirty
  spellings. TOOK the expectation that the seven are one shape;
  QUALIFIED it: they are one shape in TEXT and two debts in TIES.
- `agents/tasks/LJ-1-210/GenModel.agda`, read `:60-120`, `:340-360`,
  `:660-700` and `:1120-1260`. **Line read:** `:343-345`,
  `tagAtL-adequate`'s statement. TOOK the tag reading my `pairK` spends.
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read `:290-330`. **Line
  read:** `:321-327`, `module Ambient` and `ambient`. TOOK the ambient
  reading both tie probes carry.
- `archive/dev/TASKS-archived.md`, read `:58-75`. **Line read:** the
  `L3.32-T33` row,「Condensation crossing | DELIVERED」. TOOK SHAPE only: a
  crossing was delivered once under the retired route, whose
  `Condensation` was 885 lines with no `Agree` family at all. **No figure
  and no content transfers**, and the shape it does carry is that the
  crossing was cheaper when the two codings were one.

## 10. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:312-335`.

**THE ONE LINE THE BRIEF ASKS FOR: the generic port MERELY COMPRESSES
OURS, and section 4 shows it also exposes a cost Devlin never pays.**

The digest's engine list at `:321-327` gives items 2 and 3: Σ₀
absoluteness 1.9.15,「the bridge between satisfaction inside a transitive
carrier and ambient truth」, and the ℒ-analogue translation 1.9.11,「each
LST formula has an ℒ-formula with the same meaning over transitive sets」.
**Devlin pays the bridge ONCE, at the language level, in Chapter I.**
Bedrock proves it per NOTION, and the port makes the thirty per-notion
proofs serve two carriers instead of one. **That is compression of our
shape, not movement toward his.** A move toward Devlin's shape would
replace the family with one language-level translation, and this port does
not touch that question.

**And wave 2 adds one line of evidence about the price of our shape.** The
seven's telescopes carry the ties because the two codings differ about
what the bound `K` contains. **Devlin's single coding has no bound to tie
anything to.** The upward debt of section 4 is the arithmetic of the
choice, not of the port.

**WHY NOT the rest of the digest.** Items 1, 5 and 6 are the collapse, KP
recursion and reflection, none of which the seven reach. Items 7 to 12
partition the level recursion by tower, which is Devlin's axis and not
DD4's; C-46 forbids using it as the DD4 axis and `[LJ-1.272]` measured the
defect in 12 of 62 figures. Section 7's errata territory does not reach
II.5.

## 11. WHAT I DID NOT SETTLE

- **The other five modules' tie supplies.** Two sites are measured. P-l
  binds: `WitnessAgree`, `KeyAgree`, `DefinesAgree`, `SatGraphAgree` and
  `LeafAgree` stay unmeasured, and `LeafAgree`'s fifteen ties are the
  biggest unmeasured end.
- **`KValue`'s own port.** It is class-specific, it is not in the seven's
  closure, and a generic `KValue` would meet the class commitment
  `[LJ-1.213]` measured at `GenPowerset`.
- **`StepAgree` and `ApproxAgree`.** Still absent from `src/` and still
  the route's widest unpriced term, as `[LJ-1.302]` left them. Wave 2
  changes nothing there.
- **Whether `q'` is true.** Neither confirmed nor refuted.
- **The landed chapter's own seconds.** My 31 s prices my file with wave
  1's interface cached and the chapter's remainder absent.
- **The replacement's edit cost at the class.** Section 6 measures that
  the names serve; it does not price the landing.

## 12. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. **No invocation reached 30 minutes; the
longest was 34 s.** I ran
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` before every
invocation and it returned **0 every time**, so I held one slot and no
sibling was live. Machine load average 20.53 to 16.75, 3 users, which is
high for the box and prices these seconds pessimistically.

| file | exit | seconds | note |
|---|---:|---:|---|
| `GenDirty.agda` | 42 | 2 | scope: `AmbiguousModule GM.AbsL` |
| `GenDirty.agda` | **0** | **31** | cold elaboration, 7 of 7 ported |
| `GenDirty.agda` | 0 | 2 | reload |
| `ProbeTies336.agda` | 42 | 5 | scope: `GD.numeralL` is a parameter, not an export |
| `ProbeTies336.agda` | 42 | 34 | my own bad edit, `fst (# 0)` |
| `ProbeTies336.agda` | **0** | **9** | the second module's three ties supplied |
| `ProbeTiesNoShare336.agda` | **0** | **9** | the same, with `[LJ-1.302]` NOT imported |
| `ControlA.agda` | **42** | 3 | **EXPECTED RED**, locality |
| `ControlB.agda` | **42** | 21 | **EXPECTED RED**, non-vacuity |
| `ProbeServe336.agda` | **0** | **10** | 18 serving checks |
| `ProbeSeal336.agda` | **42** | 3 | **EXPECTED RED**, the seal |

Python runs cost under 2 s each and take no Agda slot: `closure336.py`,
`dirt336.py`, `build336.py`, `verify336.py`, `control336.py`,
`agents/tasks/LJ-1-308/closure_check.py` and
`scripts/measure/ledger.py --reuse`.

## 13. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-336/`: this report, `head336.agda`,
`GenDirty.agda`, `ProbeTies336.agda`, `ProbeTiesNoShare336.agda`,
`ProbeServe336.agda`, `ProbeSeal336.agda`, `ControlA.agda`,
`ControlB.agda`, and the scripts `closure336.py`, `dirt336.py`,
`build336.py`, `verify336.py`, `control336.py` with their JSON outputs.
`src/` holds no probe of mine, and `check-probes.py` reports clean.
`src/L/Condensation.lagda.md`, `src/L/GCH.lagda.md`,
`src/L/BoundedSubset.lagda.md` and the `src/L/Coding/` masters were read
and copied from, never opened for writing. `agents/tasks/LJ-1-302/`,
`agents/tasks/LJ-1-306/` and `agents/tasks/LJ-1-308/` were read and
re-run, never edited. I did not open `src/Everything.lagda.md`,
`dev/PLAN.md`, `dev/LESSONS.md`, `dev/ledger.toml`, `AGENTS.md` or
`.claude/` for writing. No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`scripts/gate/lint-agda.py --check` both pass. No em dash in any language.
`_build/` holds only Agda's own interface files for my modules.
