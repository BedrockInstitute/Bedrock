# LJ-1.227 report: the gate list for A-prime's reading residue

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Recon only. **No
Agda ran.** No master, brief or report was edited. No commit, no push.

Every negative is marked **MEASURED** (read at the cited line) or **INFERRED**
(my judgement). ASD-STE100 applies to this report.

## 0. LEAD: ZERO DISSOLVE, FIVE NAMED TERMS

**None of the five blocks dissolves.** I asked the dissolution question first
for every block. Each block is needed. The answer is the same for all five.

**All five blocks have a named widest term.** Each section below names it at
`file:line`, names the probe that measures it, and gives its INFERRED Agda
minutes.

**The residue is still 555, not smaller.** The brief's hypothesis that
`[LJ-1.217]`'s composition is stale is MEASURED FALSE. Section 6.

**The five overlaps re-price the sum.** Four of the five overlaps are RESOLVED
by `[LJ-1.176]` and `[LJ-1.217]`. One stands, and it double-counts A2's
predicate inside A4. The corrected sum is **1,470 to 1,521**, not 1,548.
Section 5.

## 1. A1: `⟨ isL x ⟩` replaces "assume V = L", 40 lines

**What it is.** The per-site hypothesis `⟨ isL α ⟩` on each ordinal the chain
touches, in place of one global `V = L` assumption. Route A-prime exists to
avoid that assumption.

**Is it needed.** YES. MEASURED. The chain masters `StageCardinal` and
`BoundedSubset` open `hPropStructure 𝒮ᵥ`, the ambient carrier
(`src/L/BoundedSubset.lagda.md:56`). They carry no `⟨ isL α ⟩`. The trophy is
`L ⊨ GCH`, so the chain's ordinals must be L-ordinals. The restatement is
real work. It is the cheapest block, but it is not zero.

**Widest unmeasured term.** Whether `⟨ isL α ⟩` alone supplies every ordinal
fact the restated chain needs at each site, or a site silently needs more.
The candidates are `⟨ isL (sucV α) ⟩`, `isL-trans` and `Lset-cumul`. The
three delivered sites that take the shape today are
`src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795` and
`src/L/Choice/Transversal.lagda.md:77`. Those sites are consumers of the order
stack, not of the square-law chain. **Nobody has restated one chain theorem
with `⟨ isL α ⟩` per site and checked which L-machinery the site demands.**
That gap is the term.

**The probe.** Restate ONE theorem of the ambient chain, `Chain.theorem` or
`LeastCardInj`, with `⟨ isL α ⟩` per site and no global assumption. Check
`--safe`, exit 0. Record which extra L-lemmas the site demands. The ambient
chain is 393 lines at 133 s cold (`agents/tasks/LJ-1-156/lj-1.156-report.md:189`, `:252`).
A single theorem restatement is a fraction of that.

**INFERRED cost: under 2 Agda minutes.**

**D-10.** The target is not false. The hypothesis shape is delivered and
consumed. No cardinality obstruction exists.

## 2. A2: injection as an L element, read back, 170 lines

**What it is.** The object-language predicate "g codes an injection from a to
b" plus the readback `toFun` and `toFun-inj`. Every block downstream names
this predicate.

**Is it needed.** YES. MEASURED. `injAt` and `IsInjGraph` exist nowhere in
`src/L/`. My grep over `src/L/**/*.lagda.md` returns zero hits. The core
lives only in the untracked probe `src/ProbeLJ1134A.agda:61-93`. A3, A4 and
A5 all state "g is an injective graph from a to b". Until that predicate is a
master, nothing downstream is statable (`agents/tasks/LJ-1-136/lj-1.136-report.md:351-354`).

**Widest unmeasured term.** The range set and the `ranAt` formula with
adequacy. `[LJ-1.134]` named both unpriced:
`agents/tasks/LJ-1-134/lj-1.134-report.md:177-180`. Its probe took "every
value lies in C" as a hypothesis. A master must produce C by replacement over
the graph, and write `ranAt` to mirror `domAt`. The core is measured at 78
lines. The two range pieces are not.

**The probe.** Build the range set with `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:277`) and write `ranAt` with both adequacy
readings, mirroring `domAt` at `src/L/Coding/Model.lagda.md:278`. The probe is
the same shape as `[LJ-1.134]`'s, plus the replacement step.

**INFERRED cost: 4 to 5 Agda minutes.** `[LJ-1.136]` measured `hasReplacementL`
at one site at 254 s (`agents/tasks/LJ-1-136/lj-1.136-report.md:1059`).
The replacement is the dominant term. The `ranAt` description adds little.

**D-10.** The target is not false. `[LJ-1.134]` measured the readback GO,
`--safe`, exit 0.

## 3. A3: the `<_L`-least injection, 45 lines

**What it is.** The canonical selection `leastOf (orderAt β)` over A2's
predicate. Canonicity is what makes the truncation discharge.

**Is it needed.** YES. MEASURED. `[LJ-1.136]` Probe B measured the selection
and canonicity GO (`agents/tasks/LJ-1-136/lj-1.136-report.md:897-913`). The
selection is the only term that discharges the chain's `inj` parameter. It is
not dissolvable into A2, because A2 does not select. It is not dissolvable
into A4, because A4 consumes it.

**Widest unmeasured term.** Obtaining `β` from the delivered `stageBound`, and
the master-level crossing. `[LJ-1.134]` states it:
`agents/tasks/LJ-1-134/lj-1.134-report.md:238`. Its Part B fixed `β` as a
parameter. A master must produce `β` from `stageBound`
(`src/L/Choice/Stage.lagda.md:328`), which is delivered. The selection itself
is measured at 22 lines. The unmeasured piece is whether `stageBound` supplies
`β` for free at every site, or each site owes a bound proof.

**The probe.** Instantiate `stageBound` at one real ordinal, feed the result
to `leastOf (orderAt β)` over A2's predicate, and check the canonical
selection elaborates as a master with no `β` hypothesis. The selection already
measured GO at 1.27 s (`agents/tasks/LJ-1-136/lj-1.136-report.md:12`).

**INFERRED cost: under 2 Agda minutes.**

**D-10.** The target is not false. The selection is measured GO.

## 4. A4: internal least cardinal and internal `IsCardinal`, 190 lines

**What it is.** The internal form of `LeastCard`: the least `δ` such that an
L-element codes an injection `⟪ κ ⟫ ↪ ⟪ δ ⟫`, plus internal `IsCardinal`.

**Is it needed.** YES. MEASURED. The ambient `IsCardinal` is delivered at
`src/L/BoundedSubset.lagda.md:1046-1047`, but it is the geometric form over
the ambient carrier. The internal form is the object the GCH statement
quantifies over. `[LJ-1.91]` measured that the ambient and internal cardinals
are different objects and no delivered lemma converts them
(`agents/tasks/LJ-1-136/lj-1.136-report.md:243-247`). So A4 is needed and is
not derivable from the ambient form.

**Widest unmeasured term.** The SECONDS of the internal least-of, not its
lines. The ambient `LeastCardInj` is 44 lines and 100.64 s, 76 percent of the
chain's whole 133 s (`agents/tasks/LJ-1-156/lj-1.156-report.md:208`, `:216`).
The internal form adds a truncated L-element existential inside the same
least-of, and `[LJ-1.136]` INFERRED the seconds rise, not fall
(`agents/tasks/LJ-1-136/lj-1.136-report.md:454`). **The term is the cold
seconds of the internal least-of, at the site that is already 2.26 s per
line.**

**The probe.** Build internal `LeastCard` (A2's predicate under a `⋁` over
`orderAt`), instantiate at one real ordinal, and measure cold seconds under
the C-12 cap. Report the rate against DD24's bar. This probe also settles the
seconds risk that `[LJ-1.136]` section 17.3 flagged.

**INFERRED cost: 2 to 4 Agda minutes.** The ambient term is already 100 s. The
internal form is not cheaper.

**D-10.** The truth risk is not that the target is false. It is that the
internal cardinal may not be the object GCH needs. That question is shared
with A7 and is a formulation risk, not a falsity. The well-order `orderAt` is
delivered, so the least-of terminates.

## 5. A7: the internal GCH statement, 110 lines

**What it is.** The statement `L ⊨ GCH`, in the shape of the delivered
`ChoiceStatement`.

**Is it needed.** YES. The statement IS the trophy. No dissolution is
possible.

**Widest unmeasured term.** The FORMULATION. The delivered comparable is 13
in-fence lines (`src/L/Choice/Transversal.lagda.md:372-384`). A7's 110 lines
are mostly reading, because the GCH statement must name the internal cardinal
(A4) and the square law (A5, A6) in exactly the shape those blocks deliver. If
the statement is formulated wrong, A5 and A6 cannot discharge it, whatever
their line counts. **The unmeasured term is the statement's shape: does it
quantify over A4's internal `IsCardinal` and demand the surjection that A5's
`sq` and A6's `absorbs` actually prove.**

**The probe.** Write the GCH statement in the `ChoiceStatement` shape and
check two things. First, that it elaborates and names only `S`, `∈ˢ`,
internal `IsCardinal` and the square-law shape. Second, that A5's `sq` and
A6's `absorbs` have conclusions that match its hypotheses. `[LJ-1.136]`
section 6.1 already ruled the statement should be written second, straight
after A2, as the consumer that audits the rest
(`agents/tasks/LJ-1-136/lj-1.136-report.md:381-392`).

**INFERRED cost: under 1 Agda minute.** It is a statement. The cost is the
formulation, which is reading, not elaboration.

**D-10.** The target is not false. It is a statement. The risk is that it is
the WRONG statement, and the probe settles that before A5 or A6 is funded.

## 6. THE COMPOSITION IS NOT STALE

The brief asked whether `[LJ-1.217]`'s 555 is stale against the tree. **MEASURED
FALSE: it is not stale.**

| block | figure | still holds? | evidence |
|---|---:|---|---|
| A1 | 40 | YES | shape still delivered at `src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795` |
| A2 | 170 | YES | `injAt` still absent from `src/L/`, zero grep hits; core still in the probe |
| A3 | 45 | YES | Part B measured at 22 lines; `stageBound` delivered at `src/L/Choice/Stage.lagda.md:328` |
| A4 | 190 | YES | ambient `IsCardinal` delivered at `src/L/BoundedSubset.lagda.md:1046-1047`; internal form absent |
| A7 | 110 | YES | `ChoiceStatement` delivered at `src/L/Choice/Transversal.lagda.md:372-384`; GCH statement absent |

**The residue is still 555.** The composition is not smaller than 555.

## 7. THE OVERLAPS, RE-CHECKED

The five overlaps from `agents/tasks/LJ-1-175/lj-1.175-report.md:142-148`,
re-checked against `[LJ-1.176]`'s 547 and `[LJ-1.217]`'s 446.

| # | overlap | status |
|---|---|---|
| 1 | A6's price names A5 | **RESOLVED.** `[LJ-1.217]` measured A6's own charge at 296 lines. A6 is now 150 + 296 = 446, one number. It inherits nothing from A5 (`agents/tasks/LJ-1-217/lj-1.217-report.md:156-162`) |
| 2 | A5's object list contains A6's object | **RESOLVED.** The partition ruling moved `ShiftAbs`/`Shiftω` into A6. A5's object list is now composition, `CSB`, inclusion `j`, column square, `pairω` (`agents/tasks/LJ-1-176/lj-1.176-report.md:192-206`). `[LJ-1.176]` also ruled `pairω` is A5's and not A6's (`agents/tasks/LJ-1-176/lj-1.176-report.md:452`) |
| 3 | A4's extra content is A2's content | **STANDS.** This is the one double-count that remains. Section 7.1 |
| 4 | A4 and A6 are steps of the probe whose whole is A5's basis | **RESOLVED.** A5's basis is no longer the 582-line ambient probe. It is now the five objects built into L. `LeastCard` (A4's basis) and `ShiftAbs` (A6's basis) are no longer steps of A5's basis |
| 5 | a 300-line item sits undivided across A4 and A5 | **RESOLVED, DISSOLVED.** `[LJ-1.176]` ruled the item names no object, so no block owns it, and its basis is measured false (`agents/tasks/LJ-1-176/lj-1.176-report.md:314-317`). It is not divided |

### 7.1 The one that stands, and the corrected figure

**Overlap 3 is a real double-count.** `[LJ-1.136]` prices A4 at 190 as "the
internal form's extra content is A2's predicate under a `⋁`, which A2
measures" (`agents/tasks/LJ-1-136/lj-1.136-report.md:302`, `:87`). A2's own
170 counts that same predicate.

**The lines that double are A2's injection-graph predicate.** A2 is built
first, and A4 consumes A2's predicate rather than rewriting it
(`agents/tasks/LJ-1-136/lj-1.136-report.md:359-368`). So A4's 190 over-counts
by the predicate's size.

**The size is not one number, and I say why.** The predicate's measured floor
is 27 lines, the `injAt` description in `[LJ-1.134]`'s per-part table
(`agents/tasks/LJ-1-134/lj-1.134-report.md:219-227`). Its ceiling is A2's
full measured core, 78 lines. A4 needs the description and the adequacy
conjuncts. It does not need the readback. No report separates those two
pieces, so reading alone cannot pin the double-count closer.

**Corrected figure: 1,470 to 1,521.** 1,548 minus 27 to 78. The conservative
figure is **1,470**. I do not quote 1,548 as A-prime's total, and neither
figure is a price. The 555 reading residue is what both refusals said it is.

## 8. TOWER-NEUTRALITY (DD4)

`dev/literature/devlin-II5.md:387-389` says the per-tower content is exactly
two objects: the level-hood certificate (Step C) and the definable well-order
(Steps D, G). The answer for the five blocks:

| block | tower status | why |
|---|---|---|
| A1 | **PER-TOWER. It is object 1, the level-hood certificate** | `⟨ isL x ⟩` is the level-hood predicate. On the J tower it is `⟨ isJ x ⟩` |
| A2 | **TOWER-NEUTRAL** | the predicate is the coding layer. It names no `isL` and no L stage. `[LJ-1.223]` measured the coding chain tower-neutral with zero residual (`agents/tasks/LJ-1-223/lj-1.223-report.md:56-63`) |
| A3 | **PER-TOWER. It is object 2, the definable well-order** | the selection is `leastOf` over `orderAt`, which is `<_L` |
| A4 | **PER-TOWER. It is object 2, applied to cardinality** | the internal least cardinal is `leastOf` over `orderAt` plus the injection predicate |
| A7 | **TOWER-NEUTRAL** | it is a statement. It names the structure and the internal cardinal, exactly as `ChoiceStatement` does |

**So the two per-tower objects are A1 (level-hood) and A3 plus A4 (definable
well-order).** A2 and A7 are tower-neutral and should be written generic from
their first line. A1, A3 and A4 are the blocks where the Def tower and the J
tower differ, and they should be written as structure parameters rather than
fixed to L.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-175/lj-1.175-report.md`, read WHOLE.** TAKEN: the five
  overlaps at `:142-148`; the NO FIGURE EXISTS negative at `:219` and `:247`;
  the 555 sum at `:51-52`; the 100 measured lines at `:57-58`; the gap list at
  `:266-275`.
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`, read WHOLE.** TAKEN: A5 at 547
  and its object list at `:192-206`; the dissolution of the 300-line item at
  `:314-317`; the ruling that `pairω` is A5's not A6's at `:452`; the two
  reasons 547 may be wrong at `:191-215`.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`, read WHOLE.** TAKEN: A6 at 446
  at `:8-14`; the 296-line charge at `:156-162`; the seven-cell sum and the
  refusal to quote it at `:25-27`; the 85 percent generic figure at
  `:183-185`.
- **`agents/tasks/LJ-1-156/lj-1.156-report.md`, read WHOLE.** TAKEN: the
  dissolution template at `:11-16`; the ambient chain at 133 s over 393 lines
  at `:189` and `:252`; `LeastCardInj` at 100.64 s over 44 lines at `:208` and
  `:246`; the 48-times-bar rate at `:301-303`.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`, read WHOLE.** TAKEN: the
  re-priced table at `:84-90`; the method table at `:299-305`; the A4 raise at
  `:318-322`; the build order at `:351-392`; the A4 seconds inference at
  `:454`; the ambient/internal cardinal split at `:243-247`; Probe A at 254 s
  at `:1059`; Probe B GO at `:897-913`.
- **`agents/tasks/LJ-1-134/lj-1.134-report.md`, read WHOLE.** TAKEN: the
  per-part table at `:219-227`; the range set and `ranAt` unpriced at
  `:177-180`; the A3 stage direction at `:238`.
- **`agents/tasks/LJ-1-223/lj-1.223-report.md`.** TAKEN: the coding chain
  tower-neutral with zero residual at `:56-63`; the two per-tower objects
  living above the coding chain at `:70-72`.
- **`src/L/BoundedSubset.lagda.md:56,1046-1047`.** TAKEN: the ambient carrier
  and the delivered ambient `IsCardinal`.
- **`src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795`,
  `src/L/Choice/Transversal.lagda.md:77,372-384`,
  `src/L/Choice/Stage.lagda.md:328`, `src/L/Model.lagda.md:99`,
  `src/L/Coding/Model.lagda.md:278`, `src/L/Axioms/Full.lagda.md:277`.** TAKEN:
  the delivered shapes each block consumes.
- **`archive/dev/TASKS-archived.md` and
  `archive/src/2026-08-09-rud-route/`.** NOT READ for figures. `[LJ-1.175]`
  already MEASURED that `grep -rn "\bA5\b"` over the archived tasks returns
  ZERO hits (`agents/tasks/LJ-1-175/lj-1.175-report.md:74-77`). The seven-block
  split postdates the archive. I record the omission rather than claim a
  survey.

## 10. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  exactly two objects: the level-hood certificate (Step C) and the definable
  well-order (Steps D, G). Section 8 maps the five blocks onto them.
- **`dev/literature/devlin-II5.md:370-383`.** USED. The twelve-row table, eight
  EITHER and four PER-TOWER. Confirms A1, A3 and A4 are the per-tower rows.
- **Does Devlin settle the shape or only the existence of each block.**
  Devlin settles the EXISTENCE of A1, A3 and A4, because the level-hood
  certificate and the definable well-order are his Step C and Steps D, G. He
  does not settle the SHAPE of A2, A7 or the range formula, because those are
  the internalization machinery of this tree, not Devlin's theorem.

## 11. THE NEGATIVES, CLASSIFIED

- **MEASURED. None of the five blocks dissolves.** Section 0.
- **MEASURED. All five blocks are needed.** Sections 1 to 5.
- **MEASURED. The residue is still 555, not smaller.** Section 6.
- **MEASURED. `injAt` and `IsInjGraph` exist nowhere in `src/L/`.** One grep,
  zero hits.
- **MEASURED. The ambient `IsCardinal` is delivered, the internal one is
  not.** `src/L/BoundedSubset.lagda.md:1046-1047`.
- **MEASURED. Overlap 3 stands.** A4's cell names A2's predicate,
  `agents/tasks/LJ-1-136/lj-1.136-report.md:302`.
- **MEASURED. The other four overlaps are resolved.** Section 7.
- **INFERRED. Every probe cost in Agda minutes.** Sections 1 to 5. They are
  judgements from measured seconds, and P-l says so.
- **INFERRED. The corrected sum is 1,470 to 1,521.** The double-count's floor
  and ceiling are measured; the band between them is my judgement.
- **NOT MEASURED IN EITHER DIRECTION. Whether A4 needs A2's readback or only
  its description.** That is why the double-count is a band, not one number.

## 12. WORKING TREE, AS MY REPORT DESCRIBES IT

One file added: `agents/tasks/LJ-1-227/lj-1.227-report.md`, this file. No
master edited. No brief or report edited. No probe written. **No Agda process
ran at any point.**
