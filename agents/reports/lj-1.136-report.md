# LJ-1.136 report: gate the remaining A-prime blocks

tier: opus (version `override`). Gate only. **No block was built.** No master
edited. No commit, no push. No probe written yet.

Every claim is marked **MEASURED** (read at the cited line, or a machine
result) or **INFERRED** (my composition or judgement).

**STATUS: reading, grep and site counting are COMPLETE. Agda is HELD.**
`[LJ-1.135]` is measuring build times and its Agda process is live
(`ghc-9.12.3` at 97.6 percent CPU, measured at 14:04). I start no Agda
process until the orchestrator sends the word. Section 9 says what I would
run and what it would settle.

## 0. LEAD FINDING, and it moves two blocks and one basis

**Three things, in order of how much they move the price.**

**(1) A5's basis carries a claim its source does not make, and `dev/LESSONS.md`
C-38 names the error class. MEASURED.**
`[LJ-1.131]:371` writes that `[LJ-1.107]` measured "582
lines for the ambient chain at this site, of which 455 closed
unconditionally". The number 582 is correct
(`agents/reports/lj-1.107-report.md:11-12`, and I re-counted the archived
probe: `archive/probes/ProbeLJ1107A.agda` is 582 non-blank lines). **The
number 455 appears nowhere in `[LJ-1.107]`.** It is the sum of the six
per-step line counts in that report's table at `:51-56`
(97+38+103+42+142+33 = 455). **The qualifier "closed unconditionally" is
MEASURED FALSE**: `archive/probes/ProbeLJ1107A.agda:630` declares
`module Chain (inj : ... → ⟪ α ⟫ ↪ ⟪ κ ⟫)`, so the injection is a MODULE
PARAMETER and no line of the probe proves `sq α` unconditionally at a
non-initial ordinal. A5's band therefore rests on a number with a property
attached to it that its source does not support.

**C-38 (`dev/LESSONS.md:3427`) is exactly this error class**: "A hypothesis
is discharged when something SUPPLIES it, never when it is restated. ...
Until something instantiates the module, 'discharged' means 'restated'."
`[LJ-1.131]:371` prices A5 on the words "the restatement rewrites types,
not proofs". **The chain is a module awaiting an instantiation, and the
instantiation is the price.**

**(2) The carrier crossing is NOT the risk, and its price is one line, not
22. MEASURED.** Section 2. The tree already crosses the `𝒮ᵥ`/`𝒮ʟ` boundary
at **13 call sites in 10 masters**, each ONE LINE, through the delivered
`Lset→isL` (`src/L/Constructible.lagda.md:395`). Three delivered masters of
the AC stack open `𝒮ʟ` and consume the ambient `orderAt` in the same file
without any wrapper (`src/L/Choice/Table.lagda.md:73` against `:113`).
`[LJ-1.134]`'s 22 lines are its whole Part B, the selection AND the
crossing, not the crossing alone.

**(3) The real unpriced term is the OPPOSITE direction, and no block names
it. MEASURED absence.** `[LJ-1.134]` measured **reading an L-element back
as a function**. Route A-prime also needs **writing a function into L as an
element**, at every point where the chain BUILDS an injection rather than
refutes one. The tree's delivered instrument for that is
`hasReplacementL` / `hasSeparationL`, and both take a **Formula**
(`src/L/Axioms/Full.lagda.md:277`, `src/L/Recursion.lagda.md:361`: "The
chapter is a wrapper around `hasReplacementL`, and that is the point"). So
each built injection owes an object-language description with its adequacy.
**No block in `[LJ-1.131]:367-373` names this cost.** Section 3.

## 1. THE RE-PRICED TABLE

DD8: one best-effort figure each, and each names its basis. In-fence
non-blank lines, the ledger's caliber. Standing tree at dispatch: **28,617
lines over 85 masters** (`.venv/bin/python scripts/ledger.py --brief`,
MEASURED at 14:04).

| block | `[LJ-1.131]` band | MY figure | basis | how I gated it |
|---|---|---|---|---|
| A1 `⟨ isL x ⟩` replaces "assume V = L" | 30 to 60 | **40** | `stageBound` delivered (`src/L/Choice/Stage.lagda.md`, `𝒮ᵥ` at `:68`); `isL` is already the hypothesis shape the order stack takes (`src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795`) | **READING.** Three delivered sites take this exact hypothesis shape today |
| A2 injection as an ELEMENT of L, read back | 120 to 220 | **170** | `[LJ-1.134]` MEASURED 78 lines for the core; the range formula and `ranAt` adequacy are named unpriced at `agents/reports/lj-1.134-report.md:175-180` | **DELIVERED MEASUREMENT** (`[LJ-1.134]`, `--safe`, exit 0) plus reading for the two unpriced pieces |
| A3 the `<_L`-least injection by `leastOf` over `orderAt` | 40 to 80 | **45** | `[LJ-1.134]` Part B MEASURED at 22 lines; `leastOf` takes an arbitrary metatheoretic hProp predicate (`src/L/WellOrder/Base.lagda.md:158-161`), so **no object-language description is needed for the SELECTION**; three delivered instances of the pattern (`src/L/BoundedSubset.lagda.md:463-497`, `:1099-1141`, `src/L/Hull.lagda.md:158-159`) plus `[LJ-1.134]`'s Part B | **READING plus `[LJ-1.134]`'s measurement.** Lowered; section 5 |
| A4 internal least cardinal and internal `IsCardinal` | 90 to 170 | **190** | `[LJ-1.107]`'s ambient `LeastCard` is 38 lines **and 91.98 cold seconds, the dominant term of that probe** (`agents/reports/lj-1.107-report.md:52`, `:59-63`). The internal form replaces the truncated ambient bijection by a truncated L-element bijection, so it needs A2's predicate inside the least-of | **READING.** Raised, and the SECONDS matter more than the lines; section 6 |
| A5 the square-law chain over L-injections | 300 to 450 | **NOT PRICED. See section 3** | the band's stated basis is arithmetic-derived and its qualifier is MEASURED FALSE (section 0.1); the block's real content is unmeasured in the direction that matters | **NEITHER.** This is the block that needs the probe. Section 9 |
| A6 `absorbs` as a theorem | 100 to 180 | **150 plus A5's per-construction charge** | `[LJ-1.107]` measured `ShiftAbs`+`Shiftω` at 103 lines and 2.83 s (`:53`), MEASURED and correct as quoted. But that is the AMBIENT injection; the L-element form owes one built graph | **READING.** The quoted basis checks out; the block inherits A5's open charge |
| A7 the internal GCH statement | 80 to 160 | **110** | `ChoiceStatement` with `hasChoiceL` is 13 in-fence lines (`src/L/Choice/Transversal.lagda.md:372-384`), stated wholly at `𝒮ʟ` with no ambient object; `L⊨ZFC` is the shape (`src/L/Model.lagda.md:99`) | **READING.** The consumer shape is delivered and I read it |

**Total of the six priced blocks: 705.** A5 is open, and it was the largest
band. **I decline to state a total until A5 is measured**, because a total
that carries an unmeasured largest term is a band centre wearing a number's
clothes, which is what DD8 forbids.

## 2. THE CARRIER-CROSSING SITE COUNT. MEASURED

This was the brief's first number. **The answer is that the crossing is
already routine in the delivered tree, and it costs one line.**

### 2.1 How many masters hold both carriers. MEASURED

**40 masters name both `𝒮ᵥ` and `𝒮ʟ`**; 5 name only `𝒮ʟ`. Counted by
`grep -rl` over `src/**/*.lagda.md` and intersecting.

**41 masters open `hPropStructure 𝒮ʟ`; 20 open `hPropStructure 𝒮ᵥ`.**
Counted with `grep -rl "^open hPropStructure 𝒮ʟ"` and the `𝒮ᵥ` twin, over
85 masters. The list matters at three places and I checked each:

- `src/L/Choice/Step.lagda.md:78` opens `𝒮ᵥ`. `orderAt` at `:740` is
  ambient. **MEASURED, and it confirms `[LJ-1.134]`.**
- `src/L/Coding/Model.lagda.md:70` opens `𝒮ʟ using ( S )`. **MEASURED, and
  it confirms `[LJ-1.134]`.**
- `src/L/Hull.lagda.md:52` opens `𝒮ᵥ`. **So `L.Hull` uses `orderAt` at
  `:159` with NO crossing at all**, both sides ambient. `[LJ-1.131]:516-518`
  cites `L.Hull` as proof the GCH wing already runs on the AC order. That
  is true, and it is NOT evidence about the crossing, because Hull never
  crosses.

### 2.2 The delivered crossing device and its call sites. MEASURED

`Lset→isL : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ isL x ⟩`,
`src/L/Constructible.lagda.md:395-396`. It is the ambient-to-L crossing and
it is **one line at every site**.

**13 call sites across 10 consumer masters.** MEASURED, by grep, 25 hits
minus 2 definition lines minus 10 `using(...)` import lines:

| master | call sites |
|---|---:|
| `src/L/Choice/Table.lagda.md` | 2 |
| `src/L/Choice/Before.lagda.md` | 2 |
| `src/L/Choice/Limit.lagda.md` | 2 |
| `src/L/Choice/Step.lagda.md` | 1 |
| `src/L/Choice/Order.lagda.md` | 1 |
| `src/L/Choice/Faithful.lagda.md` | 1 |
| `src/L/Choice/Transversal.lagda.md` | 1 |
| `src/L/Axioms/Basic.lagda.md` | 1 |
| `src/L/Axioms/Separation.lagda.md` | 1 |
| `src/L/Reflect.lagda.md` | 1 |

### 2.3 The proof that the crossing is not a boundary at all. MEASURED

`src/L/Choice/Table.lagda.md:73` opens `hPropStructure 𝒮ʟ`, so its `S` is
the L carrier. At `:113` the same file writes

```
Ordering : (α : V ℓ) → IsOrd α → Mem (Lset α) → Mem (Lset α) → Ω
```

**It names `V ℓ` in the type where it wants the ambient carrier, and it
pays nothing.** The two carriers coexist inside one master with no wrapper,
no transport and no conversion, because `𝒮ʟ = 𝒮ᵥ ↾ isL`
(`src/L/Constructible.lagda.md:411`) makes the L carrier a `Σ` over the
ambient one with an hProp second component
(`src/FOL/ZFStructure.lagda.md:145-152`).

**Three consequences, all MEASURED by reading:**

1. `L/Choice/Faithful` (`:86`), `L/Choice/Order` (`:83`) and
   `L/Choice/Table` (`:73`) all open `𝒮ʟ` AND consume `orderAt`.
   **19 `orderAt` code occurrences across those three files: 6, 2 and 11.**
   MEASURED by grep, excluding `using (` import lines and `{.Agda}` prose
   references. Every one is a delivered crossing that already works.
2. **`⟪_⟫` does not change under the carrier switch.** The presentation
   comes from `Cubical.HITs.CumulativeHierarchy.Properties` and applies to
   `V ℓ` (`src/V/Presentation.lagda.md:20-42`). `ZFStructure` carries no
   presentation field (`src/FOL/ZFStructure.lagda.md:91-97`). For an L-set
   `a`, the presentation is `⟪ fst a ⟫`, and `isL-trans`
   (`src/L/Constructible.lagda.md:378`) makes every member of it
   constructible. **So every injection type `⟪ _ ⟫ ↪ ⟪ _ ⟫` in
   `SquareLaw`, `StageCardinal` and `IsCardinal` is ALREADY carrier-neutral
   and needs no rewriting.**
3. Therefore **`[LJ-1.131]:458-465`'s "structural warning" overstates the
   cost.** That paragraph says restating the wing "changes which carrier
   every `∈ˢ`, `⟪_⟫` and `↪` in the chain refers to", and attributes about
   300 lines of A-prime's excess over Route A to it. **The `⟪_⟫` half and
   the `↪` half are MEASURED FALSE**: neither changes. Only `∈ˢ` changes,
   and `src/L/Choice/Table.lagda.md` shows that costs one qualifier.

### 2.4 Verdict on the brief's first question

**The crossing is paid ONCE and shared, not per site.** MEASURED, and it is
the opposite of the abort criterion the brief anticipated. **The carrier
crossing does not re-price A-prime. It is the cheapest thing in the block
list.**

## 3. WHAT DOES RE-PRICE A-PRIME, AND IT IS A5

### 3.1 The direction nobody measured

`[LJ-1.134]` measured **L-element to function**: given a graph in L with
`svAt` and `domAt`, extract `toFun` with `toFun-inj`. GO, 78 lines for the
core (`agents/reports/lj-1.134-report.md:229-233`).

Route A-prime also needs **function to L-element**, and the chain needs it
at every point where it BUILDS an injection. From
`archive/probes/ProbeLJ1107A.agda`, the chain builds six:

| built object | where in the archived probe | delivered as an L-element? |
|---|---|---|
| `pairω`, the pairing on `ω` | `:636-637` via `NumeralPresentation` | **NO** |
| the column square `pair` | `src/L/Ordinal/SquareLaw.lagda.md:944-950` | **NO** |
| `ShiftAbs` / `Shiftω`, `sucV γ ↪ γ` | probe step 3 | **NO** |
| `Incl`, the inclusion `β ↪ κ` | probe step 4 | **NO** |
| the `CSB` bijection | `archive/probes/ProbeLJ1107A.agda:99-207`, `:489-490` | **NO** |
| composition of two injections | throughout | **NO** |

**MEASURED: `CSB` does not exist anywhere in `src/`.** Zero hits for
`csb`, `bernstein`, `schroeder`, `schröder` over
`src/**/*.lagda.md`. It exists only in `archive/probes/ProbeLJ1107A.agda`
and `archive/probes/ProbeLJ1111A.agda`. **So A5's basis is not a
restatement of delivered master code. It is the promotion of an
un-delivered probe, plus an internalization.** `[LJ-1.131]:371` calls A5
"the square-law chain **restated** over L-injections", and no master holds
the chain to restate.

### 3.2 Why the built objects must be in L, and it is not avoidable

The whole point of A-prime is that `leastOf` breaks the truncation because
a least element is unique (`isPropLeastOf`,
`src/L/WellOrder/Base.lagda.md:136-139`). The order that gives leastness is
`orderAt`, which orders `Mem (Lset γ)`: **sets**. So the object selected is
a SET IN L, and the leastness is leastness among SETS IN L.

`[LJ-1.107]`'s chain refutes leastness by producing a bijection
(`noinj²`, `archive/probes/ProbeLJ1107A.agda:472`, `:489-490`, feeding
`leastα`). Under A-prime the leastness is L-leastness, so **the refuting
bijection must itself be in L**, and `CSB` must deliver an L-element.

**The alternative that would avoid this is REFUTED. MEASURED.** Keep the
ambient `LeastCard` and require an L-witness only at the end. Then the
route needs "every ordinal has a CONSTRUCTIBLE bijection to its AMBIENT
least cardinal", which is an instance of `V = L`, and Route A-prime exists
precisely to avoid assuming it. `[LJ-1.91]` measured the same boundary from
the other side: `ω₁ᴸ` does not provably satisfy the ambient `IsCardinal`,
because the sentence is independent
(`agents/reports/lj-1.91-report.md:36-48`, recorded at
`agents/reports/lj-1.131-report.md:303-309`). **The ambient and the internal
cardinal are different objects and no delivered lemma converts them.**

### 3.3 What one internalization costs, with the two delivered comparables

Both are MEASURED, they differ by a factor of 40, and **the gap between
them IS the gate**.

**The cheap comparable, and it is the right shape.** `[LJ-1.134]` wrote a
NEW object-language formula on the delivered `L/Coding/` layer: `injAt`
with `injAt-out` and `injAt-in`, **27 non-comment lines**
(`agents/reports/lj-1.134-report.md:84-86`). A formula plus two adequacy
readings, riding on `src/L/Coding/Model.lagda.md` (1,288 in-fence lines,
delivered).

**The expensive comparable, and it is the cautionary bound.**
`src/L/Choice/Table.lagda.md` is the tree's ONE delivered instance of
exactly the write direction: it takes the metatheoretic `orderAt` and
produces `relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S` (`:795`), an element of L,
with adequacy both ways (`relL-fill`, `relL-rep`, `:825-832`). **It cost
411 in-fence lines, and its object-language description cost
`src/L/Choice/Internal.lagda.md`, 780 more. 1,191 lines for ONE object.**
MEASURED, counted with the ledger's fence caliber.

**Which comparable governs is the unmeasured term of A5, and I will not
guess it.** P-l forbids exactly that: a price from a comparable elsewhere
is a hypothesis. The two comparables differ because `Table` and `Internal`
describe the ORDER, a three-key comparison recursive over the tower, whose
own chapter says the description is still incomplete and needs three more
things (`src/L/Choice/Table.lagda.md:326-341`). An injection graph is a far
simpler object. **INFERRED that A5 lands nearer the cheap comparable. That
inference is what the probe must settle, and it carries the largest band in
the route.**

### 3.4 The consequence for the band

`[LJ-1.131]` priced A5 at 300 to 450 against an ambient chain it measured
at 582 lines. **The band is BELOW its own comparable**, and the report gives
one sentence for the reduction: "the restatement rewrites types, not
proofs". Section 2.3 above shows the type rewrite is nearly free, which
would support the reduction. Section 3.1 shows the chain is not delivered
and six objects must be built into L, which cuts the other way and is
larger. **The two corrections do not cancel and nobody has measured either
of them at this site. A5 is UNGATED and I am not going to gate it by
reading.**

## 4. METHOD PER BLOCK, AND WHY

The brief asked which blocks may be gated by reading. **Five may. One may
not. One is already measured.**

| block | method | why this method is admissible |
|---|---|---|
| A1 | **READING** | The hypothesis shape is delivered and consumed at three sites I read: `src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795`, `src/L/Choice/Transversal.lagda.md`. Nothing new is elaborated |
| A2 | **DELIVERED MEASUREMENT** | `[LJ-1.134]` ran it. `--safe`, exit 0, 207 lines, 2.51 s upper bound. I add only the two pieces that report marks unpriced |
| A3 | **READING plus `[LJ-1.134]`** | Part B is measured at 22 lines. The reading that matters: `leastOf`'s predicate is an arbitrary metatheoretic hProp (`src/L/WellOrder/Base.lagda.md:158-161`), and `src/L/Hull.lagda.md:392` passes a satisfaction predicate to it today. **So A3's SELECTION needs no object-language work.** That is readable, not a guess |
| A4 | **READING** | `IsCardinal`'s delivered shape is at `src/L/BoundedSubset.lagda.md:1046-1047` and I read it. The internal form's extra content is A2's predicate under a `⋁`, which A2 measures |
| A5 | **NEITHER. Needs a probe** | Section 3. Its stated basis is arithmetic over another report's table with a false qualifier, and its real content is unmeasured in the write direction |
| A6 | **READING** | The quoted basis checks out at `agents/reports/lj-1.107-report.md:53`. The block then inherits one instance of A5's open per-construction charge, which I state rather than absorb |
| A7 | **READING** | `ChoiceStatement` at `src/L/Choice/Transversal.lagda.md:372-384` is the delivered shape, wholly at `𝒮ʟ`, and `src/L/Model.lagda.md:99` is how the trophy consumes it |

## 5. THE BLOCKS WHOSE PRICE MOVED, AND WHY

**A3: 40 to 80, down to 45.** Two measurements support the low end.
`[LJ-1.134]` Part B is 22 lines. And the reading in section 4: `leastOf`
accepts any metatheoretic hProp predicate, so A3 owes no formula.
`[LJ-1.134]` itself pointed at 40 to 60 as a direction
(`agents/reports/lj-1.134-report.md:236-239`) and declined to re-price
because `β` must come from `stageBound`. I read `stageBound`'s chapter:
`src/L/Choice/Stage.lagda.md:68` opens `𝒮ᵥ`, the same carrier as
`orderAt`, so obtaining `β` costs no crossing. **I re-price it.**

**A4: 90 to 170, up to 190, and the LINES are not what moved.** The band's
basis is `[LJ-1.107]`'s ambient `LeastCard` at 38 lines. **That is correct
and it is the least useful half of that measurement.** The same table
(`agents/reports/lj-1.107-report.md:52`) records `LeastCard` at **91.98
cold seconds, out of 117 s for the whole 582-line probe.** The report names
it: "The dominant term is step 2: the least-of over the well-order on the
successor's presentation (`⟪ sucV α ⟫` normalizes the union structure, the
P-m instantiation class)" (`:59-63`). **38 lines cost 79 percent of the
probe's time.** DD24 sets the quality bar as cold seconds over in-fence
lines: at 2.42 s per line, `LeastCard` is by far the worst ratio anywhere
in this route. The internal form puts an extra truncated existential inside
that same least-of. **INFERRED that the seconds go up, not down. I raise
the line figure modestly and flag the seconds as the block's real risk.**

**A5: band withdrawn.** Section 3.

**A6: 100 to 180, held at 150, with a named open charge.** The quoted basis
is MEASURED and correct. I do not fold A5's per-construction charge into
A6's number, because that would hide an unmeasured term inside a priced
block, which is the pattern `[LJ-1.131]` fell into at A5.

**A1, A2, A7: inside their bands.** No evidence moves them.

## 6. BUILD ORDER AND DEPENDENCIES

The dependency graph, MEASURED from what each block consumes.

```
A1  ──────────────┐
                  ├──► A2 ──► A3 ──┬──► A4 ──► A5 ──► A6 ──► A7
(delivered stack) ┘                └──────────────────┘
```

**A2 must be built first, and it is the only block that unblocks the
others.** MEASURED reason: A3's selection predicate, A4's internal cardinal
and A5's L-injections all speak "g is an injective function graph from a to
b". That predicate is A2. Until it is a master-level definition, nothing
downstream is even statable, so nothing downstream is checkable.

**Order, with the reason for each position:**

1. **A2.** The read-back plus the range formula. Everything names it.
   `[LJ-1.134]` already elaborated its core, so this is the lowest-risk
   first build in the route.
2. **A1.** Independent of A2 and small. It can go first or second. Put it
   second so A2's shape settles first.
3. **A3.** One `leastOf (orderAt β)` over A2's predicate. It is what makes
   the selection canonical, and canonicity is what `[LJ-1.114]` measured as
   missing (`g₂' != g₁`).
4. **A4.** The internal least cardinal. It consumes A3's canonical
   selection and A2's predicate.
5. **A5.** Only after A4, because the chain's leastness refutations are
   refutations against A4's definition.
6. **A6.** `absorbs` from `sq`, exactly as `[LJ-1.118]` recorded the
   reduction (`agents/reports/lj-1.129-report.md:182-186`).
7. **A7.** The PROOF last. Its statement moves, and section 6.1 says why.

### 6.1 The correction C-35 forces, and it is the only change I make to the order

`dev/LESSONS.md:3200`, C-35: "A delivered block with no consumer is
UNTESTED: its first consumer is its first real audit. ... A block that
nothing imports has never been asked to mean anything."

**A7 is the consumer of A1 to A6.** If A7 is written last, then A4, A5 and
A6 sit un-consumed for the whole build, and this tree has shipped two
vacuous frames that passed prose review
(`agents/reports/lj-1.129-report.md:334-338`).

**So split A7.** Write **A7's STATEMENT second, straight after A2**, in
`ChoiceStatement`'s shape, and leave it unproved. It is the small half of
the block: the delivered comparable is **9 in-fence lines**
(`src/L/Choice/Transversal.lagda.md:372-380`), 13 with its proof. It makes
every later block answer to a consumer on the day it lands. **Prove it
last.** Revised order: **A2, A7-statement, A1, A3, A4, A5, A6,
A7-proof.**

**The one place the order could still be wrong, and I mark it.** If A5's
probe finds that the six constructions of section 3.1 need a shared generic
"build this graph in L" helper, that helper belongs INSIDE A2, and A2 grows
before A3 starts. **INFERRED.** It is the second thing the probe settles.

## 7. DD4, ANSWERED AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic.**

**The finding, and it is positive.** Section 2 measured that the carrier
crossing is one delivered line used at 13 sites, and that `⟪_⟫` and `↪` do
not change across the carrier at all. **So the shared-code opportunity in
A-prime is larger than `[LJ-1.131]` and `[LJ-1.134]` both thought, and for
a structural reason: `𝒮ʟ = 𝒮ᵥ ↾ isL` makes the L carrier a `Σ` over the
ambient one, so the ambient presentation IS the L presentation.**

**The concrete DD4 recommendation, and it is the one that pays.** The write
direction of section 3.1 should be written ONCE, generic in the two sets
and the function, as a single helper that takes a small family and a
description and returns an element of L with both adequacy readings. Six
constructions consume it. Written once it is shared by construction;
written per site it is six copies that no checker will catch.
`src/L/Recursion.lagda.md:133` (`smallDom`) and `:229` (`mereFunct`) are
the delivered half of exactly that helper, and `src/L/Recursion.lagda.md`
is only 94 in-fence lines, so the generic form is cheap to extend.

**And P-w constrains HOW to write it, which is the part a DD4 answer
usually skips.** `dev/LESSONS.md:3094`: "A module application COPIES; an
interposed module cannot amortize one. ... Only three moves reduce
instantiation cost: fewer applications, fewer definitions copied per
application, cheaper types on the definitions that are copied." **So the
helper must be a FUNCTION taking its sets and its description as
arguments, not a parameterized module applied once per construction.** Six
module applications would save the lines and lose the seconds, and DD24
measures seconds over lines. **MEASURED law, INFERRED application to this
helper.**

**A second DD4 point, and it is about the OTHER trophy.** `CSB` is generic
for h-sets with LEM and names no tower object
(`agents/reports/lj-1.107-report.md:187-194`). If A5's internal version is
written generic over the carrier rather than fixed at `𝒮ʟ`, the AC side and
the J tower both get it. **INFERRED**, because no J tower exists in this
tree to check it against.

**No stop-line pushed me toward writing fixed. I wrote no code.**

## 8. THE NEGATIVES, EACH CLASSIFIED

| negative | class |
|---|---|
| the qualifier "455 closed unconditionally" in `[LJ-1.131]:371` | **MEASURED FALSE.** `archive/probes/ProbeLJ1107A.agda:630` takes the injection as a module parameter |
| the number 455 appears in `[LJ-1.107]` | **MEASURED FALSE.** Zero grep hits; it is arithmetic over that report's table at `:51-56` |
| `CSB` exists in `src/` | **MEASURED FALSE.** Zero hits in `src/**/*.lagda.md`; archived probes only |
| the carrier crossing is per-site and expensive | **MEASURED FALSE.** 13 one-line sites, and `src/L/Choice/Table.lagda.md:73` against `:113` shows the carriers coexist with no wrapper |
| `⟪_⟫` or `↪` change under the carrier switch | **MEASURED FALSE.** `ZFStructure` has no presentation field (`src/FOL/ZFStructure.lagda.md:91-97`); the presentation is ambient (`src/V/Presentation.lagda.md:20-42`) |
| `L ⊨ V = L` is delivered | **MEASURED ABSENT.** Zero hits in `src/**/*.lagda.md`. It is the standard route to Devlin 5.7 and this tree does not have it |
| a proof-transfer from "ZF proves φ" to "L ⊨ φ" is delivered | **MEASURED ABSENT.** The four transfer lemmas are Δ₀ or Π₁ only (`agents/reports/lj-1.131-report.md:311-323`) |
| the ambient least cardinal converts to the internal one | **MEASURED negative**, as recorded (`agents/reports/lj-1.91-report.md:36-48`); that report marks its own argument INFERRED |
| A5's six constructions each need an object-language description | **INFERRED**, from `src/L/Recursion.lagda.md:361` and `src/L/Axioms/Full.lagda.md:277`, both of which take a `Formula` |
| A5 lands nearer the 27-line comparable than the 1,191-line one | **INFERRED.** This is the probe |
| A4's cold seconds rise above `LeastCard`'s 91.98 | **INFERRED.** The extra existential sits inside the same least-of |
| the Devlin errata touch anything A-prime rests on | **MEASURED FALSE.** Section 10 |

## 9. THE PROBE I WOULD RUN, WITH ITS ABORT CRITERION FIXED NOW

**I have not started Agda. `[LJ-1.135]` is measuring build times and its
process is live.** This section fixes the probe in advance, per D-1, so the
criterion cannot move after the result.

**`src/ProbeLJ1136A.agda`. One file. One process at
`GHCRTS="-A64m -I0 -M8g"`. It measures the WRITE direction, once.**

1. Take two concrete L-sets and one concrete metatheoretic injection
   between their presentations. Reuse `[LJ-1.134]`'s Part C concrete graph
   shape (`src/ProbeLJ1134A.agda:190-289`) so the site is not degenerate.
2. Write ONE object-language description of "z is the ordered pair of an
   element and its image", and prove its two adequacy readings, in the
   shape `[LJ-1.134]` used for `injAt`.
3. Carve the graph out with `hasSeparationL`
   (`src/L/Axioms/Full.lagda.md`) and prove the resulting element of L
   satisfies `svAt`, `domAt` and `injAt`.
4. Feed it straight back through `[LJ-1.134]`'s `toFun` and check that the
   round trip returns the original function's values.

**GO** if the round trip elaborates. Report the lines, the cold seconds and
the load. **That number, multiplied by the six constructions of section
3.1, is A5's price.**

**NO-GO** if the description cannot be written or the separation refuses.
**A NO-GO does not kill A-prime**, because A2's read direction is already
GREEN; it means the six constructions must each be reached some other way,
and A5's band moves toward the 1,191-line comparable. **Report the exact
refusal either way.**

**Cost expectation: seconds, not minutes.** `[LJ-1.134]` MEASURED that a
probe over this import closure costs about 2.5 s with the interfaces cached
(`agents/reports/lj-1.134-report.md:60-72`). **INFERRED for my file**, and
P-l says that is a hypothesis, not a price.

## 10. LITERATURE USED (DD18)

`dev/literature/devlin-errata.md`, **read WHOLE.** `[LJ-1.131]:653-658`
marked not reading it as its own gap. **I read it and the answer is
clean.**

**MEASURED: the errata touch nothing A-prime rests on.** Mathias's own
scope sentence, quoted at `dev/literature/devlin-errata.md:36-39`, is
"The problems are chiefly confined to section 9 of Chapter I and section 1
of Chapter VI." The inventory below it covers: I.9.1 to I.9.12 (Finseq,
`F∧`, Build, Seq, Fml, Fr, Sub, Sat), II section 10 (amenability, Devlin
p. 45) and II p. 65-66 (uniformity of Sat), and VI.1.13 and VI.1.14. **None
of II.5, and none of I.1.1(vii).** A-prime rests on 5.3, 5.4, 5.5, 5.6 and
5.7 of II.5, and on 1.1(vii) (`agents/reports/lj-1.131-report.md:640-651`).

**Two notes, and each has a reason to be in the return:**

1. **The whole error class is inapplicable to Bedrock by construction.**
   Every item is about the WEAK system BS being unable to prove something
   (`dev/literature/devlin-errata.md:180-184`, "counterexamples of Solovay
   show that it is not quite strong enough"). Bedrock's ambient is a
   cubical cumulative hierarchy with LEM, not BS.
   **INFERRED**, and it is the standard reading.
2. **One item is worth carrying anyway**, because it is a proof habit
   rather than a system weakness: item 5 of the checklist
   (`:246-248`), "do not conflate the two definitions of `Σ0` function",
   class term against pointwise-with-transitive-`M`. **That is exactly the
   distinction A2 and A5 live on**: a graph as an ELEMENT against a
   function as a metatheoretic term. The tree keeps them apart by types, so
   the error class cannot be committed silently here.

`dev/literature/devlin-II5.md`: `:147-169` (5.5, 5.6, 5.7), `:346-358`
(what II.5 consumes), `:364-394` (the per-step table), `:411-418`
(1.1(vii) as generic cardinal arithmetic), `:447-452` ("every CONSTRUCTIBLE
x ⊆ κ"). Read for the requirement list only; `[LJ-1.131]` section 6
resolves the readings and I did not re-litigate them.

## 11. ARCHIVE USED (DD18)

Reports read WHOLE: `agents/reports/lj-1.134-report.md` (331 lines),
`agents/reports/lj-1.131-report.md` (669), `agents/reports/lj-1.107-report.md`
(271).

- From `[LJ-1.134]`: the GO and its `--safe` exit 0 (`:10-34`), the machine
  qualification and the cached-interface finding (`:36-72`), the carrier
  crossing (`:106-140`), the per-part sizes (`:217-227`), the two unpriced
  pieces (`:175-180`), and the A3 direction (`:236-239`).
- From `[LJ-1.131]`: the seven-block table (`:367-373`), the structural
  warning (`:458-465`), the DD4 argument (`:516-532`), the errata gap
  (`:653-658`), and the `ω₁ᴸ` negative (`:303-309`).
- From `[LJ-1.107]`: the per-step table (`:51-57`), the `LeastCard`
  dominance (`:59-63`), what closes and what does not (`:67-108`), the CSB
  step (`:112-121`), and the DD4 section (`:187-194`). **Checked, not
  quoted, as the brief required.** Two of the three bases it supplies
  check out; the third is section 0.1.

`archive/` proper, **surveyed and used**: `archive/probes/` holds the
retired probes. `archive/probes/ProbeLJ1107A.agda` read at `:90-99`,
`:205-206`, `:270-275`, `:455-495`, `:620-666`, and counted whole (582
non-blank, 500 non-blank non-comment). **This is the file that settles
section 0.1**, and reading it rather than the report is why the negative is
MEASURED. `archive/probes/ProbeLJ1111A.agda` read at `:28`, `:135-190` for
the CSB consumers, and counted (250 non-blank).
`archive/dev/`: **NOT read.** No archived record bears on whether a live
definition elaborates, and the D-series rulings are superseded by DD.

Masters read at the cited lines: `src/L/Choice/Step.lagda.md` (`:46`,
`:78`, `:740-749`), `src/L/Coding/Model.lagda.md` (`:34`, `:70`),
`src/L/Choice/Table.lagda.md` (`:40-130`, `:780-840`),
`src/L/Choice/Transversal.lagda.md` (`:352-400`),
`src/L/Constructible.lagda.md` (`:370-411`), `src/L/BoundedSubset.lagda.md`
(`:40-80`, `:1035-1075`), `src/L/StageCardinal.lagda.md` (`:1-80`),
`src/L/Ordinal/SquareLaw.lagda.md` (`:530-560`, `:675-720`, `:940-965`),
`src/L/Hull.lagda.md` (`:32-33`, `:52`, `:159`),
`src/L/Choice/Stage.lagda.md` (`:60-75`, `:285-300`),
`src/FOL/ZFStructure.lagda.md` (`:85-152`), `src/V/Presentation.lagda.md`
(whole), `src/L/Recursion.lagda.md` (`:55`, `:133`, `:229`, `:331-369`),
`src/L/Axioms/Full.lagda.md` (`:277-281`), `src/L/Model.lagda.md` (`:57`,
`:99`).

`dev/LESSONS.md`: the `probe` and `recon` bundles were loaded with
`.venv/bin/python scripts/rules.py --for probe` and `--for recon` and read.
D-1, P-l, P-i, C-12, D-10, C-22, R-40 and D-26 came back. I then read the
brief's named entries at their own lines rather than from the bundle:
D-8 (`:1377`), C-36 (`:3284`), D-30 (`:3332`), C-39 (`:3521`), P-x
(`:3564`), C-40 (`:3602`), C-38 (`:3427`), C-35 (`:3200`), P-w (`:3094`),
P-m (`:2460`), D-29 (`:3242`). **Two of them do not say what the brief says
they say, and section 12 opens with the correction.** `dev/PLAN.md` read at
`:72` and `:171-185` for DD5, DD24 and DD26.

## 12. THE RULES, ANSWERED

**First, a correction to the brief, and I make it because a wrong citation
propagates.** The brief's `MANDATORY RULES` reads "**D-8.** Gate a block
before you fund it." **`dev/LESSONS.md:1377` is D-8 and it says something
else**: "A self-containing step operator is not subset-monotone; condition
on membership." The gate rule the brief means is **`dev/LESSONS.md` D-1**
plus **`dev/PLAN.md` DD8** (one best-effort figure with its basis), and
`AGENTS.md` states it in prose under Probes. **I worked to D-1 and DD8.**
LESSONS D-8 does not bear on this task.

**Second, `P-x` is not what the brief's reading of it suggests, and the
real P-x bears harder.** `dev/LESSONS.md:3564`: "A transparent construction
in a RECORD FIELD type is paid by every elaboration of the record."
**That binds A7 directly.** `ChoiceStatement` becomes the `hasChoice` field
of `L⊨ZFC` (`src/L/Model.lagda.md:99`), so its type is forced into every
elaboration and every projection of the record. I read
`src/L/Choice/Transversal.lagda.md:372-384`: it names only `S`, `∈ˢ`,
`isContr` and the model's derived `_∩_`, and **no transparent
construction**. **A7 must copy that discipline exactly.** MEASURED by
reading, and it is a constraint on A7's shape, not only its price.

Now the bundles.

- **D-1.** Section 9 fixes the abort criterion before the probe runs. No
  probe is written yet and none will be committed.
- **DD8.** Six figures, one each, each naming its basis. **A5 gets no
  figure**, because a band centre for the largest block is what DD8 forbids.
- **P-l.** Honoured twice. I did not transfer `[LJ-1.107]`'s 582 lines to
  A5 by analogy, and I did not transfer `[LJ-1.134]`'s 22-line crossing to
  the other blocks. Both are the exact move P-l forbids, and section 3.3
  names the two comparables rather than averaging them.
- **C-38, and it is the lesson that names A5's error class.**
  `dev/LESSONS.md:3427`: "A hypothesis is discharged when something
  SUPPLIES it, never when it is restated. ... Until something instantiates
  the module, 'discharged' means 'restated'." **`[LJ-1.131]:371` prices A5
  on the words "the restatement rewrites types, not proofs".**
  `archive/probes/ProbeLJ1107A.agda:630` holds the injection as a module
  parameter, so the chain is exactly a module awaiting an instantiation.
  **A5's price is the price of the INSTANTIATION, and C-38 says the
  restatement is not it.** That is the single clearest statement of why A5
  needs a probe.
- **C-35.** "A delivered block with no consumer is UNTESTED: its first
  consumer is its first real audit." It changes the build order, and
  section 6.1 records the change.
- **P-m.** `dev/LESSONS.md:2460`: parameterized content checks near 0.01 s
  per line, instantiation content near 0.22. **`[LJ-1.107]` measured
  `LeastCard` at 91.98 s over 38 lines, which is 2.42 s per line**: eleven
  times the instantiation class and about 306 times DD24's AC-wing bar of
  0.0079 s per line (`dev/PLAN.md:182`, DD26-rebased at `:185`). That
  report classifies it itself: "the P-m instantiation class"
  (`agents/reports/lj-1.107-report.md:59-63`). **A4 inherits that site.**
- **P-w.** `dev/LESSONS.md:3094`: a module application COPIES, and only
  fewer applications, fewer definitions per application or cheaper types
  reduce the cost. **It constrains section 7's DD4 helper**: the shared
  write-direction device must be a FUNCTION taking its parameters, not a
  parameterized module applied six times, or the line saving buys a seconds
  loss.
- **C-39, C-40.** Section 0.1 is a figure that reached a brief and a table
  before anyone checked it. I checked it against the archived probe, which
  is the consumer-side check C-40 asks for.
- **D-30.** The consumer is `L ⊨ GCH` stated in L. I read the delivered
  consumer shape (`ChoiceStatement`, `src/L/Choice/Transversal.lagda.md:372-384`)
  and priced A7 against it, not against Devlin 5.6.
- **C-36.** The lesson is "a failed substitution is not a proof of
  impossibility". I report no impossibility. **Every negative in section 8
  is an absence I measured by grep or a claim I checked against its
  source, and not one rests on a coercion refusal.**
- **C-12.** No Agda process started. Cap not raised. Section 9 states the
  cap for the run I am holding.
- **C-22.** This file was created as a skeleton before any reading and
  filled as answers landed.
- **D-29.** "A shared layer propagates a FIX and a DEFECT at the same
  rate." It qualifies section 7: one shared write-direction helper
  concentrates the route's risk into one place. That is the right trade
  here, and it is a reason to probe the helper before six blocks consume
  it.
- **D-26.** It bears: a stage built as a definable power carries no
  generation data, so its well-founded key needs syntax. That is why
  `src/L/Choice/Name.lagda.md` is a naming order, and it is the structural
  reason A5's built graphs need descriptions rather than keys.
- **R-40.** Not yet exercised. It is a risk for A4, whose least-of runs
  over `⟪ sucV α ⟫`, exactly the presentation R-40 and P-m warn about.
- **C-31, C-32, C-33, C-34, C-37, I-5, D-10.** Read. C-34 is answered:
  section 9 PRICES the cure rather than naming it. C-33 is answered: the
  probe names the OBLIGATION, the write direction, not one entry point.
  The rest do not bear on a gate that builds nothing.
- **DD23.** No mathematical prose written.
- **DD4.** Section 7.

## 13. MACHINE STATE

**Load averages 4.59 / 5.45 / 8.52 at 14:04, four users. MEASURED with
`uptime`.** A `pCloud Drive` process at 52.8 percent and a `Bitcoin-Qt`
process at 33.9 percent are the standing background load.

**`[LJ-1.135]`'s Agda process is live**: `ghc-9.12.3` at 97.6 percent CPU,
started 14:04. **I quote no seconds of my own, because I ran no Agda.**
Every second in this report is a recorded figure from an earlier dispatch
and carries that dispatch's own load, quoted beside it.

## 14. WHAT I AM WAITING FOR

**Only Agda is left. I am waiting for the orchestrator's word that
`[LJ-1.135]` has finished.**

On the word I run section 9's probe, one process, and fill sections 1 and 3
with A5's measured figure. Nothing else in this report changes.
