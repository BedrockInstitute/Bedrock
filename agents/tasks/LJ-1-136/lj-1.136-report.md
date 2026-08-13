# LJ-1.136 report: gate the remaining A-prime blocks

tier: opus (version `override`). Gate only. **No block was built.** No master
edited. No commit, no push. No probe written yet.

Every claim is marked **MEASURED** (read at the cited line, or a machine
result) or **INFERRED** (my composition or judgement).

**STATUS: BOTH PROBES RUN. PROBE B IS GO, PROBE A IS GO, AND A5 NOW HAS A
SECONDS PROBLEM RATHER THAN A LINES PROBLEM.**
Section 16 holds the result. `src/ProbeLJ1136B.agda`, `--safe`, exit 0,
104 non-blank non-comment lines, **1.27 s upper bound** at load
6.52 / 5.43 / 4.97.

**The orchestrator's question is answered: the injection parameter
discharges, and it is not a STOP.** `pick-canonical`, the term
`[LJ-1.114]` could not write, elaborates.

**The owner ruled that A5 is gated too** (relayed 2026-08-13). Section 9.1
is that gate. **Section 0.1's finding is what sent it**, and section 9.1
turns the finding into a question the machine can answer.

**The orchestrator audited section 0.1 and confirmed every load-bearing
claim, including that its own D-8 citation was wrong.** I record that here
because C-40's point is that the author's own check is blind by
construction, and this return was checked by someone else.

## 0. LEAD FINDING, and it moves two blocks and one basis

**Three things, in order of how much they move the price.**

**(1) A5's basis carries a claim its source does not make, and `dev/LESSONS.md`
C-38 names the error class. MEASURED.**
`[LJ-1.131]:371` writes that `[LJ-1.107]` measured "582
lines for the ambient chain at this site, of which 455 closed
unconditionally". The number 582 is correct
(`agents/reports/lj-1.107-report.md:11-12`, and I re-counted the archived
probe: `agents/reports/LJ-1-107/ProbeLJ1107A.agda` is 582 non-blank lines). **The
number 455 appears nowhere in `[LJ-1.107]`.** It is the sum of the six
per-step line counts in that report's table at `:51-56`
(97+38+103+42+142+33 = 455). **The qualifier "closed unconditionally" is
MEASURED FALSE**: `agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` declares
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
| A4 internal least cardinal and internal `IsCardinal` | 90 to 170 | **190 lines, and see section 17.3 for the seconds** | `[LJ-1.107]`'s ambient `LeastCard` is 38 lines **and 91.98 cold seconds, the dominant term of that probe** (`agents/reports/lj-1.107-report.md:52`, `:59-63`). The internal form replaces the truncated ambient bijection by a truncated L-element bijection, so it needs A2's predicate inside the least-of | **READING.** Raised, and the SECONDS matter more than the lines; section 6 |
| A5 the square-law chain over L-injections | 300 to 450 | **about 590 lines (INFERRED), and about 25 minutes of cold check (INFERRED). Sections 16 and 17** | the band's stated basis is arithmetic-derived and its qualifier is MEASURED FALSE (section 0.1); the block's real content is unmeasured in the direction that matters | **NEITHER.** This is the block that needs the probe. Section 9 |
| A6 `absorbs` as a theorem | 100 to 180 | **150 plus A5's per-construction charge** | `[LJ-1.107]` measured `ShiftAbs`+`Shiftω` at 103 lines and 2.83 s (`:53`), MEASURED and correct as quoted. But that is the AMBIENT injection; the L-element form owes one built graph | **READING.** The quoted basis checks out; the block inherits A5's open charge |
| A7 the internal GCH statement | 80 to 160 | **110** | `ChoiceStatement` with `hasChoiceL` is 13 in-fence lines (`src/L/Choice/Transversal.lagda.md:372-384`), stated wholly at `𝒮ʟ` with no ambient object; `L⊨ZFC` is the shape (`src/L/Model.lagda.md:99`) | **READING.** The consumer shape is delivered and I read it |

**Total of the six priced blocks: 705.** With A5's post-probe figure the
route is about **1,295 lines**, above `[LJ-1.131]`'s 760-to-1,320 band but
inside its top end.

**The line total is no longer the interesting number.** Sections 16 and 17
measured that A-prime's binding constraint is SECONDS, not lines: two
independent sites check at about 2.5 s per line, 168 to 181 times DD24's
current module bar of 0.014367 (`dev/ledger.toml:2685`). **A route that
lands inside its line band and 170 times outside its seconds bar is priced
wrong by whoever quotes only the lines.**

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
`agents/reports/LJ-1-107/ProbeLJ1107A.agda`, the chain builds six:

| built object | where in the archived probe | delivered as an L-element? |
|---|---|---|
| `pairω`, the pairing on `ω` | `:636-637` via `NumeralPresentation` | **NO** |
| the column square `pair` | `src/L/Ordinal/SquareLaw.lagda.md:944-950` | **NO** |
| `ShiftAbs` / `Shiftω`, `sucV γ ↪ γ` | probe step 3 | **NO** |
| `Incl`, the inclusion `β ↪ κ` | probe step 4 | **NO** |
| the `CSB` bijection | `agents/reports/LJ-1-107/ProbeLJ1107A.agda:99-207`, `:489-490` | **NO** |
| composition of two injections | throughout | **NO** |

**MEASURED: `CSB` does not exist anywhere in `src/`.** Zero hits for
`csb`, `bernstein`, `schroeder`, `schröder` over
`src/**/*.lagda.md`. It exists only in `agents/reports/LJ-1-107/ProbeLJ1107A.agda`
and `agents/reports/LJ-1-111/ProbeLJ1111A.agda`. **So A5's basis is not a
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
(`noinj²`, `agents/reports/LJ-1-107/ProbeLJ1107A.agda:472`, `:489-490`, feeding
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
| the qualifier "455 closed unconditionally" in `[LJ-1.131]:371` | **MEASURED FALSE.** `agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` takes the injection as a module parameter |
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
| A5 needs `CSB` at all once leastness is stated over INJECTIONS rather than bijections | **INFERRED, and it is mine.** Section 9.1 tabulates all three `CSB` sites and argues each refutes directly. **It is a hypothesis until Probe B speaks**, and if it holds it is the largest single saving in the route |
| `[LJ-1.107]`'s injection parameter discharges under A-prime | **INFERRED.** It is Probe B's GO criterion, and its failure is Probe B's STOP |
| the Devlin errata touch anything A-prime rests on | **MEASURED FALSE.** Section 10 |

## 9. THE TWO PROBES, WITH BOTH ABORT CRITERIA FIXED BEFORE EITHER RUNS

**The owner ruled that A5 is gated too** (relayed 2026-08-13). That is a
second probe, and this section fixes both in advance, per D-1, so no
criterion can move after a result.

**I have not started Agda.** `[LJ-1.135]` was still building at 14:25
(`agda src/L/Choice/Internal.lagda.md`, seen by the orchestrator). Both
probes are written here in full so that when the machine frees I run and do
not design.

### 9.0 Why there are two, and which runs first

The two probes measure **different** unmeasured terms, and section 3
separated them:

- **Probe B measures the CHAIN**: does `[LJ-1.107]`'s injection parameter
  discharge when the injection is selected from L? It carries the STOP.
- **Probe A measures the OPERATIONS the chain assumes**: putting a function
  into L as an element. It carries the per-construction price.

**Probe B runs first.** Three reasons, and the third is practical.
It carries the STOP, so a red result saves Probe A entirely. It gates the
largest block, which is what the owner ruled. And **it need not import
`L.Coding.Model`**, so it does not depend on a warm interface cache;
`[LJ-1.135]` may have cleared `_build/`, and `[LJ-1.134]` MEASURED that its
own 2.51 s rested on cached interfaces
(`agents/reports/lj-1.134-report.md:60-65`). **A probe whose price is
dominated by someone else's cold tree measures the tree, not the probe.**

### 9.1 PROBE B: `src/ProbeLJ1136B.agda`. Does the parameter discharge?

**The question, exactly.** `agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` declares
`module Chain (inj : ... → ⟪ α ⟫ ↪ ⟪ κ ⟫)`. **Why** is that a parameter?
Because `LeastCard`'s witness is the truncation `∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁` and
`↪` is not an hProp, so `PT.rec` refuses
(`agents/reports/lj-1.107-report.md:96-108`). **MEASURED cause.**

**The cure A-prime claims.** The class of L-elements coding the injection
carries an `SWO`, namely `orderAt`, so `leastOf` extracts an HONEST element
and `isPropLeastOf` (`src/L/WellOrder/Base.lagda.md:136-139`) makes it
canonical. Canonicity is the missing property: `[LJ-1.114]` failed with
`g₂' != g₁`, two independently chosen injections giving colliding codes
(`agents/reports/lj-1.114-report.md:34-45`).

**THE DESIGN QUESTION THE PROBE ALSO SETTLES, and it may remove CSB from
A5 entirely.** INFERRED, and it is mine, so it is a hypothesis until the
machine speaks.

`[LJ-1.107]` states leastness over **bijections** (`κ-min-at` takes
`∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁`). That is why every refutation must manufacture an
equivalence, and that is the only reason `CSB` is in the chain at all:
`agents/reports/LJ-1-107/ProbeLJ1107A.agda:489-490` builds `csb` from two
injections purely to contradict `leastα`.

**State leastness over INJECTIONS instead**, that is, let `κ` be the least
`δ ∈ sucV α` admitting an L-injection `⟪ α ⟫ ↪ ⟪ δ ⟫`. Then all three CSB
sites refute directly:

| site | `[LJ-1.107]` route | injection-leastness route |
|---|---|---|
| `noinj²`, the square clause | compose to `⟪α⟫ ↪ ⟪β⟫`, then **CSB** to an equivalence, then `leastα` | the composite IS an L-injection `⟪α⟫ ↪ ⟪β⟫` with `β ∈ κ`; leastness refutes it directly |
| `succ-closure` | `ShiftAbs` plus inclusion, then **CSB** to `γ ≃ sucV γ` | `ShiftAbs` IS an L-injection `⟪sucV γ⟫ ↪ ⟪γ⟫`; leastness refutes it directly |
| `NonInitial` | `α ↪ κ` from the parameter, `κ ↪ α` by inclusion | both are injections already; no equivalence is wanted |

**If that holds, A5 sheds `CSB` (97 ambient lines, and the single most
expensive object to internalize in section 3.1).** It is the largest single
saving available anywhere in the route, and it costs one design decision.

**The file, in four parts.**

1. **The interface.** `LInj γ a b = Σ[ g ∈ Mem (Lset γ) ] ⟨ IsInjGraph g a b ⟩`,
   with `IsInjGraph` hProp-valued. Three operations as PARAMETERS:
   `lid` (identity), `lcomp` (composition), `lread : LInj γ a b → ⟪ a ⟫ ↪ ⟪ b ⟫`.
   **P-l: every set stays a parameter. No type names `sucV`, `# n` or any
   transparent presentation.**
2. **The canonical selection, and this is the load-bearing step.**
   `select γ a b nonempty = leastOf (orderAt γ) lem (IsInjGraph _ a b) nonempty`,
   then prove
   **`select-canonical : (n₁ n₂ : nonempty) → select γ a b n₁ ≡ select γ a b n₂`**
   through `isPropLeastOf`. **This is the exact term `[LJ-1.114]` could not
   write.**
3. **The chain.** Re-state `LeastCard` over `LInj`, then run
   `[LJ-1.107]`'s `InitialCase`, `NonInitial` and `Chain` at this
   interface, and **declare `Chain` with NO `inj` parameter.** Import no
   `CSB`.
4. **The C-38 guard, and it is why this probe is not vacuous.** An abstract
   interface that nothing satisfies is exactly what `dev/LESSONS.md:3427`
   warns about: "a restatement that nothing can satisfy makes the module
   vacuously true: it typechecks, it is fast, and it proves nothing."
   **So part 4 instantiates `LInj` at the real definition and discharges
   `lread` concretely**, reusing `[LJ-1.134]`'s `toFun` and its Part C
   non-degenerate graph (`src/ProbeLJ1134A.agda:190-289`, `:99-141`).
   `lid` and `lcomp` go to Probe A, and **until all three are instantiated
   A5's figure is a projection and I will label it one.**

**ABORT CRITERIA, fixed now.**

- **GO.** `select-canonical` elaborates AND `Chain` declares without the
  `inj` parameter AND no `CSB` is imported. **Then `[LJ-1.107]`'s
  conditionality was forced by the ambient setting, it discharges under
  A-prime, and A5 is CHEAPER than its 300-to-450 band**, because the chain
  is `[LJ-1.107]`'s 455 step lines minus CSB's 97, plus the interface.
  Report lines, seconds and load.
- **STOP, and this is the one the orchestrator named.** `select-canonical`
  does NOT elaborate. Then the L-least selection fails to be canonical at
  this site, A-prime walks straight back into `[LJ-1.114]`'s `g₂' != g₁`,
  and **the route is refuted, not merely re-priced.** Report the exact
  refusal text and stop. **Do not attempt a repair inside this dispatch.**
- **PARTIAL.** `select-canonical` elaborates but some step still demands an
  equivalence rather than an injection. Then A5 carries internal `CSB`,
  its price moves toward the 1,191-line comparable of section 3.3, and
  **the injection-leastness design above is refuted while the route
  survives.** Name which of the three sites refused.
- **C-36 guard, binding on every negative above.** `dev/LESSONS.md:3284`:
  a type error says the types differ, never that no term connects them.
  **No refusal is reported as impossibility on a coercion failure alone.**
  Each gets its exact text, and each gets one named alternative attempted
  before it is written down.

### 9.2 PROBE A: `src/ProbeLJ1136A.agda`. What does one write-direction cost?

**Runs second, and only if Probe B is GO or PARTIAL.** A STOP makes it
pointless.

1. Take two concrete L-sets and one concrete metatheoretic injection
   between their presentations. Reuse `[LJ-1.134]`'s Part C graph
   (`src/ProbeLJ1134A.agda:190-289`) so the site is not degenerate: that
   report built it precisely because this tree has shipped two vacuous
   frames (`agents/reports/lj-1.129-report.md:334-338`).
2. Write ONE object-language description of "z is the ordered pair of an
   element and its image", with its two adequacy readings, in the shape
   `[LJ-1.134]` used for `injAt` (`src/ProbeLJ1134A.agda:61-93`, 27 lines).
3. Carve the graph out with `hasSeparationL`
   (`src/L/Axioms/Full.lagda.md:277`) and prove the result satisfies
   `svAt`, `domAt` and `injAt`.
4. **Discharge Probe B's `lid` and `lcomp`**: the identity graph on an
   ordinal, and the composite of two graphs in L. These are the two
   operations Probe B leaves open, and `lid` is what supplies the chain's
   non-emptiness at `δ = α`.
5. Round-trip through `[LJ-1.134]`'s `toFun` and check the values agree.

**ABORT CRITERIA, fixed now.**

- **GO.** The round trip elaborates. **Report the line count of ONE
  write-direction, and that figure times the number of constructions Probe
  B leaves standing is A5's construction charge.** Note that Probe B may
  cut that number from six to four by removing `CSB` and its composite.
- **NO-GO.** The description cannot be written, or the separation refuses.
  **A NO-GO does not kill A-prime**, because A2's read direction is already
  GREEN (`[LJ-1.134]`, `--safe`, exit 0). It means A5's band moves toward
  the 1,191-line comparable and A6 inherits the same charge. Report the
  exact refusal.
- **P-w applies to what I write, not only to what I recommend.**
  `dev/LESSONS.md:3094`: a module application COPIES. The helper in step 4
  is a FUNCTION taking its sets as arguments, never a module applied twice,
  so that the probe measures the shape I would actually recommend.

### 9.3 What both probes share, and the discipline on the figures

One agda process at a time. `GHCRTS="-A64m -I0 -M8g"`. **Cap never
raised**; a heap exhaustion is reported as a wall and not worked around.
Both files are `.agda`, both are thrown away, neither is committed
(D-1, and `scripts/check-probes.py` reports clean today).

**Every second I report will be an UPPER BOUND and will carry the load
measured beside it.** The machine has four users and a standing background
load; section 13 records what it was. **If the interface cache is cold
because `[LJ-1.135]` cleared `_build/`, I say so beside the figure and do
not compare it with `[LJ-1.134]`'s 2.51 s**, which was explicitly a warm
assembly figure (`agents/reports/lj-1.134-report.md:60-65`). P-q and P-l
both forbid that comparison.

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

`archive/` proper, **surveyed and used**. **PATH NOTE: a sibling moved
`archive/probes/` to `agents/reports/<task>/` while I was running, so every
citation below carries the NEW path and the probes I read are the same
files.** They hold the retired probes. `agents/reports/LJ-1-107/ProbeLJ1107A.agda` read at `:90-99`,
`:205-206`, `:270-275`, `:455-495`, `:620-666`, and counted whole (582
non-blank, 500 non-blank non-comment). **This is the file that settles
section 0.1**, and reading it rather than the report is why the negative is
MEASURED. `agents/reports/LJ-1-111/ProbeLJ1111A.agda` read at `:28`, `:135-190` for
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
  `agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` holds the injection as a module
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

## 13. MACHINE STATE, AS I MEASURED IT

**Reading phase, 14:04:** load 4.59 / 5.45 / 8.52, four users, and
`[LJ-1.135]`'s Agda live at 97.6 percent CPU. No figure of mine was taken
then.

**Probe phase, 14:37 to 15:07:** the machine was mine. I confirmed it
rather than taking it on trust: `ps aux | grep agda` returned ONE process,
`zsh _build/tools/agda-watchdog.sh`, which is the watchdog and not a
typechecker.

| moment | load (1/5/15) |
|---|---|
| 14:37, before the first run | 4.03 / 4.02 / 4.54 |
| 14:44, Probe B green | 4.53 / 4.71 / 4.69 |
| 14:52, Probe B with the C-38 guard | 6.61 / 5.39 / 4.95 |
| 15:00, Probe A green | 5.83 / 5.62 / 5.28 |
| 15:07, final confirmation | 5.54 / 7.04 / 6.16 |

**Every second in sections 16 and 17 is an UPPER BOUND** and carries the
load beside it. **I ran ONE agda process at a time throughout**, under
`GHCRTS="-A64m -I0 -M8g"`, and **the cap was never raised**, including
across three heap exhaustions.

**THE CACHE STATE, which I checked rather than taking on trust.** 300
`.agdai` files present at 14:37, and I verified by name that
`L/Coding/Model`, `L/Choice/Step`, `L/WellOrder/Base`, `L/Constructible`
and `L/Choice/Stage` were all PRESENT. **That matches what `[LJ-1.135]`
reported**, and it is why section 9.3's bar is met: my figures and
`[LJ-1.134]`'s 2.51 s are both warm-assembly figures over the same cached
tree, so they are comparable. `src/ProbeLJ1134A.agdai` was also present,
built 13:43, which is why Probe B could import it cheaply.

## 14. WHAT REMAINS, AND IT IS ONE QUESTION FOR THE OWNER

**Nothing is waiting on me.** Both probes ran and both are GO.

**The one open question is not a measurement, it is a ruling.** Section
17.4 measured that A-prime's write direction runs at about 2.59 s per line
and `[LJ-1.107]`'s `LeastCard` at 2.42, both about 170 to 180 times DD24's
current module bar. **The route works. Whether the project accepts it at
that rate is DD24's question and it belongs to the owner, not to me.**

**The one measurement I would run next**, named rather than guessed
(C-34): can two L-graphs be composed WITHOUT a second `hasReplacementL`?
If yes, A5 pays the 254 s once or twice instead of six times, and the
seconds problem shrinks by a factor of three. Section 17.5 states it.

**The CSB question is still NOT REACHED**, and section 16.5 marks it. My
claim that injection-based leastness removes `CSB` from the chain stays
INFERRED.

## 15. WORKING TREE, AS MY REPORT DESCRIBES IT

**No master edited. No commit, no push.** No `git checkout`, `stash`,
`reset` or `clean` was run at any point. Three siblings hold uncommitted
work and I touched none of it.

**My additions:** `agents/reports/lj-1.136-report.md`, and two probes,
`src/ProbeLJ1136A.agda` and `src/ProbeLJ1136B.agda`. **Both probes are
untracked and ignored** (`git check-ignore` confirms `.gitignore:27`,
`src/Probe*.agda`), and `scripts/check-probes.py` reports clean.
**Neither is committed and both are throwaway, per D-1.**

`src/ProbeLJ1134A.agda` is unmodified at 12,996 bytes. Probe B imports it;
it does not edit it.

**A PATH CHANGE HAPPENED UNDER ME.** A sibling moved `archive/probes/` to
`agents/reports/<task>/` mid-dispatch. **I re-pathed all fourteen affected
citations in this report and the two in Probe B**, and verified the target:
`agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` still reads
`module Chain (inj : ...)`. **The evidence is unchanged; only its address
moved.**

Linters: `lint-prose.py --check` exit 0 on the report; `lint-agda.py
--check` exit 0 on both probes. Neither probe contains a `postulate`, a
`TERMINATING` pragma or a hole, and both carry `--safe`.

## 16. PROBE B RESULT: GO. THE PARAMETER DISCHARGES

**Ran 2026-08-13 from 14:41. `src/ProbeLJ1136B.agda`, `--safe`, exit 0,
zero postulates, zero holes, `lint-agda.py --check` exit 0.**
185 non-blank lines, **104 non-blank non-comment lines**.
One agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, **cap never
raised**.

### 16.1 The verdict, against the criterion fixed in section 9.1

**GO.** All four parts elaborate.

| part | what it proves | result |
|---|---|---|
| 1. `pick-canonical` | the `<_L`-least selection does not depend on WHICH proof of non-emptiness reached it | **GREEN** |
| 2. `discharge` | a term of `Chain`'s parameter shape, PRODUCED from a truncated existence | **GREEN** |
| 3. `agree` | the produced injection is canonical, so two demands in one induction return the same function | **GREEN** |
| 4. `Witness`, `WitnessZero` | the interface is INHABITED at a concrete non-degenerate graph | **GREEN** |

**`agents/reports/LJ-1-107/ProbeLJ1107A.agda:630` assumed
`inj : ... → ⟪ α ⟫ ↪ ⟪ κ ⟫` as a module parameter. Probe B produces a
term of that shape.** The cause of the assumption was MEASURED at
`agents/reports/lj-1.107-report.md:96-108`: the witness is a truncation
and `↪` is not an hProp. **`leastOf` over `orderAt` supplies exactly the
missing propositional character**, because `isPropLeastOf`
(`src/L/WellOrder/Base.lagda.md:136-139`) makes the selected element
unique.

**So `[LJ-1.107]`'s conditionality was forced by the ambient setting, and
A-prime removes it.** MEASURED.

### 16.2 The C-38 guard, and why it is not decoration

C-38: "a restatement that nothing can satisfy makes the module vacuously
true: it typechecks, it is fast, and it proves nothing"
(`dev/LESSONS.md:3427`). **Parts 1 to 3 alone would have been exactly
that.** Part 4 instantiates the whole interface at `[LJ-1.134]`'s concrete
graph `{<a,a>}` with domain `{a}`, proves the fourth conjunct rather than
assuming it, and `WitnessZero` fixes `a` at `numeralL 0`.
**`theInjection` and `theInjection-inj` are honest functions at a concrete
site, so nothing above them is vacuous.**

### 16.3 A DESIGN CORRECTION the probe forced, and it is a real finding

`[LJ-1.134]` section 2.6 left the range obligation unpriced and stated it
OUTSIDE the selection (`src/ProbeLJ1134A.agda:303-304`, a hypothesis of
`Small`). **Probe B moves it INSIDE the selection predicate**, as a fourth
conjunct of `Good`.

**Why it matters, and it is not cosmetic.** With the range condition
outside, `discharge` needs an argument `Ran (pick h)` about the SELECTED
graph, which no caller can supply because the selection is abstract. Every
downstream consumer would carry it. **Inside, the selected graph carries
its own range condition and `discharge` takes the non-emptiness and
nothing else.** MEASURED: `discharge : Ne → Σ[ f ] injective`, one
argument.

### 16.4 TWO HEAP WALLS, BOTH MEASURED, AND BOTH CURED

**This is the most transferable thing in the probe, and it prices A5's
craft rather than its mathematics.** C-12: a heap exhaustion is reported as
a wall and the cap is never raised. I raised nothing.

| what | seconds | result |
|---|---:|---|
| **two `Small` module applications, unsealed** | 138.52 | **Heap exhausted at 8g** |
| one `Small` application, unsealed | 2.01 | GREEN |
| `Data≡` alone, no `agree` | 1.34 | GREEN |
| `agree-generic`, consumer ABSTRACT | 1.36 | GREEN |
| **`agree` instantiated at `injOf`, unsealed** | 98.42 | **Heap exhausted at 8g** |
| **the same file with `injOf` sealed `opaque`** | 1.27 | **GREEN** |

**Reading 1, P-w, MEASURED at this site.** `dev/LESSONS.md:3094` says a
module application COPIES and only fewer applications, fewer definitions
per application, or cheaper types reduce the cost. **Here the difference
between two applications and one is the difference between an exhausted
8g heap and 2.01 s.** Section 7 recommended the shared write-direction
helper be a FUNCTION rather than a module applied per site. **That
recommendation is now measured, not inferred.**

**Reading 2, and it is the stronger one.** The generic statement costs
1.36 s and the instantiation costs an exhausted heap. That is P-m's
content-class law showing up as a cliff rather than a slope
(`dev/LESSONS.md:2460`). **The cure is the tree's own: seal it.**
`orderAt` is `opaque` for precisely this reason
(`src/L/Choice/Step.lagda.md:744`). Sealing `injOf` brought the file to
1.27 s **with both `Small` applications restored**.

**THE CONSTRAINT ON A5, and it is a hard one. MEASURED.**
**Every injection A5 derives from a selected graph must be sealed at the
point it is defined.** Unsealed, the chain does not merely run slowly; it
does not check at all under C-12's cap. **No line count reveals this**, and
it is exactly the class of cost DD24 measures in seconds rather than lines.

### 16.5 What Probe B did NOT settle, and I mark it

**The CSB question is NOT answered.** Section 9.1 tabulated three sites
where injection-based leastness would refute directly and remove `CSB`
from the chain. **Probe B proves the selection and the discharge; it does
not run `InitialCase`, `NonInitial` or `succ-closure`.** So the verdict on
section 9.1's PARTIAL branch is **NOT REACHED**, and my claim that A5 sheds
`CSB` remains **INFERRED**. It stays in section 8's table as a hypothesis.

**What Probe B does establish about it**: the input those three sites need,
an honest canonical injection out of a truncated L-existence, is delivered.
Whether they then close without an equivalence is a separate measurement
and it is the next probe, not this one.

### 16.6 What this does to A5's price

**I still decline a single figure, and the reason has changed.**

Before Probe B, A5 was unpriced because its basis was arithmetic with a
false qualifier (section 0.1). **Now the conditionality is MEASURED to
discharge**, which removes the largest risk, and two of the three `CSB`
sites are the only thing standing between A5 and a figure.

**What is now MEASURED for A5:**

- the discharge apparatus: **104 non-blank non-comment lines**, of which
  the selection and canonicity are about 20 and the rest is interface and
  the non-vacuity witness;
- the seal is mandatory, and it costs nothing in lines;
- `[LJ-1.107]`'s chain content: 455 step lines, of which `CSB` is 97.

**What is still INFERRED:** whether those 97 lines leave. **That is a one-
probe question and it is the next gate**, not a band centre I should write
down now. DD8 says one best-effort figure with its basis; the basis for
A5 is one measurement away and I would rather name the measurement.


## 17. PROBE A RESULT: GO ON LINES, AND A 254-SECOND WARNING

**Ran 2026-08-13 from 14:56. `src/ProbeLJ1136A.agda`, `--safe`, exit 0,
zero postulates, zero holes, `lint-agda.py --check` exit 0.**
140 non-blank lines, **98 non-blank non-comment lines**.
One agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

### 17.1 The verdict

**GO, against the criterion fixed in section 9.2.** The write direction
works. `src/ProbeLJ1136A.agda` builds the **identity graph on an arbitrary
L-set as an element of L**, through `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:277`), and proves **all four conjuncts** of
Probe B's selection predicate: `sv`, `ij`, `dm` and `ran`.

**Why this construction and not another.** It is the one that supplies the
chain's non-emptiness. The least-cardinal search needs to know that `α`
injects into itself CONSTRUCTIBLY before `leastOf` has an input at all, and
the identity graph is that witness. It is also the simplest of section
3.1's six, so it is a LOWER bound on the others.

**The description cost is small and it lands on the cheap comparable.**
The formula is `prAtL zero (suc zero) (suc zero)`, ONE delivered formula
(`src/L/Coding/Model.lagda.md:122`), and the whole obligation is
functionality: `fc`, six lines. **Section 3.3 asked whether A5 lands nearer
`[LJ-1.134]`'s 27-line comparable or `L/Choice/Table`'s 1,191-line one.
MEASURED: nearer the cheap one. 98 lines for a complete write direction
with all four conjuncts.**

### 17.2 THE SECONDS, and they are the finding

**254.22 s cold, at load 5.83 / 5.62 / 5.28, on a machine with no sibling
Agda running.** That is the whole file.

**A free bisection, from the run that failed.** Run 2 errored at line 139,
the first conjunct, after **250.71 s**. Everything before that line is the
graph construction. So:

| part | seconds | share |
|---|---:|---:|
| the graph construction, through `hasReplacementL` | 250.71 | **98.6 percent** |
| all four conjuncts, `sv` `ij` `dm` `ran` | 3.51 | 1.4 percent |
| whole file | 254.22 | 100 percent |

**MEASURED: the cost is the REPLACEMENT, not the description and not the
proofs.** Putting one set into L costs about four minutes at this site,
and the mathematics on top of it is free by comparison.

### 17.3 The rate, against the bar that is actually current

The orchestrator is right that my A4 figure needed restating, and the
restatement changes which comparison is honest.

**`dev/ledger.toml:2685` now carries `ac_baseline_module_rate = 0.014367`
over `ac_baseline_module_lines = 20286`.** That is the per-module rate and
it is the right bar for a single new module, which is what A2 to A7 each
are. The older `ac_baseline_seconds_per_line = 0.008793` (`:2564`) is the
whole-tree cone rate and it is NOT the right comparison for one module.

| what | seconds per line | against `0.014367` |
|---|---:|---:|
| DD24 module bar (`dev/ledger.toml:2685`) | 0.014367 | 1x |
| P-m parameterized class (`dev/LESSONS.md:2460`) | about 0.01 | 0.7x |
| P-m instantiation class | about 0.22 | 15x |
| **Probe B**, the discharge | 1.27 s over 104 lines = **0.0122** | **0.85x, INSIDE the bar** |
| `[LJ-1.107]` `LeastCard`, 91.98 s over 38 lines | **2.42** | **168x** |
| **Probe A**, the write direction, 254.22 s over 98 lines | **2.594** | **181x** |

**My earlier A4 figure said 306x against 0.0079. Against the correct
current bar it is 168x. The conclusion does not change and the number
does**, exactly as the orchestrator predicted.

**And Probe A measures WORSE than `LeastCard`.** Two independent sites in
this route now sit near 2.5 s per line, about 170 to 180 times DD24's
module bar and more than ten times even P-m's instantiation class.
**MEASURED, twice, at two different constructions.**

### 17.4 What this does to A5, and it is not what section 3 expected

Section 3 predicted A5's risk was LINES: six constructions times an unknown
per-construction line cost, bracketed between 27 and 1,191.

**Both probes refute that framing. MEASURED.**

- **The lines are fine.** One complete write direction is 98 lines, near
  the cheap comparable. Six of them is about 590 lines, and several are
  cheaper than the identity graph because they compose rather than build.
- **The seconds are not.** One write direction is 254 s. **Six of them,
  naively, is about 25 minutes for A5 alone**, against DD24's bar of about
  8.5 s for 590 lines. **INFERRED by multiplication, and P-l says a
  multiplication is not a measurement.** But the per-site figure is
  measured twice and both times near 2.5 s per line.

**So A5's gate has moved from "can it be written" to "can it be written at
a rate the project accepts".** That is a DD24 question, not a D-8 one, and
it is the question I would put to the owner.

### 17.5 The cure I would probe next, and why I did not probe it here

**Do not build six graphs. Build ONE and compose.** Probe A's 254 s is
`hasReplacementL` at one site. If composition of two L-graphs can be
written WITHOUT a second replacement, by separation over a product already
in L, then A5 pays the replacement once or twice rather than six times.

**That is the next probe and it is not this one.** I name it rather than
guess it, per C-34: a return that names a cure prices it or reports the
wall that stops it. The wall here is budget, not mathematics.

**P-w is already banked as part of the cure.** Section 16.4 measured that
the shared helper must be a FUNCTION, not a module applied per site;
applied twice unsealed it exhausted an 8g heap.
