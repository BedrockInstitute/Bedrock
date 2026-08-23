# `[LJ-1.591]` Is row 2's square the same square as row 5's

**GO. THE OBLIGATION IS INHABITED, AND THE ANSWER TO THE BRIEF'S QUESTION IS NO.**
`agents/tasks/LJ-1-591/Probe591.agda:265-271`.

    one-square-two-rows : P583.SquareCoded → P581.SquareStepInf

**THE TWO ARE NOT ONE OBJECT. ROW 2's IS THE WIDER STATEMENT, AND IT PAYS ROW 5.
ROW 5's DOES NOT PAY ROW 2 WITHOUT ONE FURTHER RESTATEMENT THAT NOBODY HAS
BUILT.** Section `## HOW MANY ROWS ONE SQUARE BUYS` gives the count with the
name of each implication.

**AND THE BRIEF'S OWN GUESS IS WRONG IN ITS DIRECTION.** The brief says "THE
INFINITY CLAUSE IS THE LIKELY DIFFERENCE". It is not. Row 2's square carries NO
side condition at all: no ordinal, no cardinal, no infinity clause. So it cannot
be row 5's step minus one clause. The brief asked me not to agree with it, and I
do not.

## W3, AND IT IS GO

The slice is `agents/tasks/LJ-1-591/runs/W3.agda`, run `runs/w3-1.out`.
**205.69 s real, exit 0, 1.14 GB maximum resident, green on the FIRST run, all
imports cold.** There is no red predecessor.

The question W3 settles is the brief's own: whether the two types can be written
in ONE file at all. **THEY CAN.** The reason is that `LJ-1-583.Probe583` and
`LJ-1-581.Probe581` carry the same module telescope `{ℓ} (lem : LEM (ℓ-suc ℓ))`,
so one `ℓ` and one `lem` serve both, and both types land at `Type (ℓ-suc ℓ)`.
The number measured is 205.69 s and not the brief's estimate of under 2 minutes.
**The brief's estimate was for the Agda, and the price is the two probe chains
behind it**, `Probe583` over `Probe576` over `L.CodedShift` and `L.Absorption`,
and `Probe581` over `Probe556`.

## THE TWO SQUARES

**ROW 2.** `SquareCoded`, `agents/tasks/LJ-1-583/Probe583.agda:195-196`.

    SquareCoded = (κ β : S) → ⟪ fst κ ⟫ ↪ ⟪ fst β ⟫ → InjL κ β

| | value | evidence |
|---|---|---|
| carrier | TWO free L-elements, `κ` and `β`. Neither is an ordinal. | `Probe583.agda:196` |
| pair | **NONE. No pair set occurs in this type.** | `Probe583.agda:196` |
| side conditions | **NONE.** One hypothesis, and it is an AMBIENT injection of the member types. | `Probe583.agda:196` |

**THE NAME IS THE CALL SITE'S AND NOT THE STATEMENT'S.** `[LJ-1.583]` wrote the
type as "the exact remaining ask" at `src/L/SquareLawClosed.lagda.md:109`
(`agents/tasks/LJ-1-583/lj-1.583-report.md:152`), and that site's middle factor
happens to come from a square (`src/L/SquareLawClosed.lagda.md:111-112`).
**The statement itself is not about squares. It is an unrestricted
internalization: every ambient injection between two L-elements yields a code.**

**ROW 5.** `SquareStepInf`, `agents/tasks/LJ-1-581/Probe581.agda:427-432`.

    SquareStepInf =
        (κ : S) → IsOrd (fst κ) → ⟨ ω ∈ fst κ ⟩ → IsCardinalL κ
      → ( (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → ⟨ ω ∈ fst β ⟩
          → Coded β )
      → Coded κ

| | value | evidence |
|---|---|---|
| carrier | ONE free L-element `κ`. | `Probe581.agda:428` |
| pair | `P556.Square.sqL κ`, the L-set of the ordered pairs of `κ`, and it IS the domain of the code: `Coded κ = ∥ Σ[ F ∈ S ] InjCode F (sqL κ) κ ∥₁`. | `agents/tasks/LJ-1-556/Probe556.agda:148-149`, `Probe581.agda:127-128` |
| side conditions | **FOUR.** Ordinal, infinite, L-cardinal, and an induction hypothesis at every infinite ordinal member. | `Probe581.agda:428-431` |

**THE ONE PLACE THE TWO AGREE IS DEFINITIONAL AND IT IS PAID HERE.** Row 5's
conclusion IS row 2's conclusion at the diagonal pair `(sqL κ , κ)`.
`Probe591.agda:132-136` writes both directions and NEITHER has a proof term:
both are `λ x → x`. `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
(`src/L/GCH.lagda.md:37-38`) and `Coded κ` is that at `a := sqL κ`, `b := κ`
(`Probe581.agda:127-128`).

**SIDE CONDITIONS FIRST, AS THE BRIEF ORDERED.** `[LJ-1.585]` found that side
conditions broke the last resemblance. Here the side conditions do not break the
resemblance in the way the brief expected. They are not a mismatch between two
similar statements. **They are the entire content of one side and are absent
from the other.**

## THE IMPLICATION, AND WHERE ITS PRICE SITS

`one-square-two-rows` (`Probe591.agda:265-271`) is three lines. The work is in
`module MakeInit` (`Probe591.agda:197-259`), and the whole of it builds ONE
object: `Init (fst κ)` (`src/L/Ordinal/SquareLaw.lagda.md:692-698`), the
hypothesis of the tree's delivered ambient square law
`via-col-square : (α : S) → Init α → sq α`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`).

**THE TREE'S OWN PROOF OF `Init` CANNOT BE IMPORTED, AND THE REASON IS EXACTLY
THE AMBIENT-AGAINST-CODED SPLIT.** `init-at-kappa`
(`src/L/SquareLawClosed.lagda.md:166-177`) is stated at `fst (κL a oa)`, the
ambient least cardinal, and both of its hard conjuncts reach `κ-min-atL`
(`src/L/SquareLawClosed.lagda.md:86-89`), which refutes an AMBIENT injection.
Row 5's `κ` is arbitrary and carries `IsCardinalL`, which refutes a CODE
(`src/L/Cardinal.lagda.md:230-233`).

**`no-inj` IS THE JOIN, AND IT IS THE ONLY LINE OF THE FILE THAT SPENDS ROW 2's
SQUARE.** `Probe591.agda:206-212`:

    no-inj δ oδ δ∈κ f = cκ δL δ∈κ (sc κ δL f)

Row 2's square turns the ambient injection into a code and `IsCardinalL` refutes
the code. Everything else in `MakeInit` is the tree's own argument transplanted:
conjunct 4 is `src/L/SquareLawClosed.lagda.md:96-115` with `κ-min-atL` replaced
by `no-inj`, and conjunct 3 is `src/L/SquareLawClosed.lagda.md:125-158` with the
same three trichotomy cases and the same two shift injections
(`Probe591.agda:217-256`).

**AND ROW 5's `ih` IS READ DOWN BY `[LJ-1.581]`'s OWN TERM.** Conjunct 4 of
`Init` wants an ambient `sq β`; row 5's `ih` gives `Coded β`. The reading is
`P581.Read.square-from-coded` (`Probe581.agda:203-204`) and it is not rebuilt
here.

**THE BRIDGE.** Row 2's square consumes an ambient injection out of
`⟪ fst (sqL κ) ⟫`, and `via-col-square` delivers one out of
`⟪ fst κ ⟫ × ⟪ fst κ ⟫`. **The reading between them is the OPPOSITE of
`[LJ-1.581]`'s.** `Read.ix→mem` goes index-to-member (`Probe581.agda:165-166`);
this file needs member-to-index, which is `sqL-out` (`Probe556.agda:186`).
`sqL-out` is UNTRUNCATED, so nothing is chosen and no `PT.rec` is spent
(`Probe591.agda:151-177`).

## HOW MANY ROWS ONE SQUARE BUYS

**ROW 2's SQUARE BUYS BOTH ROWS. ROW 5's SQUARE BUYS ONE ROW TODAY AND THE
SECOND ONLY AFTER A RESTATEMENT NOBODY HAS BUILT.** The two counts are not the
same number, so "one square-law task clears two rows" is TRUE of one of the two
squares and not of the other. **Which one the campaign funds decides the count.**

| direction | name | state | evidence |
|---|---|---|---|
| row 2 square pays row 5 | `one-square-two-rows` | **TERM. Unconditional.** | `Probe591.agda:265-271` |
| row 2 square pays row 5 with no side condition | `square-coded→bare` | **TERM.** | `Probe591.agda:286-287` |
| row 5 square pays row 2's site `:109` | `coded-clause4` | **TERM, but its antecedent is a hypothesis.** | `Probe591.agda:325-327` |
| row 5 square pays row 2 outright | none | **NOT INHABITED, AND NOT CLAIMED.** | this report |

**WHAT `coded-clause4` SAYS AND WHAT IT DOES NOT.** `Probe591.agda:321-327`
inhabits

    CodedClause4 = (a κ β : S) → InjL a κ → InjL κ (sqL β) → Coded β → InjL a β

with two applications of `[LJ-1.583]`'s delivered `codedComp`
(`Probe583.agda:169-175`) and no new principle. **So row 5's `Coded β` closes
row 2's site `src/L/SquareLawClosed.lagda.md:109` AS SOON AS that site's
clause-4 hypothesis `f` is stated CODED rather than ambient.** Today it is
ambient: `Init`'s conjunct 4 takes a bare `f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫`
(`src/L/Ordinal/SquareLaw.lagda.md:696-698`).

**DO NOT READ A DISCHARGE INTO THIS.** Restating conjunct 4 of `Init` in coded
form is unbuilt, is not attempted here, and I did not price it. That is a
mathematical judgement and it is not mine (AD3).

**AND `square-coded→bare` IS WHY THE FOUR SIDE CONDITIONS ARE NOT THE
DIFFERENCE.** `Probe591.agda:282-287` shows row 2's square gives `Coded κ` at
EVERY `κ` that has an ambient square, with no ordinal, no cardinal, no infinity
and no induction hypothesis. **Row 5's four side conditions are the price of the
ambient square itself**, paid through `Init` in `MakeInit`, and row 2's square
takes that square as a hypothesis instead of paying for it.

## D-10. PRICE THE TRUTH OF ROW 2's SQUARE BEFORE PRICING ITS PROOF

**THIS IS THE FINDING I MOST WANT THE NEXT BRIEF TO READ, AND IT IS A TERM AND
NOT AN OPINION.**

`[LJ-1.590]` delivered the DOWNWARD reading, unconditionally:
`bare-inj-of : (a b : S) → InjL a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫`
(`agents/tasks/LJ-1-590/Probe590.agda:207-213`). Row 2's square is the UPWARD
one. `Probe591.agda:306-312` puts the two together:

    square-coded→ambient-is-coded : SquareCoded → AmbientIsCoded

**SO ROW 2's SQUARE MAKES "AMBIENT INJECTION" AND "L-CODED INJECTION" THE SAME
RELATION AT EVERY PAIR OF L-ELEMENTS.** A second term says the same thing in the
form the bill cares about: `square-coded→no-collapse` (`Probe591.agda:292-297`)
gives, from row 2's square alone, that **no L-cardinal is ambiently collapsed**.

**NOTHING ON THE FIVE-ROW BILL CLAIMS THAT, AND NO ROW NEEDS IT.**
`agents/tasks/LJ-1-564/Probe564.agda:456` is the bill. Row 5 needs one code at
one `κ`. Row 2's site `:109` needs one factor. **Row 2's square as written
decides an ambient-against-L question at every pair of L-elements.**

**I DID NOT REFUTE IT AND I DO NOT CLAIM IT IS FALSE.** A non-implication is not
writable in Agda and this file does not pretend one. What I measured is that the
statement's consequences are far wider than its one call site, and D-10 says the
five minutes go to the target's truth before the discharge is funded. The
orthodox route does not internalize a bare ambient injection: it internalizes
through CONDENSATION applied to a hull, then reads the ordinal bound off the
collapse (`dev/literature/devlin-II5.md:151-155`). **Row 2's square has no hull
and no collapse in it.**

**AND `[LJ-1.581]`'s REFUTATION DOES NOT REACH ROW 2's SQUARE.**
`squarestep-false` (`Probe581.agda:387`) refutes the form WITHOUT the ω
clause, at `κ := 2`. Row 2's square does not reach that form: `square-coded→bare`
still needs an ambient square at `κ`, and at `κ := 2` there is none.
`Probe591.agda:341-344` records this.

## THE PRICE

| run | file | seconds | maximum resident | exit |
|---|---|---|---|---|
| `runs/w3-1.out` | `runs/W3.agda`, everything cold | 205.69 | 1.14 GB | 0 |
| `runs/p-1.out` | `Probe591.agda`, imports warm from W3 | 2.29 | 484 MB | 0 |
| `runs/p-2.out` | `Probe591.agda`, own interface deleted | 1.96 | 439 MB | 0 |
| `runs/p-final.out` | `Probe591.agda`, after the citation corrections below | 2.14 | 439 MB | 0 |

**GREEN ON THE FIRST RUN OF THE PROBE, GREEN AGAIN WITH ITS OWN INTERFACE
DELETED, AND GREEN AFTER THE CORRECTIONS.** No red predecessor and no bisection.
**THE CORRECTIONS WERE TO COMMENTS ONLY**, and every one was a citation I checked
against its file and found off by a line or two: `via-col-square` is at
`src/L/Ordinal/SquareLaw.lagda.md:960-961` and not near `:1005`,
`square-from-coded` is at `Probe581.agda:203-204`, `squarestep-false` at `:387`,
`codedComp` at `Probe583.agda:169-175`, `bare-inj-of` at
`Probe590.agda:207-213`, `isL-ord` at `src/L/SquareLawClosed.lagda.md:51`, and
`Read.ix→mem` at `Probe581.agda:165-166`. **No term changed.** **NO HEAP EVENT.** The program
set `GHCRTS="-A64m -I0 -M8g"` on this pane; I did not set it, and I ran one Agda
process at a time.

**THE FILE IS 345 LINES AND THE OBLIGATION IS 7 OF THEM** (`Probe591.agda:265-271`).
The brief estimated about 130 lines with about 30 for the obligation. **The
obligation came in FOUR TIMES SMALLER than the estimate and the file came in
larger**, and the reason is the same in both directions: the obligation is one
application of `via-col-square` to an `Init` that `MakeInit` builds in 63 lines
(`Probe591.agda:197-259`), and the rest of the file is the comparison the brief
asked for, in terms rather than in prose.

**THE RATIO BAR CANNOT FIRE ON THIS TASK.** The write scope holds no
`.lagda.md` master under `src/`, so the in-fence line count is 0 and the divisor
does not exist. `Probe591.agda` is a raw `.agda` probe and carries no fence.

## WHAT I DID NOT DO

- **I did not build either square.** `SquareCoded` is a hypothesis at every use
  in the file and `SquareStepInf` occurs only as a conclusion.
- **I did not postulate.** No hole, no postulate, `--safe` on
  (`Probe591.agda:1`).
- **Nothing lands in `src/`.** Every file I wrote is under
  `agents/tasks/LJ-1-591/`.
- **I did not write a coded `Init`.** `coded-clause4`'s antecedent
  `InjL κ (sqL β)` is a hypothesis and nothing in the file supplies it.
- **I did not attempt rows 1, 3 or 4** of `agents/tasks/LJ-1-564/Probe564.agda:456`.
- **I did not commit and did not push.**

**DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** Four types are
named in the file and are hypotheses or conclusions only: `RowTwo`
(`Probe591.agda:121-122`), `RowFive` (`:124-125`), `SquareStepBare` (`:282-284`)
and `CodedClause4` (`:321-323`). Of these, `SquareStepBare` and `CodedClause4`
have terms; `RowTwo` and `RowFive` do NOT.

## WHAT THE NEXT BRIEF NEEDS

1. **ONE SQUARE-LAW TASK CAN CLEAR TWO ROWS, BUT ONLY IF IT TARGETS ROW 2's
   SQUARE.** `one-square-two-rows` is the implication and it is unconditional.
2. **AND ROW 2's SQUARE IS THE ONE WHOSE TRUTH IS UNPRICED.** Section `## D-10`
   gives two terms measuring how wide it is. **Price that before funding the
   discharge.** If it does not survive the price, the surviving route is row 5's
   square plus a coded restatement of `Init`'s conjunct 4, and `coded-clause4`
   is already the term that pays row 2's site from it.
3. **THE ROW-2 RESTATEMENT IS THE UNMEASURED OBJECT.** How much of
   `src/L/SquareLawClosed.lagda.md` must be restated to carry a CODED conjunct 4
   is not measured here and I did not price it.
4. **A HISTORICAL PRICE EXISTS FOR ROW 5's OBJECT AND IT IS LARGE.**
   `[LJ-1.327]` priced a coded square law at about 820 lines and declined it
   (`archive/dev/LJ-dispatch-index.md:382`). That number is from the retired
   route and it does not transfer; a measured cure does not transfer by analogy
   (`AGENTS.md:45`). **It is a warning about the size class and nothing more.**

## THE C-42 SWEEP

**C-42 asks for the COUNT of sites carrying the shape a refutation named, before
the cure is priced. There is no refutation in this task**, so the sweep asks
instead how many sites carry the shape row 2's square would internalize.

`grep -rn "κ-min-atL" src/` returns FIVE occurrences and they are all in one
file:

| line | what it is |
|---|---|
| `src/L/SquareLawClosed.lagda.md:86` | the sealed signature |
| `src/L/SquareLawClosed.lagda.md:89` | the sealed body |
| `src/L/SquareLawClosed.lagda.md:109` | consumer, inside `clause4-at-kappa` |
| `src/L/SquareLawClosed.lagda.md:141` | consumer, inside `kappa-limit` |
| `src/L/SquareLawClosed.lagda.md:156` | consumer, inside `kappa-limit` |

**THREE CONSUMERS, WHICH IS THE COUNT `[LJ-1.576]` GAVE**
(`agents/tasks/LJ-1-576/Probe576.agda:389-391`). `[LJ-1.583]` closed two of them
with `coded-shift-comp` (`agents/tasks/LJ-1-583/Probe583.agda:182-187`).
**So row 2's square has exactly ONE open consumer in `src/`, at
`src/L/SquareLawClosed.lagda.md:109`, and no shape is under-counted.**

**AND THE SAME SWEEP RUN THE OTHER WAY.** `grep -rn "IsCardinalL" src/` returns
NINE occurrences in THREE files: `src/L/Cardinal.lagda.md`, `src/L/GCH.lagda.md`
and `src/L/SquareLawClosed.lagda.md`. That is the coded refutand `no-inj`
(`Probe591.agda:206-212`) spends. If row 2's square lands, every one of those
sites gains the ambient reading through `square-coded→no-collapse`
(`Probe591.agda:292-297`). **So the shape row 2's square touches is nine sites
wide and its one open consumer is one site. That gap is what the D-10 section
asks the next brief to price.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED, THREE ROWS.**
  - `archive/dev/LJ-dispatch-index.md:182` reads
    "| LJ-1.106 | Build Init at the Hartogs cardinal | YES, NO HYPOTHESIS LEFT | 507 lines, 31.2 s, choice-free and LEM-free. sq at the Hartogs cardinal follows from the delivered via-col-square |".
    This is the precedent for section 4: `Init` at ONE named cardinal, then
    `via-col-square`. `MakeInit` does the same at an arbitrary L-cardinal and
    pays the two hard conjuncts from row 2's square instead.
  - `archive/dev/LJ-dispatch-index.md:351` reads
    "| LJ-1.294 | Is an infinite cardinal a limit ordinal | PROVED. kappa-limit | Init's rows 1 to 3 are now available at the use site. Row 4, noinj-squared, has NO term anywhere in src/ |".
    That row is why `MakeInit`'s conjunct 4 is written out and not imported.
  - `archive/dev/LJ-dispatch-index.md:382` reads
    "| LJ-1.327 | Describe the square law's pairing as a FORMULA | EXPENSIVE, ABOUT 820, AND DO NOT FUND IT | pairomega is a well-founded RECURSION, and a coded square law is consumed by NOTHING today |".
    This is the historical size class cited in `## WHAT THE NEXT BRIEF NEEDS`
    item 4, and it is from the retired route.
- `archive/dev/JOURNAL-archived.md`. **SEARCHED, NOT USED.** 29 hits for
  "square", all on the retired route's ambient square law and its seconds.
  `archive/dev/JOURNAL-archived.md:1338` reads
  "the cardinal step consumes is delivered CONDITIONAL on one named bound, the square law (an infinite".
  That is a size and sequencing record for the ambient law. **This task compares
  two CODED statements and neither number transfers.** Declined.
- `archive/dev/JOURNAL.md`. **READ, NOT USED.** `archive/dev/JOURNAL.md:1` reads
  "# ARCHIVED 2026-08-20". The file states at `:10` that "Nothing below is
  current." Declined.
- `archive/dev/DECISIONS-archived.md`. **SEARCHED, NOT USED.** One hit for
  "square", inside D30's craft-freeze narrative at `:50`, which is about check
  cost and the D18 archival. **This task adds no line to `src/` and spends no
  seconds budget.** Declined.
- `archive/dev/DD-archived.md`. **SEARCHED, NOT USED.** ZERO hits for "square".
  The `DD` series is set aside in this form by amendment A7. Declined.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED, in `## D-10`.**
  `dev/literature/devlin-II5.md:154` reads
  "|M| = |L_α|; collapse M to L_γ by condensation; L_α ∪ {x} is transitive, so".
  **This is the orthodox internalization and it is a hull plus a collapse.** Row
  2's square carries neither, which is the reason its truth is unpriced.
- `dev/literature/terms-2026-08.md`. **SEARCHED, NOT USED.** 31 hits for
  "square". `dev/literature/terms-2026-08.md:288` reads "## 8. square law".
  That entry settles the RENDERING of the term for the owner's ruling. **This
  task adds no term and I added no `dev/glossary.toml` entry.** Declined.
- `dev/literature/digest.md`. **SEARCHED, NOT USED.** ZERO hits for "square".
  It pins the orthodox rud route. Not this task's subject. Declined.
- `dev/literature/truncation-and-selection.md`. **SEARCHED, NOT USED.** ZERO
  hits for "square". `sqL-out` is UNTRUNCATED (`Probe556.agda:186`) and this
  file spends one `PT.rec`, at `Probe591.agda:220-222`, on `[LJ-1.581]`'s own
  reading. **No witness is selected anywhere in this task.** Declined.
- `dev/literature/level-formula-slot-roles.md`. **SEARCHED, NOT USED.** ZERO
  hits for "square". No formula is written in this task and no slot is bound.
  Declined.
