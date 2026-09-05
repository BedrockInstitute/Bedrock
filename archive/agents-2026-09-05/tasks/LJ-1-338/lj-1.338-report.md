# LJ-1.338 report: a THIRD tie site, to tighten 250 to 350

tier: opus (in-harness-subagent-mode). Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**THE THIRD SITE IS 234 NON-BLANK LINES, AND THAT IS A THIRD NUMBER.**
Site 1 measured 51, site 2 measured 42, site 3 measures **234** on the
same caliber. **The seven's ambient tie supply is 327 lines, MEASURED at
three sites and no longer an extrapolation**, because the third site
CONTAINS the other four unmeasured modules.

**THE RANGE COLLAPSES ON ITS OWN TERMS AND THE DEBT CHANGES KIND.** The
250 to 350 range was right on magnitude and wrong on shape. The debt is
not seven similar blocks. **It is three blocks of very different size,
51, 42 and 234, and 51 of the third site's 234 lines are RESIDUE: tie
STATEMENTS that no closure argument discharges, at either carrier.**

**`KValue` TRANSPORTS, AND THAT IS THE BEST OUTCOME THE BRIEF NAMED.**
`src/L/Condensation.lagda.md:7264-7318` copies to the ambient carrier at
**0 changed lines of 50**, behind an adapter of **15 code lines**.
MEASURED, by alignment.

**THE REMAINING FOUR DO NOT NEED FOUR MEASUREMENTS.** `LeafAgree`
instantiates `WitnessAgree`, `KeyAgree`, `SatGraphAgree` and
`DefinesAgree` inside itself (`src/L/Condensation.lagda.md:7191-7209`),
and my green run forced all four. **One measurement covered five
modules.** MEASURED.

| site | module | ties | figure | basis |
|---|---|---|---:|---|
| 1 | `DomainAgree` | 2 | 51 | `[LJ-1.302]`, MEASURED |
| 2 | `EnvOneAgree` | 3 | 42 | `[LJ-1.336]`, MEASURED |
| **3** | **`LeafAgree`** | **`KFacts` + 14 ties + 2 non-ties** | **234** | **here, MEASURED** |

**Runs.** `ProbeKValue338.agda` exit 0 in 9 s. `ProbeLeaf338.agda` exit 0
in 40 s. Three controls, all RED at the right line. No wall; the longest
invocation was 40 s. One Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap
never raised.

## 1. THE SITE I PICKED, AND WHY

**I picked `LeafAgree`, `src/L/Condensation.lagda.md:7107-7243`.**

**Reason 1, DD8: it is the widest unmeasured term.** It carries
`f : KFacts` and fifteen more parameters, against `DomainAgree`'s two
ties and `EnvOneAgree`'s three.

**Reason 2, and this is the one that decides: `LeafAgree` is the UNION
site.** It proves nothing about its own ties. It hands them to four other
modules of the seven, at `:7191-7209`:

| consumer | line | what it gets |
|---|---|---|
| `WitnessAgree` | `:7191-7198` | `f`, `witK`, `wCodesK`, `wUnCodesK`, `wEntryK` |
| `KeyAgree` | `:7200-7201` | `f .tagEq1`, `f .numK1`, `keyValK` |
| `SatGraphAgree` | `:7203-7205` | `f`, the two twelve readings, `gCodesK`, `gUnCodesK`, `gEntryK`, `domEntryK`, `domK`, `graphWitK` |
| `DefinesAgree` | `:7207-7209` | `f .tagEq0`, `f .numK0`, `envK`, `defPairK`, `satK` |

**So a measurement at `LeafAgree` prices FOUR of the five unmeasured
modules at once.** MEASURED twice: by reading `:7191-7209`, and by the
green instantiation at `agents/tasks/LJ-1-338/ProbeLeaf338.agda:353-356`,
which forces all four applications.

**Reason 3: its first tie is exactly `KValue`'s output**, so the site
also tests the brief's best-outcome branch.

### What I did NOT pick

- **`TagAgree` (`:6670-6698`), the brief's suggestion.** It is a wave 1
  CLEAN module and it is NOT one of the seven that 250 to 350 prices, so
  a figure there cannot move that range. Its two ties, `tagEq` and
  `numK`, are a strict subset of `EnvOneAgree`'s three, already measured.
  **Section 6 answers the brief's premise about it by reading, at no Agda
  cost, and the premise is FALSE as stated and TRUE in substance.**
- **`KeyAgree` (`:6699-6747`) and `DefinesAgree` (`:6778-6834`).** Both
  are instantiated inside `LeafAgree`, at `:7200` and `:7207`, so site 3
  measures them.
- **`SatGraphAgree` (`:6844-7097`).** Also inside `LeafAgree`, at
  `:7203`.
- **`WitnessAgree` (`:6576-6657`).** Also inside, at `:7191`.

## 2. `KValue` AT THE AMBIENT CARRIER: IT TRANSPORTS

**`agents/tasks/LJ-1-338/ProbeKValue338.agda`, exit 0, cold 9 s,
reload 4 s.**

**THE 50 LINES OF `module KValue` TRANSPORT AT 0 CHANGED LINES.** I
copied `src/L/Condensation.lagda.md:7264-7318` below a marker at
`ProbeKValue338.agda:92-95` and changed nothing.
`agents/tasks/LJ-1-338/count338.py` aligns the copy against the chapter
span with `difflib.SequenceMatcher`, `autojunk=False`, the method
`[LJ-1.308]` wrote and `[LJ-1.336]` re-used: **50 expected non-blank
lines, 0 delete, 0 replace.** MEASURED.

**THE PRICE IS AN ADAPTER OF 15 CODE LINES**, at
`ProbeKValue338.agda:65-90`:

| name | L class home | ambient re-spelling | code lines |
|---|---|---|---:|
| `numeralL` | `L.Axioms.Numerals` | `# k , tt*` | 2 |
| `LsetS` | `src/L/Axioms/Basic.lagda.md:160-161` | `Lset β , tt*` | 2 |
| `module Bound` | `src/L/Coding/Bound.lagda.md:130-145` | `num∈λ` and `prʟ∈λ` pushed through the ambient sort | 11 |

**`Bound` itself is NOT re-proved.** `BoundOver`
(`src/L/Coding/Bound.lagda.md:41-56`) is already generic in the tower and
in the sort. Only `Bound`'s two L presentations, `num∈λ` at `:139-140`
and `prʟ∈λ` at `:142-145`, name the L sort. `num∈λ` re-spells as one call
of `B0.#∈Tλ`; `prʟ∈λ` re-spells as one `subst` along `prʟ-fst`. **The
mathematics was already generic and only the presentation was
class-bound.** MEASURED.

**With the six `open` lines the block needs, the head is 21 lines against
the chapter's own four opens at `:7259-7262`.** So the delta is **17
lines**, and the 50 lines of the value are FREE.

**A fact the brief did not carry, and it changes how to read the
transport.** **`KValue` has ZERO consumers anywhere in `src/`, including
inside its own chapter.** MEASURED, by grep for `KValue` over `src/`:
one hit, its own declaration at `:7264`. **So the L side built the value
and never wired it.** The ambient debt is not「redo what L already
did」. It is the same unwired block at a second carrier.

## 3. THE THIRD FIGURE: 234 NON-BLANK LINES

**`agents/tasks/LJ-1-338/ProbeLeaf338.agda`, exit 0, 40 s.** It builds
`LeafAgree` at a concrete ambient environment, with `n := 9`, indices in
`Fin 14` and an environment of 17 slots whose last fourteen are
`KValue`'s own `Kenv` (`:145-148`).

**THE CALIBER IS THE SIBLINGS', RE-DERIVED TODAY (C-44).** Site 1's 51 is
`ProbeLJ1302B.agda:81` to end of file, non-blank. Site 2's 42 is
`ProbeTies336.agda:94-145`, non-blank. Site 3's figure is
`ProbeLeaf338.agda:112-366`, non-blank. **I re-ran the first two counts
and both reproduce, 51 and 42.** MEASURED, by
`agents/tasks/LJ-1-338/breakdown338.py` and the inline count in the run
log.

| span of site 3 | line range | non-blank | code |
|---|---|---:|---:|
| `Supply` head, the bound and the carrier | `:112-115` | 4 | 4 |
| **residues 1 and 2, in the telescope** | `:116-128` | **13** | 9 |
| environment, `KFacts` lift, the shared block | `:129-180` | 45 | 37 |
| **the ten SUPPLIED ties** | `:181-313` | **122** | 82 |
| **residues 3 to 6 and the two twelve readings** | `:314-352` | **38** | 25 |
| instantiation and the two ambient crossings | `:353-366` | 12 | 12 |
| **TOTAL, the site 1 and site 2 caliber** | `:112-366` | **234** | 169 |
| of which SUPPLY, residues excluded | | **183** | 135 |
| of which RESIDUE | | **51** | 34 |

**THE `KFacts` TIE AND THE TEN SUPPLIED TIES, AND WHAT EACH COSTS.** Every one is
type-VERBATIM from the chapter telescope, so the supply meets the tie the
chapter states, not a weaker one.

| tie | chapter | supplied by | cost |
|---|---|---|---|
| `f : KFacts` | `:7109-7115` | `KValue`, lifted three times by `KFactsCons` | 8 code lines |
| `wEntryK` | `:7135-7138` | `pairDown`, one call | 1 |
| `wCodesK` | `:7122-7128` | `pairDown`, three calls, plus RESIDUE 1 | 9 |
| `wUnCodesK` | `:7129-7134` | `pairDown`, two calls, plus RESIDUE 2 | 8 |
| `gCodesK` | `:7145-7152` | `wCodesK` at the `d` slot | **1** |
| `gUnCodesK` | `:7153-7159` | `wUnCodesK` at the `d` slot | **1** |
| `gEntryK` | `:7160-7163` | `wEntryK` at the `d` slot | **1** |
| `domEntryK` | `:7164-7167` | `wEntryK` at the `e` slot | **1** |
| `domK` | `:7168-7170` | `KFacts.arityK`, one call | 1 |
| `keyValK` | `:7181-7182` | the tag reading and one `pairDown` | 6 |
| `satK` | `:7187-7189` | `KFacts.carrierK`, one call | 1 |

**THE GRAPH FRAME COSTS ONE LINE PER TIE.** `gCodesK`, `gUnCodesK`,
`gEntryK` and `domEntryK` are the witness-frame ties read at the `d` and
`e` slots, so each is one application (`ProbeLeaf338.agda:235-264`).
MEASURED. **That is the largest single compression in the site, and the
brief's about-10-per-module rate does hold for these four.**

**WHERE THE 122 LINES GO.** 82 of them are code, and 40 of the 122 are
comment lines naming the chapter source of each type. The types
themselves are the bulk: `wCodesK`'s statement alone is 7 lines and its
proof is 9.

## 4. THE RESIDUE, AND IT IS A THIRD KIND OF DEBT

**FOUR TIES OF `LeafAgree` HAVE NO SUPPLIER AT EITHER CARRIER, AND FOUR
MORE ARE SUPPLIED ONLY UP TO ONE CONJUNCT.** They stay parameters of my
probe, named, at `ProbeLeaf338.agda:116-128` and `:315-352`.

| residue | tie | what it says | why closure cannot give it |
|---|---|---|---|
| 1 | `wCodesK`, `gCodesK` last conjunct | the arity of a binary code is a numeral | it is a fact about the CODE SET, not about the bound |
| 2 | `wUnCodesK`, `gUnCodesK` last conjunct | the same, unary | the same |
| 3 | `witK` (`:7116-7118`) | the witness set is inside the bound | the hypothesis puts the CODE inside `w'`, which is downward; the conclusion is upward |
| 4 | `graphWitK` (`:7171-7180`) | the clause set and the graph are inside the bound | the same, for two of its three components |
| 5 | `envK` (`:7183-7184`) | the one-entry environment is inside the bound | its entry `z` carries NO hypothesis, so the tie climbs from an unbounded set |
| 6 | `defPairK` (`:7185-7186`) | the tagged pair over that same `z` | the same |

**THIS IS THE FINDING THE BRIEF ASKED FOR.** `[LJ-1.336]` measured two
debts, a DOWNWARD one and an UPWARD one. **Site 3 measures a THIRD: a
CONSTRUCTION debt.** It says「this set is inside the bound because the
construction built it there」and「this component is a numeral because
the coding put one there」. **Neither `[LJ-1.302]`'s downward block nor
`[LJ-1.336]`'s `Bound` states anything of that form.** MEASURED, by the
supply that exits 0 with exactly these six left over.

**RESIDUES 5 AND 6 MAY BE FALSE AS STATED, AND D-10 SAYS TO PRICE THAT
BEFORE PRICING THE PROOF.** `envK` and `defPairK` quantify over `z` with
no hypothesis that bounds it, and conclude that a set BUILT over `z` is
inside the bound. **A `z` outside the bound refutes them.** **INFERRED,
by reading `:7183-7186`. I did not build the counterexample and I did not
run Agda on it.** **Nobody has ever met these two, because `LeafAgree`
has zero consumers in `src/`** (MEASURED, by grep: `LeafAgree` appears
only at its own declaration). **A brief that funds the residue must price
the TRUTH of these two first.**

## 5. THE SHARING, AGAINST BOTH MEASURED SITES

**SITE 3 SHARES WITH BOTH, AND THAT IS THE OPPOSITE OF WHAT SITES 1 AND 2
DO WITH EACH OTHER.** `[LJ-1.336]` measured the sharing between sites 1
and 2 at ZERO. Site 3 needs both suppliers.

| against | what site 3 reuses | at | how much |
|---|---|---|---|
| site 1, `[LJ-1.302]` | `x∈pair`, `y∈pair`, `pair∈pr`, imported unchanged | `ProbeLJ1302B.agda:97-108`, used at `ProbeLeaf338.agda:132` and `:172-179` | **10 non-blank lines, MEASURED** |
| site 2, `[LJ-1.336]` | `L.Coding.Bound`'s `Bound`, the upward supplier site 2 introduced | `src/L/Coding/Bound.lagda.md:130-145`, through the adapter at `ProbeKValue338.agda:77-90` | the whole supplier |

**What site 3 does NOT reuse from site 1: everything else.** Site 1's
`Ltr` (`:93`), `entryK` (`:113-122`), `domK` (`:125-127`) and its
three-slot environment are all unused here, because site 3's transitivity
comes from `Bound.trans∈λ` at the bound itself and its ties are stated at
a 17-slot environment. **MEASURED, by what the file names.**

**THE SHARED BLOCK IS 4 LINES AT SITE 3.** `pairDown`
(`ProbeLeaf338.agda:172-179`) wraps site 1's three lemmas and
`Bound.trans∈λ` into one downward step, and **six of the ten supplied
ties are one or two calls of it**. That is the same shape `[LJ-1.302]`
predicted for its own site and `[LJ-1.336]` refuted BETWEEN sites: **the
shared block is real WITHIN the downward family and absent BETWEEN
families.**

**SO THE THREE FIGURES DO NOT ADD BLINDLY.** 51 + 42 + 234 = 327, and 10
of those lines are site 1's, reused rather than rewritten. **327 is the
seven's ambient tie supply as far as closure can build it, MEASURED at
three sites, of which 51 lines are residue statements and 6 ties are
unpaid.**

## 6. THE BRIEF'S PREMISE ABOUT `TagAgree`

**The brief flagged it: 「`TagAgree`'s tie may be free because wave 1
ported it clean」.**

**FALSE AS STATED, MEASURED.** Wave 1's port changed nothing about ties.
「Clean」means the module's TYPES named no committed delivery, which the
brief itself says. `TagAgree`'s telescope at
`src/L/Condensation.lagda.md:6670-6672` carries `tagEq` and `numK`
exactly as the dirty modules carry theirs, and porting it did not
discharge them.

**TRUE IN SUBSTANCE, AND FOR A BETTER REASON, MEASURED.** The chapter's
own consumer supplies both from the `KFacts` record: `LeafAgree` gives
`KeyAgree` its two ties as `(f .tagEq1) (f .numK1)` at
`src/L/Condensation.lagda.md:7200-7201`, and `DefinesAgree` its two as
`(f .tagEq0) (f .numK0)` at `:7207-7209`. **`KFacts` holds twelve
`tagEq` fields and twelve `numK` fields (`:6079-6102`), and `KValue`
supplies all twenty-four.** **So the whole `tagEq`/`numK` family costs
NOTHING beyond `KValue`, and `KValue` transports at 0 changed lines.**
**The upward family IS cheaper than site 2's 42 suggested, which is what
the brief guessed, but the reason is `KValue`, not wave 1.**

## 7. THE NEGATIVE CONTROLS

**THREE CONTROLS, EACH A ONE-LINE EDIT, ALL RED AT THE RIGHT LINE.**
`agents/tasks/LJ-1-338/control338.py` builds them and prints the changed
line count, which is 1 for each.

**CONTROL A, LOCALITY INSIDE THE COPIED BLOCK.**
`ControlA338.agda` changes one field of the VERBATIM copy of `KValue`,
`numK0 = B.num∈λ 0` to `B.num∈λ 1`. **Exit 42 in 4 s, and Agda refuses at
`ControlA338.agda:133.15-24`, which is that field, with `UnequalTerms`.**
**The refusal is INSIDE the copied block**, so the copy is not decoration.
MEASURED.

**CONTROL B, THE CODE SLOT IS SPECIFIC.** `ControlB338.agda` degrades
site 3's code slot from `prʟ (numeralL 1) (numeralL 0)` to `numeralL 0`.
**Exit 42 in 5 s, refused at `ControlB338.agda:143.10-75`**, the proof
that puts the code slot inside the bound. MEASURED.

**CONTROL C, NON-VACUITY OF THE TIE.** `ControlC338.agda` changes the TAG
the inhabitant claims, from one to two, and touches nothing else. The tie
`keyValK` is unchanged and still true; only the WITNESS dies. **Exit 42
in 7 s, refused at `ControlC338.agda:293.18-295.48`, which is
`keyValK-live`.** **So tie 9's hypothesis is a real constraint and this
environment meets it for one tag and not another.** Without this control
the tie could be true because nothing meets it. MEASURED.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `KValue` needs changed lines to transport | **MEASURED FALSE.** 50 of 50, 0 delete, 0 replace |
| `KValue` transports for free | **MEASURED FALSE.** 15 code lines of adapter, 21 with its opens |
| `Bound` must be re-proved at ambient | **MEASURED FALSE.** `BoundOver` is already generic; two presentations re-spell in 4 lines |
| `KValue` has a consumer in `src/` | **MEASURED FALSE.** One grep hit, its own declaration at `:7264` |
| the third figure repeats 51 or 42 | **MEASURED FALSE.** It is 234 |
| the remaining four modules need four measurements | **MEASURED FALSE.** All four are inside `LeafAgree` and my green run forced them |
| `LeafAgree`'s ties are all closure facts | **MEASURED FALSE.** Six residues survive an exit-0 supply |
| the ties are ONE debt | **MEASURED FALSE** at site 3 too, and there are THREE kinds: downward, upward, construction |
| sites 1 and 3 share nothing, as sites 1 and 2 do | **MEASURED FALSE.** Site 3 imports site 1's three pair lemmas, 10 lines |
| site 3 reuses site 1's `entryK`, `domK` or `Ltr` | **MEASURED FALSE.** None is named in my file |
| the graph-frame ties cost as much as the witness-frame ones | **MEASURED FALSE.** Four of them are one line each |
| `TagAgree`'s tie is free because wave 1 ported it clean | **MEASURED FALSE.** Wave 1 changed no tie; the family is free because `KValue` supplies `KFacts` |
| the supply typechecks vacuously | **MEASURED FALSE.** Control C, red at `keyValK-live` |
| a break in the copied `KValue` goes unnoticed | **MEASURED FALSE.** Control A, red inside the copied block |
| `envK` and `defPairK` are true as stated | **INFERRED FALSE.** Their `z` is unbounded. I built no counterexample |
| the residue has a supplier at the L class | **MEASURED FALSE.** `LeafAgree` has zero consumers in `src/`, so nobody has met its ties |
| the seven's tie supply is about 100 lines | **MEASURED FALSE.** 327, and that excludes the residue's proofs |
| the two twelve readings are ties | **MEASURED FALSE**, by `[LJ-1.302]:200-203`, which I re-read and took |
| a run hit a wall | **MEASURED FALSE.** The longest was 40 s |
| a probe under `src/` was written | **MEASURED FALSE.** Every file sits in `agents/tasks/LJ-1-338/` |
| a sibling task directory was edited | **MEASURED FALSE.** `git status` shows my directory only |
| the whole chapter typechecks with this supply landed | **INFERRED.** Nothing landed and I ran no whole-chapter check |
| `StepAgree` and `ApproxAgree` moved | **MEASURED FALSE.** Still absent from `src/`; this task did not touch them |

## 9. THE NEW RANGE, WITH ITS BASIS (DD8)

**ONE NUMBER: 327 non-blank lines for the seven's ambient tie supply.**

**BASIS.** Three measured sites, 51 + 42 + 234, on one caliber re-derived
today. **The third site CONTAINS the four that were unmeasured**, by
`src/L/Condensation.lagda.md:7191-7209` and by the green instantiation.
**So this is no longer an extrapolation over five unmeasured sites, and
P-l no longer binds the way it bound `[LJ-1.336]`.** 10 of the 327 lines
are site 1's, reused.

**WHAT THE NUMBER DOES NOT COVER, AND THE PROJECT MUST FUND THIS
SEPARATELY.**

1. **The six residues.** 51 of the 234 lines STATE them; nothing proves
   them. Their proofs are unpriced, and two of them may be false (D-10).
2. **The two twelve readings.** Not ties. `[LJ-1.298]` priced that port
   at about 180 hand-written lines, and I did not re-measure it.
3. **`StepAgree` and `ApproxAgree`.** Still absent from `src/`, still the
   route's widest unpriced term, exactly as `[LJ-1.302]` and
   `[LJ-1.336]` left them.

**SECONDS.** 40 s for the whole third site with the two waves cached, at
0.17 s per non-blank line. Site 2 cost 9 s. **The site costs seconds in
proportion to its ties, not to its lines.** MEASURED.

## 10. DD4, WITH THE AXIS NAMED (C-46)

**MY AXIS IS THE L-AGAINST-AMBIENT AXIS, AND IT IS NOT DD4's OWN.** DD4's
own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. `[LJ-1.308]` was marked down for leaving
the qualifier out and `[LJ-1.336]` put it back, so I say it first.

**ON DD4's OWN AXIS THIS PROBE IS NEUTRAL BY STRUCTURE, RE-DERIVED
TODAY.** `scripts/measure/ledger.py --reuse` prints **AC 73 masters,
17,197 lines; GCH 48 masters, 8,889 lines; SHARED 43 masters, 7,596
lines.** Those are `[LJ-1.336]`'s figures, unchanged today. MEASURED, by
running the instrument. `L.Condensation` is in neither closure, so
nothing here moves either trophy.

**ON THE L-AGAINST-AMBIENT AXIS, SITE 3 ADDS 15 LINES TO THE 99.**
`[LJ-1.336]` measured waves 1 and 2 together at **5,576 copied lines
serving two carriers for 99 lines of hand-written code**. **`KValue`'s 50
lines now serve two carriers too, for 15 lines of adapter. So the paid
instance is 5,626 copied lines for 114 hand-written.** MEASURED, by the
alignment in section 2 and `[LJ-1.336]`'s own counts on the same caliber.

**AND THE 183 LINES OF TIE SUPPLY ARE NOT PART OF THAT RATIO, WHICH IS
THE HONEST HALF.** They are the J tower's own instantiation price, and no
port removes them. **What the port makes free is the 5,626 lines of
mathematics. What it does not make free is the site facts, and this task
measures those at 327 for the seven.**

**C-55 is respected.** Nothing here folds a telescope into a record. The
six residues are MODULE PARAMETERS at `ProbeLeaf338.agda:315-352`, never
record fields, exactly as the brief ordered. `KFacts` arrives from wave 1
as the chapter wrote it.

**P-l, and the honest half.** Site 3 is one site. Its 234 is MEASURED at
ONE environment, `n := 9` with a 17-slot frame. **A different environment
could make a supplied tie harder or a residue derivable**, and I did not
test a second environment. INFERRED that the classification of the six
residues holds at any environment, because each residue's obstruction is
in the tie's own quantifier structure and not in my choice of slots.

## 11. ARCHIVE USED (DD18)

One line read per archived file.

- **`agents/tasks/LJ-1-336/lj-1.336-report.md`, read WHOLE, FIRST, as the
  brief orders.** **Line read:** `:241-247`,「`module KValue` at
  `src/L/Condensation.lagda.md:7264-7318` is the block that builds the
  one `KFacts` VALUE ... It costs 50 non-blank lines at the L class
  alone」. **TOOK** it as the first thing to test, and section 2
  transports it. **CORRECTED nothing**: its 50 reproduces exactly.
- **`agents/tasks/LJ-1-336/ProbeTies336.agda`, read WHOLE and re-counted.**
  **Line read:** `:104`, `module B = Bound lam ordλ succλ ∅∈λ`. **TOOK**
  the ambient scaffold and the eight-parameter `GenDirty` application
  verbatim; my two probes reuse it unchanged.
- **`agents/tasks/LJ-1-302/lj-1.302-report.md`, read `:150-230`.** **Line
  read:** `:191`,「The ties are ONE debt, not sixteen」. **TOOK** it as
  the claim under test; site 3 refutes it a second way, by exhibiting a
  THIRD kind of debt that neither measured site states.
- **`agents/tasks/LJ-1-302/ProbeLJ1302B.agda`, read WHOLE and IMPORTED
  unchanged.** **Line read:** `:105-108`, `pair∈pr`. **TOOK** the three
  pair lemmas; they are the only lines site 3 reuses from site 1, and
  section 5 measures that at 10.
- **`agents/tasks/LJ-1-306/GenAgree.agda`, read `:40-80` and
  `:4885-4930`.** **Line read:** `:4886`, the generic
  `record KFacts`. **TOOK** the confirmation that the RECORD is already
  generic and only the VALUE was missing at ambient.
- **`archive/dev/TASKS-archived.md`, read `:55-80`.** **Line read:**
  `:60`, the `L3.32-T26` row,「Shared pair kit | GO」. **TOOK SHAPE
  only:** the retired route also found the pair lemmas worth writing once
  and sharing. **No figure transfers**: that route's carrier, coding and
  chapter are all different, and its GO priced a kit nobody here uses.

## 12. LITERATURE USED (DD18)

**THE ONE LINE THE BRIEF ASKS FOR: no mathematical literature bears on
the line cost of an ambient tie supply.** The cost is an artefact of our
two-coding architecture, and Devlin has no second coding to tie anything
to.

`dev/literature/devlin-II5.md`, read `:312-335`. **Line read:**
`:321-325`, item 2,「Σ₀ absoluteness 1.9.15 ... the bridge between
satisfaction inside a transitive carrier and ambient truth」. **This is
the closest thing in the source to my ties, and it is NOT the same
thing.** Devlin pays one language-level bridge in Chapter I; the ties are
per-notion facts about what a BOUND contains, and a single-coding
development has no bound to tie to. **So the residue of section 4 is the
price of our architecture, not of the port.**

**WHY NOT the rest of the digest.** Items 1, 5 and 6 are the collapse, KP
recursion and reflection, none of which `LeafAgree` reaches. Items 7 to
12 partition the level recursion by tower, which is Devlin's axis and not
DD4's; C-46 forbids using it as the DD4 axis.

## 13. WHAT I DID NOT SETTLE

- **The residue's proofs.** Six ties are stated and unproved, and two of
  them may be false. That is the next brief, and D-10 says it prices the
  TRUTH before the proof.
- **A second environment for site 3.** One frame is measured. INFERRED
  that the residue classification is frame-independent.
- **The two twelve readings.** Taken as hypotheses, not measured.
- **`StepAgree` and `ApproxAgree`.** Untouched, still absent from `src/`.
- **Whether `q'` follows.** Neither confirmed nor refuted.
- **The landing cost.** This probe lands nothing, and it does not price
  the edit at the chapter.

## 14. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. **No invocation reached 30 minutes; the
longest was 40 s.** I ran
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` before every
invocation and it returned **0 every time**, so I held one slot and no
sibling was live at those moments.

| file | exit | seconds | note |
|---|---:|---:|---|
| `ProbeKValue338.agda` | 42 | 3 | scope: a module cannot be renamed by `=` |
| `ProbeKValue338.agda` | 42 | 4 | scope: `_^_` comes from `AbsL` |
| `ProbeKValue338.agda` | 42 | 5 | my own bad level argument on `𝒮ᵥ` |
| `ProbeKValue338.agda` | **0** | **9** | `KValue` transported, 0 changed lines |
| `ProbeKValue338.agda` | 0 | 4 | reload |
| `ProbeLeaf338.agda` | **0** | **13** | the ten supplied ties, before the instantiation |
| `ProbeLeaf338.agda` | **0** | **40** | site 3 complete, `LeafAgree` instantiated |
| `ControlA338.agda` | **42** | 4 | **EXPECTED RED**, inside the copied block |
| `ControlB338.agda` | **42** | 5 | **EXPECTED RED**, the code slot |
| `ControlC338.agda` | **42** | 7 | **EXPECTED RED**, non-vacuity |

Python runs cost under 2 s each and take no Agda slot: `count338.py`,
`breakdown338.py`, `control338.py`, and
`scripts/measure/ledger.py --reuse`.

## 15. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-338/`: this report,
`ProbeKValue338.agda`, `ProbeLeaf338.agda`, `ControlA338.agda`,
`ControlB338.agda`, `ControlC338.agda`, and the scripts `count338.py`,
`breakdown338.py` and `control338.py`. `git status` shows my directory
only. `src/` holds no probe of mine.
`src/L/Condensation.lagda.md`, `src/L/Coding/Bound.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/Powerset.lagda.md`,
`src/L/Axioms/Basic.lagda.md` and `src/L/Constructible.lagda.md` were
read and copied from, never opened for writing. `agents/tasks/LJ-1-302/`,
`agents/tasks/LJ-1-306/` and `agents/tasks/LJ-1-336/` were read, imported
and re-counted, never edited. I did not open `src/Everything.lagda.md`,
`dev/PLAN.md`, `dev/LESSONS.md`, `dev/ledger.toml`, `AGENTS.md` or
`.claude/` for writing. No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`. No telescope was folded into a
record (C-55). Nothing was re-ported.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`scripts/gate/lint-agda.py --check` both pass. No em dash in any
language.
