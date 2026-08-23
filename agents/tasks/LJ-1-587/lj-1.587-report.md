# [LJ-1.587] report: does either `InjCode` producer widen

## HEAD
head_slot: coder
machine: shared
task: LJ-1.587
obligation: agents/tasks/LJ-1-587/Probe587.agda::producer-widened
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-587/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **NO HEAP EVENT**: the largest maximum resident set size of any run
is 667,860,992 bytes, about 0.62 GiB, against the 8 GB cap
(`agents/tasks/LJ-1-587/runs/w3-1.out`). No run gave exit 251 and no run
printed a heap message. Nothing is postulated, the probe carries `--safe`
(`agents/tasks/LJ-1-587/Probe587.agda:1`), and there is no hole. Nothing lands
in `src/`. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**ONE RUN OF THE ELEVEN WAS NOT GREEN AND I NAME IT.** `runs/s3-1.out` is exit
42. It is not a mathematical failure: section 3 used `StageBound` before I had
added it to the `L.InjChain` import list. `runs/s3-2.out` is the same section
with the import line added, exit 0. Every other run in `runs/` is exit 0.

## VERDICT

**GO on `producer-widened`.** The obligation is
`agents/tasks/LJ-1-587/Probe587.agda:91`:

    producer-widened : (D C : S)
                     → ((z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩)
                     → Σ[ F ∈ S ] InjCode F D C

The pair is ARBITRARY, not merely other than `(sucʟ γ , γ)`. Nothing in that
term or its proof names `sucʟ`, an ordinal, `ω` or a numeral. **The probe is
green, exit 0, five clean runs** (`runs/final-1.out` to `runs/final-5.out`,
each after deleting `_build/2.8.0/agda/agents/tasks/LJ-1-587/Probe587.agdai`).

**AND THE WIDENING IS THE PRODUCER'S OWN METHOD, NOT A SIBLING'S.**
`producer-widened-by-carve` (`Probe587.agda:195`) delivers the same type by
instantiating `Carve` ITSELF, the module `src/L/Absorption.lagda.md:386` that
the Absorption producer is built from. Section 2 is the cheap route, section 3
is the answer to the question the brief actually asked.

**THREE CORRECTIONS TO PREMISE 1, ALL MEASURED.** Premise 1 is "two producers,
both at one shape", basis
`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:105-108`, which
records that it came from `grep -rn "InjCode" src/`.

1. **THE TWO SITES ARE ONE TERM.** `src/L/CodedShift.lagda.md:37-52` is byte
   for byte `src/L/Absorption.lagda.md:611-626`; `diff` of the two ranges is
   empty. `two-sites-one-term` (`Probe587.agda:223`) is the elaborator's word
   for it, by `refl`. **The count of methods at that shape is ONE.**
2. **THE COUNT OF MACHINES IS FOUR, NOT TWO.** `src/L/InjChain.lagda.md`
   carries two more that deliver `InjCode`'s four conjuncts at an arbitrary
   pair and never write the word `InjCode`, which is why a grep for the name
   did not see them: `InclGraph` (:575) and `Comp` (:314). A grep for a NAME
   is not a count of PRODUCERS.
3. **THE ARCHIVE ALREADY SAID SO.** `archive/dev/LJ-dispatch-index.md:380`
   records `[LJ-1.325]`'s finding in one line: "InjCode's four conjuncts are
   already PROVED in three modules and thrown away at the last step". That
   record is older than `[LJ-1.580]` and it contradicts premise 1 directly.

**NEITHER CORRECTION MAKES THE BILL EASIER.** See `## WHAT REUSE IS WORTH`.

## THE TWO METHODS

**METHOD ONE, `src/L/Absorption.lagda.md:611-626`.** The formula is `shiftFo D
γ ω z` (`:224-226`), a one-place description that reads "p is the pair `<x,y>`
for some x in D, and y is the shift value of x". The shift value is three
cases, `shiftRel γ ω z` (`:221-222`): a member of `ω` goes to its successor, the
member equal to `γ` goes to `z`, and every other member goes to itself. The
parameters come from `ShiftGraph` (`:539-541`), the Part-4 instantiation, which
sets `D := sucV γ` with a transported `isL`, `C := γ`, `ω := ωʟ` and `z := ∅ʟ`,
and builds `sh` from the ambient `ShiftAbs` (`:74`). **The proof, however, is
not in `ShiftGraph`.** It is `Carve` (`:386-402`), whose FIRST TWO PARAMETERS
`D C` ARE the pair of `InjCode F D C`, already abstract, with the bound and the
separation field also parameters. So the site fixes the shape and the method
does not. **INCIDENTAL.**

**METHOD TWO, `src/L/CodedShift.lagda.md:37-52`.** There is no second method.
The file imports `module ShiftGraph` from `L.Absorption` (`:16`) and then
repeats method one's sixteen lines unchanged. `two-sites-one-term`
(`Probe587.agda:223`) proves the two terms equal by `refl`, so the question
"which of the two is more general" has no content: they are the same term
typed twice. Asked of the one method that exists, the answer is the paragraph
above. **INCIDENTAL, for the same reason and by the same lines.**

**WHICH ONE I PICKED AND WHY.** The choice was forced, so the real choice was
which hypothesis of `Carve` to pay at a new pair. I picked the one that makes
all three cases collapse: `ω := ∅ʟ` empties case 1, `γ := D` empties case 2 by
`∈-irrefl` and makes `D-in-dec` return its own second argument, and case 3 is
then everything and says the value is the same SET. What remains is a subset
witness, and that is the whole hypothesis of `producer-widened`. Widening by
degeneration is worth more than widening by a new three-case shift, because the
result names no ordinal at all.

## WHAT REUSE IS WORTH

**Reuse buys exactly two pair shapes and no third: a SUBSET pair
(`injL-from-subset`, `Probe587.agda:255`) and a COMPOSITE pair
(`injL-compose`, `:259`), both at arbitrary L-elements and both stated at the
trophy's own truncation `InjL` (`src/L/GCH.lagda.md:38`).** I could not read
the briefs of `[LJ-1.584]` or `[LJ-1.586]`, which are not in this worktree, so
I answer only for what my own brief and the tree state: `[LJ-1.584]` is
writing a formula from scratch at its own pair and this file does not shorten
that; row 5 and `[LJ-1.580]`'s residue `InjL (Lset β) α`
(`agents/tasks/LJ-1-580/Probe580.agda:311`) CANNOT take `injL-from-subset`,
because its hypothesis is `Lset β ⊆ α` and a stage is not a subset of an
ordinal, so on the evidence I have **none of the three can take the subset
route, and the one thing that may still help them is `injL-compose`, which
turns any two coded legs into one code and asks nothing about their shapes.**

## D-10, BEFORE ANY AGDA

The brief ordered the two producers read and their parameters traced before
writing Agda. That read produced the four findings of `## VERDICT` and the two
paragraphs of `## THE TWO METHODS`, all before the first `agda` invocation
(`runs/w3-1.out`, started 04:48:41Z). The one thing the read changed about the
plan: the brief expected a choice between two methods, and there is one method,
so the task became "what does `Carve`'s hypothesis list cost at a new pair"
instead.

## W3, THE WIDEST UNMEASURED TERM

Written FIRST and typechecked ALONE, as ordered. `runs/w3-1.out`, exit 0,
6.52 seconds real, 667,860,992 bytes peak RSS. The brief estimated about 15
lines and under 2 minutes; the section is 15 lines
(`Probe587.agda:50-64`) and took 6.52 seconds.

    formula-at-abstract-pair : (D C γ ω z : S) → Formula S 1
    formula-at-abstract-pair D C γ ω z = shiftFo D γ ω z

**GO, and it settles more than the brief asked.** The formula does not merely
state with an abstract pair: `C` DOES NOT OCCUR IN IT. The description is of
the domain and the value rule only, so the codomain enters through the fourth
conjunct `ran` and never through the syntax. That is why the widening of
section 2 and section 3 costs a subset witness and no new formula.

## WHAT IS BUILT, SECTION BY SECTION

| Section | Term | Line | What it measures |
|---|---|---|---|
| 1 | `formula-at-abstract-pair` | `:63` | W3. The formula states with the pair abstract, and `C` is absent |
| 2 | `producer-widened` | `:91` | THE OBLIGATION. A producer at an arbitrary pair |
| 2 | `producer-widened-at-ordinal` | `:100` | The same at `D ∈ C` with `C` an ordinal, through `OrdIncl` |
| 3 | `WidenedCarve` | `:130` | Absorption's own `Carve`, instantiated at an arbitrary pair |
| 3 | `producer-widened-by-carve` | `:195` | The obligation's type again, by the producer's METHOD |
| 4 | `two-sites-one-term` | `:223` | The two `src/` sites are one term, by `refl` |
| 4 | `producers-compose` | `:230` | `Comp` read as `InjCode`, at an arbitrary composite pair |
| 5 | `injL-from-subset` | `:255` | The subset route at the trophy's truncation |
| 5 | `injL-compose` | `:259` | The composite route at the trophy's truncation |

261 lines total. The brief estimated about 160, of which about 40 the
obligation. The obligation is 6 lines (`:91-96`) because `InclGraph` had
already carved it; the overrun is sections 3 to 5, which the brief did not ask
for and which are what makes the answer usable.

## W2 (DD4), ANSWERED

**Satisfied, and at the maximum available.** Every term in this file is written
at a generic carrier: `producer-widened`, `producer-widened-by-carve`,
`producers-compose`, `injL-from-subset` and `injL-compose` all quantify over
the pair, and `WidenedCarve` is a module in `(D C : S)` and a subset witness.
Nothing here is instantiated at a fixed shape, and nothing here is written
twice. The one instantiation offered, `producer-widened-at-ordinal` (`:100`), is
a two-line application and not a copy.

## W4 (DD13), AND A RETIREMENT CANDIDATE I DID NOT ACT ON

**`src/L/CodedShift.lagda.md` is a candidate and I left it exactly where it
is.** The evidence, and no action, because acting lands in `src/` and this
brief's scope is `agents/tasks/LJ-1-587/`:

- Its mathematical content is `:37-52`, byte for byte
  `src/L/Absorption.lagda.md:611-626`, proved equal at `Probe587.agda:223`.
- **NOTHING IMPORTS IT** except `src/Everything.lagda.md:377`. `grep -rn
  "CodedShift" src/` returns that one line outside the file itself.
- It is 39 in-fence non-blank lines.

Priced the W4 way, the ideal form written fresh today is ZERO lines: the term
already exists at `src/L/Absorption.lagda.md:611`, exported, and the chapter it
would need to justify its own existence does not exist. **This is a
mathematician's call and an owner's call, not mine**, and the archive row
`archive/dev/LJ-dispatch-index.md:380` suggests the duplication is older than
the file.

## LAWS THE BUNDLE NAMED

- **D-10** (`dev/LESSONS.md:1375`). Answered above under its own heading. The
  target of premise 1 was checked before any Agda and it is wrong in three
  ways, all recorded in `## VERDICT`.
- **C-22** (`dev/LESSONS.md:2297`). This file was a skeleton before the first
  `agda` run and was filled as each section landed.
- **C-42** (`dev/LESSONS.md:3752`). This task IS the sweep C-42 demands, and it
  changed the count. `[LJ-1.580]` measured ONE site's shape and reported a
  tree-wide count from a grep for a name. **The corrected count is: one
  method at the successor shape, duplicated across two files, plus two
  machines in `src/L/InjChain.lagda.md` that produce the four conjuncts at an
  arbitrary pair.** No cure should be funded against the number two.
- **P-l** (`dev/LESSONS.md:2357`). Consistent with what section 5 does: the
  types of `injL-from-subset` and `injL-compose` quantify over L-elements and
  name no presentation, so nothing unfolds. The 2.5-second checks are the
  measurement.
- **D-26** (`dev/LESSONS.md:1735`). Not used. No term in this file well-orders
  a tower or needs generation data, and the widening removed the ordinal from
  the statement rather than adding structure to it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED, and it changed the
  report.** `archive/dev/LJ-dispatch-index.md:380` reads
  "| LJ-1.325 | Re-price PLAN 0.0 against the restated trophy | MORE BY 600, AND 800 UNDER THE SURVEY | InjCode's four conjuncts are already PROVED in three modules and thrown away at the last step |".
  That is `[LJ-1.325]`'s record of the same finding this task re-measured, and
  it is older than `[LJ-1.580]`'s count. I also read
  `archive/dev/LJ-dispatch-index.md:371`, "| LJ-1.314 | DD25 review of InjData's NECESSITY | SPLIT. THE RESIDUE IS NOT A NEW PRINCIPLE | Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it. Green probe |",
  which is the provenance of this brief's premise 5.
- `archive/dev/JOURNAL-archived.md`: searched for `InjCode`, `InclGraph`,
  `shift-coded`; the two hits (`:1107`, `:4053`) are about an inclusion
  TRANSFER between stages and not about a code. NOT USED.
- `archive/dev/JOURNAL.md`: searched, no hit on any of the four terms.
  DECLINED.
- `archive/dev/DECISIONS-archived.md`: searched, no hit; it is 61 lines and
  is the archived `D<n>` series, which binds nothing here. DECLINED.
- `archive/dev/ORCHESTRATION.md`: not read. It is the archived operating
  document and carries no mathematics. DECLINED.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ AND USED.** Line 76
  reads "truncated existence of an injection.** That is the HoTT Book's own definition,".
  That is the grade section 5 states its two reductions at, and it is why
  `injL-from-subset` and `injL-compose` are stated at `InjL` and not at the
  untruncated `Σ`.
- `dev/literature/devlin-II5.md`: **READ, NOT USED for a build step.** Line
  156 reads "|L_α| = |α| and |L_γ| = |γ|, so |γ| = |M| = |α| < κ, hence γ < κ and".
  `[LJ-1.580]`'s review cites this passage as the source of the residue
  `InjL (Lset β) α`; I read it to confirm that the residue is a SIZE fact about
  a stage and therefore not a subset fact, which is the negative half of
  `## WHAT REUSE IS WORTH`. It funded no term.
- `dev/literature/digest.md`: searched for `InjCode`, `injection`,
  `inclusion`, `subset`; the hits are about when new subsets appear in the J
  hierarchy, which no term here touches. NOT USED.
- `dev/literature/terms-2026-08.md`: searched, one hit at `:390` about a
  chapter subject's naming. This task added no term and no glossary entry, so
  it is out of scope. DECLINED.
- `dev/literature/glossary-review-2026-08.md`: not surveyed. It is a
  PASS/FAIL review record for glossary entries, and this task proposes none.
  DECLINED.

## WHAT THE NEXT BRIEF SHOULD KNOW

1. **DO NOT WRITE ANOTHER BRIEF AGAINST "TWO PRODUCERS".** The number is wrong
   and `## VERDICT` gives the three reasons at `file:line`.
2. **`InjCode` AT A SUBSET PAIR AND AT A COMPOSITE PAIR ARE NOW FREE**, at
   `Probe587.agda:91` and `:230`, and at the `InjL` grade at `:255` and `:259`.
   A brief that needs either should import them, not restate them.
3. **THE REMAINING ROWS STILL NEED A FORMULA.** Nothing here weakens that. What
   is now measured is WHY: `shiftFo` does not mention the codomain
   (`## W3`), so a code is a description of the DOMAIN and the VALUE RULE, and
   a pair whose value rule is neither the identity nor a composite has no
   description in the tree today.
4. **THE OPEN QUESTION I WOULD ASK NEXT.** `producers-compose` (`:230`) takes
   two codes and asks nothing about their shapes. `[LJ-1.580]` already built
   `leg1-coded : InjCode Leg1.G βᴸ πXᴸ` (`agents/tasks/LJ-1-580/Probe580.agda:232`).
   **Is there a second leg out of `πXᴸ` that the tree can already code?** If
   there is, the residue closes by composition and no new formula is needed. I
   did not attempt it: the brief gave this task one obligation (AD12) and told
   me to attempt no row of the bill.
