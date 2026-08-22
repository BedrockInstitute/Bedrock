# LJ-1.526 report: does the successor L-cardinal exist

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO ON THE OBLIGATION, GO ON THE REDUCTION

Written early as a skeleton and filled as each run landed (C-22). No commit, no
push. I wrote only in `agents/tasks/LJ-1-526/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event. Nothing is postulated. The probe is a raw
`.agda` file, so it carries no ` ```agda ` fence and the ratio bar cannot fire on
it.

## VERDICT

**NO-GO ON THE OBLIGATION. `SuccCardExists` IS NOT INHABITED AND I DO NOT
INHABIT IT.** The NO-GO is stated at
`agents/tasks/LJ-1-526/review-of-SuccCardExists.md`, as the coder slot's
instruction requires. The type is written at `Probe526.agda:169-174` at the
brief's own binding, with no hole.

**THE OBLIGATION IS NOT REFUTED EITHER, AND THE BRIEF'S LARGEST FEARED FINDING
DOES NOT HAPPEN.** The brief asked whether `[LJ-1.91]`'s ambient obstruction
reaches the internal predicate, and said that if it does, GCH's δ is unreachable
by the route the tree has. **IT DOES NOT REACH.** Section `## AMBIENT AGAINST
INTERNAL` gives the measurement.

**WHAT IS DELIVERED INSTEAD IS THE REDUCTION, GREEN AND WITH NO HOLES**
(`Probe526.agda:285-292`):

    reduction : CardAboveL → SuccCardExists

**B4 IS NOT SEVEN THINGS OR THREE. IT IS ONE**, and `CardAboveL`
(`Probe526.agda:178-183`) names it: SOME ordinal L-cardinal strictly above κ,
truncated, with no leastness and no bound.

**THE LEASTNESS CLAUSE, WHICH THE BRIEF FORBADE WEAKENING, IS NOT ASSUMED AND
NOT WEAKENED. IT IS PRODUCED.** `leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`)
over the ordinal well-order returns the least candidate and its minimality in
one object, and `leastness` (`Probe526.agda:255-283`) turns that minimality into
`SuccCardL`'s fourth conjunct (`src/L/GCH.lagda.md:50-53`) at every ordinal
L-cardinal above κ, inside the selection domain and outside it.

**AND THE STATEMENT IS NOT VACUOUS.** `gchHypAtω` (`Probe526.agda:146-148`)
inhabits `GCHStatement`'s whole κ slot at ω.

**TWO ARCHIVE FINDINGS DID NOT SURVIVE RE-MEASUREMENT**, both in
`## AMBIENT AGAINST INTERNAL`: `[LJ-1.90-A]`'s "IsCardinal is never inhabited"
and the transfer of `[LJ-1.91]`'s obstruction to the internal predicate.

Three forced rechecks, exit 0 each: `runs/s4-sealed-1.out` to `-3.out`.

## AMBIENT AGAINST INTERNAL

**THE TWO PREDICATES DIFFER IN ONE PLACE ONLY: WHAT COUNTS AS AN INJECTION.**

| | `IsCardinal` | `IsCardinalL` |
|---|---|---|
| home | src/L/BoundedSubset.lagda.md:1046-1047 | src/L/Cardinal.lagda.md:230-233 |
| the κ it speaks of | `SV.S`, a bare `V ℓ` | `SL.S`, an L-element |
| the δ it quantifies over | every `δ : SV.S` with `⟨ δ ∈ˢ κ ⟩` | every L-element δ with `⟨ fst δ ∈ fst κ ⟩` |
| what it refutes | `⟪ κ ⟫ ↪ ⟪ δ ⟫`, an AMBIENT function with an ambient injectivity proof | `∥ Σ[ F ∈ SL.S ] InjCode F κ δ ∥₁`, an L-ELEMENT that CODES such a function |
| can the tree inhabit it at some set | **YES.** `ω-card : IsCardinal ω`, Probe526.agda:130-133 | **YES.** `ω-cardL : IsCardinalL ωʟ`, Probe526.agda:137 |
| can the tree inhabit it at ∅ | yes, vacuously, by the same argument as section 1 | **YES**, `someCardinalL`, Probe526.agda:59-63 |

**THE DELTA COLUMN IS THE SAME DOMAIN, NOT A WIDER ONE.** `isL-trans`
(`src/L/Constructible.lagda.md:379`) makes every member of an L-element an
L-element, so the two δ ranges differ only by a certificate that is always
available, never by which sets they reach.

**SO THE ONLY REAL DIFFERENCE IS THE REFUTAND, AND IT DECIDES THE DIRECTION.**
`readL` (`src/L/CantorBernstein.lagda.md:33-38`) turns a code into an ambient
injection. A code is therefore a HARDER thing to have than a function, and
refuting the harder thing is EASIER. The implication runs

    ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ

and it is BUILT and GREEN at `agents/tasks/LJ-1-526/Probe526.agda:105-107`.
**`IsCardinalL` is the WEAKER predicate.**

**THE CONVERSE IS STATED AND NOT INHABITED** (`Probe526.agda:115-116`). It would
need every ambient injection between two L-elements to be coded by an L-element,
which is the definability direction of the readback.
`src/L/CantorBernstein.lagda.md` delivers `readL` and nothing the other way.

### Does `[LJ-1.91]`'s obstruction reach the internal predicate

**NO, AND THE REASON IS THE DIRECTION ABOVE.**
`archive/dev/LJ-dispatch-index.md:167` records: "IsCardinal is ambient, so the
internal omega-1-L does not provably satisfy it". That is a statement that one
predicate is out of reach at one site. **Being out of reach transfers UPWARD, to
stronger statements, never downward to weaker ones**, and section 2 measures
`IsCardinalL` to be the weaker one. The obstruction does not reach it.

### `[LJ-1.90-A]` IS NO LONGER TRUE OF THE TREE

`archive/dev/LJ-dispatch-index.md:166` records: "Orchestrator audit: IsCardinal
is never inhabited. CONFIRMED. Two hits in src: the definition and the
hypothesis. The probe's own kappa, sucV omega, is not a cardinal either".

**THAT WAS A COUNT OF TERMS IN `src/`, AND A COUNT IS NOT AN IMPOSSIBILITY.**
`IsCardinal ω` is FOUR LINES from delivered parts, and it is green:

    ω-card : IsCardinal ω
    ω-card δ δ∈ω (f , finj) =
      finite-excl-ω δ (mem-ord {A = ω} ω-ord δ δ∈ω) δ∈ω
        (λ x → f x , f x) (λ x y e → finj x y (cong fst e))

`Probe526.agda:130-133`. The only input is `finite-excl-ω`
(`src/L/InjChain.lagda.md:152-156`), which refutes an injection of ω into the
SQUARE of a finite ordinal; the diagonal `λ x → f x , f x` turns a plain
injection into that shape. **`[LJ-1.90-A]`'s own counter-example, `sucV ω`, is
beside the point: ω itself is the cardinal, not its successor.**

I did not re-audit `[LJ-1.90-A]`'s claim as a claim about the tree on the date it
was written. I measured what the tree can do TODAY, which is what C-42 and D-10
ask for.

## W3, DOES ANYTHING SATISFY IsCardinalL

**GO, TWICE, AND THE SECOND ONE IS THE ONE THAT MATTERS.**

**1. THE LITERAL W3 IS GO AND IT IS VACUOUS.** The brief's type is inhabited at
the empty set (`Probe526.agda:59-63`):

    someCardinalL : ∥ Σ[ κ ∈ SL.S ] (IsOrd (fst κ) × IsCardinalL κ) ∥₁
    someCardinalL = ∣ ∅ʟ , ∅-ord , vacuous ∣₁

`IsCardinalL κ` quantifies over the members of κ, so ∅ satisfies it with nothing
to prove, exactly as `∅-ord` satisfies `IsOrd` (`src/L/Ordinal.lagda.md:77-79`).
`∅ʟ` is delivered at `src/L/Axioms/Basic.lagda.md:508-509`.

**A VACUOUS GO WOULD HAVE MISLED THE NEXT BRIEF**, because the obligation's κ is
INFINITE. So I measured the question behind the question.

**2. AN INFINITE ONE EXISTS AND THE HYPOTHESIS TRIPLE OF `GCHStatement` IS
INHABITED.** `Probe526.agda:137-145`:

    ω-cardL : IsCardinalL ωʟ
    ω-cardL = ambient→internal ωʟ ω-card

    gchHypAtω : Σ[ κ ∈ SL.S ]
                  (IsOrd (fst κ) × IsCardinalL κ × (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥))
    gchHypAtω = ωʟ , ω-ord , ω-cardL , ∈-irrefl ω

**THIS IS THE THREE CERTIFICATES `GCHStatement` DEMANDS OF ITS κ**
(`src/L/GCH.lagda.md:60-63`), filled at one set. **The trophy statement is not
vacuous: it has at least one instance to prove, and that instance is ω.**
`ωʟ` is delivered at `src/L/Axioms/Infinity.lagda.md:69-70`.

**THE CAMPAIGN LOST THREE DISPATCHES TO A STATEMENT NOTHING SATISFIED
(`[LJ-1.507]`). THIS IS NOT THAT CASE.**

## THE OBLIGATION

**WRITTEN AT THE BRIEF'S TYPE, NOT INHABITED** (`Probe526.agda:169-174`):

    SuccCardExists : Type (ℓ-suc ℓ)
    SuccCardExists =
        (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

It is the same type as `[LJ-1.523]`'s row B4
(`agents/tasks/LJ-1-523/Probe523.agda:191-195`), which I re-typed rather than
imported so that this file states its own obligation.

### The reduction, and what it costs

`reduction : CardAboveL → SuccCardExists` (`Probe526.agda:285-292`) is green
with no holes. It runs through `module Reduce` (`Probe526.agda:189-283`), and
the arithmetic of the parts is this:

| part | at | how it is discharged |
|---|---|---|
| the crossing `up`, and `self`, `self-eq` | Probe526.agda:195 | REUSED from `LeastCardInjL` (src/L/Cardinal.lagda.md:77-79, :103-107). Not rebuilt. |
| the selection domain | Probe526.agda:197-198 | `⟪ sucV (fst θ) ⟫`, the tower at the successor of the witness |
| the well-order | Probe526.agda:203-212 | `ordSWO` (src/L/Ordinal/SquareLaw.lagda.md:176-182), SEALED |
| the predicate | Probe526.agda:221-223 | the conclusion's OWN two clauses, `IsCardinalL (up b)` and `κ ∈ up b`. Both are hProps, so `leastOf` accepts them |
| non-emptiness | Probe526.agda:228-231 | the witness θ itself, transported along `Σ≡Prop` |
| `IsOrd (fst δ)` | Probe526.agda:242-243 | `mem-ord` (src/L/Ordinal.lagda.md:221) |
| `IsCardinalL δ` | Probe526.agda:245-246 | first clause of `⟨ Good δ ⟩` |
| `⟨ fst κ ∈ fst δ ⟩` | Probe526.agda:248-249 | second clause of `⟨ Good δ ⟩` |
| the LEASTNESS clause | Probe526.agda:255-283 | `leastOf`'s minimality, plus `ord-tri` (src/L/Ordinal/Linear.lagda.md:136) |

**THE LEASTNESS CLAUSE IS THE PART I EXPECTED TO COST AND IT DID NOT.** Because
both conjuncts of the predicate are hProps, `leastOf` hands back the least
candidate together with the proof that nothing below it qualifies, and
`SuccCardL`'s fourth conjunct is that proof read at an arbitrary c. The three
cases of `ord-tri (fst δ) (fst c)` are: δ ∈ c, where c's own transitivity gives
δ ⊆ c; δ = c, where there is nothing to do; and c ∈ δ, where c is a qualifying
candidate strictly below the least one, which `δ-min` refutes.

**A CANDIDATE ABOVE THE WITNESS θ NEVER ENTERS THE SELECTION AND DOES NOT NEED
TO.** The selection runs over `⟪ sucV (fst θ) ⟫`. If c lies outside it, then
`ord-tri` puts δ ∈ c or δ = c, and both branches close without touching the
domain. So the bound the selection needs costs no generality in the conclusion.

## WHAT IT NEEDS

**ONE INPUT. NOT SEVEN, NOT THREE, ONE** (`Probe526.agda:178-183`):

    CardAboveL : Type (ℓ-suc ℓ)
    CardAboveL =
        (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ θ ∈ SL.S ]
           (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

The three-way split the brief asked for, over every name the reduction consumes:

| input | status | at |
|---|---|---|
| `CardAboveL`, some ordinal L-cardinal above κ | **STATED NOWHERE** | Probe526.agda:178-183 |
| `ambient→internal` | delivered in a probe, HERE | Probe526.agda:106-108 |
| `readL`, code to ambient injection | delivered in `src/` | src/L/CantorBernstein.lagda.md:33-38 |
| `leastOf` and `IsLeast` | delivered in `src/` | src/L/WellOrder/Base.lagda.md:130-131, :158-160 |
| `ordSWO`, the ordinal well-order | delivered in `src/` | src/L/Ordinal/SquareLaw.lagda.md:176-182 |
| `ord-tri`, trichotomy | delivered in `src/` | src/L/Ordinal/Linear.lagda.md:136 |
| `mem-ord` | delivered in `src/` | src/L/Ordinal.lagda.md:221 |
| `suc-ord` | delivered in `src/` | src/L/Ordinal.lagda.md:96 |
| `up`, `self`, `self-eq`, the crossing at a stage | delivered in `src/` | src/L/Cardinal.lagda.md:77-79, :103-107 |
| `member`, `fiber` | delivered in `src/` | src/V/Presentation.lagda.md:31, :34 |
| `isL-trans` | delivered in `src/` | src/L/Constructible.lagda.md:379 |
| `finite-excl-ω` | delivered in `src/` | src/L/InjChain.lagda.md:152-156 |
| `ωʟ`, `∅ʟ` | delivered in `src/` | src/L/Axioms/Infinity.lagda.md:69-70, src/L/Axioms/Basic.lagda.md:508-509 |
| `∈-irrefl` | delivered in `src/` | src/V/Hierarchy.lagda.md:155 |
| `SuccCardL`, `IsCardinalL`, `IsCardinal`, `InjCode` | delivered in `src/` | src/L/GCH.lagda.md:46-53, src/L/Cardinal.lagda.md:230-233, :223-228, src/L/BoundedSubset.lagda.md:1046-1047 |
| `internal→ambient`, the converse readback | **STATED NOWHERE** and NOT on this bill | Probe526.agda:115-116 |

**`internal→ambient` IS ON THE LIST BECAUSE THE NEXT BRIEF WILL WANT IT AND THE
REDUCTION DOES NOT.** Row B5 of `[LJ-1.523]`
(`agents/tasks/LJ-1-523/lj-1.523-report.md:230`) needs an AMBIENT refutation at
δ, and what this task delivers at δ is the INTERNAL one. The bridge between the
two runs the wrong way for that row: section 2's implication is ambient ⟹
internal, and B5 wants internal ⟹ ambient. **So B4 and B5 are not the same fact
twice, and closing B4 does not touch B5.**

### What `CardAboveL` is, and why I do not price it

**IT IS THE HARTOGS FACT, AND THE BRIEF FORBADE ASSUMING A HARTOGS
CONSTRUCTION EXISTS.** It does not exist: `grep -rn "Hartogs" src` returns
nothing, which re-confirms `[LJ-1.523]`'s check
(`agents/tasks/LJ-1-523/lj-1.523-report.md:292`) at this date.
`archive/dev/LJ-dispatch-index.md:167` priced an AMBIENT one at 490 to 890
lines, and `archive/dev/LJ-dispatch-index.md:170` records that one WAS built
and green:

> | LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |

**1058 lines is a MEASURED ambient price, and it is not in the tree today.**

**I DO NOT CARRY THAT NUMBER OVER TO THE INTERNAL FORM, AND NOBODY MAY.** A
measured price does not transfer by analogy any more than a measured cure does
(`AGENTS.md:45`). Two things differ at the internal form and I cannot say from
here which way they push:

1. The predicate is WEAKER (section 2), so refuting membership of the Hartogs
   set is HARDER, not easier: `IsCardinalL θ` demands only that no L-CODE
   injects θ into a member.
2. The construction must produce an L-ELEMENT θ, so whatever set is collected
   must be shown constructible. That is a demand the ambient form does not make.

**PRICING IT IS THE MATHEMATICIAN'S CALL AND THIS REPORT DOES NOT MAKE IT.**

### The literature does not supply it either

`dev/literature/devlin-II5.md:160` quotes Devlin 5.6: "Proof. By 5.5, 𝒫(κ) ⊆
L_{κ⁺} for all infinite cardinals κ." **The successor cardinal κ⁺ appears in the
source as ambient background and is never constructed there.** So the route
document behind this campaign carries no evidence about the price of B4, and a
brief that funds it against Devlin funds it against nothing.

## MEASUREMENTS

Caliber `-A64m -I0 -M8g`, read off the pane, never set by me. One Agda process
at a time. `_build/2.8.0/agda/agents/tasks/LJ-1-526/Probe526.agdai` deleted
before every run, so each number is the probe re-elaborated against warm `src/`
interfaces. **A cold-tree number is not in this report and nothing may be funded
against these as if it were.**

Sections 1 to 3 only, `runs/s23-1.out`: 4.15 s, peak RSS 701693952 B.

W3 alone (section 1), three forced rechecks, `runs/w3-1.out` to `w3-3.out`.
The slice is kept at `runs/w3-slice.agda.txt`.

| run | wall | peak RSS |
|---|---|---|
| 1 | 2.16 s | 384401408 B |
| 2 | 2.03 s | 384401408 B |
| 3 | 1.97 s | 384385024 B |

Median **2.03 s**, median peak RSS **384401408 B**, which is 366.6 MiB.

Full file, sealed, three forced rechecks, `runs/s4-sealed-1.out` to `-3.out`:

| run | wall | peak RSS |
|---|---|---|
| 1 | 13.98 s | 1551482880 B |
| 2 | 14.03 s | 1551482880 B |
| 3 | 14.16 s | 1551466496 B |

Median **14.03 s**, median peak RSS **1551482880 B**, which is 1479.6 MiB.

A fourth run after the last edit to this report, `runs/final.out`, is exit 0 at
14.43 s. **The delivered file is the file that was measured.**

### THE SEAL, RE-MEASURED AT A NEW SITE

**UNSEALED, THIS FILE TOOK 112.98 s** (`runs/s4-2.out`; the source is kept at
`runs/unsealed.agda.txt`). Sealed, the median of three is 14.03 s. **The factor
is 8.05, and the only change is four lines: `opaque` around `w`, and `w-lt`
proved by `refl` inside a second `opaque unfolding w`.**

**THE UNSEALED NUMBER IS ONE RUN AND NOT A MEDIAN.** I ran the unsealed file
once, saw the cost, and sealed. Nothing may be funded against 112.98 s as if it
were three runs.

`src/L/Cardinal.lagda.md:85-92` states the cure and its measurement: "The
well-order is SEALED. Transparent, its comparison unfolds the union
representation `⟪ sucV (fst α) ⟫` once in `least` below, and again inside every
conversion check that `κ-min-at` runs. The seal makes `leastOf w` a stuck atom
... and the whole master falls from about 100 s to about 9 s."

**THIS IS A RE-MEASUREMENT AND NOT A TRANSFER.** I hit the 113 s first, on a
different predicate, a different consumer and a different file, and applied the
cure afterwards. The Boundary's "a measured cure does not transfer by analogy"
is answered: it was re-measured at its own site and it holds, at 8.05x here
against about 11x there.

**THE CONSUMER THAT PAYS IS THE SAME SHAPE.** There it was `κ-min-at`; here it
is `leastness`, and both are the one place where a member of the tower is
compared with the selected one. A future selection over `ordSWO` should seal
before it measures.

### Estimate against measured

**ESTIMATE for the Agda was about 150 lines, of which the obligation about 40.
MEASURED 292 lines, 142 of them non-blank and non-comment.** The file is 195
percent of the estimate on raw lines and 95 percent on code lines.

- **The obligation: estimated about 40, measured 6** (`Probe526.agda:169-174`),
  and it is a TYPE and not a term.
- **W3: estimated about 25 lines and under 40 seconds. Measured 5 code lines
  and 2.03 s** (`Probe526.agda:72-77`). The estimate was 5x high on lines and
  20x high on seconds, because it priced a search for a witness and the witness
  was ∅.
- **The reduction was not in the estimate and it is 104 code lines**
  (`Probe526.agda:178-292`). It is why the file is at 195 percent.
- **Comments are 150 of the 292 lines.** Every `file:line` in this report that
  points into the probe is also written beside the definition it justifies.

## WHAT THE NEXT BRIEF SHOULD KNOW

**1. B4 IS ONE INPUT AND IT HAS A NAME.** `CardAboveL`. Everything else the
successor cardinal needs is in the tree today, and the reduction is green.
`[LJ-1.523]`'s seven unpaid inputs become six the moment `CardAboveL` lands.

**2. DO NOT SEND A BRIEF THAT ASKS FOR κ⁺ DIRECTLY.** It would rebuild the 104
lines of `module Reduce` and discover the same wall. Ask for `CardAboveL`.

**3. THE ambient-TO-internal BRIDGE EXISTS AND THE OTHER DIRECTION DOES NOT.**
Any row of `[LJ-1.523]`'s list B that wants an AMBIENT fact out of an INTERNAL
one, and B5 is exactly that (`agents/tasks/LJ-1-523/lj-1.523-report.md:230`),
is not helped by this task. **The two directions are separate purchases.**

**4. ω IS A CARDINAL BOTH WAYS AND IT COST FOUR LINES.** Any statement in this
campaign that was parked because nothing satisfied a cardinal predicate should
be re-read against `Probe526.agda:135-148` before it is re-priced.

**5. SEAL A SELECTION OVER `ordSWO` BEFORE MEASURING IT.** 8.05x here.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ.**
  `archive/dev/LJ-dispatch-index.md:166` reads: "| LJ-1.90-A | Orchestrator audit: IsCardinal is never inhabited | CONFIRMED | Two hits in src: the definition and the hypothesis. The probe's own kappa, sucV omega, is not a cardinal either |".
  `archive/dev/LJ-dispatch-index.md:167` reads: "| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |".
  Both are answered in `## AMBIENT AGAINST INTERNAL`, and neither survived
  re-measurement in the form the brief carried it.
- `archive/dev/JOURNAL-archived.md`. **READ.**
  `archive/dev/JOURNAL-archived.md:1371` reads: "the predicates GENERALLY (equinumerosity, cardinal, successor cardinal, as formulas with their".
  This is a formulation ruling for a cardinal chapter that was never built, and
  it does not bind the reduction: `SuccCardL` is already stated in `src/`
  (`src/L/GCH.lagda.md:46-53`) and the brief forbade weakening it, so I had no
  formulation choice to make.
- `archive/dev/JOURNAL.md`. **READ, AND IT CARRIES NOTHING FOR THIS TASK.**
  `archive/dev/JOURNAL.md:1` reads: "# ARCHIVED 2026-08-20". The file is a
  tombstone: the per-episode journal is retired in favour of
  `agents/tasks/<CODE>/`. Zero hits for `IsCardinal`, `successor cardinal` or
  `Hartogs`.
- `dev/ARCHIVE.md`. **DECLINED, AND THE DECLINE IS MEASURED.** It is the
  registry of retired MODULES. `dev/ARCHIVE.md:3` reads:
  "The registry of Bedrock's retired modules. One entry per module, written at".
  Nothing in this task retires a module, and the file has zero hits for `IsCardinal`,
  `successor cardinal` and `Hartogs`. Not used.
- `archive/dev/DD-archived.md`. **DECLINED.** `archive/dev/DD-archived.md:1`
  reads: "# THE `DD` RULING SERIES, archived in full 2026-08-18". It is the
  ruling series set aside by amendment A7, and its dispositions live at
  `dev/memos/LJ-4-pod-program-design.md` section 7.1. Zero hits for
  `IsCardinal`, `successor cardinal` and `Hartogs`. Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ, AND IT CARRIES A FINDING.**
  `dev/literature/devlin-II5.md:160` reads: "> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),".
  **Devlin's 5.6 USES κ⁺ and never constructs it.** The successor cardinal is
  ambient background in the source, so the route document behind this campaign
  carries no evidence about B4's price. This is in
  `## WHAT IT NEEDS`.
- `dev/literature/truncation-and-selection.md`. **READ.**
  `dev/literature/truncation-and-selection.md:76` reads: "truncated existence of an injection.** That is the HoTT Book's own definition,".
  It settles why `CardAboveL` and the obligation are both stated under `∥_∥₁`
  and why that costs nothing: the conclusion `∥ Σ[ δ ] SuccCardL δ κ ∥₁` is a
  proposition, so `PT.map` carries the witness through
  (`Probe526.agda:286`) with no untruncation question to answer.
- `dev/literature/digest.md`. **DECLINED.** `dev/literature/digest.md:1` reads:
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  It pins the RUD route, which is the definability layer under `Def`. This task
  touches no definability question. Not used.
- `dev/literature/geology.md`. **DECLINED.** `dev/literature/geology.md:1`
  reads: "# Geology dossier: set-theoretic geology sources and the five questions".
  Set-theoretic geology opens under `[L6]` after the trophies land
  (`dev/literature/geology.md:8`). Not surveyed.
- `dev/literature/terms-2026-08.md`. **DECLINED.**
  `dev/literature/terms-2026-08.md:1` reads: "# The terminology dossier: fourteen renderings for the owner's ruling".
  It is translation-terminology evidence for an owner's ruling, and this report
  mints no term. The Boundary forbids me choosing a glossary entry anyway. Not
  used.

## HOUSEKEEPING

Written only in `agents/tasks/LJ-1-526/`, which is this task's declared write
scope. Nothing landed in `src/`. No commit, no push. No em dash anywhere in this
report or in the probe. No `SPDX-*` header.

The only `_build/` path this task touches is
`_build/2.8.0/agda/agents/tasks/LJ-1-526/Probe526.agdai`, the interface Agda
writes for the probe. **Its lifecycle is already declared**:
`dev/build-manifest.toml:118` is `glob = "2.8.0/**"`, the Agda interface store.
No new manifest entry is owed. I deleted that file before every measurement, so
no number in `## MEASUREMENTS` was taken against a warm interface for the probe
itself.
