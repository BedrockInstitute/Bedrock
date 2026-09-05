# lj-1.589-report: the infinity clause, threaded through row 5

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-589/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one Agda process of mine at a time. I did not
set `GHCRTS`. Nothing is postulated, the probe carries `--safe`, and there is no
hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP EVENT.** The largest maximum resident set size of any run of mine is
1,900,740,608 bytes, about 1.8 GiB, against an 8 GB cap
(`agents/tasks/LJ-1-589/runs/import-2.out:13`). That run is the import price
measurement and it is the longest at 37.28 s (`:12`). No run reported exit 251
and no run printed a heap message.

## VERDICT

**GO. THE OBLIGATION IS INHABITED, AND THE CHEAP ROUTE THE BRIEF PREDICTED IS
THE ONE THAT PAID.** `row5-carries-infinity` is
`agents/tasks/LJ-1-589/Probe589.agda:302-312`. The program's own witness meter
reports `pass exit=0 3.35s`, `0 UNRESOLVED of 1`, `probe_red=False`
(`agents/tasks/LJ-1-589/runs/witness-2.out:3-4`). The probe is green, exit 0 in
3.83 s cold (`agents/tasks/LJ-1-589/runs/final-1.out:4`, `:22`).

**THE THREAD COSTS ONE APPLICATION.** `GCHStatement`'s fourth hypothesis is
already bound at row 5's spend site. `gch-route-without-stage`
(`agents/tasks/LJ-1-558/Probe558.agda:118-128`) binds `κ∉ω` at `:122` and spends
it on row 4 alone at `:123`; row 5 is applied five lines later as `b10 κ δ sc`
(`:128`). The thread is that line with the arguments it already has in scope:
`b10 κ δ ordκ cardLκ κ∉ω sc` (`Probe589.agda:312`). Nothing had to be built, and
nothing had to be weakened.

**AND THE BILL DOES NOT GROW.** Section 7 of the probe closes `[LJ-1.564]`'s
five-row bill with the narrowed row in its fifth place: `gch-from-five-inf`
(`Probe589.agda:421-429`) against `P564.gch-from-five`
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`). Five rows before, five rows
after. `gch-from-five-old-still-pays` (`Probe589.agda:433-440`) shows the old
bill is a special case of the new one, so no route that reads today stops
reading.

**AND THE `CodedShift` SPELLING PAYS THE BILL WITH NO TRANSLATION STEP.**
`gch-from-five-codedshift` (`Probe589.agda:446-453`). That is the line the
square-law brief is aimed at, and section 4 of the probe is why it exists.

## W3, THE WIDEST UNMEASURED TERM

**GO, ON THE FIRST RUN, AND IT WAS THE CHEAP OUTCOME.** The brief named the
term as "whether the trophy's ω-exclusion reaches the consumer", TYPE ONLY, and
ordered it written first and typechecked alone. `agents/tasks/LJ-1-589/runs/W3.agda`
is that slice: `SuccIntoPowerInf` at `:60-64`, row 5 with `src/L/GCH.lagda.md:64`
copied letter for letter into it and nothing else in the file. It imports no
predecessor probe, so it measures the clause and not `[LJ-1.558]`'s import cost.

`agents/tasks/LJ-1-589/runs/w3-1.out:4` is 1.68 s real, `:22` is `EXIT=0`. It
was rechecked alone after the citation corrections landed in its header:
`agents/tasks/LJ-1-589/runs/w3-2.out:4` is 1.74 s, `:22` is `EXIT=0`.

ESTIMATE was about 12 lines and under 90 seconds. MEASURED: 63 lines of file, of
which 5 are the type and the rest are the header and the imports, and 1.68 s.
The seconds estimate held. The line estimate counted the type and not the file.

## THE SPELLING I CHOSE

**I CHOSE THE TROPHY'S OWN SPELLING**, `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`,
`src/L/GCH.lagda.md:64`. It is `ClauseTrophy` at `Probe589.agda:94-95`.

**THE THREE SPELLINGS ON THE PAGE.** The brief named two. There are three types,
because `src/L/CodedShift.lagda.md:37-39` carries TWO hypotheses and only the
first of them is a clause about ω. Naming the second one separately is what let
me measure it.

| name | site, copied letter for letter | probe |
|---|---|---|
| A, the trophy's | `src/L/GCH.lagda.md:64`, `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` | `Probe589.agda:94-95` |
| B, `SquareStepInf`'s | `agents/tasks/LJ-1-581/Probe581.agda:429`, `⟨ ω ∈ fst κ ⟩` | `Probe589.agda:100-101` |
| C1, `CodedShift`'s first | `src/L/CodedShift.lagda.md:38`, `γ∉ω` | `Probe589.agda:106-107` |
| C2, `CodedShift`'s second | `src/L/CodedShift.lagda.md:39`, `numerals` | `Probe589.agda:109-110` |

**ARE THEY INTERDERIVABLE? A AND C YES, UNDER `IsOrd`. B NO, AND THE GAP IS
EXACTLY ω.** Four measurements, each a term and not a sentence.

1. **A AND C1 ARE ONE TYPE, not merely equivalent.** `𝒮ᵥ`'s `_∈ˢ_` field IS the
   library's `_∈_` (`src/V/Hierarchy.lagda.md:83`), and `ωʟ` is the pair
   `(ω , ω∈L)` (`src/L/Axioms/Infinity.lagda.md:70`), so `fst ωʟ` is `ω` by
   reduction. Four identity functions say it: `trophy-is-codedshift∉` and
   `codedshift∉-is-trophy` (`Probe589.agda:122-126`), and `∈ˢ-is-∈` and
   `∈-is-∈ˢ` underneath them (`:130-134`), so the reading does not rest on the
   negation hiding a difference.
2. **B IMPLIES A, and it needs no hypothesis on κ.** `squarestepinf→trophy`
   (`Probe589.agda:148-149`). If ω belonged to κ and κ belonged to ω, then ω
   would belong to ω, because ω is transitive (`ω-ord`,
   `src/L/Ordinal.lagda.md:263-264`), and `∈-irrefl`
   (`src/V/Hierarchy.lagda.md:155-156`) refuses that.
3. **A DOES NOT IMPLY B, AND ω IS THE COUNTEREXAMPLE.** `ωʟ` is an L-ordinal
   (`ωʟ-ord`, `Probe589.agda:153-154`, from `ω-ord`), so the trophy's Π genuinely
   reaches it. It satisfies A (`ωʟ-trophy`, `:157-158`) and it REFUTES B
   (`ωʟ-not-squarestepinf`, `:161-162`). So no function can turn A into B at
   every κ: `no-trophy→squarestepinf` (`:167-169`). **Adding `IsOrd` does not
   repair it**, because ω is an ordinal: `no-trophy→squarestepinf-ord`
   (`:174-178`).
4. **C2 IS FREE.** `CodedShift` takes `numerals` as a SEPARATE hypothesis. It
   does not have to. Under `IsOrd` and A, `numerals` is a theorem by trichotomy:
   `numerals-from-trophy` (`Probe589.agda:193-203`), through `ord-tri`
   (`src/L/Ordinal/Linear.lagda.md:136-137`). The other direction is the first
   projection (`trophy-from-codedshift`, `:206-208`). So A and C are
   interderivable under `IsOrd`: `codedshift-from-trophy` (`:211-215`).

**WHY THAT DECIDES IT.** B is strictly stronger than A, and the κ it excludes
is ω. `GCHStatement` quantifies every κ with `IsOrd (fst κ)`, `IsCardinalL κ`
and A (`src/L/GCH.lagda.md:61-64`). **I MEASURED TWO OF THOSE THREE AT ω AND NOT
THE THIRD.** `ωʟ-ord` is `IsOrd (fst ωʟ)` (`Probe589.agda:153-154`) and
`ωʟ-trophy` is A at ω (`:157-158`); **I did NOT build `IsCardinalL ωʟ` and this
report does not assert it.** So what is proved is this: B's clause is false at
an L-ordinal that satisfies A, and no hypothesis this probe carries repairs
that. If ω is also an L-cardinal, and the literature's theorem is stated for
every infinite cardinal (`dev/literature/devlin-II5.md:160`), then B skips a
required instance outright. A and C are the same clause, so choosing between
them is a matter of idiom and not of strength; I state row 5 in A because A is the type
`GCHStatement` already writes and the spend site already binds, and I give the C
form as well (`SuccIntoPowerCS`, `Probe589.agda:251-256`) so a proof written in
`CodedShift`'s idiom plugs in with no translation.

**AND THIS IS A RE-MEASUREMENT, NOT A TRANSFER.** `AGENTS.md:45` forbids moving
a measured cure by analogy, and the same cure was measured before at a different
site: `archive/dev/LJ-dispatch-index.md:179` records `[LJ-1.103]` choosing "alpha
not in omega" over a stronger premise because "the site runs at omega", and
`:192` records `[LJ-1.116]` finding that "Init is false at omega and at
successors". `Init`'s second conjunct is `⟨ ω ∈ˢ α ⟩`
(`src/L/Ordinal/SquareLaw.lagda.md:694`), which is spelling B, and the chapter's
own comment says "so omega itself is not initial" (`:689-690`). Those two rows
agree with what section 3 of the probe proves. I did not import either
conclusion. The terms above are measured at this site.

## WHAT THE SQUARE-LAW BRIEF SHOULD SAY

The square-law task must conclude a coded square at every κ that satisfies
`IsOrd (fst κ)`, `IsCardinalL κ` and `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`, in that
spelling, because those three are what row 5 now carries
(`SuccIntoPowerInf`, `agents/tasks/LJ-1-589/Probe589.agda:243-247`) and what the
campaign's bill now passes down (`gch-from-five-inf`, `:421-429`). It must NOT
be stated as `SquareStepInf` (`agents/tasks/LJ-1-581/Probe581.agda:427-432`),
because that type's clause `⟨ ω ∈ fst κ ⟩` is refuted at ω
(`Probe589.agda:161-162`), which is an L-ordinal the trophy's own clause admits
(`:153-158`), and no hypothesis the tree has repairs that gap (`:174-178`). It
may equally be stated in `CodedShift`'s two-hypothesis idiom
(`src/L/CodedShift.lagda.md:38-39`), because the second hypothesis is derivable
from the first plus `IsOrd` (`numerals-from-trophy`, `Probe589.agda:193-203`)
and because that form already closes the bill without a translation step
(`gch-from-five-codedshift`, `:446-453`).

## WHAT THE OBLIGATION IS, AND WHAT IT IS NOT

**IT IS.** `row5-carries-infinity` (`Probe589.agda:302-312`):

    (zf : ModelL.isZFModel)
  → P558.SuccCardExists → P558.PowerIntoSucc zf → SuccIntoPowerInf zf
  → GCHStatement zf

Rows 4 and the hard leg are `[LJ-1.558]`'s own types, taken as that task
delivered them and not retyped (`Probe589.agda:80-81`). `[LJ-1.558]` is GO
(`agents/tasks/LJ-1-558/lj-1.558-report.md:7`).

**IT IS NOT `SquareStepInf` AND IT IS NOT THE SQUARE LAW.** The brief forbids
both and AD12 gives this brief one obligation. Neither name occurs as a
definition in the probe. Section 3 REFUTES B's clause at ω; it does not build B.

**IT IS NOT A WEAKENING OF WHAT WAS OWED.** `wider-pays-min`, `wider-pays-full`
and `wider-pays-cs` (`Probe589.agda:260-270`) show `[LJ-1.558]`'s row 5 pays all
three narrowed forms, so nothing already owed became harder. The narrowing makes
row 5 a SMALLER obligation, which is the whole point.

**THREE NARROWED FORMS, AND THEY ARE ORDERED.** `SuccIntoPowerInfMin` carries
the clause and nothing else (`:234-238`; it is W3's type).
`SuccIntoPowerInf` carries all four of `GCHStatement`'s hypotheses on κ
(`:243-247`). `SuccIntoPowerCS` carries `CodedShift`'s pair (`:251-256`).
`min-pays-full` (`:276-278`), `full-pays-cs` (`:280-282`) and `cs-pays-full`
(`:284-287`) move between them, so the choice is free at the consumer and the
square-law brief may take whichever it finds easiest to prove.

## THE C-42 SWEEP: HOW FAR THE SHAPE EXTENDS

C-42 says a measurement of one site says nothing about how many other sites
carry the shape, so I counted before reporting the cure as done.

**THE SHAPE IS: A ROUTE THAT TAKES ROW 5 AS A HYPOTHESIS.** If row 5 is narrowed,
each such route needs the same one-application change. I grepped `SuccIntoPower`
over `agents/tasks` and `src`.

**`src/` HAS NO HIT.** Row 5 is not in `src/` today, under any of its names. The
narrowing touches no master.

**IN `agents/tasks`, THE COUNT IS 19 HYPOTHESIS LINES ACROSS 7 LIVE PROBES**,
plus one line where row 5 is a CONCLUSION and not a hypothesis:

| probe | row 5 as a hypothesis, at | conclusion |
|---|---|---|
| `agents/tasks/LJ-1-558/Probe558.agda` | `:120`, `:189` | `GCHStatement zf` |
| `agents/tasks/LJ-1-558/Probe558.agda` | `:257` | `StageCountedCoded` |
| `agents/tasks/LJ-1-564/Probe564.agda` | `:337`, `:374`, `:414`, `:460` | `GCHStatement zf` |
| `agents/tasks/LJ-1-569/Probe569.agda` | `:193`, `:210` | `GCHStatement zf` |
| `agents/tasks/LJ-1-569/Probe569.agda` | `:115` | `P550.AmbientCardAtSucc` |
| `agents/tasks/LJ-1-570/Probe570.agda` | `:114`, `:203` | `GCHStatement zf` |
| `agents/tasks/LJ-1-571/Probe571.agda` | `:197`, `:224` | `GCHStatement zf` |
| `agents/tasks/LJ-1-578/Probe578.agda` | `:200`, `:468`, `:554` | `GCHStatement zf` |
| `agents/tasks/LJ-1-550/Probe550.agda` | `:196` | `GCHStatement zf` |
| `agents/tasks/LJ-1-550/Probe550.agda` | `:338` | a longer chain |
| `agents/tasks/LJ-1-546/Probe546.agda` | `:163` is row 5 as the CONCLUSION | `SuccIntoPower zf` |

**SIXTEEN OF THE NINETEEN CONCLUDE `GCHStatement zf` DIRECTLY, so at each of
them the clause is bound for free** by the trophy's own Π, exactly as it is at
`Probe558.agda:122`. Every one of the seven probes already writes `κ∉ω`
somewhere. **THREE DO NOT** (`Probe558.agda:257`, `Probe569.agda:115`,
`Probe550.agda:338`): they conclude a non-trophy type, so at those the clause
must be added to the consumer's own statement first. That is the same threading
problem one level up, and it is the only place this cure is not one application.

**AND THE ONE CONCLUSION SITE IS FREE.** `transfer-suffices`
(`agents/tasks/LJ-1-546/Probe546.agda:163`) PRODUCES row 5. Narrowing row 5
weakens that theorem's conclusion, so it keeps paying.

**NONE OF THOSE PROBES IS EDITED BY THIS TASK.** They are frozen records of
closed tasks. The count is what the mathematician needs when a row is finally
written into `src/`, not a list of files to change now.

## THE PRECEDENT, AND IT IS NOT MINE

**`[LJ-1.564]` ALREADY MADE THIS EXACT MOVE ONCE, ON THE OTHER LEG.**
`PowerIntoSuccAt` is the hard leg narrowed by `IsOrd (fst κ)` and by the
trophy's fourth hypothesis, and the file says so in those words:
"`PowerIntoSucc` with the two premises `GCHStatement` already binds"
(`agents/tasks/LJ-1-564/Probe564.agda:325-330`).
`gch-route-with-premised-hard` (`:335-345`) is that task's type check that the
route still closes with the weaker row, and its comment at `:321-322` says what
the check is for. Section 7 of this probe is that move on row 5, built on that
task's own terms.

**SO THE ANSWER TO "CAN ROW 5 CARRY THE CLAUSE" WAS ALREADY YES FOR ROW 3, AND
NOBODY HAD ASKED IT FOR ROW 5.** `[LJ-1.581]` is the task that noticed
(`agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md:141-149`).

## WHAT IS TAKEN FROM WHOM

- **`[LJ-1.558]`, GO** (`agents/tasks/LJ-1-558/lj-1.558-report.md:7`).
  `SuccCardExists`, `PowerIntoSucc` and `SuccIntoPower` are taken as that task
  delivered them.
- **`[LJ-1.564]`, GO** (`agents/tasks/LJ-1-564/lj-1.564-report.md:8`).
  `PowerIntoSuccAt`, `power-into-succ-at`, `bounded-subset-theorem`, `b4-paid`,
  `b6-paid`, `b7-paid`, `b8-paid` and `StageCountedCoded` are taken as that task
  delivered them.
- **`[LJ-1.550]`, NO-GO** (`agents/tasks/LJ-1-550/lj-1.550-report.md:6`).
  **NOTHING `[LJ-1.550]` FAILED TO DELIVER IS USED AS A FACT.** Its residues
  `AmbientCardAtSucc`, `SqAt`, `CoHyps`, `SubsetIntoStage`, `AbsorbsAt`,
  `LimitAbove` and `BoundedSubsetTheorem` appear ONLY as HYPOTHESES of section
  7's statements, exactly as they appear in `[LJ-1.564]`'s own GO type
  (`agents/tasks/LJ-1-564/Probe564.agda:458-460`), so section 7 asserts nothing
  about their truth. Its refused obligation `bridge-without-B5` is not named
  anywhere in this probe.
- **`[LJ-1.581]`, NO-GO, UPHELD** (`agents/tasks/LJ-1-581/review-of-LJ-1-581-1.md:6`).
  **I INHABIT NOTHING OF ITS BRIEF'S TYPE.** I take from it only the two names it
  put on the page for the next brief to choose between, and section 3 REFUTES
  the clause of one of them at ω.

## MEASUREMENTS

Every number below is from a file in `agents/tasks/LJ-1-589/runs/`, under
`GHCRTS="-A64m -I0 -M8g"`, one Agda process at a time.

| run | what | real | max RSS | exit |
|---|---|---|---|---|
| `w3-1.out` | W3 alone, TYPE ONLY, no predecessor probe | 1.68 s (`:4`) | 387,514,368 (`:5`) | 0 (`:22`) |
| `import-1.out` | `LJ-1-558.Probe558` alone | 1.96 s (`:5`) | 420,839,424 (`:6`) | 0 (`:23`) |
| `probe-1.out` | `Probe589.agda`, sections 1 to 6, first check | 1.70 s (`:4`) | 396,361,728 (`:5`) | 0 (`:22`) |
| `probe-2.out` | the same, own interface removed | 1.82 s (`:4`) | | 0 (`:22`) |
| `probe-3.out` | the same, warm recheck | 1.54 s (`:3`) | 416,514,048 (`:4`) | 0 (`:21`) |
| `neg-1.out` | THE NEGATIVE CONTROL, expected red | 0.77 s (`:7`) | 271,613,952 (`:8`) | **42** (`:25`) |
| `import-2.out` | `LJ-1-564.Probe564` alone | 37.28 s (`:12`) | 1,900,740,608 (`:13`) | 0 (`:30`) |
| `probe-4.out` | `Probe589.agda` with section 7, warm | 3.81 s (`:4`) | 715,358,208 (`:5`) | 0 (`:22`) |
| `probe-5.out` | the same, own interface removed, FINAL | 3.66 s (`:4`) | 715,358,208 (`:5`) | 0 (`:22`) |
| `witness-1.out` | the program's own witness meter | 2.96 s (`:57`) | | 0 (`:59`) |
| `w3-2.out` | W3 alone, rechecked after the header corrections | 1.74 s (`:4`) | 387,497,984 (`:5`) | 0 (`:22`) |
| `final-1.out` | `Probe589.agda` FINAL, own interface removed | 3.83 s (`:4`) | 715,358,208 (`:5`) | 0 (`:22`) |
| `witness-2.out` | the witness meter, FINAL | 3.35 s (`:4`) | | 0 (`:5`) |
| `final-2.out` | `Probe589.agda`, last green check of the return, warm | 2.82 s (`:3`) | 758,611,968 (`:4`) | 0 (`:21`) |

**THE NEGATIVE CONTROL IS WHY SECTION 2's IDENTITY FUNCTIONS ARE A MEASUREMENT.**
`agents/tasks/LJ-1-589/runs/Neg589.agda.txt:41-43` writes the identity function
section 3 says cannot exist. It FAILS with `[UnequalTerms]`,
`⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥ !=< fst (ω ∈ fst κ)`
(`agents/tasks/LJ-1-589/runs/neg-1.out:4-6`), exit 42 (`:25`). So the elaborator
does not accept `λ x → x` between any two of these types, and the four that it
does accept are facts. **It is kept as a `.txt` and not as an `.agda`**, so
`make probes` and the closure gate never see a red file, which is how
`[LJ-1.558]` kept its own control
(`agents/tasks/LJ-1-558/runs/NoStage558.agda.txt`).

**THE COST OF SECTION 7 IS 2.27 SECONDS AND 298,844,160 BYTES**, warm against
warm: `probe-3.out` is 1.54 s and 416,514,048 max RSS without it (`:3`, `:4`),
`probe-4.out` is 3.81 s and 715,358,208 with it (`:4`, `:5`). The 37.28 s of
`import-2.out` is the one-time cold cost of `LJ-1-564.Probe564` and the six
probes it carries (`import-2.out:4-11`).

## ESTIMATE AGAINST MEASURED

The brief estimated about 150 lines in the probe, of which the obligation is
about 35, on the basis that `[LJ-1.581]` worked the same site and called this
smaller than the square law.

**MEASURED: 453 lines in the probe, of which the obligation is 11**
(`Probe589.agda:302-312`). The obligation came in at under a third of the
estimate, because the clause was already in scope at the spend site and the
thread is one application. The file is three times the estimate, and the reason
is nameable and not a slip: **the estimate priced the thread, and the file also
carries the decision.** Sections 1 to 4 exist because the brief made the
spelling choice this task's main deliverable, and a choice between three types
is worth nothing unless the comparisons are terms. Sections 1 to 4 are
`Probe589.agda:82-215`, 134 lines. Section 7 is `Probe589.agda:333-453`, 121
lines, and it is not in the estimate at all: it closes the campaign's own bill
rather than `[LJ-1.558]`'s route, which the brief did not ask for and which the
next brief needs. Section 5 is 72 lines and section 6 is 45.

**THE BRIEF'S PREDICTION WAS RIGHT.** It said "So the clause may already be
available at the consumer and simply not threaded. That is the cheap outcome and
you should test it first." It is, and it was.

## W2 AND W4

**W2.** Answered. The mathematics is written once at a generic carrier and
instantiated. `ClauseTrophy`, `ClauseSquareStepInf`, `ClauseCodedShift∉` and
`ClauseCodedShiftNum` are functions of an arbitrary `κ : SL.S`
(`Probe589.agda:94-110`), and `numerals-from-trophy` (`:193-203`) is proved at
an arbitrary γ, not at a site. The one instantiation is the counterexample, `ωʟ`
(`:153-162`), and a counterexample is a site by definition. Nothing in this task
is written twice at two carriers, and the two trophies share it: the clause and
the row are stated at `𝒮ʟ` and `GCHStatement`, which is the shared statement.
No deadline forced a fixed form and there is no conflict to report.

**W4.** Not engaged. This task retires no module. Nothing was moved to
`archive/` and nothing was deleted. `dev/ARCHIVE.md` is untouched.

## WHAT THE NEXT BRIEF SHOULD KNOW

1. **THE SPELLING IS SETTLED AND IT IS THE TROPHY'S.** `## THE SPELLING I CHOSE`
   above has the four terms. The next brief may write the clause as
   `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` or as `CodedShift`'s pair, and it must not write
   it as `⟨ ω ∈ fst κ ⟩`.
2. **ROW 5 NOW HAS THREE NARROWED FORMS, ALL OF WHICH CLOSE THE BILL.** Pick by
   which is easiest to prove, not by which the consumer wants:
   `gch-from-five-inf`, `gch-from-five-old-still-pays` and
   `gch-from-five-codedshift` (`Probe589.agda:421-453`) close it from three
   different fifth rows.
3. **THREE SITES STILL DO NOT CARRY THE CLAUSE**, and they conclude a non-trophy
   type: `Probe558.agda:257`, `Probe569.agda:115`, `Probe550.agda:338`. The
   `## THE C-42 SWEEP` section has the count and the reason. None of them is on
   the five-row bill.
4. **I DID NOT TEST WHETHER THE NARROWED ROW 5 IS TRUE.** This task measured that
   the clause can be carried and that carrying it costs nothing upstream. Whether
   `SuccIntoPowerInf` is inhabitable is the square-law question and it is open.
   `[LJ-1.581]` refuted the un-clause'd form (`Probe581.agda:376-379`); nothing
   in this file refutes or inhabits the clause'd form.
5. **`IsCardinalL ωʟ` IS UNMEASURED AND I DID NOT ASSUME IT.** Section 3 proves
   `IsOrd (fst ωʟ)` and that ω satisfies the trophy's clause. It does NOT prove
   ω is an L-cardinal, so "B skips the first infinite CARDINAL" is a sentence
   this report does not license, and I have not written it. What is licensed is
   that B is false at an L-ordinal the trophy's clause admits. If the
   square-law brief wants the stronger sentence, `IsCardinalL ωʟ` is the term
   to fund, and it is small.
6. **`[LJ-1.581]`'s FIRST REOPENER IS NOW HALF ANSWERED.** It offered
   `SquareStepInf` "or the same type with the `γ∉ω`-plus-`numerals` spelling"
   (`agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md:166-167`). Its critic
   already warned they are not the same type
   (`agents/tasks/LJ-1-581/review-of-LJ-1-581-1.md:199-203`). This task proves
   the critic right by a term and says which of the two to fund.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:192`: **READ.** The line holds
  `Init is false at omega and at successors`, in the outcome cell of
  `[LJ-1.116]`. That row records the same finding my section 3 proves by a term:
  the `Init` spelling, which is spelling B, fails at ω.
  `archive/dev/LJ-dispatch-index.md:179`: **READ.** The line holds
  `The premise is alpha not in omega, matching sq`, in the outcome cell of
  `[LJ-1.103]`. That row records the same CURE, chosen at a different site and
  landed in `src/`. `AGENTS.md:45` forbids transferring it by analogy, so I
  re-measured it here and imported neither conclusion. I grepped this file for
  `SuccIntoPower` and `GCHStatement` first: no hit, so it holds no history of
  row 5 itself.
- `archive/dev/JOURNAL-archived.md`: declined. It is the retired route's episode
  log, archived 2026-08-09 when the two-tower route was ruled. Row 5 is on the
  ruled route, not the retired one, and the file has no `SuccIntoPower` hit.
- `archive/dev/JOURNAL.md`: declined. It is the per-episode journal, retired
  2026-08-20 because every task keeps its own record. This task's record is
  `agents/tasks/LJ-1-589/`. No `SuccIntoPower` hit.
- `archive/dev/PLAN-archived.md`: declined. It is the construction registry as of
  archival day. The live bill is `agents/tasks/LJ-1-564/Probe564.agda:456-463`
  and it is a term, not a registry row. No `SuccIntoPower` hit.
- `archive/dev/DECISIONS-archived.md`: declined. The whole `D` series was
  archived 2026-08-09 and a bare `D<n>` resolves only against it. No clause of
  this task cites a `D` code, and the file has no `SuccIntoPower` hit.
- `dev/ARCHIVE.md`: not used. It is the retired-module registry and W4 is not
  engaged: this task retires nothing.

## LITERATURE USED

- `dev/literature/devlin-II5.md:160`: **READ.** The line holds
  `for all infinite cardinals κ. So by 1.1(vii),`, inside the quoted proof of
  5.6. The source proves GCH at ALL infinite cardinals, and ω is one of them.
  That is the outside check on the spelling: a clause that excludes ω, which is
  spelling B, does not state the theorem the literature proves. My section 3
  refutes B at ω from inside the tree; this line says the literature would not
  have accepted it either. W8 does not abort.
- `dev/literature/terms-2026-08.md:292`: **READ.** The line holds
  `cited as a bound, not proved as a theorem`, closing the sense entry for the
  square law, whose subject two lines above is an infinite ordinal. The square
  law's own statement carries an infinity condition, so the row that consumes it
  must carry one too. It is a terminology dossier, so I take the sense from it
  and no number.
- `dev/literature/truncation-and-selection.md`: not used. This task builds no
  truncation and makes no selection; the one `∥_∥₁` in the obligation is
  `GCHStatement`'s own and is mapped, not eliminated (`Probe589.agda:307`).
- `dev/literature/geology.md`: declined. Set-theoretic geology is not this route.
- `dev/literature/digest.md`: not used. Its Gödel-pairing material is about a
  condition on an infinite ordinal in the literature's own construction. That is
  the square law's business and this brief forbids the square law. No number of
  mine comes from it.
