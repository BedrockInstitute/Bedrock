# LJ-1.593 report: the coded square law, at the spelling its predecessor decided

## HEAD
head_slot: coder
machine: shared
verdict: STOP

obligation: agents/tasks/LJ-1-593/Probe593.agda::square-coded (NOT INHABITED)
stop: agents/tasks/LJ-1-593/review-of-square-coded.md

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22, `dev/LESSONS.md:2297`), because the brief ordered it: "Write the
report as a skeleton first and fill it as runs land". No commit, no push. I
wrote only inside `agents/tasks/LJ-1-593/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M8g"`
(`agents/tasks/LJ-1-593/runs/w3-1.out:2`), ONE Agda process at a time. I did
not set `GHCRTS`. Nothing is postulated and no hole is left, so every reduction
in the probe is a measurement and not a claim. Every file of this task is a raw
`.agda`, a `.sh` or a `.md`, so none carries an ` ```agda ` fence, all count 0
in-fence lines, and the ratio bar cannot fire on them.

## VERDICT

**STOP, AND IT IS A REDUCTION AND NOT A WALL.** The obligation is not
inhabited: no term of `agents/tasks/LJ-1-593/Probe593.agda` is named
`square-coded`. The stated stop is
`agents/tasks/LJ-1-593/review-of-square-coded.md`.

**THE PROBE IS GREEN, EXIT 0**, on the file as it now stands:
`agents/tasks/LJ-1-593/runs/final-3.out:22`, a run made after the interface was
deleted. It carries no hole and no postulate, so every reduction in it is a
measurement and not a claim.

**AND THIS IS THE THIRD STOP ON THIS OBJECT, WHICH THE BRIEF SAYS WOULD BE A
RULING. I THINK THE RULING SHOULD BE THE OPPOSITE OF THE ONE THE BRIEF
ANTICIPATED.** The brief says a third NO-GO "would be a ruling: the
mathematician would take to the owner that the coded square law is the
campaign's standing blocker, with three measured attempts behind it". **The
coded square law is not a blocker and it is not standing. It is B9, and B9 is
already row four of the campaign's bill.**

Four results, each a term in a green file.

1. **THE AMBIENT SQUARE LAW IS FREE AT THIS SPELLING, AND `IsCardinalL` IS NOT
   EVEN SPENT.** `ambient-square` (`Probe593.agda:144`). `sq-trunc-closed`
   (`src/L/SquareLawClosed.lagda.md:325-328`) is CLOSED, and its band is a
   MODULE parameter (`src/L/SquareLawClosed.lagda.md:19-20`), so a caller that
   wants the law AT κ instantiates the band AT κ and `self∈sucV`
   (`src/V/Model.lagda.md:236-237`) pays the band membership with nothing.
   **So `[LJ-1.556]`'s induction hypothesis is not what the tree lacks:
   `src/` has already paid it.**
2. **THE PAIRS INJECT INTO κ, AMBIENTLY, AT EXACTLY THE THREE HYPOTHESES.**
   `pairs-inject-ambiently` (`Probe593.agda:279`). **So nothing about the SIZE
   of the domain is open.** What was open was one thing: a CODE.
3. **AND THE CODE IS B9 AT κ, PLUS 84 GREEN LINES OF AGDA THAT ARE NOW
   WRITTEN.**
   `square-from-b9` (`Probe593.agda:532`) and
   `square-from-the-bills-own-b9` (`Probe593.agda:568`), the second stated at
   `[LJ-1.564]`'s own row and not at a retyped copy.
4. **SO THE CODING WALL HAS ONE PAID SITE AND TWO OPEN SITES, NOT THREE.** See
   `## THE SWEEP (C-42)`.

**W3 IS GO** and green on the first run.

**AND `[LJ-1.552]`'s PRICE IS OVERTURNED.** Its review ruled the coded square
law "a chapter and not a task"
(`agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-192`). Measured: on top
of B9 it is 120 lines, and those lines are written.

## D-10, BEFORE ANY AGDA

The brief orders this section first and calls it "the spelling".

**THE TYPE, IN FULL.**

    square-coded :
        (κ : S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → InjL (P556.Square.sqL κ) κ

**THE THREE HYPOTHESES, EACH AT ITS OWN SITE.** They are not retyped from the
brief; each is copied from the file that carries it.

| hypothesis | site | what it is |
|---|---|---|
| `IsOrd (fst κ)` | `src/L/GCH.lagda.md:61` | `GCHStatement`'s first |
| `IsCardinalL κ` | `src/L/GCH.lagda.md:63` | `GCHStatement`'s third |
| `⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥` | `src/L/GCH.lagda.md:64` | `GCHStatement`'s fourth |

`[LJ-1.589]` carries the same three at `agents/tasks/LJ-1-589/Probe589.agda:243-247`
(`SuccIntoPowerInf`) and the campaign's bill passes them down at
`agents/tasks/LJ-1-589/Probe589.agda:421-429` (`gch-from-five-inf`).

**THE CONCLUSION.** `InjL a b` is `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
(`src/L/GCH.lagda.md:37-38`), and `InjCode` is four conjuncts
(`src/L/Cardinal.lagda.md:223-228`). The domain is `[LJ-1.556]`'s section 1
object, `Square.sqL` (`agents/tasks/LJ-1-556/Probe556.agda:169-176`). So the
conclusion is `[LJ-1.556]`'s `InternalSquare κ`
(`agents/tasks/LJ-1-556/Probe556.agda:332-333`); the probe carries two identity
functions that say the two names are ONE type
(`internal-is-injL`, `injL-is-internal`).

## THE SPELLING I USED

**SPELLING A, THE TROPHY'S: `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`, at
`src/L/GCH.lagda.md:64`.** It is `[LJ-1.589]`'s `ClauseTrophy`
(`agents/tasks/LJ-1-589/Probe589.agda:96-97`).

**WHY, IN ONE SENTENCE.** It is the clause the campaign's bill already passes
down (`gch-from-five-inf`, `agents/tasks/LJ-1-589/Probe589.agda:421-429`), so a
statement at spelling A plugs into row 5 with no translation step at all.

**AND THE CHOICE COSTS THE CONSUMER NOTHING, WHICH IS A TERM AND NOT AN
OPINION.** The brief allows `CodedShift`'s two-hypothesis idiom
(`src/L/CodedShift.lagda.md:38-39`) as an equal alternative. It is equal:
`a-pays-cs` and `cs-pays-a` (probe section 4) move any statement between the
two spellings with no hypothesis added, and they are built from
`trophy-is-cs∉` and `numerals-from-trophy` (probe section 1), which are
`[LJ-1.589]` sections 2 and 4 rebuilt at this file's own bindings rather than
imported. **So the next brief may write either one.**

**I FOUND NO THIRD SPELLING.** I did not state `SquareStepInf`
(`agents/tasks/LJ-1-581/Probe581.agda:427-432`), which `[LJ-1.589]` refuted at
ω (`agents/tasks/LJ-1-589/Probe589.agda:161-162`), and no clause of the probe
mentions `⟨ ω ∈ fst κ ⟩` in any position.

**ONE THING THE SPELLING DECIDED THAT THE BRIEF DID NOT ANTICIPATE.** Spelling
A is exactly the hypothesis `shift-coded` carries
(`src/L/CodedShift.lagda.md:37-40`), so the ONE code the tree has PAID becomes
usable as a LEMMA inside this task. It is what proves κ is a limit
(`Stage.succ-closed`), and that is the hinge of the whole result below. At
spelling B the lemma is not reachable, because `shift-coded` does not take
`⟨ ω ∈ fst γ ⟩`.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND GREEN ON THE FIRST RUN.** The slice is
`agents/tasks/LJ-1-593/runs/W3.agda`, written before any other Agda of this
task and typechecked alone: `agents/tasks/LJ-1-593/runs/w3-1.out:21` reports
`EXIT=0`, at 1.57 s and 397 MB maximum resident against the 8 GB cap
(`runs/w3-1.out:3-4`).

The brief's estimate was about 15 lines and under 2 minutes. Measured: the
slice is 91 lines, of which 42 are comment and 10 blank, so 39 lines of Agda,
and 20 of those are the pragma, the module header and the imports
(`runs/W3.agda:1`, `:35-53`). **The Agda that answers W3 is 19 lines**, against
an estimate of 15, and it ran in 1.57 s against a ceiling of 2 minutes.

**WHAT IT MEASURED.** The pairs of κ can be NAMED as an L-set, with both
readings, under the three hypotheses. And the slice measured one thing more,
which the brief asked for in the words "check it is the same object under these
hypotheses": **the object does not depend on any of the three.**
`unconditional-pays` (`runs/W3.agda:90-91`) is the term. So the narrowing the
brief made to the hypothesis list costs the DOMAIN nothing, and any difficulty
this task meets is in the conclusion and not in the domain.

## WHAT ROW 5 NOW NEEDS

The brief requires this section and asks whether I agree with `[LJ-1.574]`, in
its words: "step 3 is then a `hasSeparationL` over a description it already
carries".

**I AGREE WITH THE SENTENCE AND I CORRECT WHICH STEP MY OBLIGATION IS.**

The sentence is at `agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md:94-96`.
Its three steps are `[LJ-1.552]`'s, at
`agents/tasks/LJ-1-552/review-of-succ-assignment.md:177-187`:

1. compose down to κ, by `L.InjChain.Comp`;
2. the square law inside L;
3. the separation that carves the coded subset, given 1 and 2.

**WHERE I AGREE.** Step 3 needs no new device. `[LJ-1.549]`'s `Residue δ κ`
(`agents/tasks/LJ-1-549/Probe549.agda:668-679`) already suffices for the row
(`residue-suffices`, `agents/tasks/LJ-1-549/Probe549.agda:681-683`), and
`[LJ-1.574]`'s `residue-closes` (`agents/tasks/LJ-1-574/Probe574.agda:775-777`)
closes the obligation from it. `[LJ-1.574]` inhabited that residue at a STAGE
(`residue-at-stage`, `agents/tasks/LJ-1-574/Probe574.agda:715-717`). So the
whole remaining difference is the BOUND, exactly as its report says.

**WHERE I CORRECT IT, AND THE CORRECTION MOVES WORK OFF THIS OBLIGATION.**
`[LJ-1.574]`'s reopener 1 asks for step 2 as its own task and says step 3
follows. **Step 2 is not what moves the bound.** `Residue`'s first clause is
`⟨ s k ⊆ˢ κ ⟩` (`agents/tasks/LJ-1-549/Probe549.agda:671`) and what
`[LJ-1.574]` delivered is that clause at `LsetS β oβ`
(`agents/tasks/LJ-1-574/Probe574.agda:716`). Moving a subset of a STAGE to a
subset of κ is `[LJ-1.552]`'s step 1, the composition down to κ, and step 1's
missing input is **B9** and not the square law.

**AND SECTION 8 OF THE PROBE MAKES THAT PRECISE RATHER THAN ARGUED.** The coded
square law itself reduces to B9 (`square-from-b9`). So step 1 and step 2 are
NOT two independent inputs of row 5: **step 2 is a corollary of step 1's own
missing row.** A brief that funds B9 gets both.

**SO WHAT ROW 5 NOW NEEDS IS ONE ROW AND NOT TWO.** It needs B9 at an infinite
L-cardinal, `B9Inf` in the probe. Everything the square law was going to
contribute is then a term this file already carries.

## THE SWEEP (C-42)

C-42 (`dev/LESSONS.md:3752`) says a refutation measures ONE site and never says
how far the shape extends, so the next action is the sweep and the COUNT comes
before the cure. `[LJ-1.533]` refuted this shape at B9 and reported it had been
refuted twice before that (`agents/tasks/LJ-1-533/lj-1.533-report.md:29-31`).
**Nobody has counted the sites. This is the count.**

**THE SHAPE, AS A TYPE AND NOT AS A PARAGRAPH.** `CodeShape a b`
(`Probe593.agda:301`) is "an ambient injection at this pair, turned into a CODE
at this pair". The four instances below are types in the probe, so the table is
checkable and not believable.

| site | pair | ambient injection | code | state |
|---|---|---|---|---|
| 1 | `sucʟ γ ↪ γ` | `ShiftAbs`, `src/L/Absorption.lagda.md` | `shift-coded`, `src/L/CodedShift.lagda.md:37-40` | **PAID** |
| 2 | `Lset δ ↪ δ` | `stage-card-upper`, `src/L/StageCardinal.lagda.md:564-565` | B9, `agents/tasks/LJ-1-564/Probe564.agda:127-130` | OPEN, `[LJ-1.533]` NO-GO |
| 3 | `Pairs κ ↪ κ` | `pairs-inject-ambiently`, `Probe593.agda:279` | this obligation | **NOT INDEPENDENT: IT IS SITE 2** |
| 4 | `α ↪ κL α` | `κ-inj`, `src/L/Cardinal.lagda.md:133` | `InternalLeastCard.Selected`'s `nonempty`, `src/L/Cardinal.lagda.md:238-243` | OPEN, and NO CONSUMER in `src/` |

**THE PRODUCER COUNT, RE-MEASURED AT TODAY'S TREE AND NOT QUOTED.** `src/` has
exactly TWO terms that BUILD an `InjCode`, `src/L/Absorption.lagda.md:614` and
`src/L/CodedShift.lagda.md:40`, and they are the SAME term at two names, both
of shape `InjCode F (sucʟ γ) γ`. `src/L/CantorBernstein.lagda.md:33` (`readL`)
CONSUMES one and builds none. That is site 1 and nothing else.

**SITE 4 IS WORTH ONE SENTENCE TO THE MATHEMATICIAN AND NOT A TASK.**
`InternalLeastCard` (`src/L/Cardinal.lagda.md:234`) is referenced by no other
file of `src/`, measured by grep over `src/`. So its unpaid code obligation
costs the bill nothing today.

**WHAT MADE SITE 1 PAYABLE, WHICH IS THE ACTIONABLE PART OF THE SWEEP.** The
code was NOT built from an ambient injection. It was built from a FORMULA.
`Carve` (`src/L/Absorption.lagda.md:386-402`) is the engine, and its body uses
exactly FOUR things from the formula side: `Fo.out`, `Fo.into`, `Fo.val-cong`
and `Fo.val-inj` (measured: those four names, five occurrences, over
`src/L/Absorption.lagda.md:385-540`). Everything else in its parameter list
(`γ ω z`, `shNum`, `shTop`, `shOther`, `D-in-dec`) is the SHIFT's three-case
formula hard-wired in. **A `Carve` parameterized by a formula and those four
lemmas would serve every site of this wall, and it is a narrow refactor of a
green module rather than new mathematics. Nobody has priced it.** I did not
build it: the brief gives me one obligation.

## WHAT I TOOK FROM WHOM

The brief orders this: "COPY WHAT IS GREEN ... Say which lines you took."

**TAKEN BY IMPORT, AS THE TYPE THAT PREDECESSOR DELIVERED (my slot's rule).**

- **`[LJ-1.556]`, section 1, whole.** `Square.sqL`, `Square.sqL-in`,
  `Square.sqL-out`, `Square.Comp`, `Square.pw`, `Square.toκ`, `Square.Ix`
  (`agents/tasks/LJ-1-556/Probe556.agda:143-202`). Verdict taken from its
  report: sections 1 and 2 are green and copyable
  (`agents/tasks/LJ-1-556/lj-1.556-report.md:311`).
- **`[LJ-1.564]`, its B9 row.** `StageCountedCoded`
  (`agents/tasks/LJ-1-564/Probe564.agda:127-130`). Verdict taken from its
  report: GO (`agents/tasks/LJ-1-564/lj-1.564-report.md:8`).

**NOT TAKEN, AND THE REASON IS THAT ITS OWN SUCCESSOR REFUTED IT.**

- **`[LJ-1.556]`'s `BriefTarget`** (`agents/tasks/LJ-1-556/Probe556.agda:335`)
  and **`SquareStep`** (`:357-362`). Both FALSE, measured by `[LJ-1.581]`
  (`obligation-false`, `agents/tasks/LJ-1-581/Probe581.agda:376`;
  `squarestep-false`, `:387`). Neither appears in the probe in any position.
- **`[LJ-1.581]`'s `SquareStepInf`** (`agents/tasks/LJ-1-581/Probe581.agda:427-432`),
  refuted at ω by `[LJ-1.589]` (`agents/tasks/LJ-1-589/Probe589.agda:161-162`).
  No clause of the probe mentions `⟨ ω ∈ fst κ ⟩` in any position.
- **`[LJ-1.550]`'s residues.** No term of `[LJ-1.550]` appears in the probe.

**REBUILT FROM `src/` RATHER THAN IMPORTED, and each cites the predecessor that
measured it first.**

- `[LJ-1.589]`'s sections 2 and 4 (`trophy-is-cs∉`, `cs∉-is-trophy`,
  `numerals-from-trophy`, `Probe593.agda:83-104`), so this file pays no import
  for them.
- `[LJ-1.564]`'s `inclusion-coded` and `injl-trans` (`Probe593.agda:417-427`),
  from `src/L/InjChain.lagda.md:575-598` and `:314-434`.

**NOT USED, THOUGH THE BRIEF NAMES IT.** `[LJ-1.567]`'s `col-step`
(`agents/tasks/LJ-1-567/Probe567.agda:259`). **The route this task found needs
no recursion at all**, so the collapse's step formula has no place in it. I
read it and I declined it, and that is the single largest saving of the task.
`[LJ-1.576]`'s `isPropInjCode` (`agents/tasks/LJ-1-576/Probe576.agda:77`) was
also not needed: every conclusion here is already a `∥_∥₁`.

## PRICES

**CALIBER.** `GHCRTS="-A64m -I0 -M8g"`, set by the program on this pane and not
by me (`agents/tasks/LJ-1-593/runs/final-2.out:2`). ONE Agda process at a time.
**NO HEAP EVENT.** The largest maximum resident set of the task was 2.077 GB
against the 8 GB cap, on `s5-1`, the run that first compiled the `[LJ-1.564]`
chain (`agents/tasks/LJ-1-593/runs/s5-1.out:13`).

| run | what | wall s | max RSS | exit |
|---|---|---|---|---|
| `w3-1` | W3 alone, first Agda of the task | 1.57 | 397 MB | 0 |
| `s1-1` | sections 1 and 2 | 6.49 | 657 MB | 0 |
| `s2-1` | sections 1 to 5, `[LJ-1.556]` compiled cold | 194.91 | 677 MB | 0 |
| `s3-1` | sections 1 to 7 | 2.11 | 417 MB | 0 |
| `s4-1` | section 8, first form | 2.18 | 449 MB | **42** |
| `s4-3` | section 8, corrected | 2.16 | 449 MB | 0 |
| `s5-1` | section 9, `[LJ-1.564]` chain compiled cold | 31.59 | 2,077 MB | 0 |
| `final-1` | whole probe, cold for this file | 3.56 | 733 MB | 0 |
| `final-2` | whole probe, cold for this file, repeat | 3.56 | 733 MB | 0 |
| `final-3` | whole probe after one cosmetic edit, cold for this file | 3.58 | 733 MB | 0 |

**`final-1`, `final-2` AND `final-3` ARE ALL COLD FOR THIS FILE.** The interface
`_build/2.8.0/agda/agents/tasks/LJ-1-593/Probe593.agdai` was deleted before
each. Three runs, 3.56, 3.56 and 3.58 s. **The probe itself costs 3.56 s.**

**ONE RED RUN, AND IT WAS A BAD IMPLICIT AND NOT A WALL.** `s4-1` is
`UnsolvedConstraints` on `mem-ord`'s implicit `{A}`
(`agents/tasks/LJ-1-593/runs/s4-1.out:4-7`). Two `{A = fst κ}` fixed it.

**ONE RUN WAS REFUSED BY MY OWN GUARD AND STARTED NO AGDA.** `s4-2`
(`agents/tasks/LJ-1-593/runs/s4-2.out:1`). The guard was a `pgrep` pattern, and
a POLL command of mine carried that same pattern in its own argv, so the guard
matched the poll. **I replaced the pattern with a PID file**
(`agents/tasks/LJ-1-593/runs/run.sh:12-16`) and recorded why in the script, so
the next task that copies it does not repeat the fault. No number is affected:
the refused run measured nothing.

**ESTIMATE AGAINST MEASURED, IN LINES.**

The brief estimated about 260 lines in the probe, of which about 70 the
obligation, and said the estimate was "the least certain in the queue".

| | lines | of which Agda |
|---|---|---|
| estimate | 260 | 70 (the obligation) |
| measured | 569 | 241 |

**THE OVERRUN IS NOT THE OBLIGATION.** The obligation is not inhabited and cost
0 lines. The 241 Agda lines are: 32 for the spelling, 9 for the ambient square
law, 8 for the domain, 19 for the type, 25 for the ambient injection at the
domain, 9 for the split, 18 for the sweep, **84 for the reduction to B9**, and
7 for the identity to the bill's own row. **Two of those nine sections were not
in the brief's plan at all**: the sweep, which C-42 demands, and the reduction,
which is the result.

**THE BRIEF'S COMPARABLES WERE SOUND AS SHAPE AND THE SHAPE CHANGED.** It named
`[LJ-1.567]`'s one formula and `[LJ-1.566]`'s assembled code. This task built
neither: **the route needs no formula of its own and assembles no code of its
own.** It composes two codes `src/` already carries. That is why the estimate
could not have been right in either direction, and I do not treat it as an
error of the brief.

## ARCHIVE USED

Every CANDIDATE the brief listed is named.

- **`archive/dev/LJ-dispatch-index.md`**: READ. `:100` says
  "| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master | fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and levelIn survive on the hull adequacy |".
  I read it to check the 775-line figure `[LJ-1.556]` warned about
  (`agents/tasks/LJ-1-556/lj-1.556-report.md:322-327`). **It is a number in a
  paragraph and `AGENTS.md:17-18` refuses it, so nothing in this task is funded
  against it.** It also confirms the ambient `SquareLaw` master is the object
  that landed, not a coded one, which is the distinction this task turns on.
- **`archive/dev/JOURNAL-archived.md`**: NOT USED, declined. Not read past a
  `grep` for "square". It is the closed narrative record and a live document
  carries no history; nothing in it can settle a type question at today's tree.
- **`archive/dev/JOURNAL.md`**: NOT USED, declined. Same reason.
- **`archive/dev/DECISIONS-archived.md`**: NOT USED, declined. Its `D<n>` series
  is the archived decision series and it binds nothing today.
- **`dev/ARCHIVE.md`**: NOT USED, declined. Not read past `:1`, "# ARCHIVE.md:
  the archive registry". I retired no module, so clause W4 gives me no row to
  write there.

## LITERATURE USED

Every CANDIDATE the brief listed is named.

- **`dev/literature/devlin-II5.md`**: READ, and it is the one that mattered.
  `:148` says "> κ (or more generally if x ⊆ L_α for some α < κ), then x ∈ L_κ.".
  **THIS IS NOT THE FACT I USED, AND SAYING SO IS THE POINT.** Devlin 5.5 is a
  heavy statement whose proof needs 5.4 and condensation (`:153-159`). Step (b)
  of my route needs only the elementary closure of a LIMIT stage under the
  ordered pair, which the tree already carries as `Bound.prʟ∈λ`
  (`src/L/Coding/Bound.lagda.md:142-144`). Reading 5.5 is what let me see that
  the two are different, and that the cheap one suffices.
- **`dev/literature/truncation-and-selection.md`**: READ. `:313` says
  "pairing that reads only the reachable set is symmetric, hence not injective:".
  It is a warning about a pairing that fails injectivity. It does not apply
  here: the injection is not built by a pairing at all, it is an inclusion
  composed with B9, and injectivity comes from `InclGraph` and `Comp`.
- **`dev/literature/terms-2026-08.md`**: NOT USED, declined. Not read past a
  `grep`. It is the terminology dossier; this task names nothing new and the
  Boundary forbids me to add a glossary entry.
- **`dev/literature/digest.md`**: NOT USED, declined. Not read past a `grep`.
  It pins the orthodox RUD route and the Gödel-pairing surjection at `:241`;
  this task builds no pairing and no surjection.
- **`dev/literature/glossary-review-2026-08.md`**: NOT USED, declined. Not read
  past a `grep`. It reviews pre-protocol glossary entries and I added none.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the square law. `--safe`
is on. `src/` is untouched. **No term named `square-coded` exists in any file of
this task.** I did not state `SquareStepInf` and I did not re-dispatch
`[LJ-1.556]`'s `BriefTarget` or `SquareStep`. I did not attempt row 5 and I did
not attempt B9: AD12 gives this brief one obligation, and B9 is another row.

**I DID NOT PROVE B9 FROM THE SQUARE LAW AND I DO NOT CLAIM THE TWO ARE
EQUIVALENT.** The reduction runs one way and the probe carries no term the other
way.

**I DID NOT ASSERT B9.** It is a hypothesis of `square-from-b9`,
`square-from-b9inf` and `square-from-the-bills-own-b9`, and of nothing else.
`[LJ-1.533]` is B9's NO-GO and its finding 1 calls the bill's spelling FALSE for
want of infinitude (`agents/tasks/LJ-1-533/lj-1.533-report.md:26-28`); that is
exactly why `B9Inf` exists and why the derivation spends it.

**I DID NOT BUILD THE GENERIC `Carve`** that `## THE SWEEP (C-42)` recommends,
and I did not price it beyond the four-name measurement recorded there.

I did not set `GHCRTS`. I ran ONE Agda process at a time; one run, `s4-2`, was
refused by my own run script's guard and no Agda started for it
(`agents/tasks/LJ-1-593/runs/s4-2.out:1`). I did not run `make check`, because
I committed nothing. I did not commit and did not push.
