# LJ-1.642 report: clause (i) at the ordinal index, which the brief ruled

## HEAD
head_slot: coder
machine: exclusive
agda_tier: heavy
task: LJ-1.642
obligation: agents/tasks/LJ-1-642/Probe642.agda::clause-i-at-ord
verdict: **GO on the obligation. The ruling pays, and it pays more than the
brief asked for.** The obligation is green and metered
(`runs/meter-obligation.out`, `pass exit=0 2.33 s`,
`0 UNRESOLVED of 1`, `probe_red=False`).
**READ THIS BEFORE YOU QUEUE ANYTHING: the term carries `Det` and `Wit` as
named hypotheses, exactly as the brief words the obligation, and NEITHER
supplier is built. So clause (i) is REDUCED at the ruled index. It is not
yet PROVED there.**

**WHAT THE TASK EARNS, IN ONE SENTENCE.** At the ruled index the
certificate's clause (i) is not three open statements but ONE:
`ClauseIAtOrd` and `CodedLevelsAtOrd` imply each other
(`Probe642.agda:364`), `Det` alone is vacuous (`:108`), the level is
always a MEMBER of the stage (`:327`), and `Wit`'s own existential costs
nothing (`:354`). What is still owed is a FORMULA over the hull's codes
that holds of the tower's own value, and nothing else.

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-642/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M4g"`, the HEAVY tier, ONE Agda process at a time.
I did not set `GHCRTS`. Nothing is postulated, the probe carries `--safe`,
the delivered probe is green and carries no hole, and nothing lands in `src/`.
The probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 740,278,272 bytes against the 4,294,967,296-byte heavy cap
(`runs/w3-1.out`), and the longest run is 4.06 s against the caps I set
(300 s for W3, 600 s for the floor, 900 s for the probe). The caps are
wall-clock caps enforced by a perl alarm (`runs/run.sh` carries the
mechanism), because this macOS has no `timeout` ([LJ-1.602], [LJ-1.610]).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(709 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

## THE FLOOR, BEFORE ANY PROOF

The standing coder clause orders a floor on a heavy object. The floor slice
is `runs/FLOOR.agda.txt`: the trimmed frame, the obligation's whole type,
and a HOLE where the term goes. Its run is `runs/floor-1.out`:
**exit 42 at 2.40 s, peak 693,862,400 bytes**, with
`[UnsolvedInteractionMetas]` at the one designed hole and no other error.

**THE FRAME COSTS 0.65 GiB AGAINST A 4 GiB CAP, AND THE IMPORT SET IS WHY.**
The brief's premise 4 ordered clause (i) taken by RESTATEMENT and not by
import, because `[LJ-1.598]` measured that `[LJ-1.578]`'s own file walls
under the WIDE cap with every dependency warm
(`agents/tasks/LJ-1-598/runs/chain-578.out`, exit 251 at 15.92 s). I obeyed
that and imported `src/` only. **The premise is confirmed at this site: with
`src/`-only imports the frame is not the risk it was, and the heavy tier was
not needed for the heap.** The finished probe peaks at 639,959,040 bytes
(`runs/p-final.out`), which is BELOW the wide cap of 2 GiB. A next task at
this frame can run WIDE.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX AND THAT IS DELIBERATE.**
It is red by design, and every `.agda` under a task's own directory is a
verification target of the acceptance run (`scripts/pod/facts.py:489`,
`verification_target`). A red slice left as `.agda` would fail conjunct 1
and would report this task's landed obligation as a NO-GO. The bytes are
what produced `runs/floor-1.out`, and the file's own header carries the two
commands that reproduce the run.

## THE OBLIGATION, AND WHAT ITS TYPE SAYS

`clause-i-at-ord` (`Probe642.agda:398-408`):

    clause-i-at-ord : (lam ...) (ψ : Formula (Frame.T.Code ...) 2)
      → Frame.Det ... ψ → Frame.Wit ... ψ
      → Frame.ClauseIAtOrd lam ordλ succλ X X⊆Lλ ∅∈λ

**THE BRIEF WORDS THE OBLIGATION AS "discharged from `[LJ-1.598]`'s
`graph-gives-level` PLUS ITS `Det` AND `Wit` SUPPLIERS", so the two
suppliers are the term's inputs.** That is the reading I built. I record
the other reading and why I did not take it: if the obligation had demanded
a CLOSED term, it would demand a concrete `ψ` with both `Det ψ` and
`Wit ψ`, and section "WHAT I COULD NOT CLOSE" gives the evidence that no
such `ψ` is constructible from today's tree. **Under EITHER reading the
next brief needs the same one thing, and the report names it.**

`ClauseIAtOrd` (`:125-131`) is `[LJ-1.578]`'s clause (i)
(`agents/tasks/LJ-1-578/Probe578.agda:236-240`) with ONE change: the
hypothesis is `IsOrd (fst (T.val c))` and not
`IsOrd (HS.C.π (fst (T.val c)))`. That is the brief's premise 2.

**WHAT THE RULING BOUGHT, MEASURED.** `[LJ-1.598]` could not compose its
own green `graph-gives-level` into its own `ClauseI`: the composition needed
`PreimageOrd` (`agents/tasks/LJ-1-598/Probe598.agda:257`), which is built
nowhere and which that report could see no route to. At the ruled index the
composition is ONE line (`Probe642.agda:182-184`) and needs no third
supplier. **The ruling deletes a supplier and adds none.** That is the
brief's premise 2 confirmed by a term.

## THE MAIN FINDING: THE REMAINDER IS ONE STATEMENT, NOT THREE

The brief asks which of `Det`, `Wit` and `CodedLevels` falls out at the
ordinal index. The answer is machine-checked and it is sharper than the
question.

**1. `Det` ALONE FALLS OUT, AND IT IS VACUOUS.** `det-vacuous : Det ⊥̇`
(`Probe642.agda:108`). An unsatisfiable formula determines its value
vacuously. This is the `Det` twin of `[LJ-1.598]`'s `only-level-vacuous`
(`Probe598.agda:104`) at the same site. **So no brief may fund `Det`
alone.** The content is the PAIR, `Wit` under a `Det`.

**2. `ClauseIAtOrd` AND `CodedLevelsAtOrd` IMPLY EACH OTHER.**
`clause-i-iff-coded` (`Probe642.agda:364-366`) is the pair of terms.
`coded-gives-clause-i` (`:211`) is `[LJ-1.598]`'s equation route restated.
**`clause-i-gives-coded` (`:274`) is new, and it is the half nobody had
written.** `[LJ-1.598]` called the equation route "CIRCULAR for the
certificate" and stopped (`Probe598.agda:148-154`). The circle is an
EQUIVALENCE. The mechanism is the hull's own Skolem closure and nothing
else: a formula over hull codes that is satisfied at the stage's inner world
has its LEAST satisfier named by a code outright, `wit k (absFo φ)
(constantsFo φ)` (`src/L/Hull.lagda.md:74` for the constructor, `:105`
for `val-wit`). That is the construction inside `closed`
(`src/L/Hull.lagda.md:120-138`) with the CODE kept instead of discarded.
The term is `skolem` (`Probe642.agda:244-272`), 29 code lines. **No
truncation survives**, because the equation the code must satisfy is a path
in a set, and `leastOf` picks the witness without choice
(`src/L/WellOrder/Base.lagda.md:158-161`).

**3. `Det ψ × Wit ψ` IMPLIES BOTH.** `graph-gives-clause-i` (`:182`) and
`graph-gives-coded` (`:388`). So the triangle closes and the three named
residues of `[LJ-1.598]` are ONE.

**4. AND THE SAME ROUTE BUYS FACT A AT THE RULED INDEX.**
`clause-i-gives-hull-levels` (`:381`) gives
`⟨ Lset (fst (T.val c)) ∈ˢ HS.M ⟩`, which is `Facts.HasLevels`
(`agents/tasks/LJ-1-578/Probe578.agda:120-122`) at the ruled index. The
certificate's own `cert-gives-A` (`Probe578.agda:254`) needed the
collapse index for this. Here it is four lines and needs no bridge.

## THE SECOND FINDING: THE STAGE ALREADY HAS THE LEVEL

**`level-in-stage` (`Probe642.agda:327-334`) IS A THEOREM AT THE RULED
INDEX, AND IT WAS A HYPOTHESIS BEFORE.** At an ordinal index of the stage
the level is a MEMBER of the stage, from the frame's own data and three
delivered facts:

- an ordinal of a level is a member of that level's index: `rank-Lset`
  composed with `rank-fix`, the same composition `β-succ` uses at
  `src/L/BoundedSubset.lagda.md:976-978`;
- a set is a definable subset of itself: `defSet⊤≡A`,
  `src/L/Definability.lagda.md:178-179`, which gives `self∈𝒟ₒ`
  (`Probe642.agda:324`);
- a member of the step at an index below is a member of the stage:
  `Lset-in`, `src/L/Constructible.lagda.md:329`.

**THIS IS `levelIn` READ AT THE STAGE.** `Condense` takes exactly this
shape as a HYPOTHESIS at the COLLAPSE (`src/L/BoundedSubset.lagda.md:917`),
and `StageBound` takes it twice more (`src/L/StageBound.lagda.md:80`,
`:106`). At the stage it is a theorem. **The ruling is what makes it one**:
the old hypothesis `IsOrd (HS.C.π ...)` gives no ordinal to feed
`rank-fix`, and `[LJ-1.598]`'s `δ = {{∅}}` reading is exactly a case where
the collapse is an ordinal and the value is not.

**SO `Wit`'s OWN EXISTENTIAL COSTS NOTHING.** `wit-from-holds`
(`Probe642.agda:354-356`): a formula that HOLDS at the tower's own value
gives `Wit` outright, because that value is a stage member.
**This sharpens `[LJ-1.610]` WALL 1.** That wall says a witness read at the
stage's inner world must be a member of the stage
(`agents/tasks/LJ-1-610/review-of-graph-stage.md`). For THIS `Wit` the
witness is the tower's value, and the value is now in the stage. The
approximation that `[LJ-1.610]` could not build enters only through the
FORMULA's own existential, when the formula chosen is the graph.

## WHAT I COULD NOT CLOSE, AND THE EVIDENCE

**ONE THING IS OWED: a formula `ψ` over the hull's codes, two slots, that
holds of `(δ, Lset δ)` at every ordinal `δ` of the stage and of nothing
else.** Everything above says the certificate's clause (i) at the ruled
index costs exactly that. I did not build it, and here is why, at
`file:line`, in four walls. Three of them are not mine to remove.

1. **THE GRADE.** The tree's machine-grade graph matrix
   (`ApproxAt`/`StepAt`, the body of `LsetGraphAt`,
   `src/L/Coding/Sequence.lagda.md:286-292`) is NOT Delta-zero, because
   `domAt` and `extAt` carry UNBOUNDED quantifiers
   (`agents/tasks/LJ-1-610/review-of-graph-stage.md`, WALL 3, citing
   `src/L/Coding/Model.lagda.md:278` and `:662`). Without a Levy
   certificate the stage-to-class transfer (`σ₁-up`,
   `src/FOL/Absoluteness.lagda.md:182-184`) does not apply, so no reading
   of a stage satisfaction reaches `Lset-only`
   (`src/L/Hierarchy.lagda.md:334`), which is the only determination the
   tree proves.
2. **THE ARITY.** The tree's Delta-zero matrix is `levelHoodB`
   (`src/L/BoundedSubset.lagda.md:108-111`), and it carries its bound `K`
   as a FOURTH variable slot. `Det` and `Wit` give TWO slots, index and
   value. A bound placed in a CONSTANT would have to hold every
   approximation below `lam` at once, and such a set is not a member of
   `Lset lam`. So the bound must be bound by an existential, which returns
   the formula to grade Sigma-one and to wall 1.
3. **THE CARRIER.** `levelHoodB` lives at the constructible-CLASS carrier
   `CS.S`. `ψ` must live at the hull's code alphabet `T.Code`. `[LJ-1.610]`
   paid the STAGE-side slide for the numerals (`numSL`,
   `agents/tasks/LJ-1-610/Probe610.agda:131-142`, from `Bound.num∈λ`,
   `src/L/Coding/Bound.lagda.md:139-140`) and recorded that **the HULL-side
   slide has no delivered supplier at all** (WALL 2). I did not build one
   either.
4. **THE WITNESS, WHICH IS THE MATHEMATICS AND NOT THE SYNTAX.** Devlin's
   (b) needs the witnessing `z` inside the carrier, that is 2.6(ii), the
   sequence `(L_δ | δ ≤ γ) ∈ L_α` for `γ < α`
   (`dev/literature/devlin-II5.md:220-222`). Nothing in `src/` builds it.
   The nearest delivered machinery, `BoundOver.Iter.pow∈λ`
   (`src/L/Coding/Bound.lagda.md:109-118`), needs `powIter`, and its own
   comment says "The fact is a HYPOTHESIS here and it has no supplier;
   `src/` assumes the same fact twice, as `DefOK` and as `PowOK`"
   (`src/L/Coding/Bound.lagda.md:103-105`).

**THIS IS THE SAME WALL FROM A FOURTH SIDE.** `[LJ-1.595]` reached it on
clause (ii), `[LJ-1.598]` on clause (i) at the collapse index, `[LJ-1.610]`
on face G+ (`agents/tasks/LJ-1-610/review-of-graph-stage.md`, WALL 1 names
the first three). This task reaches it on clause (i) at the ORDINAL index,
and it reaches it with three of the four earlier obstacles removed:
`PreimageOrd` is deleted by the ruling, the level's membership in the stage
is now a theorem, and `Wit`'s own existential is free. **What is left is
2.6(ii) and only 2.6(ii).**

## D-10, BEFORE ANY AGDA: IS THE TARGET TRUE?

D-10 asks for the truth of the target before its proof is priced. I spent
that check and it returns ONE finding.

**THE FRAME ADMITS `lam = ω`, AND DEVLIN'S CITED CLAUSE DOES NOT COVER IT.**
The frame's hypotheses are `IsOrd lam`, `succλ`, `X`, `X⊆Lλ` and `∅∈λ`
(`Probe642.agda:71-77`, `[LJ-1.578]`'s own six slots). `∅∈λ` with `succλ`
makes `lam` a limit and puts every numeral in it
(`#∈λ`, `src/L/Coding/Bound.lagda.md:55-57`). It does NOT make `lam`
greater than `ω`, and `lam = ω` satisfies all six. Devlin's requirement is
"**Uniform Δ₁ at limit α > ω**" (`dev/literature/devlin-II5.md:218`), and
clause (b) itself is stated at that `α` (`:99`).

**WHAT THIS DOES AND DOES NOT SAY.** It does not refute the target. At
`lam = ω` the stage is the hereditarily finite sets and each `L_δ` for
`δ < ω` is definable there without parameters, so clause (i) is plausible
at `ω` too. **It says the certificate's own instantiation must either
exclude `lam = ω` or must not route through (b) there.** The next brief
should decide which, because a supplier funded against (b) inherits the
`α > ω` hypothesis and the frame does not carry it. This is a reading of
the frame and of the digest, and it is not machine-checked.

**THE ERRATA DO NOT BITE HERE, AND I CHECKED.** The brief's premise 6 sends
me to Mathias's WS section 10, the inventory of "false Delta-0 claims for
syntax" (`dev/literature/digest.md:69`). **This task certifies NO leaf as
bounded.** It builds no Delta-zero witness, quotes none, and its four walls
above are the reason: the grade wall is where a Delta-zero certificate
WOULD be needed, and I stop at it rather than assert one. The named failure
mode of `[LJ-1.34]` (the brief's premise 5,
`archive/dev/LJ-dispatch-index.md:52`) is therefore not reproduced here,
because no leaf is delivered at all.

## W3, THE WIDEST UNMEASURED TERM

**GO.** The brief names `Det` and `Wit` at a general `ψ`, estimated at 150
to 300 lines. The slice is `agents/tasks/LJ-1-642/runs/W3.agda` (58 lines,
32 code lines), written FIRST and typechecked ALONE:
`runs/w3-1.out`, **exit 0 at 2.46 s, peak 740,278,272 bytes**, under the
five-minute cap I set. **The two TYPES are 6 code lines together**
(`Probe642.agda:91-97`), and the slice that holds them is 32, almost all
frame. So the brief's estimate is right about the SUPPLIERS and wrong about
the TYPES by two orders of magnitude, in the same way `[LJ-1.598]`'s W3
estimate was: the statement is cheap and the content is not in the
statement.

**AND THE MEASUREMENT CORRECTS THE QUESTION A SECOND TIME.** `Det` alone is
vacuous (`det-vacuous`), and `Wit`'s own existential is free
(`wit-from-holds`). So the widest unmeasured term is neither `Det` nor
`Wit`: it is `Holds ψ` (`Probe642.agda:349-352`), "the formula holds at the
tower's own value", which is Devlin's (b) forward half and nothing less.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M4g]`, ONE AGDA
PROCESS PER RUN, WITH A WARM `src/` INTERFACE CACHE.** Non-blank
non-comment lines counted by `awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 408 | 189 | `Probe642.agda` |
| header and imports | 64 | 27 | `:1-64` |
| the frame | 15 | 7 | `:65-79` |
| S1 W3 and the `Det` vacuity | 31 | 8 | `:80-110` |
| S2 clause (i) restated at the ruled index | 33 | 16 | `:111-143` |
| S3 the graph route and the composition | 42 | 25 | `:144-185` |
| S4 the equation route | 33 | 17 | `:186-218` |
| S5 the Skolem closure and the converse | 76 | 41 | `:219-294` |
| S6 the level in the stage, and `Holds` | 63 | 20 | `:295-357` |
| S7 the equivalence and Fact A | 35 | 17 | `:358-392` |
| the obligation | 16 | 11 | `:393-408` |
| W3 slice | 58 | 32 | `runs/W3.agda` |
| floor slice | 87 | 50 | `runs/FLOOR.agda.txt` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 alone, forced recheck, exit 0 | 2.46 s | 740,278,272 | `runs/w3-1.out` |
| floor, trimmed frame, one hole | 2.40 s (exit 42, by design) | 693,862,400 | `runs/floor-1.out` |
| first full draft, one type error | 2.71 s (exit 42) | 737,394,688 | `runs/p-1.out` |
| first green draft | 4.06 s | 736,575,488 | `runs/p-2.out` |
| with `level-in-stage` | 3.08 s | 643,301,376 | `runs/p-3.out` |
| with `Holds` | 3.04 s | 640,024,576 | `runs/p-4.out` |
| with Fact A | 3.08 s | 640,008,192 | `runs/p-5.out` |
| **forced recheck of the delivered file** | **2.85 s** | **639,959,040** | `runs/p-final.out` |
| the name meter, 25 names, grouped | 2.59 s | not taken | `runs/meter-1.out` |
| the obligation alone | 2.33 s | not taken | `runs/meter-obligation.out` |

**THE ESTIMATE WAS 150 TO 300 LINES FOR `Det` AND `Wit`.** Neither was
built, so that estimate is untested. The file is 408 lines and 189 code
lines, and 41 of those code lines are the Skolem closure the brief did not
ask for and did not price.

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1` (the W3 slice, green),
`floor-1` (the floor, red at its one designed hole), `p-1` (exit 42, one
placeholder I left in `clause-i-gives-coded`, fixed by giving `skolem` a
plain target instead of a stage member), `p-2` to `p-5` (the four green
drafts as each section landed), `p-final` (the forced recheck of the
delivered file, after the interface was deleted, and its output carries its
own `Checking` line so the number is a recheck and not an interface reuse),
`meter-1` (the 25-name meter) and `meter-obligation` (the obligation
alone). Every Agda `.out` carries `GHCRTS=`, a cap line, a start stamp, an
end stamp and `EXIT=`; the two meter files are the meter's own output and
carry its verdict line instead.

## THE NAMES THAT LAND, ALL METERED

**25 NAMES, EVERY DECLARATION IN THE PROBE, AND ALL 25 RESOLVE**
(`runs/meter-1.out`, `0 UNRESOLVED of 25`, 2.59 s, `probe_red=False`).

| what | `Probe642.agda` | conditional on |
|---|---|---|
| W3: `Det`, `Wit` | `:91`, `:95` | nothing |
| `Det` alone is vacuous | `:108` | nothing |
| clause (i) at the ruled index, and its body | `:125`, `:133` | nothing |
| the body identity | `:140` | nothing |
| the graph route: `inF`, body, clause | `:158`, `:161`, `:182` | `Det`, `Wit` |
| the equation route: `eqF`, `eq-sat`, `eq-uniq` | `:197`, `:200`, `:203` | nothing |
| `CodedLevelsAtOrd`, and clause (i) from it | `:207`, `:211` | `CodedLevelsAtOrd` |
| the hull's Skolem closure | `:244` | nothing |
| clause (i) gives a code (NEW) | `:274` | nothing |
| clause (i) gives the level in the stage | `:286` | nothing |
| a set is a definable subset of itself | `:324` | nothing |
| the level is in the stage (NEW) | `:327`, `:336` | nothing |
| `Holds`, and `Wit` from it (NEW) | `:349`, `:354` | nothing |
| the equivalence, in one name (NEW) | `:364` | nothing |
| Fact A at the ruled index (NEW) | `:374`, `:381` | `CodedLevelsAtOrd` |
| the triangle | `:388` | `Det`, `Wit` |
| **THE OBLIGATION** | **`:398`** | **`Det`, `Wit`** |

## C-42, THE SWEEP

The refutation this brief cures is `[LJ-1.598]`'s: clause (i) hypothesized
the ordinal-hood of the COLLAPSE and concluded at `Lset` of the VALUE. C-42
demands the count of the shape before the cure is priced. The command is
`grep -rn "IsOrd (HS.C.π" agents/ src/`, run today.

| where | hits today |
|---|---:|
| `src/`, every file | **0** |
| `agents/`, every file, this task excluded | 69 |
| `agents/`, `.agda` files only, this task excluded | 41 |

**THE FIRST ROW IS THE ONE THAT MATTERS: THE SHAPE IS NOT IN `src/` AT ALL.**
The ruling therefore costs `src/` nothing, and no master needs an edit.

**THE DECLARATION SITES, RE-READ TODAY.** `[LJ-1.598]` named four, all in
one file, and all four still read as it reported:

| site | statement | at `file:line` | this task |
|---|---|---|---|
| 1 | `Facts.HasLevels` | `agents/tasks/LJ-1-578/Probe578.agda:120-122` | CURED at the ruled index, `Probe642.agda:381` |
| 2 | `Facts.LevelsCommute` | `:126-128` | open, and this task does not touch it |
| 3 | `Cert.DefinesLevel`, clause (i) | `:236-240` | THIS TASK, restated at `Probe642.agda:125` |
| 4 | `Cert.DefinesLevelAcross`, clause (iii) | `:503-510` | open |

**TWO PROBES HAVE JOINED THE COUNT SINCE `[LJ-1.598]` SWEPT.**
`agents/tasks/LJ-1-602/Probe602.agda` carries 6 hits and
`agents/tasks/LJ-1-606/Probe606.agda` carries 2, both on the clause (iii)
and crossing families, and `[LJ-1.602]` uses the hypothesis to EXCLUDE a
candidate obstruction rather than to conclude at a level
(`agents/tasks/LJ-1-602/review-of-defines-level-across.md:44`). So the cure
list is unchanged: sites 2 and 4, and neither is in `src/`.

## W2, THE GENERIC CARRIER

**Nothing is written twice, and the one place where duplication was
tempting is named.** The probe's one frame is `[LJ-1.578]`'s own
`HullStage` frame, and every route is stated at it once. `skolem`
(`Probe642.agda:244`) is generic in the formula and in the TARGET set, so
`clause-i-gives-coded` instantiates it once and any later consumer can
instantiate it again without a second proof. The equation route and the
graph route share `BodyAtOrd` and `clause-i-from-body` rather than
repeating the tuple.

**THE ONE PLACE I DECLINED TO DUPLICATE.** The floor slice
`runs/FLOOR.agda.txt` states the obligation a second time. I did NOT fill
its hole with a copy of the delivered term, which would have put the graph
route's 25 code lines in the tree twice for no mathematical gain. The slice
stays as the measurement it is. No deadline forced a fixed form and there is
no conflict to report.

## W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/` changed,
and `dev/ARCHIVE.md` takes no row from this task. The ideal form written
fresh today is the form delivered: the probe is new text at a new site.

**P-l: obeyed and not re-measured.** No type in the probe names a stage
presentation. `Det`, `Wit`, `ClauseIAtOrd`, `BodyAtOrd`, `CodedLevelsAtOrd`
and `Holds` quantify over codes and over `HS.ASt.SL`, and `⟪ Lset lam ⟫`
appears nowhere in the probe. `level-in-stage` mentions `Lset δ` at a
VARIABLE `δ`, which is the law's permitted case: the statement is ABOUT a
level without naming a transparent presentation of one.

## WHAT THE SHAPE RESISTED

- **What it cost.** 189 code lines for a green probe with 25 metered names,
  2.85 s and 639,959,040 bytes at the forced recheck, and no heap wall
  anywhere.
- **What the shape resisted.** Almost nothing, and that is itself the
  finding. One type error in the whole task (`runs/p-1.out`): I first gave
  `skolem` a STAGE MEMBER as its target, which needs the level to be in the
  stage before the level is known to be in the stage. Giving `skolem` a
  plain set as its target removed the circle in one edit, and
  `level-in-stage` then landed on the first attempt. **The plumbing fits;
  the formula's meaning is the whole cost**, which is the third dispatch in
  a row to say so.
- **What I had to weaken.** Nothing. The obligation carries `Det` and `Wit`
  as NAMED TYPES and not as hidden postulates, exactly as the brief words
  it, and every other term in the probe is unconditional or names its
  hypothesis in its own type.
- **What I could not close.** `Holds ψ` at any `ψ`, which is Devlin's (b)
  forward half and 2.6(ii) under it. `Det` and `Wit` follow the moment a
  supplier of `Holds` exists together with a determination.
  `CodedLevelsAtOrd` is equivalent to the whole clause, so it is not a
  separate debt. The brief forbade `PreimageOrd` and the ruling removed the
  need for it.

## WHAT THE NEXT BRIEF NEEDS

1. **FUND ONE STATEMENT, NOT THREE.** At the ruled index `ClauseIAtOrd`,
   `CodedLevelsAtOrd` and `Σ[ψ] (Det ψ × Wit ψ)` are one debt
   (`Probe642.agda:364`, `:388`). A brief that funds two of them funds the
   same thing twice.
2. **THE DEBT IS `Holds`, AND ITS PRICE IS 2.6(ii).** Do not fund `Wit`:
   its existential is free (`Probe642.agda:354`). Fund a formula that holds
   at the tower's own value inside the stage. Its one unbuilt input is the
   approximation for the tower below the index, AS A MEMBER OF THE STAGE:
   `dev/literature/devlin-II5.md:220-222`, and `[LJ-1.610]`'s `WitStage`
   (`agents/tasks/LJ-1-610/Probe610.agda:235-238`) is the same statement in
   the stage's own carrier. **Four dispatches now name it. It is the
   keystone and it should be the next mathematical task, not another
   consumer of it.**
3. **THE NEXT TASK AT THIS FRAME CAN RUN WIDE.** The trimmed frame peaks at
   0.65 GiB and the finished probe at 0.60 GiB, both under the 2 GiB wide
   cap (`runs/floor-1.out`, `runs/p-final.out`). The heavy tier was not
   needed. `[LJ-1.598]`'s wall was the IMPORT of another probe, and premise
   4's cure holds.
4. **DECIDE `lam = ω`.** The frame admits it and Devlin's clause is stated
   at a limit above `ω` (`dev/literature/devlin-II5.md:218`). Either add
   the hypothesis to the certificate's frame or route the supplier around
   (b). See the D-10 section.
5. **SITES 2 AND 4 OF THE C-42 TABLE ARE STILL AT THE COLLAPSE INDEX.**
   `Facts.LevelsCommute` and clause (iii). Nothing in `src/` carries the
   shape, so the cure is an edit to one probe file and not a sweep.
6. **THE HULL-SIDE CARRIER SLIDE HAS NO SUPPLIER, AND SOMEBODY WILL NEED
   IT.** `[LJ-1.610]` paid the stage-side slide and recorded that the
   hull-side one is missing. Any concrete `ψ : Formula T.Code 2` needs it.
   It is smaller than 2.6(ii) and it can be funded in parallel.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-642/`. Gates run:
`check-probes.py --check` clean (9739 tracked files),
`lint-agda.py --check` exit 0, `check-fences.py --check` clean (103
masters). I did not run `make check`: I commit nothing. No commit, no push.
`git status` shows only `agents/tasks/LJ-1-642/` as new.

**I did NOT write `review-of-clause-i-at-ord.md`, and that is a decision.**
My standing clause says a `review-of-*.md` is how a coder states a NO-GO,
and a NO-GO means the brief's type was not inhabited. The brief's type
carries `Det` and `Wit` as its own inputs and it IS inhabited, green and
metered. **The one thing a reader must not miss is in the HEAD block and in
"WHAT I COULD NOT CLOSE": neither supplier is built, so clause (i) at the
ruled index is reduced and not proved.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, one row, and it is the
  brief's premise 5.** `:52` reads

      | LJ-1.34 | GATE leg D: the certificate story vs the machine | NO-GO, under DD25 review | 0.436 per line, and the Delta-0 certificate does NOT close: the delivered leaves carry unbounded quantifiers |

  TOOK the failure mode and CHECKED it: this task certifies no leaf as
  bounded at all, so the mode is not reproduced. The D-10 section says so
  with the reason.
- `dev/ARCHIVE.md`: **READ, first line only, and declined for content.**
  `:1` reads `# ARCHIVE.md: the archive registry`. W4 is not applicable
  here, so this task adds no row and needs none.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. A history, and
  nothing in this task needed one.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DD-archived.md`: **declined, not read beyond its first
  line.** `:1` reads

      # THE `DD` RULING SERIES, archived in full 2026-08-18

  The live rules are the five files the program cats, and no
  clause of this task rests on a `DD` number.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it carries the D-10 finding
  and the residue's name.** `:99` reads

      > (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].

  and `:218` reads

      2. Uniform Δ₁ at limit α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α,

  and `:222` reads

         γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not

  TOOK three things: the index discipline `(∀γ < α)` over ORDINALS, which
  the ruling now matches; the `α > ω` hypothesis, which the frame does not
  carry (the D-10 section); and the residue's name, "witnessed inside the
  carrier", which is 2.6(ii) and is what `Holds` costs.
- `dev/literature/truncation-and-selection.md`: **READ, and this task
  SPENDS it.** `:17` reads

      LEAST witness under a definable well-order, and all three write leastness with

  TOOK the law that the classical sources select the LEAST witness under a
  definable well-order, with no choice. `skolem` (`Probe642.agda:244`) is
  exactly that mechanism inside the machine: `leastOf` over the stage's own
  order (`src/L/WellOrder/Base.lagda.md:158-161`) turns a TRUNCATED
  satisfiability into an UNTRUNCATED code, which is what makes the converse
  half of the equivalence provable at all.
- `dev/literature/digest.md`: **READ, one line, and it is the brief's
  premise 6.** `:69` reads

      Mathias's WS section 10 as the inventory: false Delta-0 claims for syntax

  TOOK the warning and CHECKED it against this task's own output: no
  Delta-zero certificate is delivered, quoted or assumed here, so the
  inventory has nothing to bite. The D-10 section records that reasoning.
- `dev/literature/terms-2026-08.md`: **not used.** `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  No naming question arose and this task proposes no `dev/glossary.toml`
  entry.
- `dev/literature/geology.md`: **not used, and declined.** `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Set-theoretic geology is a different subject from the level-hood
  certificate, and no clause of this task rests on it.
