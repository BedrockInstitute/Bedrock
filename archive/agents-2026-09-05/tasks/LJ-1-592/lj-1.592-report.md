# [LJ-1.592] report: any coded injection of `Lset α` into `α`

## HEAD
head_slot: coder
machine: shared
task: LJ-1.592
obligation: agents/tasks/LJ-1-592/Probe592.agda::stage-counted
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-592/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **NO HEAP EVENT**: the largest maximum resident set size of any run
is 2,098,135,040 bytes, about 1.95 GiB, against the 8 GB cap
(`agents/tasks/LJ-1-592/runs/s2-1.out`). No run gave exit 251 and no run
printed a heap message. Nothing is postulated, the probe carries `--safe`
(`agents/tasks/LJ-1-592/Probe592.agda:1`), and there is no hole. Nothing lands
in `src/`. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**ONE RUN OF THE TWELVE WAS NOT GREEN AND I NAME IT.** `runs/s2-1.out` is exit 42,
one `UnequalSorts` error: W3's `untrunc-free` was written at
`{A : Type (ℓ-suc ℓ)}` and `sq δ` is `Type ℓ`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). I generalised W3 to
`{ℓ' : Level} {A : Type ℓ'}`, re-ran W3 alone (`runs/w3-2.out`, exit 0), and
`runs/s2-2.out` is the same section, exit 0. Every other run in `runs/` is
exit 0.

## VERDICT

**NO-GO on `stage-counted`.**
`agents/tasks/LJ-1-592/review-of-stage-counted.md` states it. THE OBLIGATION IS
NOT IN THE PROBE and no weaker term is offered as one.

**ROUTE 1 IS CLOSED, AND THE PROBE SAYS WHY IN ONE SENTENCE: THE TRUNCATION WAS
NEVER THE OBSTRUCTION.** The permission the route rests on is real and free.
It removes one obstruction that was really there. It does not touch the one
that stops this pair.

## D-10, BEFORE ANY AGDA

The brief orders two things said at `file:line`: what `PT.rec` lets me assume,
and that the target is an hProp so the recursion is legal.

**WHAT `PT.rec` LETS ME ASSUME: ANYTHING TRUNCATED, AT ANY UNIVERSE LEVEL, FOR
FREE.** `untrunc-free` (`agents/tasks/LJ-1-592/runs/W3.agda:70-72`) is the whole
permission.

**THE TARGET IS AN hProp AND THE RECURSION IS LEGAL.** `isPropTarget`
(`runs/W3.agda:64-65`) is `PT.squash₁` and nothing else, because `InjL a b` is
`∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`) and the truncation
is OUTSIDE the Σ.

**AND IT DOES NOT REST ON `isPropInjCode`, WHICH THE BRIEF GIVES AS THE
MEASURED BASIS.** `agents/tasks/LJ-1-576/Probe576.agda:77-84` is true and it is
about the Σ's BODY. This route needs only the outer truncation, so the two are
not the same claim. This is a correction to the brief's reasoning and not to
its conclusion: the conclusion, that the recursion is legal, is right, and it
is right for a cheaper reason.

**AND D-10's OWN QUESTION, THE TRUTH OF THE TARGET, HAS AN ANSWER THE BRIEF
DOES NOT CARRY.** `[LJ-1.584]`'s `Reopener` (`Probe584.agda:250-251`) takes
`IsOrd α` and nothing else. `target→ambient∥` (`Probe592.agda:107-110`) shows
the target implies an ambient injection at the SAME pair through `readL`
(`src/L/CantorBernstein.lagda.md:33-38`), so it implies one at finite ordinals
too. The tree proves an ambient injection only with two side conditions,
`α ∈ˢ sucV α₀` and `α ∉ ω` (`src/L/StageCardinal.lagda.md:564-565`);
`archive/dev/LJ-dispatch-index.md:81` records that coverage as "every infinite
alpha"; and the classical statement is restricted the same way, Devlin 1.1(vii)
being `|L_α| = |α|` for infinite α (`dev/literature/devlin-II5.md:155-156`).
**THE TYPE AS WRITTEN IS WIDER THAN THE MATHEMATICS, AND THE EXCESS HAS NOTHING
TO DO WITH CODING.** `Restricted` (`Probe592.agda:129-132`) is the corrected
target and it sits beside the original, as D-10 orders.

**I DO NOT CLAIM THE TARGET IS FALSE.** `[LJ-1.533]`'s review says it "did not
prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ"
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55`), and I did not
either.

## W3, THE WIDEST UNMEASURED TERM

**IT WAS WRITTEN FIRST AND TYPECHECKED ALONE**, as the brief orders. The slice
is `agents/tasks/LJ-1-592/runs/W3.agda`, a real `.agda` and not a transcript,
and `Probe592.agda:69-70` IMPORTS it rather than restating it, so the interface
cannot drift.

- `runs/w3-1.out`: exit 0, 1.57 s, peak 386,367,488 bytes.
- `runs/w3-2.out`: exit 0, 1.74 s, same peak, after the level generalisation.

**THE MEASURED NUMBER, NOT THE BRIEF'S GUESS.** The brief estimated "about 10
lines, under 60 seconds". W3 is 72 lines of which the two obligation terms are
5, and it ran in 1.57 s. The line estimate is low because the slice carries
`isL-ord`, `ordS` and `Target` so that it stands alone; the time estimate is
high by a factor of about 38.

**AND IT IS INHABITED**, which is what the brief asked. `isPropTarget` is
green.

## WHICH INJECTION I BUILT

**NONE AT THE OBLIGATION'S PAIR.** No coded injection of `Lset α` into `α` is
in the probe.

**WHAT I DID BUILD, AND IT IS GREEN AND FREE:**

- `ord-into-stage` (`Probe592.agda:173-174`): `InjL (ordS α oα) (LsetS α oα)`,
  at every ordinal, with no hypothesis. It is coded because
  `injL-from-subset` (`agents/tasks/LJ-1-587/Probe587.agda:255-257`) carves the
  identity graph by one separation at `inclFo` (`src/L/InjChain.lagda.md:480`),
  and the subset witness it needs is the tree's own
  (`src/L/StageCardinal.lagda.md:193-195`). **THIS IS THE CONVERSE OF THE
  OBLIGATION.**
- `target→bijection` (`Probe592.agda:181-187`): with `ord-into-stage` and the
  trophy's own Cantor-Schroeder-Bernstein
  (`src/L/CantorBernstein.lagda.md:51-55`), whoever pays the obligation pays a
  BIJECTION and not merely an injection. **This is the honest price of the
  target and the next brief should quote it.**
- `coded-step→restricted` (`Probe592.agda:275-279`): the whole induction, over
  a propositional motive, from ONE coded step. See the next section.

## WHICH ROW THIS PAYS

**NEITHER.** No row of `[LJ-1.564]`'s bill and no residue of `[LJ-1.580]` is
discharged by this task, and I read no discharge into either.

- Row 4 is `StageCountedCoded` (`agents/tasks/LJ-1-523/Probe523.agda:258-261`).
  NOT PAID: the obligation is not inhabited.
- Row 1's residue is `Leg2Coded`, which
  `agents/tasks/LJ-1-580/Probe580.agda:311-317` measures to BE
  `InjL (Lset β) αᴸ`. NOT PAID, for the same reason.

**AND THE BRIEF'S WARNING IS UNNEEDED HERE BUT I ANSWER IT.** `[LJ-1.585]`
measured that one formula buys at most one of the two rows
(`agents/tasks/LJ-1-585/Probe585.agda:245-258` gives row 4 plus a gap to row 1,
and `:267-278` gives row 1 to the gap with no row 4 at all). I claim neither,
so the question does not arise.

## THE TWO `[LJ-1.587]` PRODUCERS, TRIED

The brief calls them the obvious material and orders them tried first, with an
answer on whether they suffice. **THEY DO NOT.** Both are applied at this pair,
both applications typecheck, so what is measured is the input each still wants.

| producer | applied at | still wants |
|---|---|---|
| `injL-from-subset` (`Probe587.agda:255-257`) | `subset-route` (`Probe592.agda:160-163`) | `Lset α ⊆ α`. Not available; the tree has the other inclusion |
| `injL-compose` (`Probe587.agda:259-261`) | `compose-route` (`Probe592.agda:195-198`) | a middle `b` and BOTH legs. The left leg is the target's own shape at `b` |

The one middle the tree hands over free is the wrong way round, and
`converse-composes` (`Probe592.agda:204-208`) is that reading: it concludes at
the CONVERSE target.

## WHAT ROUTE 1 REALLY BUYS, AND IT IS NOT NOTHING

**THIS IS THE PART THE NEXT BRIEF NEEDS MOST.**

`stage-card-upper` concludes at `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, which is NOT a
proposition, so its `∈-induction` takes the square law as DATA at every
sub-stage. That is `SqFam` (`src/L/StageBound.lagda.md:36-40`), and the tree
reaches `SqFam` only through `SqCollect`, which
`src/L/StageBound.lagda.md:42` marks "Not inhabited".

**THE TARGET IS A PROPOSITION, SO THAT COLLECTION IS NOT NEEDED.**
`coded-step→restricted` (`Probe592.agda:275-279`) is the same `∈-induction`
(`src/V/Hierarchy.lagda.md:177-180`) over the propositional motive `Motive`
(`Probe592.agda:253-255`), spending `sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-328`) POINTWISE through `sq-trunc-spends`
(`Probe592.agda:245-249`). **It is green.**

**AND IT USES NO `sq` PARAMETER, BY MODULE STRUCTURE AND NOT BY ASSERTION.**
The probe's top-level module takes `lem`, `α₀` and `oα₀` only
(`Probe592.agda:38-39`). Every predecessor at this site took the family
(`agents/tasks/LJ-1-561/Probe561.agda:44-49`,
`agents/tasks/LJ-1-568/Probe568.agda:45`,
`agents/tasks/LJ-1-584/Probe584.agda:38-43`). The family enters only in
`module WithSq` (`Probe592.agda:309`), so nothing in sections 0 to 2 can have
consumed it.

**WHAT REMAINS IS `CodedStep` (`Probe592.agda:263-268`)**: at one stage `δ`,
with the square law at `δ` as data and the CODED conclusion already held at
every member of `δ`, produce the coded conclusion at `δ`.

## WHERE IT STOPS, AND WHAT THE SHAPE RESISTED

**`CodedStep` IS A CODE, NOT A TRUNCATION, AND THE SAME `W` PAYS IT.**

1. `target→ambient∥` (`:107-110`): the target reads BACK as an ambient
   injection, by `readL`.
2. `sqfam→ambient` (`:332-335`): the family builds the ambient injection, by
   `stage-card-upper`.
3. `ambient→target` (`:343-344`): the arrow in the missing direction is
   `[LJ-1.561]`'s `w→code` (`Probe561.agda:287`), and its hypothesis is `W`
   (`Probe561.agda:160-163`).
4. `w→coded-step` (`:368-370`): `W` pays `CodedStep` outright.

`trunc-route-meets-W` (`:358-363`) is the two routes meeting. `W` is
`[LJ-1.554]`'s missing input and `[LJ-1.533]`'s wall, and that report's own
answer to "what turns an arbitrary ambient function into an `InjCode`" is
"**NONE.**" (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`).

**WHAT I HAD TO WEAKEN.** Nothing was weakened into a claim. The obligation is
absent and `Restricted` sits beside it as the corrected target, not as a
substitute deliverable.

## THE C-42 SWEEP: "ANY CODED INJECTION" IS A COUNT OF THREE

C-42 orders the count before the cure (`dev/LESSONS.md:3752`). The shape here
is the brief's own permission, so the number that settles the brief is how many
ways the tree can build a coded injection. **THREE, AND NO MORE.**

| way | site | what it needs |
|---|---|---|
| separation at `inclFo D` | `src/L/InjChain.lagda.md:480` | `D ⊆ C`; the range conjunct at `:544-547` spends the subset witness |
| separation at `shiftFo D γ ω z` | `src/L/Absorption.lagda.md:413` | the pair `(sucʟ γ , γ)` |
| composition of two codes held | `src/L/InjChain.lagda.md:314-446` | both legs |

Six files of `src/` name `InjCode`: the definition
(`src/L/Cardinal.lagda.md:223-228`), its truncation
(`src/L/GCH.lagda.md:37-38`), a comment (`src/FOL/Bernstein.lagda.md:106`), a
CONSUMER (`src/L/CantorBernstein.lagda.md:33-38`), and two that are ONE term by
the elaborator (`agents/tasks/LJ-1-587/Probe587.agda:223-230`). Every other
`hasSeparationL` application in `src/` carves something that is not an
injection graph (`src/L/Axioms/Power.lagda.md:190`,
`src/L/Choice/Before.lagda.md:232`, `src/L/Choice/Table.lagda.md:785`,
`src/L/Choice/Limit.lagda.md:608`, `src/L/Coding/CodeSet.lagda.md:310`,
`src/L/Coding/EnvSet.lagda.md:190`), and `src/L/Coding/Key.lagda.md:258` is a
third `Carve` that names no `InjCode`.

**SO A NEW CODED INJECTION IS A NEW `Formula S 1` PLUS A BOUND, SEPARATED.**
That is `[LJ-1.568]`'s `Def` (`agents/tasks/LJ-1-568/Probe568.agda:189`), which
`[LJ-1.584]` refuted at the only injection this pair has. **A TRUNCATION
SUPPLIES NO FORMULA.** `archive/dev/JOURNAL.md:940` records what the square law
supplies instead: `src/L/StageCardinal.lagda.md:15-19` demands an injective
`⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` "and nothing more".

**A CORROBORATION I DID NOT LOOK FOR.** `check-unbound-hyp` flags five
hypotheses in `src/` worth a refutation attempt, and two of them are the very
parameters this task turns on: `sep` at `src/L/InjChain.lagda.md:471` and `ih`
at `src/L/StageCardinal.lagda.md:281`. I ran the gate, I did not change it, and
I make no claim about the other three.

## WHAT THE NEXT BRIEF NEEDS

1. **CORRECT THE QUANTIFIER BEFORE ANYTHING ELSE.** A brief that keeps
   `Reopener`'s bare `IsOrd α` asks for more than `L.StageCardinal` proves, for
   a reason unrelated to `InjL`. `Restricted` (`Probe592.agda:129-132`) is the
   target that matches the mathematics.
2. **AIM AT `CodedStep`, NOT AT THE TOWER.** It is one stage, with the square
   law as data and the coded induction hypothesis in hand.
   `coded-step→restricted` already carries it to the corrected target. Priced
   against nothing measured: named as a route, not funded.
3. **ONE NAMED ROUTE IS NOW UNNECESSARY AT THIS TARGET.** `[LJ-1.584]`'s route
   3 (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:141-148`) asks
   for a weakly constant endomap on `sq δ`, which by Kraus, Escardo, Coquand
   and Altenkirch Theorem 16 lifts `∥ sq δ ∥₁` to `sq δ`
   (`dev/literature/truncation-and-selection.md:158-160`). **That lift buys
   nothing here.** The same file's first question is "Is the goal a
   proposition? Then `PT.rec` applies and there is nothing to discuss"
   (`:288-289`), and `sq-trunc-spends` is the whole lift in one line. The
   endomap is still a route to a CANONICAL `stage-card-upper`, which is a
   different object.
4. **AND ROUTE 2 IS UNTOUCHED.** `[LJ-1.594]` carries it
   (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:131-139`). The
   sweep above is the reason it is the only remaining shape.
5. **THE COLLECTION PROBLEM REAPPEARS ONE LEVEL DOWN IF THE STEP IS BUILT
   AMBIENTLY.** `ih→ambient∥` (`Probe592.agda:289-293`) shows the coded
   induction hypothesis reads back as ONE TRUNCATION PER SUB-STAGE, and the
   ambient injection type is not a proposition, so these do not assemble into
   the family `limit-step` consumes (`src/L/StageCardinal.lagda.md:281` takes
   `ih` as data). **A `CodedStep` built by going out to the ambient world and
   back pays twice.**

## RUNS AND CALIBER

Caliber on this pane: `GHCRTS="-A64m -I0 -M8g"`, set by the program. I did not
set it. One Agda process at a time. Twelve runs, all recorded in
`agents/tasks/LJ-1-592/runs/` by `runs/run.sh`, which prints the caliber it saw
and never sets one.

| run | file | exit | real | peak RSS |
|---|---|---|---|---|
| w3-1 | `runs/W3.agda` alone | 0 | 1.57 s | 386,367,488 |
| w3-2 | `runs/W3.agda` alone, after the level fix | 0 | 1.74 s | 386,367,488 |
| s0-1 | `Probe592.agda` section 0 | 0 | 15.89 s | 1,324,089,344 |
| s1-1 | sections 0 to 1 | 0 | 3.48 s | 790,511,616 |
| s2-1 | sections 0 to 2 | **42** | 16.79 s | 2,098,135,040 |
| s2-2 | sections 0 to 2, fixed | 0 | 3.73 s | 810,565,632 |
| s3-1 | sections 0 to 3 | 0 | 4.19 s | 978,436,096 |
| s4-1 | the whole probe | 0 | 3.91 s | 976,289,792 |
| final-1 | the whole probe | 0 | 3.95 s | 976,338,944 |
| final-2 | the whole probe | 0 | 4.02 s | 976,322,560 |
| final-3 | the whole probe | 0 | 3.92 s | 976,338,944 |
| final-4 | the whole probe, both interfaces deleted | 0 | 4.26 s | 956,416,000 |

`final-1` to `final-3` each ran after
`_build/2.8.0/agda/agents/tasks/LJ-1-592/Probe592.agdai` was deleted; `final-4`
ran after both that file and `runs/W3.agdai` were deleted. The
`s0-1` and `s2-1` times include the first elaboration of the imported chapters
and probes; the later runs read those interfaces from `_build`.

**THE PROBE'S SIZE, MEASURED.** `Probe592.agda` is 457 lines, `runs/W3.agda` is
72. The brief estimated "about 180 lines in the probe, of which the obligation
is about 45". The probe is about 2.5 times the estimate and the obligation is
0 lines, because it is not inhabited; the extra length is the measurement of
why.

## GATES

Every conjunct of `make check` except `typecheck`: `markers`, `lint`,
`lint-agda`, `glossary`, `ledger`, `probes`, `closure`, `fences`, `reuse`,
`ruleids`, `specsurface`. **ALL CLEAN.** `reuse` refused under `make` because
this worktree has no `.venv/bin/reuse`; I ran
`/Users/alsg/Agentic/Bedrock/.venv/bin/reuse lint -q` from the main checkout's
pinned environment instead, and it is clean. Every other gate ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter, with the
working directory left in this worktree.

`scripts/measure/check-unbound-hyp.py` reports 5 pre-existing hypotheses in
`src/`. None is in this task's files, and I changed none of them.

**TWO GATES I DID NOT RUN, AND WHY.** `typecheck` builds the whole tree.
`git status --porcelain` shows ONE entry, the untracked
`agents/tasks/LJ-1-592/`, so no master changed and a whole-tree typecheck would
measure nothing about this task; it would also be a SECOND Agda process while
other panes may hold one. `ratio` is not a conjunct of `make check`, and the
probe carries no ` ```agda ` fence, so the bar cannot fire on it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.** `:81` reads
  "| LJ-1.21 | Build: the carrier-level descent for the level size | DELIVERED, and it cost | StageCardinal 174 to 484 lines, 0.90 to 42.03 s. Init dropped, so every infinite alpha. LJ-1.25 cured it |".
  I used the phrase "every infinite alpha" as the record of what
  `stage-card-upper` covers, in the D-10 section.
- `archive/dev/JOURNAL.md`: **READ.** `:940` reads
  "`src/L/StageCardinal.lagda.md:15-19` both demand an injective". I used it in
  the C-42 sweep for what the square-law parameter supplies, which is an
  injection and no formula.
- `archive/dev/JOURNAL-archived.md`: **NOT READ.** I grepped it for `InjL`,
  `StageCardinal`, `square law` and `stage-card`; the four hits (`:1338`,
  `:1394`, `:1437`, `:1449`) are all size and funding estimates from the
  campaign that priced the square law, and this task prices nothing. Declined.
- `dev/ARCHIVE.md`: **NOT USED.** The same grep gives no hit. Nothing was
  retired by this task, so W4 has no row to write here. Declined.
- `archive/dev/DD-archived.md`: **NOT USED.** The same grep gives no hit, and
  the `DD` series is set aside in this form by amendment A7. Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ.** `:288` reads
  "1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to".
  I used it twice: as the law behind W3, and to retire `[LJ-1.584]`'s route 3
  at this target. `:158` reads
  "- **Theorem 16: \"A type X has a constant endomap if and only if it has split",
  which is the theorem that route 3 rests on.
- `dev/literature/devlin-II5.md`: **READ.** `:155` reads
  "part (ii) fixes it pointwise, in particular π(x) = x; by 1.1(vii),". I used
  it in the D-10 section: the classical statement `|L_α| = |α|` is at INFINITE
  α, so the obligation's bare `IsOrd α` is wider than the source.
- `dev/literature/digest.md`: **NOT READ.** It is the rud route's orthodox
  form; this task builds no rud and names no J tower. Declined.
- `dev/literature/level-formula-slot-roles.md`: **NOT USED.** It answers what a
  level-hood formula binds. This task writes no formula: the C-42 sweep is why
  the next brief will need it, and that is `[LJ-1.594]`'s work, not mine.
  Declined.
- `dev/literature/terms-2026-08.md`: **NOT USED.** It is a terminology dossier
  for a glossary ruling. No term was named or renamed here. Declined.
