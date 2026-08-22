# LJ-1.546 report: what B10 wants beside a code, and the two coordinates do not cost the same

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-546/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated and there is no hole. The probe
is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it. I did not write
`review-of-transfer-suffices.md`: the GO branch forbids that file.

## VERDICT

**GO. THE OBLIGATION IS INHABITED.** `transfer-suffices`
(`agents/tasks/LJ-1-546/Probe546.agda:163-171`) has the brief's type, with the
named fact as its one hypothesis. Exit 0 on every run.

**THE BRIEF ASKED FOR A DISTANCE AND THE DISTANCE IS NOT SYMMETRIC.** The pair
mismatch is on BOTH coordinates, as the brief expected. But one coordinate is
free and the other carries the whole price, and that is this task's finding:

| coordinate | CodedShift has | B10 wants | price |
|---|---|---|---|
| target | `γ`, an ordinal | `𝒫 κ`, a power set | **FREE**, and PAID in this probe |
| source | `sucʟ γ`, an ordinal successor | `δ`, a cardinal successor | **THE WHOLE RESIDUE** |

**THE POWER SET IS NOT A CODING WALL.** `shift-into-power`
(`Probe546.agda:189-208`) delivers `InjL (sucʟ κ) (𝒫 κ)` from terms already in
`src/`, with no new hypothesis beyond the four `shift-coded` already takes. So
`InjCode` accepts a power set in its second argument, and it accepts an
inhabitant there, not only a type.

**READ THAT RESULT AT ITS OWN SIZE.** It is a CODING result and not a CARDINAL
one. `sucʟ κ` is the ordinal successor, so the injection it codes is cardinally
trivial. Its value is that a code whose target is `𝒫 κ` now exists in the tree
as a term, so no later brief has to ask whether the target is reachable.

## D-10, BEFORE ANY AGDA, AND IT IS THE DISTANCE

**WHAT PAIR `CodedShift` DELIVERS A CODE AT.** `(sucʟ γ , γ)`, at
`src/L/CodedShift.lagda.md:40`:

    → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

**WHAT PAIR B10 WANTS.** `(δ , 𝒫 κ)`. `SuccIntoPower`
(`agents/tasks/LJ-1-523/Probe523.agda:266-269`) concludes `InjL δ (𝒫 κ)`, and
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:38`).

**THE DIFFERENCE IN ONE SENTENCE.** It is both: an ordinal successor against a
cardinal successor on the source, and an ordinal against a power set on the
target.

**AND THE STRUCTURAL REASON THE TWO DO NOT COST THE SAME.** `InjCode F a b` has
four conjuncts (`src/L/Cardinal.lagda.md:223-227`). The TARGET `b` occurs in
conjunct 4 alone, and there only as an upper bound on the range. The SOURCE `a`
occurs in conjunct 2 alone, but `domAt f d` is a BICONDITIONAL
(`src/L/Coding/Model.lagda.md:279-280`): its first half sends an entry of the
table to a member of `a`, and its second half sends a member of `a` back to an
entry. Conjuncts 1 and 3, `svAt` and `injAt`, name neither `a` nor `b`
(`src/L/Coding/Model.lagda.md:210-211`, `src/L/Coding/Injection.lagda.md:44-45`).

Both halves of that reading are MEASURED and not argued:

- **`code-target-mono`** (`Probe546.agda:114-119`). Enlarging the target costs
  one composition, and the first three conjuncts are returned untouched.
- **`code-source-determined`** (`Probe546.agda:127-133`). Two codes that share a
  table have the same source, member by member. So no monotone analogue of the
  first term can exist, and the only move on the source is a `subst` along a
  path, which is exactly what `src/L/CodedShift.lagda.md:52` does.

## THE NAMED FACT

**IT IS `SuccIntoSubsets`** (`Probe546.agda:152-157`), stated in full:

    SuccIntoSubsets : Type (ℓ-suc ℓ)
    SuccIntoSubsets =
        (κ δ : SL.S) → SuccCardL δ κ
      → ∥ Σ[ b ∈ SL.S ] Σ[ F ∈ SL.S ]
           ( InjCode F δ b
           × ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

**IN WORDS.** δ admits a code into SOME L-set every member of which is a subset
of κ. It does not ask for that set to BE `𝒫 κ`.

**I DID NOT INHABIT IT AND I DID NOT REFUTE IT. IT IS LEFT OPEN**, as the brief
ordered. What I built is the implication, `transfer-suffices`.

**IT PASSES THE BRIEF'S THREE TESTS.**

1. **Self-contained at its own frame.** It names δ, κ, `InjCode` and the model's
   `_⊆ˢ_` and nothing else. It names no model record: there is no `zf` in its
   type, so a later coder can take it with no `isZFModel` in scope.
2. **It does not mention `SuccIntoPower`.** It does not mention `𝒫` either.
3. **One obligation.** It is one truncated existential with one hypothesis.

**WHY DROPPING `𝒫` IS A REAL REDUCTION AND NOT A RENAMING.** `𝒫 κ` is
`℩ (hasPower κ)` (`src/FOL/ZFModel.lagda.md:287-288`), and `℩-spec` gives
`IsSetOf`, which is a POINTWISE EQUALITY of truth values
(`src/FOL/ZFModel.lagda.md:74-75`). To prove a constructed set IS `𝒫 κ` you owe
both directions of that equality at every member. To prove its members are
subsets of κ you owe one direction. `transfer-suffices` spends `hasPower` once,
in the only place the model is used, and buys the other direction back.

**WHAT A TASK THAT BUILDS IT WOULD COST, IN ONE SENTENCE.** It is a
formula-carving task of the `Carve` class (`src/L/Absorption.lagda.md:386`): the
builder must write ONE `Formula` that defines the assignment from a member of δ
to a subset of κ, and prove its adequacy, because `[LJ-1.533]` measured that both
generators of an L-element take a `Formula` in their type
(`agents/tasks/LJ-1-533/lj-1.533-report.md`, section `## WHAT CODES AN AMBIENT
INJECTION`), so the uniformity the truncated Σ demands cannot come from anywhere
else. **NOTHING MAY BE FUNDED AGAINST THAT COMPARABLE**: it is a comparable of
SHAPE, and the brief's own rule and `AGENTS.md:45` both forbid transferring a
measured price by analogy.

## THE LEASTNESS CLAUSE, ANSWERED BY THE ELABORATOR

**THE BRIEF SAID TO SAY THIS LOUDLY, SO: THE TRANSFER NEEDS NO PART OF
`SuccCardL`, AND THAT INCLUDES THE LEASTNESS CLAUSE.** The measurement is
`leastness-not-consumed` (`Probe546.agda:238-247`), which is section 4's term
with the whole `SuccCardL` hypothesis deleted from both sides. If any line of
`transfer-suffices` projected `sc`, that term would not exist. This is the
`[LJ-1.540]` device (`agents/tasks/LJ-1-540/Probe540.agda:371-376`).

**THE LEASTNESS IS NOT REMOVED FROM THE PROBLEM. IT IS LOCATED**, and it is
inside `SuccIntoSubsets`, which KEEPS `SuccCardL`.

**AND IT MUST KEEP IT.** `SuccIntoSubsets⁻` (`Probe546.agda:231-236`), the
hypothesis of the measurement above, **IS FALSE**: with `SuccCardL` gone, δ
ranges over every L-element, δ := κ⁺⁺ included, so an inhabitant would refute
GCH. The probe says so at `Probe546.agda:213-221` in the loudest terms I could
write. **NO BRIEF MAY TAKE `SuccIntoSubsets⁻` AS A HYPOTHESIS.** It is a
measuring rod. I write this because `dev/pod/audit-2026-08-20.md:34` records
finding F1, where a probe took as a module hypothesis a type a predecessor had
refuted fifty minutes earlier, and the GO was hollow.

## WHAT B9 WANTS

B9 is `StageCountedCoded` (`agents/tasks/LJ-1-523/Probe523.agda:258-261`), whose
pair is (the stage, the ordinal δ), so its target is already an ordinal and
`code-target-mono` buys it nothing: there is no larger target it needs to
reach. The two rows therefore share NO fact from this reduction, because
`SuccIntoSubsets` asks for a code whose source is δ while B9 asks for a code
whose source is `Lset δ`, and `code-source-determined` (`Probe546.agda:127-133`)
says a table has exactly one source. What they DO share is the coordinate that
costs: both need a `Formula` that carves a table with the required domain, which
is the wall `[LJ-1.533]` measured for B9
(`agents/tasks/LJ-1-533/lj-1.533-report.md`, `## WHAT CODES AN AMBIENT
INJECTION`) and which this task now shows is B10's only remaining wall too. I
did not build B9, B5 or B8.

## W3, THE WIDEST UNMEASURED TERM

**THE QUESTION.** `𝒫 κ` as `InjCode`'s second argument, because `InjCode` was
written for a stage and nobody had fed it a power set.

**GO. THE TYPE FORMS.** `W3-code-at-power` (`Probe546.agda:68-70`) is
`InjCode F δ (𝒫 κ)` at B10's frame, TYPE ONLY, no inhabitant. It was written
first and typechecked ALONE, as the brief ordered. The slice is kept at
`agents/tasks/LJ-1-546/runs/w3-slice.agda.txt` and the run is
`runs/w3-1.out`: exit 0.

**THE NUMBER I MEASURED, NOT THE NUMBER THE BRIEF GUESSED.** The brief estimated
about 12 lines and under 30 seconds. The slice is 28 lines including its header
comment and imports, and it took **1.64 s** (`runs/w3-1.out`), with 399,933,440
bytes maximum resident set size against the 8 GB cap.

**AND THE ROW IS NOT REFUTED AT THE TYPE.** Section 5 goes past the type and
inhabits a code at a power-set target, so W3's fear does not survive at all.

## THE SWEEP (C-42), MY OWN, AT TODAY'S TREE

The refutations this row inherits (`[LJ-1.533]`, `[LJ-1.535]`) named their own
sites. C-42 says to count the shape before pricing anything, so I counted the
sites that DELIVER an inhabited `InjCode` at a named pair.

**SITES IN `src/` THAT DELIVER AN INHABITED `InjCode`: TWO. PAIRS THEY DELIVER
AT: ONE.**

- `src/L/Absorption.lagda.md:611-626`, `shift-coded`, at `(sucʟ γ , γ)`.
- `src/L/CodedShift.lagda.md:37-52`, `shift-coded`, at `(sucʟ γ , γ)`.

Every other occurrence of `InjCode` in `src/` is a definition
(`src/L/Cardinal.lagda.md:223`), an import, a comment, a CONSUMER
(`src/L/CantorBernstein.lagda.md:33`, `readL`, which takes an `InjCode` as an
argument and reads it back), or a refutand inside `IsCardinalL`
(`src/L/Cardinal.lagda.md:233`).

**SO B10's SOURCE HAS NO SHADOW IN `src/` AT ALL.** There is one delivered
source in the whole tree and it is `sucʟ γ`.

**ONE FINDING THE SWEEP TURNED UP THAT IS NOT MINE TO FIX.** `shift-coded` is
landed TWICE, and the two blocks are byte-identical over 16 lines:
`src/L/Absorption.lagda.md:611-626` and `src/L/CodedShift.lagda.md:37-52`. Both
masters are live and both are imported by `src/Everything.lagda.md:377`.
`[LJ-1.469]` landed the first and its report says "Import `L.Absorption` and use
`shift-coded`. Do not rebuild the term."
(`agents/tasks/LJ-1-469/lj-1.469-report.md:217`); `[LJ-1.470]` then landed the
identical term in a new master, and its report says "Later briefs can import
`L.CodedShift` and must not rebuild the term from a probe."
(`agents/tasks/LJ-1-470/lj-1.470-report.md:213`). No consumer outside
`src/Everything.lagda.md` imports either one. **I did not touch `src/`.** This is
a W4 row for the one SRC collection the direction schedules after LJ-1 closes,
and I record it here so the collection does not have to rediscover it.

## RUNS AND PRICES

Every run below deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-546/Probe546.agdai` first, because Agda
skips a file whose content is unchanged and a run that skips measures nothing.

| run | what the file was | result |
|---|---|---|
| `runs/w3-1.out` | the W3 slice ALONE, 28 lines, TYPE ONLY | exit 0, 1.64 s |
| `runs/full-1.out` | the probe before section 6, 208 lines | exit 0, 6.50 s |
| `runs/full-2.out` | with section 6, 248 lines | exit 0, 1.83 s |
| `runs/final-1.out` to `runs/final-3.out` | **the file exactly as this report describes it**, 248 lines | exit 0, 1.81 to 1.83 s |

**THE 6.50 s IS NOT THE PROBE'S PRICE AND I WILL NOT REPORT IT AS ONE.**
`runs/full-1.out` carries three `Checking` lines: `L.CodedShift` and
`L.Absorption` had no interface in this worktree yet and were built in the same
process. `runs/full-2.out` and every `final-*` run carry ONE `Checking` line.
The probe's own price with its dependencies warm is **1.81 to 1.83 s**.

**HEAP.** Peak resident 414,400,512 bytes, about 395 MiB, and peak footprint
354,435,912 bytes, against the 8 GB cap (`runs/final-2.out`). No heap event and
no WALL.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **B10's target is closed.** Do not spend another dispatch asking whether a
   code can point at `𝒫 κ`. `shift-into-power` (`Probe546.agda:189-208`) is the
   answer and it is a term.
2. **B10's residue is ONE fact and it is `SuccIntoSubsets`.** The B4 precedent
   says the next task can build it: `[LJ-1.526]` named `CardAboveL` and
   `[LJ-1.528]` built it (`agents/tasks/LJ-1-528/Probe528.agda:638-643`).
3. **BUT THE PRECEDENT DOES NOT TRANSFER WITHOUT A CHECK, AND THIS IS A D-10
   FINDING.** `CardAboveL` was a weakening of a statement the tree could already
   nearly reach. `SuccIntoSubsets` needs a `Formula` written from scratch, which
   is the class of thing the mathematician must rule on, not price by analogy.
4. **THE PROJECT'S OWN LITERATURE DOES NOT COVER B10.**
   `dev/literature/devlin-II5.md` digests Devlin 5.6, and what 5.6 proves there
   is the OTHER leg: `dev/literature/devlin-II5.md:160` reads
   "> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),".
   A search of that file for the reverse inequality returns nothing. So before
   `SuccIntoSubsets` is funded, the argument for it should be pinned in the
   literature the way the hard leg already is. This confirms in the digest what
   `agents/tasks/LJ-1-523/Probe523.agda:264-265` already said in a comment:
   "The bounded-subset theorem says nothing about it: it is not on this bridge
   at all."

## GATES RUN

`lint-prose`, `lint-agda`, `weave-i18n --check`, `check-glossary`,
`ledger --check`, `check-probes`, `check-closure --check closure`,
`check-fences`, `check-spec-surface --check` and `check-rule-ids`: all clean.

I did NOT run `make typecheck`. `git status --short` shows one entry, the
untracked `agents/tasks/LJ-1-546/`, so no master changed and a whole-tree
typecheck would measure nothing about this task.

The worktree carries no `.venv`, so every gate ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter of the
main checkout, with the working directory left in this worktree.

The standing size figure, from the only admissible source
(`scripts/measure/ledger.py --brief`): "standing 33,523 lines over 100 masters,
measured from HEAD". This task changed no master, so it moves that figure by 0.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **not read.** It is the archived index of
  the 464 dispatch rows that lived in `dev/PLAN.md` section 11. The predecessors
  this task depends on are named by the brief with live paths under
  `agents/tasks/`, and I read those directories directly, so the index would add
  no evidence.
- `archive/dev/JOURNAL-archived.md`: **declined.** It is the journal of the
  RETIRED route, archived 2026-08-09. B10 sits on the two-tower route.
- `archive/dev/JOURNAL.md`: **declined.** Archived 2026-08-20 because every task
  already keeps its brief, report and probe under `agents/tasks/<CODE>/`. I read
  those directories instead, which is what the archive header itself points to.
- `archive/dev/DD-archived.md`: **not used.** It is the 20 `DD` rows as they
  stood at the POD cutover. No `DD` row bears on a pair mismatch inside
  `InjCode`.
- `archive/dev/ORCHESTRATION.md`: **not used.** It is the orchestrator's
  operating rules, not a mathematical or coding record.

**NO HIT in the archive corpus for this task.** The evidence this task needed is
all live: `src/L/Cardinal.lagda.md`, `src/L/Coding/Model.lagda.md`,
`src/L/CodedShift.lagda.md`, `src/L/Absorption.lagda.md`, `src/L/GCH.lagda.md`,
`src/FOL/ZFModel.lagda.md`, and the LJ-1.523, LJ-1.526, LJ-1.533, LJ-1.535,
LJ-1.540, LJ-1.469 and LJ-1.470 task directories.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it produced a finding.**
  `dev/literature/devlin-II5.md:160` reads
  "> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),".
  That is the OTHER leg of GCH, not B10. The finding is in
  `## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE`, item 4: the digest does not
  cover B10 at all.
- `dev/literature/truncation-and-selection.md`: **READ.**
  `dev/literature/truncation-and-selection.md:289` reads
  "1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to".
  That is the first question of its decision procedure, and it is why
  `transfer-suffices` and `code-source-determined` can both use `PT.rec`: the
  goal of each is `hProp`-valued, `InjL` by `squash₁` and membership by
  `snd (fst x ∈ fst a')`. It is also why `SuccIntoSubsets` must stay truncated:
  its witness `b` is not unique, so nothing in that file un-truncates it, and
  `dev/literature/truncation-and-selection.md:146` reads
  "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`",
  which is the escape `[LJ-1.526]` used for leastness and which does not apply
  here.
- `dev/literature/digest.md`: **not used.** It pins the orthodox form of the rud
  route. B10 is a coding question inside the Def tower and does not turn on rud.
- `dev/literature/terms-2026-08.md`: **declined.** It is the terminology dossier
  for the owner's naming ruling. This task adds no glossary entry, and the
  Boundary forbids me choosing one.
- `dev/literature/geology.md`: **not used.** Set-theoretic geology sources for
  `[L6]`. Nothing in it bears on `InjCode`.
