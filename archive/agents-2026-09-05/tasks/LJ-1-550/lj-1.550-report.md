# LJ-1.550 report: the target crosses no ambient boundary, but the bridge's ANTECEDENT does, and the site cannot be moved

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-550/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one Agda process of mine at a time. I did not
set `GHCRTS`. Nothing is postulated, the probe carries `--safe`, and there is
no hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP EVENT.** The largest peak memory footprint of any run is
1,456,113,248 bytes, about 1.4 GiB, against an 8 GB cap
(`agents/tasks/LJ-1-550/runs/final-2.out`). No run exceeded 9 seconds. No run
reported exit 251 and no run printed a heap message.

## VERDICT

**NO-GO ON THE OBLIGATION. `bridge-without-B5` IS NOT INHABITED, AND B5 IS NOT
THE ONLY REASON.** `scripts/pod/witness.py` reports
`missing exit=42 agents/tasks/LJ-1-550/Probe550.agda::bridge-without-B5`,
1 UNRESOLVED of 1, `probe_red=False`
(`agents/tasks/LJ-1-550/runs/witness-1.out`). The probe itself is green
(`agents/tasks/LJ-1-550/runs/final-2.out`, exit 0), and the six terms it does
deliver all resolve, 0 UNRESOLVED of 6
(`agents/tasks/LJ-1-550/runs/witness-2.out`).

**THE BRIEF'S PREMISE IS CORRECT AND I CONFIRM IT.** `GCHStatement`
(`src/L/GCH.lagda.md:59-70`) names no ambient type. The chapter's own sentence
at `src/L/GCH.lagda.md:57` holds: "beyond κ itself, and no ambient function
type crosses the ⊨ boundary." The target is internal all the way down.

**BUT THE BRIDGE DOES NOT START AT THE TARGET. IT STARTS AT AN AMBIENT
THEOREM.** `[LJ-1.523]`'s bridge is
`GCHBridge zf = BoundedSubsetTheorem → GCHStatement zf`
(`agents/tasks/LJ-1-523/Probe523.agda:174-175`). Its antecedent is
`Devlin55.BoundedSubsetAt`, whose third telescope slot is
`cardκ : IsCardinal κ` (`src/L/BoundedSubset.lagda.md:1386`), and `IsCardinal`
is the AMBIENT cardinal (`src/L/BoundedSubset.lagda.md:1046-1047`). **An
inhabitant of the bridge must APPLY that antecedent, and applying it means
filling that slot.** So the crossing is real, and it is at the antecedent, not
at the target.

**AND THE SITE CANNOT BE MOVED.** `site-forced`
(`agents/tasks/LJ-1-550/Probe550.agda:385-389`, green) proves it. Section 6
below carries the argument.

**THE ANSWER TO THE BRIEF'S OWN QUESTION.** The brief asks whether the
conclusion that fails is one `GCHStatement` asks for, or one `[LJ-1.523]` added
on the way. **NEITHER. NO CONCLUSION FAILS. A HYPOTHESIS SLOT OF THE ANTECEDENT
IS UNFILLED.** That distinction is the result of this task.

## WHERE B5 IS USED

Required section.

**IN `[LJ-1.523]`'S PROBE, B5 IS CONSUMED NOWHERE. THERE ARE NO CONSUMPTION
SITES.** `AmbientSpentAtSucc` occurs at exactly three lines of that file,
`agents/tasks/LJ-1-523/Probe523.agda:218`, `:219` and `:220`, which are its own
declaration and nothing else. `CardSpentAt` occurs at `:213`, `:214` and `:220`,
which are its own declaration and B5's use of it. **No other line of the file
mentions either name.**

**THE REASON IS THAT `[LJ-1.523]` INHABITED NOTHING.** Its brief forbade the
term and ordered the type only (`agents/tasks/LJ-1-523/Probe523.agda:162-163`:
"NO HOLES. NOT INHABITED."). B5 is a row of that report's accounting table
(`agents/tasks/LJ-1-523/lj-1.523-report.md:230`), which is headed "The inputs an
inhabitant would consume" (`agents/tasks/LJ-1-523/lj-1.523-report.md:219`). **It is not an argument of any type in the
tree.** So "remove B5 from the hypotheses" is vacuous on the bridge's type: B5
was never among them.

**THE SITE B5 WAS MEANT FOR IS THIS ONE, AND IT IS A TERM.**
`UseSite.member-in-stage` (`agents/tasks/LJ-1-550/Probe550.agda:257-284`,
green) applies the antecedent at the only assignment that can serve the
statement, THEOREM's κ := `fst δ` and THEOREM's α := `fst κ`. Its first
argument is `IsCardinal (fst δ)`, and that argument goes to exactly one place:
the `cardκ` slot of `bst` at `agents/tasks/LJ-1-550/Probe550.agda:280`, and the
same slot again inside `CoHyps` at `:283`, which is the same telescope.

**WHAT THE ANTECEDENT SPENDS THERE IS B5, LETTER FOR LETTER.**
`Devlin55.BoundedSubsetAt` consumes `cardκ` exactly twice, at
`src/L/BoundedSubset.lagda.md:1597` and `:1601`, and BOTH times as
`cardκ α α∈κ`. I re-measured this by grep: `cardκ` occurs at three lines of
that file, `:1386` (the binding), `:1597` and `:1601`. At the site fixed above,
that application has type `CardSpentAt (fst δ) (fst κ)`, and
`b5-is-the-spent-slot` (`agents/tasks/LJ-1-550/Probe550.agda:411-412`) is the
identity from `AmbientSpentAtSucc` to it. **So B5 names the right object.**

**BUT B5 DOES NOT FILL THE SLOT, AND THIS IS MEASURED.** The slot is
`IsCardinal (fst δ)`, a Π over EVERY member of δ. B5 gives the refutation at
ONE member, `fst κ`. `b5-from-cardδ`
(`agents/tasks/LJ-1-550/Probe550.agda:394-396`) is the direction that holds,
from the slot to B5. **The converse does not elaborate**, exit 42,
`error: [UnequalTerms]`, `Cubical.HITs.CumulativeHierarchy.Base.V ℓ !=< Σ (⟪ fst δ ⟫ → ⟪ fst κ ⟫) ...`
(`agents/tasks/LJ-1-550/runs/neg-1.out`, source kept at
`agents/tasks/LJ-1-550/runs/Neg550.agda.txt:414-417`).

**SO THE ROW THE BRIDGE ACTUALLY OWES IS NOT B5. IT IS `AmbientAtSucc`,
`[LJ-1.523]`'s own section 4.2** (`agents/tasks/LJ-1-523/Probe523.agda:202-204`),
which that report did NOT put on its B-list. B5 is the weaker statement that
`[LJ-1.523]` derived from measuring what the module spends, and it would fill
the slot only if `src/L/BoundedSubset.lagda.md:1386` were restated with
`CardSpentAt κ α` in place of `IsCardinal κ`. **That is an edit in `src/`, and
this task writes nothing there.** The type is stated at
`agents/tasks/LJ-1-550/Probe550.agda:403-404` so the mathematician can price it.

## WHAT THE JOIN NOW STANDS AT

Required section.

**THE JOIN STILL HAS TEN ROWS AND NOBODY HAS RULED B5 OFF, BECAUSE B5 IS
LOAD-BEARING.** No row leaves the list on my measurement.

| row | state today | evidence |
|---|---|---|
| B1 | PAID, in `src/` | `src/Landmarks.lagda.md:76-77` |
| B2 | PAID, in `src/` | `src/L/CantorBernstein.lagda.md:51-55` |
| B3 | PAID, in `src/` | `src/L/CantorBernstein.lagda.md:33-38` |
| B4 | PAID, in a probe | `agents/tasks/LJ-1-528/lj-1.528-report.md:339` |
| B5 | **UNPAID, AND LOAD-BEARING** | site at `agents/tasks/LJ-1-550/Probe550.agda:257-284` |
| B6 | PAID, in a probe | `agents/tasks/LJ-1-543/lj-1.543-report.md:29-30` |
| B7 | PAID, in a probe | `agents/tasks/LJ-1-540/lj-1.540-report.md:29-30` |
| B8 | PAID, in a probe | `agents/tasks/LJ-1-544/Probe544.agda:225-228` |
| B9 | UNPAID | `agents/tasks/LJ-1-523/Probe523.agda:258-261` |
| B10 | UNPAID | `agents/tasks/LJ-1-523/Probe523.agda:266-268` |

**SEVEN OF THE TEN ARE PAID AND THREE ARE UNPAID. THE COUNT IS UNCHANGED FROM
`[LJ-1.544]`** (`agents/tasks/LJ-1-544/lj-1.544-report.md:118`).

**THE TEN-ROW TABLE UNDER-COUNTS THE BRIDGE BY SIX, AND THIS IS THE REAL
RESULT OF THE TASK.** `bridge-with-residues`
(`agents/tasks/LJ-1-550/Probe550.agda:335-363`, green, no hole) is the WHOLE
implication to `GCHStatement zf`, built from the seven inputs the brief names
plus SIX further hypotheses. Its type is therefore an exact bill. **The six are
these, and three of them are named nowhere in the ten-row table.**

| residue | what it asks for | type at | why the nine cannot give it |
|---|---|---|---|
| R1 `AmbientCardAtSucc` | `IsCardinal (fst δ)`, the FULL ambient cardinal at the successor | `Probe550.agda:301-302` | this is `[LJ-1.523]` section 4.2, not B5. It is the antecedent's own Π slot |
| R2 `SqAt` | `SqLaw (fst κ)`, the BARE square-law family | `Probe550.agda:309-310` | row B12. `SqCollect` (`src/L/StageBound.lagda.md:44-48`) is what would build it from `sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325-327`), and its own comment at `src/L/StageBound.lagda.md:42` says it is not inhabited |
| R3 `CoHyps` | `levelIn` and `cover` over the telescope | `Probe550.agda:215-230` | row B11. `src/L/BoundedSubset.lagda.md:1555-1557` states them as hypotheses and supplies neither |
| R4 `StageIsL` | the stage at δ is itself constructible | `Probe550.agda:317-318` | **not in the ten-row table.** B9 quantifies over an `Lδ` with `fst Lδ ≡ Lset (fst δ)`, so a user of B9 must produce one. `src/` has `ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434`) for the ORDINAL and nothing for the stage |
| R5 `InclusionCoded` | an internal inclusion is a coded injection | `Probe550.agda:324-326` | **not in the ten-row table.** The only producers of `InjCode` in `src/` are `src/L/Absorption.lagda.md:614` and `src/L/CodedShift.lagda.md:40`, and both deliver the one shape `InjCode F (sucʟ γ) γ` |
| R6 `InjLTrans` | coded injections compose | `Probe550.agda:332-333` | **not in the ten-row table.** `src/L/CantorBernstein.lagda.md` is the only consumer of `InjL` in `src/`, and it delivers `mutual-inj→bijection` (`:51-55`), not transitivity |

**B11 AND B12 ARE ON THIS BRIDGE'S BILL, AND `[LJ-1.523]` SAID THEY WERE NOT.**
That report writes at `agents/tasks/LJ-1-523/lj-1.523-report.md:239-242`: "B11
AND B12 ARE NOT ON THIS BRIDGE'S BILL. B11 is carried into
`BoundedSubsetTheorem` as a Π argument, so the bridge does not owe it. B12 is
carried the same way through `sq`." **That is the wrong way round.** A Π
argument of the ANTECEDENT is an argument the inhabitant must SUPPLY, not one it
receives. The antecedent's conclusion is `LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩`
(`agents/tasks/LJ-1-523/Probe523.agda:139`), so `levelIn` and `cover` are owed
too. `member-in-stage` is the measurement: it takes R2 and R3 as arguments
because `bst` cannot be applied without them.

**SO THE BRIDGE STANDS AT SEVEN OF SIXTEEN, NOT SEVEN OF TEN.** Nine inputs
paid or hypothesised by the brief, six residues open, and B5 is one of the six
in name only: what the antecedent asks for at that slot is R1, which is
strictly stronger.

## D-10, BEFORE ANY AGDA

D-10 says price the truth of a recorded residue before pricing its proof. The
brief ordered the use-site read first. I read `agents/tasks/LJ-1-523/Probe523.agda`
end to end before writing any Agda, and grepped the whole tree for both names.
**The result was that B5 has no consumption site at all**, which section
`## WHERE B5 IS USED` records. That reading changed the shape of the task: the
question is not "does the term use B5" but "what does the antecedent's
application need", and the second question needed the term that
`[LJ-1.523]` never wrote.

**A SECOND D-10 CHECK, AND IT PAID.** The brief's premise says B5 "may be
UNPROVABLE as stated". I did not test that and the brief forbade it. I tested
the neighbouring question instead: whether the site could be MOVED to an
ordinal for which an ambient cardinality fact is available. `site-forced`
answers no, and section 6 of the probe carries it. **Without that check the
NO-GO would rest on my failure to find a route, which is not evidence.**

## THE SITE IS FORCED, AND THIS IS THE PART THAT IS NEW

The antecedent concludes `x ∈ˢ Lset κ_theorem`
(`agents/tasks/LJ-1-523/Probe523.agda:139`) and demands `α ∈ˢ κ_theorem`
(`:147`). The statement needs the membership at `fst δ`. Suppose someone tried
to escape the ambient hypothesis by applying the antecedent at some OTHER
ordinal μ, one for which ambient cardinality is available.

**`ambient→internal` (`agents/tasks/LJ-1-550/Probe550.agda:375-377`, green)
closes that escape.** An ambient cardinal is an L-cardinal, because the readback
`readL` (`src/L/CantorBernstein.lagda.md:33-38`) turns any code into an ambient
injection, so an ambient refutation refutes every code.

**`site-forced` (`agents/tasks/LJ-1-550/Probe550.agda:385-389`, green) is the
consequence.** `SuccCardL`'s fourth conjunct (`src/L/GCH.lagda.md:51-53`) is
leastness among ORDINAL L-CARDINALS above κ. `ambient→internal` puts μ in that
class. So `δ ⊆ˢ μ`, that is δ ≤ μ. To land the conclusion inside `Lset (fst δ)`
the other inequality is needed, μ ≤ δ. **Both together force μ ≡ δ.**

**THIS IS WHY THE BRIEF'S TYPE ARGUMENT DOES NOT REACH THE ANSWER, AND THE
BRIEF WAS RIGHT TO ASK.** The target is internal, and that is true. The
antecedent is ambient, and the leastness clause inside the target's own
`SuccCardL` pins the antecedent's application to the one ordinal where the
ambient fact is not available. **The crossing is not a slip in `[LJ-1.523]`'s
statement. It is inherited from `Devlin55.BoundedSubsetAt` and it survives every
reassignment.**

## W3, AND WHAT IT MEASURED

The brief named the widest unmeasured term as "whether `[LJ-1.523]`'s bridge
consumes B5 anywhere at all", and ordered the miniature written first and
typechecked alone.

**I WROTE IT AND RAN IT ALONE.** `bridge-b5-unused`
(`agents/tasks/LJ-1-550/Probe550.agda:71-72`) binds B5 and never mentions it to
the right. The slice is kept byte-for-byte at
`agents/tasks/LJ-1-550/runs/w3-slice.agda.txt`. **GO. Exit 0, 3.49 s real,
peak memory footprint 707,183,696 bytes** (`agents/tasks/LJ-1-550/runs/w3-1.out`).
The brief estimated about 15 lines and under 60 seconds. The slice is 60 lines
because it carries the imports and the two copied types, and it ran in 3.49 s.

**THE MEASUREMENT IS TRUE AND IT IS NOT DECISIVE, AND I SAY SO PLAINLY.** The
brief predicted "if the elaborator accepts the term with B5 unused, the answer
is already in hand and the rest is bookkeeping." The elaborator accepts it. **The
answer was not in hand.** A type that does not mention B5 says nothing about
what an inhabitant of that type must supply, and the whole question lives in the
inhabitant. Sections 4, 5 and 6 of the probe are what actually settled it, and
they cost 350 more lines.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

Required by the coder's clauses.

**THE PROBE IS 412 LINES AND IT TYPECHECKS IN 8.47 SECONDS**, peak memory
footprint 1,456,113,248 bytes (`agents/tasks/LJ-1-550/runs/final-2.out`). **A
SECOND RUN ON THE BYTE-IDENTICAL FILE COST 3.04 s AND 707,937,336 BYTES**
(`agents/tasks/LJ-1-550/runs/final-3.out`), so 5.4 s of the first figure is
interface-cache work and not elaboration. Quote the 8.47 s figure, not the
3.04 s one: the cold number is the one a fresh consumer pays. The
brief estimated about 110 lines of which the obligation was about 20. The
estimate was for the obligation, which is not delivered; the 412 lines are the
refutation and its measurements, and about 150 of them are copied verbatim from
`[LJ-1.523]` because the brief forbade changing any hypothesis.

**NOTHING RESISTED IN THE ELABORATOR.** `member-in-stage`,
`bridge-with-residues`, `ambient→internal` and `site-forced` all typechecked at
the first attempt. There was no universe-level fight, no unsolved meta and no
transport. The one error I hit was my own malformed sketch at the tail of
section 6, `[UnequalSorts]`, repaired in one edit
(`agents/tasks/LJ-1-550/runs/final-1.out` red, `final-2.out` green).

**WHAT I HAD TO WEAKEN: NOTHING IN THE OBLIGATION.** `BridgeWithoutB5`
(`agents/tasks/LJ-1-550/Probe550.agda:188-198`) is stated at full strength, with
the nine other inputs as arguments and B5 absent, and it is left uninhabited.
`bridge-with-residues` is a SEPARATE term with six extra hypotheses and it is
labelled as not an obligation at `agents/tasks/LJ-1-550/Probe550.agda:288-290`.
I did not restate the bridge more weakly to make it go through.

**WHAT I COULD NOT CLOSE.** The six residues above. R1 is the ambient one and
the brief forbade both proving and refuting it. R2 and R3 are B12 and B11, both
recorded unbuilt for a long time. R4, R5 and R6 are new rows and none of them is
ambient: all three are coding facts about `InjL`, and they sit exactly where
`[LJ-1.533]` and `[LJ-1.535]` closed the generic-code routes.

**A FORTIORI NOTE FOR THE NEXT BRIEF.** `BridgeWithoutB5` gives the inhabitant
MORE than `GCHBridge` does, because B4 and B6 to B10 arrive as arguments rather
than being owed. So the failure of `BridgeWithoutB5` is also a failure of
`GCHBridge` (`agents/tasks/LJ-1-523/Probe523.agda:174-175`). **The bridge as
stated is not inhabitable today, and B5 is not the shortest thing standing in
the way.**

## WHAT I RECOMMEND, AND IT IS THE MATHEMATICIAN'S CALL

Not a ruling. Two routes, and they are different tasks.

**ROUTE A, EDIT THE ANTECEDENT IN `src/`.** Restate
`src/L/BoundedSubset.lagda.md:1386`'s third slot as `CardSpentAt κ α` instead
of `IsCardinal κ`. `[LJ-1.523]` measured that the module spends nothing more
(`:1597`, `:1601`), and I re-measured the same three occurrences. **Then B5
fills the slot exactly**, and R1 leaves the bill. This does not remove the
ambient hypothesis: it shrinks it from every member of δ to one. `SpentSlot`
(`agents/tasks/LJ-1-550/Probe550.agda:403-404`) is the target type.

**ROUTE B, THE BRIEF'S OWN NO-GO READING.** Restate the bridge against
`GCHStatement` directly and do not route through `Devlin55.BoundedSubsetAt` at
all. `site-forced` says that as long as the route goes through that module, the
ambient hypothesis lands at δ and cannot be moved.

**NEITHER ROUTE IS FUNDED BY THIS TASK AND NEITHER IS PRICED HERE.**

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ, AND IT CORROBORATES THE FINDING
  ROW FOR ROW.** `archive/dev/LJ-dispatch-index.md:167` reads
  "| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |".
  That is my R1, recorded before this campaign. `:170` reads
  "| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |",
  which says that once `cardκ` was supplied the NEXT blocker was `sq`: that is
  my R2, and the order matches `member-in-stage` argument for argument. `:198`
  reads
  "| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |",
  which is my R3. `:444` reads
  "| LJ-1.323 | Fable RULING: the statement of both trophies | AC UNCHANGED. GCH BECOMES THE INTERNAL EQUALITY | sq leaves, every ambient injection leaves, the conclusion is 2^kappa = kappa-plus in L |".
  **THAT ROW IS THE WHOLE STORY IN ONE LINE:** the ruling took every ambient
  injection out of the STATEMENT. It did not take them out of the ANTECEDENT,
  and this task measures the gap that left.
- **`dev/ARCHIVE.md`. Not used.** Declined: it is the registry of retired
  MODULES (`dev/ARCHIVE.md:3`, "The registry of Bedrock's retired modules"), and
  nothing was retired or moved by this task.
- **`archive/dev/JOURNAL.md`. Not used.** Declined: `archive/dev/JOURNAL.md:1`
  reads "# ARCHIVED 2026-08-20" and the file records that the per-episode
  journal is retired in favour of `agents/tasks/<CODE>/`, which is where I read
  the predecessors instead.
- **`archive/dev/JOURNAL-archived.md`. Not used.** Declined: it is the journal
  of the RETIRED route, archived 2026-08-09 when the two-tower route was ruled.
  This task is on the live route.
- **`archive/dev/DD-archived.md`. Not used.** Declined: it is the archived `DD`
  ruling series, and no `DD` row bears on which hypothesis a module telescope
  asks for.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`. READ, AND IT NAMES THE CROSSING AT ITS
  SOURCE.** `dev/literature/devlin-II5.md:147` reads
  "> 5.5 Lemma. Assume V = L. Let κ be a cardinal. If x is a bounded subset of".
  **Devlin's own 5.5 assumes V = L, so for him "cardinal" is unambiguous and no
  crossing exists.** Bedrock does not assume V = L: `[LJ-1.323]` made the
  statement internal and left the chapter ambient. That is exactly where R1
  comes from, and it is not a defect in anyone's Agda.
- **`dev/literature/truncation-and-selection.md`. READ, AND IT BEARS ON R2.**
  `dev/literature/truncation-and-selection.md:216` reads
  "**These refute the UNIVERSALLY QUANTIFIED form. They do not reach a family".
  R2 is precisely a family-indexed selection: `sq-trunc-closed`
  (`src/L/SquareLawClosed.lagda.md:325-327`) gives `∥ sq δ ∥₁` pointwise and the
  antecedent wants the bare family. **This file says a principle of that shape
  is not refuted by the standard taboo**, so R2 is open and not closed, which
  is why I recorded it as a residue and not as a wall.
- **`dev/literature/digest.md`. Not used.** Declined: `dev/literature/digest.md:1`
  is the orthodox form of the RUD route, and this task touches no rud
  machinery.
- **`dev/literature/geology.md`. Not used.** Declined: set-theoretic geology
  sources, no bearing on a telescope slot.
- **`dev/literature/terms-2026-08.md`. Not used.** Declined: a terminology
  dossier for a naming ruling, and this task names nothing new for
  `dev/glossary.toml`.
