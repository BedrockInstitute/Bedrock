# LJ-1.401: `InjCode` is a proposition, so the least code is DATA

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-401/Probe401.agda`.

    isPropInjCode : (F a b : S) → isProp (InjCode F a b)

    sel-code :
        (κ : S) (oκ : IsOrd (fst κ))
      → (nonempty : <the `Selected` module's own hypothesis, at its own type>)
      → Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
          InjCode (up F) κ (InternalLeastCard.Selected.δᴸ κ oκ nonempty)

`sel-code` is ONE application of `leastOf`, at the code, taking
`InternalLeastCard.Selected.δ-inj` as its truncated input. Read
`src/L/Cardinal.lagda.md:242-258` and take the module's own parameter names and
types from that site. **Do not restate `InternalLeastCard` and do not copy any
part of it into your file.** Open it.

**YOU MAY DROP `sel-code`'s `IsLeast` HALF.** `leastOf` returns
`Σ[ a ] IsLeast P a` (`src/L/WellOrder/Base.lagda.md:158-160`). This task needs
only the code and its `InjCode`. Keep the leastness if it is free and say so;
never spend a line on it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-401/Probe401.agda::isPropInjCode",
               "agents/tasks/LJ-1-401/Probe401.agda::sel-code"]

## SCOPE (write)
- agents/tasks/LJ-1-401/Probe401.agda
- agents/tasks/LJ-1-401/lj-1.401-report.md

## PREMISES
- `InjCode F a b` is four conjuncts: three satisfaction clauses and one Π into a membership. Basis: src/L/Cardinal.lagda.md:223-228
- `leastOf` takes a TRUNCATED non-emptiness and an hProp-valued predicate, and RETURNS the least element as DATA. Basis: src/L/WellOrder/Base.lagda.md:158-160
- `IsLeast` and its `isProp` are delivered, and `isPropIsLeast` is the shape an hProp packaging takes here. Basis: src/L/WellOrder/Base.lagda.md:130-134
- `InternalLeastCard.Selected` already runs `leastOf` ONCE, over `Mem (Lset β)`, under `orderAt`. Basis: src/L/Cardinal.lagda.md:247
- Its predicate `Good` is made an hProp BY TRUNCATING the code existential, and that truncation is what this task removes one level down. Basis: src/L/Cardinal.lagda.md:240
- `δ-inj` is already EXACTLY `leastOf`'s input shape at the code: a truncated Σ over `Mem (Lset β)`. Basis: src/L/Cardinal.lagda.md:257
- **THE CHAPTER STATES THE OBSTRUCTION THIS TASK GOES AROUND, IN ITS OWN COMMENT.** On the AMBIENT side the predicate had to be truncated to become an hProp, and so the ambient witness came out truncated. Basis: src/L/Cardinal.lagda.md:132
- `up` lifts a `Mem (Lset β)` to an L-element. Basis: src/L/Cardinal.lagda.md:240
- `orderAt β oβ` is the well-order `leastOf` consumes at this site. Basis: src/L/Cardinal.lagda.md:247

## WHAT IS DELIVERED ALREADY

**THE SELECTION AT THE CARDINAL, IN `src/`.** `InternalLeastCard.Selected`
selects `δᴸ` as data (`src/L/Cardinal.lagda.md:253`) and hands over the code
existential `δ-inj`, still truncated (`:257`).

**`leastOf`, GENERIC.** It converts a truncated non-emptiness over a
well-ordered carrier into data, spending one `lem`
(`src/L/WellOrder/Base.lagda.md:158-160`). It is the device the whole campaign
already runs twice: at `src/L/Cardinal.lagda.md:117` for the ambient least
cardinal and at `:247` for the internal one.

**THE FOUR CONJUNCTS, AS DELIVERED TERMS AT A REAL SITE.** `L.Absorption`
proves `svAt`, `injAt` and `domAt` for the successor shift
(`src/L/Absorption.lagda.md:452-481`) and its range clause at `:493-497`. That
is the shape `isPropInjCode` must show propositional, at a site where all four
already exist.

## WHAT IS MISSING

The `isProp` half. Nobody has asked whether `InjCode` is a proposition, and
every route the campaign has tried for two weeks needed it and did not know.

## THE REASONING

**THE ASYMMETRY IS THE WHOLE TASK, AND IT IS ONE LINE OF THE CHAPTER.**

`leastOf` demands `P : A → hProp`. On the AMBIENT side the payload is
`⟪ fst α ⟫ ↪ ⟪ β ⟫`, an injection, which is NOT a proposition, so the chapter
truncated it to get in. `src/L/Cardinal.lagda.md:132` says so in its own words:
「the witness, an injection, still truncated, still not an hProp」. The truncated
arrow at `:133-134` is the price, and it is the bill every recent task has been
unable to pay.

**ON THE CODED SIDE THERE IS NOTHING TO TRUNCATE.** `InjCode F a b`
(`:223-228`) is:

1. `⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩`
2. `⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩`
3. `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩`
4. `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩`

Clauses 1 to 3 are `⟨ _ ⟩` of an hProp, so each carries its own `snd`. Clause 4
is a Π into `⟨ _ ⟩` of an hProp, so `isPropΠ` twice and `isPropΠ` again over the
membership. **A product of propositions is a proposition**, and `isProp×` is the
whole derivation. This is the same three-move proof as `isPropIsLeast`
(`src/L/WellOrder/Base.lagda.md:133-134`), which is `isProp×` over an hProp and
a double `isPropΠ`. **Copy that shape.**

Then `sel-code` is one line: apply `leastOf (orderAt β oβ) lem` with the
predicate `λ F → InjCode (up F) κ δᴸ , isPropInjCode (up F) κ δᴸ` and the input
`δ-inj`. **The types already match. `δ-inj` at `:257` is
`∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ δᴸ ∥₁`, and `leastOf`'s input at
`src/L/WellOrder/Base.lagda.md:160` is `∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁`.** Nothing is
adapted and nothing is transported.

**WHAT THIS DOES NOT GIVE YOU, AND DO NOT CLAIM IT.** It gives a CODE as data.
It does not give an ambient injection: that is the readback, and it is
`[LJ-1.402]`'s obligation, not yours. It says nothing about any site other than
`InternalLeastCard`'s, and it does not touch `LeastCardInjL`, whose predicate is
genuinely not a proposition.

**ONE REQUIRED REPORT SECTION, AND IT IS READING, NOT AGDA.** Under a heading
`## THE OTHER SITE`, say whether the AMBIENT selection at
`src/L/Cardinal.lagda.md:117` is reachable by the same device, and give the
reason at `file:line`. **The expected answer is NO**, because its payload is an
injection and `:132` says so in the chapter's own comment; if you find otherwise,
that is a larger result than this task's own obligation and it must be stated
with its evidence. **Do not write Agda for it.** This section exists because a
cure measured at one site says nothing about any other (C-42), and the two sites
sit forty lines apart in one chapter.

**W2 (DD4).** Write `isPropInjCode` at a generic `F`, `a` and `b`. It must name
no cardinal, no stage and no site. Answer W2 in the report and say which of the
two terms is generic and which is sited.

**W3, THE WIDEST UNMEASURED TERM.** It is clause 4's `isProp`: clauses 1 to 3
are `⟨ _ ⟩` of an hProp by construction, and clause 4 is the only one whose
propositionality has to be built rather than projected. **The probe is
`clause4-isProp`: state that one clause alone, prove it propositional, run it,
and report the number of code lines before you write anything else.** ESTIMATE
for both obligations together: about 20 code lines. BASIS: `isPropIsLeast`, a
delivered comparable of SHAPE at 2 code lines
(`src/L/WellOrder/Base.lagda.md:133-134`), and `nonempty` plus `least` at
`src/L/Cardinal.lagda.md:113-117`, 5 code lines, the delivered comparable for a
`leastOf` application. **Neither is a comparable of size and nothing may be
funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE BILL THE CAMPAIGN HAS BEEN STUCK ON SINCE `[LJ-1.394]`.** It
turns a truncated code existential into a code as data, and `[LJ-1.402]` then
reads it back to an untruncated ambient injection. That arrow is what the band
recursion owes at every negative site.

**A NO-GO EARNS THE CLAUSE THAT IS NOT A PROPOSITION, AT `file:line`.** If one
of the four conjuncts has a non-propositional inhabitant, say which and why. That
is a fact about `InjCode`'s design and it re-plans four queued tasks. **A stated
NO-GO is a full return**, and it is worth as much as the GO.

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-401/Probe401.agda"]
  changed_files_none = ["agents/tasks/LJ-1-401/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-401/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

## LAWS (program-generated, do not edit)

MANDATORY for kind `probe` (measures one thing and keeps the file as the report's other half. Gating, heap discipline, the transplant law, which is what a probe most often gets wrong, and the extent law, because a probe that refutes has measured ONE site.):

- **D-1. The probe doctrine**
  **Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest decisive probe with its abort criterion fixed in advance; a red verdict costs the attempt and nothing else.
  Full entry: dev/LESSONS.md:1064
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-i. The conversion-explosion playbook (imported from the source project)**
  **Rule:** When cubical Agda hangs or exhausts memory on this codebase family, the cause is one of three heavy-thing classes forced into normalization, and the cure is selected by the decision tree below, not by trial. Imported whole from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md` §5, twenty measured cases); read that section before any surgery on a hang.
  Full entry: dev/LESSONS.md:229
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md  (score 52.104)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md  (score 48.771)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 41.220)
- CANDIDATE archive/dev/TASKS-archived.md  (score 33.907)
- CANDIDATE dev/ARCHIVE.md  (score 28.663)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.442)
- CANDIDATE dev/literature/devlin-II5.md  (score 24.108)
- CANDIDATE dev/literature/terms-2026-08.md  (score 21.775)
- CANDIDATE dev/literature/digest.md  (score 18.330)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
