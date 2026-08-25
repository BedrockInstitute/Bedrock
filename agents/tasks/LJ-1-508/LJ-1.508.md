# LJ-1.508: valK asks about a different slot, and nobody has asked about that one

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-508/Probe508.agda`:

    valK-family : (TFacts's valK and valK-un, at KValue's frame, under ONE
                   named frame hypothesis about slot ONE)

**or refute the bare form and name the hypothesis it needs.** Land nothing in
`src/`.

**`valK` IS NOT `codesK` AND THE DIFFERENCE IS WHICH SLOT IT ASKS ABOUT.** Read
the type at `src/L/Condensation/TwelveAgree.lagda.md:173-176`:

    valK : (k : ℕ) (c ar a b yc : S)
         → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩          -- the CODE set, slot two
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩  -- the VALUE set, slot ONE
         → ⟨ fst yc ∈ fst (lookup (suc⁶ K) γ') ⟩

**It concludes a membership in `K` from a pair in SLOT ONE.** `codesK` concludes
from the decomposition alone. **So this is a closure fact about the value set,
and every dispatch so far has asked about slot two.**

**`[LJ-1.506]` NAMED THIS AS UNASKED AND SAID ITS OWN RESULT DOES NOT SETTLE
IT.** Its report: "The `valK` question is open. 23 declarations state `valK` or
`valK-un` over the same bare slot. **Nobody has asked where those come from
either.** My counterexample does not settle them"
(`agents/tasks/LJ-1-506/lj-1.506-report.md:236-239`). It counted **19 `valK` and
4 `valK-un`** (`:152-153`).

**THE METHOD IS DELIVERED TWICE OVER.** `[LJ-1.500]` paid `codesK` by taking ONE
frame hypothesis in a module telescope and deriving from it
(`agents/tasks/LJ-1-500/Probe500.agda:225-239`). `[LJ-1.506]` proved a bare slot
insufficient by building a counterexample
(`agents/tasks/LJ-1-506/Probe506.agda:143-150`). **Use whichever the mathematics
calls for. Both are respectable returns.**

**DO NOT WAIT ON `[LJ-1.505]`.** That task is settling what OCCUPIES each front
slot. This one asks what PROPERTY slot one must have. They are different
questions and neither answer constrains the other.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-508/Probe508.agda::valK-family"]

## SCOPE (write)
- agents/tasks/LJ-1-508/Probe508.agda
- agents/tasks/LJ-1-508/lj-1.508-report.md
- agents/tasks/LJ-1-508/review-of-valK-family.md
- agents/tasks/LJ-1-508/runs/

## PREMISES

1. `valK` concludes a `K` membership from a pair in slot one. Basis: src/L/Condensation/TwelveAgree.lagda.md:173
2. `valK-un` is the same at one fewer component. Basis: src/L/Condensation/TwelveAgree.lagda.md:177
3. `[LJ-1.506]` named the `valK` question open and unasked. Basis: agents/tasks/LJ-1-506/lj-1.506-report.md:236
4. It counted the declarations over the same bare slot. Basis: agents/tasks/LJ-1-506/lj-1.506-report.md:152
5. Its counterexample was at slot two and does not settle slot one. Basis: agents/tasks/LJ-1-506/Probe506.agda:143
6. `[LJ-1.500]` is GO and paid `codesK` from one frame hypothesis. Basis: agents/tasks/LJ-1-500/lj-1.500-report.md:145
7. Its hypothesis is taken in a module telescope. Basis: agents/tasks/LJ-1-500/Probe500.agda:225
8. `[LJ-1.495]` is GO and delivers `KFacts` at the shifted indices. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
9. `KFacts` carries `arityK` and `carrierK`, which `TFacts` does not state. Basis: src/L/Condensation.lagda.md:6114
10. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FORTY ONE OF FIFTY NINE FIELD POSITIONS ARE ACCOUNTED AT THIS FRAME**: twenty
six from `[LJ-1.495]`, four from `[LJ-1.501]`, nine from `[LJ-1.499]`, two from
`[LJ-1.500]`. **`valK` and `valK-un` are the next two, and they are the first to
ask about slot one.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `arityK` and `carrierK` are `KFacts` fields that
`TFacts` does not state, and `[LJ-1.495]`'s shift delivers both at these indices.
**Say at `file:line` whether either of them, alone, closes `valK`.** `arityK`
takes `v ∈ N` and `N ∈ K` to `v ∈ K`; the pair `pr c yc` lives in slot one, not
in `K`. **If slot one being a member of `K` is what is needed, say so: that is
the hypothesis, and it is about slot one exactly as this brief expects.**

**IF THE BARE FORM IS FALSE, REFUTE IT AND STOP THERE.** Build the
counterexample the way `[LJ-1.506]` did, machine-check it, and name the weakest
hypothesis that repairs it. **A refutation plus a named hypothesis is a full
deliverable** and is worth more than a term under a hypothesis you chose for
convenience.

**TAKE THE WEAKEST HYPOTHESIS THAT WORKS.** The mathematician ruled that way
twice this day, at the omega gate and at `arNumC`. A hypothesis that pins slot
one to a particular set would pre-empt `[LJ-1.505]` and will be refused.

**DO NOT POSTULATE, AND DO NOT USE A `TFacts` FIELD AS A HYPOTHESIS.** `valK` is
a `TFacts` field; assuming one to prove another proves nothing.

**DO NOT BUILD A `TFacts` VALUE.** Fifty nine positions are out of scope and
AD12 gives this brief one obligation.

**REQUIRED REPORT SECTION `## WHAT SLOT ONE MUST SATISFY`.** State the
hypothesis as a type, say whether it is derivable from `KFacts` at the shifted
indices, and say whether it also covers `valV`, `valW` and `wKfact`
(`src/L/Condensation/TwelveAgree.lagda.md:244`, `:250`, `:256`), which read the
same slot. **Do not build those three.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.500]` built the sibling pair in a comparable file.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `arityK` alone closes it, because that is the cheapest possible
answer and it has never been tried at this field.

    valK-from-arityK : (the conclusion, from arityK and the two memberships alone)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If
`arityK` closes `valK`, the field costs nothing beyond `[LJ-1.495]`'s shift and
the other twenty two declarations may fall the same way. If it does not, the
error names what is missing and the task proceeds to the hypothesis.

ESTIMATE for W3: about 20 lines and under 30 seconds. **Do not fund it against
`[LJ-1.500]`'s 3.16 s**: that measured a decoder and this measures a closure.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS TWO MORE POSITIONS AND MAY NAME THE HYPOTHESIS FOR TWENTY THREE
DECLARATIONS AT ONCE**, since all of them read the same slot.

**A REFUTATION NAMES WHAT SLOT ONE MUST SATISFY**, which is the second half of
the frame decision the mathematician owes, and `[LJ-1.506]` supplied only the
first half.

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-508/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-508/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-508/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-508/Probe508.agda"]
  changed_files_none = ["agents/tasks/LJ-1-508/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-508/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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

**THE RATIO BAR IS LIVE AND IT IS 0.0123 SECONDS PER IN-FENCE LINE.** A green return at or above that rate is ESCALATED to a critic by row `sys-dd24-ratio-bar`, which is DD24 restored by amendment A10. The divisor is fact 7, the in-fence line count of THIS task's write scope, counted the ledger's way: non-blank lines inside ` ```agda ` fences. **A raw `.agda` probe carries no fence and counts 0**, so the bar cannot fire on a probe and it binds the moment you write a `.lagda.md` master under `src/`. Design for it rather than discovering it: the number comes from `dev/pod/table.toml` at brief build, and its measured basis is in `dev/ledger.toml [ratio]`.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 180.362)
- CANDIDATE archive/dev/JOURNAL.md  (score 174.861)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 156.103)
- CANDIDATE dev/ARCHIVE.md  (score 131.948)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 129.570)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 53.876)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 50.449)
- CANDIDATE dev/literature/digest.md  (score 48.069)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 39.919)
- CANDIDATE dev/literature/geology.md  (score 36.657)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
