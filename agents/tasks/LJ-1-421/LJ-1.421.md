# LJ-1.421: is the campaign's residue a CODING problem, or is it one UNTRUNCATION

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-421/Probe421.agda`, at a GENERIC ordinal.

    descent-from-data :
        (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

**ONE MODULE HYPOTHESIS AND EXACTLY ONE**, and it is the UNTRUNCATED form of a
term the tree already delivers truncated:

    kappa-arrow-data :
        (a : S) (oa : IsOrd (fst a))
      → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

**THERE MUST BE NO `amb-to-coded`, NO `coded-descent` AND NO `IsCardinalL` IN
THAT TELESCOPE. THAT IS THE WHOLE TASK.** You may take `κL`, `κoL` and
`kappa-decides` as further hypotheses at `[LJ-1.406]`'s and `[LJ-1.413]`'s
delivered types, because they are plumbing and not the question. **Every
hypothesis you add beyond `kappa-arrow-data` must be listed in your report with
the delivered `file:line` it was copied from.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-421/Probe421.agda::descent-from-data"]

## SCOPE (write)
- agents/tasks/LJ-1-421/Probe421.agda
- agents/tasks/LJ-1-421/lj-1.421-report.md
- agents/tasks/LJ-1-421/review-of-descent-from-data.md

## PREMISES
- `[LJ-1.413]`'s induction step splits at the ambient least cardinal and case four does the work. Basis: agents/tasks/LJ-1-413/Probe413.agda:278
- Case four turns the TRUNCATED ambient arrow into a refutation of the internal cardinal predicate. Basis: agents/tasks/LJ-1-413/Probe413.agda:282
- It then buys back an UNTRUNCATED ambient arrow from that refutation. Basis: agents/tasks/LJ-1-413/Probe413.agda:226
- The arrow it starts from is delivered truncated by the tree itself. Basis: src/L/Cardinal.lagda.md:133
- That truncation comes from a `leastOf` selection over an ordinal well-order. Basis: src/L/Cardinal.lagda.md:117
- The tree's internal cardinal predicate is stated with a CODE and not with an ambient arrow. Basis: src/L/Cardinal.lagda.md:230
- `[LJ-1.414]` left the ambient-to-coded step as a hole and called it the remaining bill. Basis: agents/tasks/LJ-1-414/Probe414.agda:139
- `[LJ-1.406]`'s `Init` at the least cardinal already spends the AMBIENT minimality and never the coded predicate. Basis: agents/tasks/LJ-1-406/Probe406.agda:92
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**CASE THREE IS PAID AND NEEDS NO CODE.** When the band ordinal IS its own
ambient least cardinal, `[LJ-1.413]` closes it with `init-at-kappa` and
`via-col-square` (`agents/tasks/LJ-1-413/Probe413.agda:270-274`). Read
`init-at-kappa`'s body: conjunct four is discharged by `κ-min-atL`, the AMBIENT
minimality (`agents/tasks/LJ-1-406/Probe406.agda:92`). **No `Formula`, no
`InjCode`, no Def tower.**

**CASE FOUR IS WHERE THE CODE ENTERS, AND IT ENTERS AS A ROUND TRIP.**
`agents/tasks/LJ-1-413/Probe413.agda:279-284` takes the truncated ambient arrow
`κ-injL`, converts it to `IsCardinalL a → Empty.⊥` through `amb-to-coded`, and
then converts that back to an ambient arrow as DATA through `coded-descent`.

## WHAT IS MISSING

**NOBODY HAS ASKED WHAT THE ROUND TRIP BUYS.** It starts at an ambient arrow
and it ends at an ambient arrow. The only thing it changes is the TRUNCATION.
If case four closes from `kappa-arrow-data` alone, then the campaign's residue
is not「code an arbitrary ambient injection」at all: it is「untruncate ONE named
arrow」, and `[LJ-1.414]`'s measurement is not the binding constraint.

**AND `[LJ-1.414]`'s OWN REPORT DOES NOT CLAIM IT IS.** The report says the
statement「is not proved and not refuted」. The independent audit records that
the harder words in that report outrun that sentence
(`dev/pod/audit-2026-08-20.md`, finding F6). **Do not treat `amb-to-coded` as
impossible and do not treat it as necessary. This task measures whether it is
NEEDED.**

## THE REASONING

**THE SHAPE IS `[LJ-1.413]`'s CASE FOUR WITH TWO LINKS DELETED.** Take
`κ := κL a ox`. `kappa-decides` (`agents/tasks/LJ-1-413/Probe413.agda:173`)
already splits `fst κ ≡ x` from `⟨ fst κ ∈ x ⟩`. In the second branch you have
`κ ∈ x`, so the induction hypothesis applies AT `κ` and gives `sq (fst κ)` as
DATA. `kappa-arrow-data` gives the arrow `⟪ fst a ⟫ ↪ ⟪ fst κ ⟫` as DATA.
`descent-data` is then applied with `d := κ`.

**SO THE QUESTION IS SHARP: DOES `d := κ` WORK?** `coded-descent` returns some
`d ∈ x`. Case four never needed a different one, unless `descent-data` demands
something of `d` that `κ` does not carry. **Find out and say which.** If `κ`
serves, `coded-descent` and `amb-to-coded` are both surplus in this branch.

**W2 (DD4).** Generic in `x`. The hypothesis is generic in `a`. Name no
cardinal and no numeral except `ω`.

**D-10, BEFORE ANY AGDA.** `kappa-arrow-data` is the untruncation of
`κ-injL` (`agents/tasks/LJ-1-406/Probe406.agda:88-89`). Ask first whether it is
TRUE at this generality, not whether it is provable here. An arrow that the
tree delivers truncated is a statement whose truth is not in doubt; what is in
doubt is the data. **If instead you find the untruncated form false, that is a
full return: record the corrected target beside the original and stop.**

**W3, THE WIDEST UNMEASURED TERM.**

    d-is-kappa

**THE PROBE.** Before the obligation, state `descent-data`'s telescope at
`[LJ-1.413]`'s delivered form and apply it with `d := κ` and nothing else
supplied. Typecheck that fragment ALONE and report exactly which argument, if
any, fails to elaborate and at which type. **That number decides the task, and
it is one small run.**

ESTIMATE for the Agda: about 30 code lines. BASIS: it is `[LJ-1.413]`'s case
four with the `notCard` and `pack` blocks removed, and those two blocks are 8
lines of the 26 at `agents/tasks/LJ-1-413/Probe413.agda:279-304`. **Comparables
of SHAPE and never of size, and nothing may be funded against them.**

**CLOSE WITH THE COMPARISON.** Write a report section `## WHAT THE ROUND TRIP
BUYS` that states, each with `file:line`: what enters case four, what leaves it,
and the ONE property that differs between the two. Then say in one sentence
whether the campaign's residue is a coding problem or an untruncation problem.

## WHAT GO AND NO-GO EACH EARN

**A GO RE-STATES THE WHOLE CAMPAIGN'S BILL.** It says the residue is one
untruncated arrow at a named ordinal, and that is a different object from
`[LJ-1.414]`'s general implication. `[LJ-1.422]` then prices that object.

**A NO-GO IS WORTH AS MUCH.** If `d := κ` cannot serve, then `coded-descent`
supplies something the least cardinal does not, and the coded detour is load
bearing. Name the property, and `[LJ-1.414]`'s bill stands as the campaign's
one residue with the evidence to back it.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-421/Probe421.agda"]
  changed_files_none = ["agents/tasks/LJ-1-421/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-421/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 160.050)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 136.618)
- CANDIDATE dev/ARCHIVE.md  (score 131.664)
- CANDIDATE archive/dev/JOURNAL.md  (score 114.963)
- CANDIDATE archive/dev/DD-archived.md  (score 100.472)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.458)
- CANDIDATE dev/literature/devlin-II5.md  (score 50.524)
- CANDIDATE dev/literature/digest.md  (score 36.245)
- CANDIDATE dev/literature/geology.md  (score 35.142)
- CANDIDATE dev/literature/terms-2026-08.md  (score 26.737)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
