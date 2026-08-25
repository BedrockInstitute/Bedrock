# LJ-1.397: the ordinal-least CODED cardinal, and the arrow as DATA

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-397/Probe397.agda`, at a GENERIC ordinal.

    coded-least : (a : S) (oa : IsOrd (fst a))
                → ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β a)) ]
                      InjCode (SiteBound.up a δ) a (SiteBound.up a δ) ∥₁
                → Σ[ b ∈ S ] ( ⟨ fst b ∈ sucV (fst a) ⟩
                             × ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                                   InjCode (SiteBound.up a F) a b ∥₁
                             × ((c : S) → ⟨ fst c ∈ fst b ⟩
                                → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                                      InjCode (SiteBound.up a F) a c ∥₁ → Empty.⊥) )

    coded-arrow : (a : S) (oa : IsOrd (fst a)) → (IsCardinalL a → Empty.⊥)
                → Σ[ b ∈ S ] (⟨ fst b ∈ fst a ⟩ × (⟪ fst a ⟫ ↪ ⟪ fst b ⟫))

**`coded-least` IS A MIRROR OF A DELIVERED MODULE. DO NOT INVENT IT.**
`LeastCardInjL` (`src/L/Cardinal.lagda.md:60-155`) does exactly this selection
with the AMBIENT predicate. Read that module line by line and mirror it with the
CODED predicate. Its own comments carry two facts you need: the well-order must
be SEALED (`:85-89`), and `w-lt` is the one read the seal needs (`:99-101`).

**TAKE THE DOOR AND THE IDENTITY CODE AS MODULE HYPOTHESES.** Both live in a
probe and you must not import it. The door is `code-untruncates`
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`). The identity code is
`code-exists` (`agents/tasks/LJ-1-386/Probe386.agda:227-230`), and you take it at
a GENERIC `a` and not at that probe's site.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-397/Probe397.agda::coded-least",
               "agents/tasks/LJ-1-397/Probe397.agda::coded-arrow"]

## SCOPE (write)
- agents/tasks/LJ-1-397/Probe397.agda
- agents/tasks/LJ-1-397/lj-1.397-report.md

## PREMISES
- `LeastCardInjL` selects the least ordinal that receives an AMBIENT injection, over the ORDINAL well-order, and it is delivered. Basis: src/L/Cardinal.lagda.md:60
- The well-order it selects over is `ordSWO (sucV (fst α))`, so its leastness IS ordinal leastness, and `w-lt` states that equality. Basis: src/L/Cardinal.lagda.md:91-101
- `InternalLeastCard` selects over `orderAt`, which orders L-stage member CODES and not ordinals, so its least element carries NO ordinal minimality. Basis: src/L/Cardinal.lagda.md:246-247
- `InternalLeastCard.Good` is the CODED predicate this task needs, and it names no membership. Basis: src/L/Cardinal.lagda.md:239-240
- `δ-inj` shows the shape of the truncated coded witness the door consumes. Basis: src/L/Cardinal.lagda.md:256-258
- The door turns a merely existing code into an ambient injection AS DATA, at arbitrary source and target. Basis: agents/tasks/LJ-1-386/Probe386.agda:264-268
- `[LJ-1.386]` returned GO on the door. Basis: agents/tasks/LJ-1-386/lj-1.386-report.md:20
- The identity code exists at a site whose placement obligation is discharged inside that probe. Basis: agents/tasks/LJ-1-386/Probe386.agda:227-230
- `IsCardinalL` refutes a merely existing CODED injection at every member. Basis: src/L/Cardinal.lagda.md:230-233
- Its code quantifier is over all of `S`, and `Good`'s is over `Mem (Lset β)`. Basis: src/L/Cardinal.lagda.md:232-233
- A member of an L-element lies in `Lset (stageBound ...)`. Basis: src/L/Choice/Stage.lagda.md:371-373
- `leastOf` needs `lem` and returns the least element with its minimality, uniquely. Basis: src/L/WellOrder/Base.lagda.md:158-160
- `[LJ-1.395]` states the campaign's next bill as the untruncated arrow below a negative site. Basis: agents/tasks/LJ-1-395/lj-1.395-report.md:205-210
- `[LJ-1.394]` measured that `lem` and `leastOf` do not reach that arrow on the AMBIENT side. Basis: agents/tasks/LJ-1-394/lj-1.394-report.md:36-44
- `_↪_`. Basis: src/L/Cardinal.lagda.md:47-48

## WHAT IS DELIVERED ALREADY

The selection over the ordinal order, with the AMBIENT predicate
(`src/L/Cardinal.lagda.md:60-155`). The selection over the code order, with the
CODED predicate (`src/L/Cardinal.lagda.md:235-262`). The door
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`).

**THE PAIR THIS TASK NEEDS IS NEITHER OF THEM: the ORDINAL order with the CODED
predicate.** Nothing in the tree holds that pair today.

## WHAT IS MISSING

An arrow, as DATA, from an ordinal down to a strictly smaller ordinal, at a site
where the ordinal is not an L-cardinal.

## THE REASONING

**THE TWO DELIVERED SELECTIONS EACH HOLD ONE HALF OF WHAT THE RECURSION NEEDS,
AND NEITHER HOLDS BOTH.**

`LeastCardInjL` is least over the ORDINAL order, so it delivers ordinal
minimality (`κ-min-at`, `src/L/Cardinal.lagda.md:140-142`). Its witness stays
truncated for ever, because an ambient injection type is not a proposition and
no device untruncates it (`[LJ-1.394]`,
`agents/tasks/LJ-1-394/lj-1.394-report.md:36-44`).

`InternalLeastCard` is least over the CODE order, so the door untruncates its
witness. It delivers NO ordinal minimality, because `orderAt` orders codes.

**THE PAIR THAT WORKS IS THE ORDINAL ORDER WITH THE CODED PREDICATE.** Then
leastness is ordinal leastness AND the witness is a code, so the door reads it
out as data. That is `coded-least`, and it is a mirror and not a discovery.

**THEN `coded-arrow` IS THREE STEPS.**

1. `¬ IsCardinalL a` gives, by `lem` at the truncated existence, a member `c` of
   `fst a` with a merely existing coded injection. The step is the standard
   stability of a truncated existence under `lem`: decide
   `∥ Σ ... ∥₁`, and in the negative case rebuild `IsCardinalL a` and apply the
   hypothesis. **The conclusion is a proposition, so nothing is untruncated
   here.**
2. `coded-least` at `a`, fed by the identity code, gives `b` as DATA with its
   coded witness and its ordinal minimality. Minimality against `c` from step 1
   gives `⟨ fst b ∈ fst a ⟩`.
3. The door at source `a` and target `b` gives `⟪ fst a ⟫ ↪ ⟪ fst b ⟫` as DATA.

**W2 (DD4).** Both terms are generic in `a`. Name no ordinal and no site in any
statement. Answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM. IT IS THE CODE QUANTIFIER MISMATCH IN STEP 1.**
`IsCardinalL` quantifies the code over all of `S`
(`src/L/Cardinal.lagda.md:232-233`) and `coded-least`'s predicate quantifies it
over `Mem (Lset (SiteBound.β a))`. **The probe is `code-lands`: state the one
implication from the `S` form to the `Mem` form, alone, and run it FIRST.** If it
fails, do not abandon the task: restate `coded-arrow` with the hypothesis in the
`Mem` form, deliver it that way, and report the mismatch as a named residue with
its own price. **A task that delivers the arrow under a repaired hypothesis is a
GO, and the repaired hypothesis is the finding.** ESTIMATE for the two
obligations: about 70 code lines. BASIS: `LeastCardInjL` as a delivered
comparable of SHAPE and of SIZE, at 95 lines including its comments
(`src/L/Cardinal.lagda.md:60-155`), and `[LJ-1.394]`'s `amb-gives-ord-data` at 18
code lines for the same selection step (`agents/tasks/LJ-1-394/Probe394.agda:189-206`).
**Do not fund anything against 70.**

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE BILL `[LJ-1.395]` NAMED** (`agents/tasks/LJ-1-395/lj-1.395-report.md:205-210`),
on the coded side, and it retires「nothing in this tree produces the arrow」as a
sentence about the AMBIENT predicate only.

**A NO-GO earns the step that fails and the repaired hypothesis.** If the code
quantifier cannot be repaired, the campaign learns that its two cardinal notions
cannot be joined, which is a fact the architecture ruling `[LJ-2.5]` needs.

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
  changed_files_any = ["agents/tasks/LJ-1-397/Probe397.agda"]
  changed_files_none = ["agents/tasks/LJ-1-397/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-397/review-of-*.md"]

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

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 159.180)
- CANDIDATE dev/ARCHIVE.md  (score 139.170)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 93.885)
- CANDIDATE archive/dev/TASKS-archived.md  (score 88.099)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Condensation.lagda.md  (score 47.844)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 51.116)
- CANDIDATE dev/literature/devlin-II5.md  (score 47.914)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.098)
- CANDIDATE dev/literature/geology.md  (score 32.038)
- CANDIDATE dev/literature/digest.md  (score 27.632)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
