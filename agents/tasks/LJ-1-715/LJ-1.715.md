# LJ-1.715: the merge lemma, in `src/` where the family has a name

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy

## THE OBLIGATION

Add ONE lemma to `src/L/Ordinal.lagda.md`, and mirror its statement in
`agents/tasks/LJ-1-715/Probe715.agda`:

    bound2-in-limit : <from `IsOrd α`, a union-closed limit notion, and `⟨ σᵢ ∈ₛ α ⟩` for both, conclude `⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩`>

**ADD. DO NOT RESTRUCTURE `bound2`.** Its shape and its seven call sites stay
exactly as they are.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** Conjunct 1
runs EVERY `.agda` under this task home.

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-715` AND PASTE ITS OUTPUT.** `[LJ-1.710]` burned four acceptance arms on ONE unnamed survey path. Do not repeat it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-715/Probe715.agda::bound2-in-limit"]

## SCOPE (write)
- src/L/Ordinal.lagda.md
- agents/tasks/LJ-1-715/Probe715.agda
- agents/tasks/LJ-1-715/lj-1.715-report.md
- agents/tasks/LJ-1-715/review-of-bound2-in-limit.md
- agents/tasks/LJ-1-715/runs/
- Never `src/L/Reflect.lagda.md`, never `src/L/ReflectFo.lagda.md`, never `src/Everything.lagda.md`.

## PREMISES

1. **[LJ-1.710] PROVED THE OBSTRUCTION IS A NAMING ONE AND NOT A MATHEMATICAL ONE.** The statement is not shown false, and the classical merge of two members below a limit is interior to it. Basis: agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:52
2. **IT NAMED THIS EXACT CURE, AND THIS BRIEF TAKES ITS SECOND OPTION.** Prove the lemma directly in `src/` rather than re-export the family. Basis: agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:57
3. **THE PROOF SKELETON IS ALREADY WRITTEN AND GREEN.** Section 3 of its probe closes the full merge statement for a family written out loud. Transcribe that, do not re-invent it. Basis: agents/tasks/LJ-1-710/Probe710.agda:1
4. **WHY A PROBE CANNOT DO THIS.** `bound2`'s where-bound family prints as `L.Ordinal.f σ₁ σ₂ o₁ o₂` and the symbol is out of scope, so `eqImage` against it cannot even be STATED. Basis: agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:37
5. **A CONVERSION FACT THAT BINDS YOUR STYLE.** A clause function is NOT convertible to its own written-out case lambda at a variable position; split on the index first. Basis: agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:41
6. **`bound2` IS A THREE-FIELD SIGMA AT A KNOWN SITE.** Basis: src/L/Ordinal.lagda.md:185
7. **THE HOST HAS FORTY DEPENDENTS, MEASURED TODAY.** `grep -rl "import L.Ordinal" src/ --include='*.lagda.md' | wc -l` gives 40, which is why this brief is `heavy` and why the lemma is ADDITIVE. Basis: src/L/Ordinal.lagda.md:185
8. **THE TARGET HAS NO SUPPLY IN THE TREE.** `bound2` has consumers in two masters and none of them proves a membership lemma. Basis: src/L/Reflect.lagda.md:453

## MEASURED TODAY

- dependents: L.Ordinal => 40
- supply: bound2-in-limit => 0
- supply: bound2 => 23

## WHAT IS DELIVERED ALREADY

The merge itself, its ordinality, and `[LJ-1.710]`'s green Section 3 proof body.
This obligation has supply 2 and its content is the transcription plus the one
name that only `src/` can give.

## THE REASONING

This is the first `src/` landing the campaign has had a MEASURED reason to make.
`[LJ-1.705]` and `[LJ-1.706]` both stop on the same uncontrolled stage, and
`[LJ-1.710]` proved the lemma that controls it is unprovable from inside a probe
for a naming reason it measured three ways. The cure is one additive lemma.

## TWO THINGS ABOUT LANDING IN A MASTER, BOTH FROM `src/README.md`

**`src/Everything.lagda.md` NEEDS NO CHANGE.** Its rule is「when you add a MODULE,
add its import here」. You add a lemma to an existing master, so the reading catalog
is untouched and your scope forbids it.

**WRITE NO MATHEMATICAL PROSE.** The Boundary forbids it until both trophies are
proved in the tree. Put what you have to say in COMMENTS INSIDE the ` ```agda `
fence. Do not open a trilingual prose block for this lemma.

## THE RATIO BAR WILL PROBABLY FIRE, AND THAT IS NOT A FAILURE

Fact 7 counts the in-fence lines of your write scope, and the bar is 0.0123
seconds per line. A small additive lemma against a whole-tree recheck sits far
above that rate, so `sys-dd24-ratio-bar` will escalate this return to a critic.
**Do not pad the file to move the meter.** Write the lemma, comment it as the
chapter's style requires, and let the critic read it.

## W3, THE WIDEST UNMEASURED TERM

Whether the union-closed limit notion the lemma needs already exists in `src/` or
must be stated here. Estimate 40 to 120 lines, basis:
agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:57

## WHAT GO AND NO-GO EACH EARN

**GO** unblocks `[LJ-1.705]` and `[LJ-1.711]` at once, and it is the first line of
GCH-downstream code to land in `src/` in this campaign. **NO-GO** earns the reason
the lemma resists even with the family named, which would move the obstruction from
naming to mathematics and would be a far more serious finding than today's.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-715/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-715/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-715/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-715/Probe715.agda"]
  changed_files_none = ["agents/tasks/LJ-1-715/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-715/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# Closes maintainer-backlog item 30, MEASURED on LJ-1.630. A real failed landing
# carries a named Agda error and NEITHER companion file, so both rows above miss
# it. This is the catch-all and it sits BELOW heap-wall-park.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
```
