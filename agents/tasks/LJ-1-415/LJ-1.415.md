# LJ-1.415: the SRC collection, W4, and the census it starts from

**THIS FILE IS A SPECIFICATION AND NOT A DISPATCHABLE BRIEF TODAY.** The queue
entry carries no `brief` key, so rule (a1) skips it and the digest prints it.
The reason is MECHANICAL and not mathematical, and it is the same reason that
holds `[LJ-1.405]`: pre-flight P14 refuses a brief whose `obligations` list is
empty (`scripts/pod/preflight.py:489-490`), and this task writes no Agda.
**The specification is written in full, so the task dispatches on the hour the
owner rules on the obligation form.**

**CORRECTION, 2026-08-20T09Z, BY THE REFILL THAT RE-MEASURED THE CENSUS. THE
COUNT BELOW IS WRONG AND THE RULING IS IN.** The table in `## WHAT IS DELIVERED
ALREADY` reads 7 and lists 2 candidates. **The count is 8 and there are 3
candidates, and all 3 rule LIVE.**

- **THE MISSED ROW is `src/L/Absorption.lagda.md`**, 620 lines. Its only mention
  outside itself is a COMMENT at `src/L/InjChain.lagda.md:66`, not an import.
- **IT IS EMPHATICALLY LIVE.** `dev/ledger.toml:202` names it one of the two
  chapters「the proof needs MOST」, and it is the only delivered caller of `Small`
  (`src/L/Absorption.lagda.md:504`), which makes it the campaign's only worked
  comparable for coding an injection.
- **`EnvSupply` AND `KeyRead` ARE UNWIRED, NOT RETIRED.** Both are the C-49
  layout cure landed as new masters (`dev/LESSONS.md:4233`). `EnvSupply` took a
  488.59 s optimization on 2026-08-16 (`dev/memos/2026-08-16-pause.md:215`),
  which is investment and not retirement.
- **THE GOVERNING PRINCIPLE WAS ALREADY WRITTEN DOWN.** `dev/ledger.toml:188`
  reads that what the proof will need carries no import edge from the statement.
  **So「no consumer」never implied「retired」**, and this pass has an EMPTY move
  list today.

**THE OBLIGATION BELOW IS DISCHARGED, NOT PENDING.** What remains for this entry
is a move, and there is nothing to move.

## HEAD

head_slot: mathematician
machine: shared

## THE OBLIGATION

For every master under `src/` that no other master consumes, rule RETIRED or
LIVE, and give the evidence for each ruling.

**A master with no consumer is NOT a retired master.** A delivered result is a
leaf by design. That difference is the whole task, and it is a judgement, which
is why AD3 puts it here and not with the coder.

## OBLIGATION NAMES

None. This task reads and rules. It writes no Agda and closes no proof
obligation. The witness meter reads an empty obligation list and returns the
vacuous pass of section 4.7.

## SCOPE (write)

- `agents/tasks/LJ-1-415/lj-1.415-report.md`

## PREMISES

1. **The direction.** The owner wrote on 2026-08-20: one SRC collection after
   LJ-1, not after `[LJ-2.5]`. The retirement meter in `dev/ledger.toml` stays
   suspended until `[LJ-2.5]`. **This pass is the record and not the re-arm.**
2. **W4 is module-granular.** Move a retired MODULE to `archive/` and never
   delete it. A dead fragment inside a live master, with no consumer, is
   deleted instead, and the `dev/LESSONS.md` entry that cited it is restated
   generally.
3. **The standing size figure is the ledger's and nobody else's.**
   `scripts/measure/ledger.py --brief` reads 33,078 lines over 97 masters,
   measured from HEAD, with thresholds SUSPENDED. Never quote a size from a
   paragraph, and never quote the census count below as a size.

## WHAT IS DELIVERED ALREADY

**THE CENSUS IS MEASURED, and this task starts from it instead of from zero.**
The refill of 2026-08-20T08:25Z counted it.

METHOD: 99 `.lagda.md` files under `src/`, counted in the WORKING TREE. The
ledger's 97 masters is a different number for a good reason: the ledger measures
from HEAD. Never mix the two, and never report the census count as a size.
For each module name, search every
other master for the dotted name. `src/Everything.lagda.md` is the import root,
so a hit there is not a consumer. A hit in the module's own file is not a
consumer.

COUNT of masters that no other master consumes: **7**.

| master | line in `Everything` | first reading |
|---|---|---|
| `src/Landmarks.lagda.md` | the trophy case | LIVE by ruling. It is the halt's address |
| `src/L/BoundedSubset.lagda.md` | | LIVE. It instantiates `L.StageCardinal` at `:1397` |
| `src/L/CantorBernstein.lagda.md` | | LIVE, delivered by `[LJ-1.362]` and `[LJ-1.368]` |
| `src/FOL/Bernstein.lagda.md` | | LIVE, delivered by the same two |
| `src/L/Condensation/TwelveAgree.lagda.md` | `:391` | LIVE. `src/L/Condensation/README.md:12` calls it the composer |
| `src/L/Coding/EnvSupply.lagda.md` | `:392` | CANDIDATE. 937 lines |
| `src/L/Coding/KeyRead.lagda.md` | `:363` | CANDIDATE. 140 lines |

**THE TWO CANDIDATES ARE THE TASK, and the five readings above are the
refill's and not a ruling.** Re-measure every row.

`L.Coding.EnvSupply` states its own purpose at `src/L/Coding/EnvSupply.lagda.md:3`:
「Step 6's environment supply, landed as a new master that imports
`L.Condensation`」. `L.Coding.KeyRead` states its own at
`src/L/Coding/KeyRead.lagda.md:1`: 「The split key, read in the object
language」. Neither names a live consumer.

**`TwelveAgree` reads as consumed and is not.** Four masters name it and every
one of the four names it in a comment: `src/L/Condensation/UpperAgree.lagda.md:55`,
`src/L/Condensation/LowerAgree.lagda.md:64` and `:93`,
`src/L/Condensation.lagda.md:6955`. A comment is not an import. That row shows
why the census needs a reader.

## WHAT IS MISSING

For each of the two candidates: did its consumer retire, or has its consumer
not arrived yet? **The two answers earn opposite rulings**, and no grep
separates them.

## THE REASONING

Read each candidate's own head comment first, because a chapter states the step
it was landed for. Then find that step. Two questions settle a row:

1. **Did the route that asked for this chapter retire?** `archive/dev/TASKS-archived.md`
   says what each retired dispatch found, and `archive/src/` holds the retired
   Agda, one directory per archival event.
2. **Does a live document still promise this chapter a consumer?** A chapter
   that waits for work still queued is LIVE and it stays.

**RULE NO ROW YOU CANNOT SOURCE.** A row with no evidence is a row for the
owner, not a row for `archive/`.

**THE MOVE IS NOT THIS TASK.** This task rules. A successor with
`head_slot: coder` moves each RETIRED master to `archive/`, keeps
`src/Everything.lagda.md` green, and writes the `dev/ARCHIVE.md` rows that W4
names: what the module is, why it left, where it was last green, and what would
reopen it. That successor has a real Agda obligation, so P14 accepts it. Name it
in your return and do not queue it before this task rules.

**W4's last sentence binds the successor and not you.** 「Price the ideal form
written fresh today, then compare it with the chapter you have」 is a
measurement, and the coder makes it.

## WHAT GO AND NO-GO EACH EARN

**GO** earns a ruling for all seven rows, each with its evidence, and the
successor task named with its candidate list.

**NO-GO** earns the named reason. 「Every consumerless master is LIVE」 is a
full return and a good one: it says the collection pass moves nothing this
hour, and it says so from evidence.

## BRANCHES

```toml pod-branches
[[branch]]
id = "ruled"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = 0

[[branch]]
id = "blocked"
priority = 15
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 0

[[branch]]
id = "attacked"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
```
