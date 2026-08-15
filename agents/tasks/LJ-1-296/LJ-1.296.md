# LJ-1.296: a quota fallback from `pi` to in-harness, triggered by the refusal

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave.** **QUEUED**: three agents are live and one holds `scripts/`.

## THE OWNER'S INSTRUCTION

**When `pi-subagent-mode`'s usage reaches its limit, fall back to in-harness.**

## THE CONSTRAINT THAT SHAPES THE WHOLE DESIGN, and I measured it before writing

**THE LIMIT IS NOT OBSERVABLE FROM THIS MACHINE. MEASURED 2026-08-15:**

- **`pi` has no usage, quota or balance subcommand.** Its subcommands are
  `install`, `remove`, `uninstall`, `update`, `list`, `config`, `auth`. **`pi
  auth check` returns only `{"status":"ready","provider":...}`**, which is
  credentials and not consumption.
- **The dispatch logs record no token counts.** I grepped
  `.claude/skills/codex-dispatch/.state/logs/` for a usage field and got
  nothing.
- **The vendor is a SUBSCRIPTION**, `dev/vendors.toml`, so there is no
  per-call price to accumulate either.

**So a design that counts usage against a limit CANNOT BE BUILT, because
neither number exists here.** **Do not build one. Do not estimate one. An
estimated quota is a number the project would then trust** (C-44's shape).

**THE ONLY HONEST TRIGGER IS THE VENDOR'S OWN REFUSAL.** When the quota is
gone, the backend says so, and that message is readable at the moment it
arrives. **That is the condition a tool can actually detect, and C-48 is the
law: a tool that can read a condition must refuse on it.**

## WHAT TO BUILD

**A fallback that fires on a MEASURED refusal from the vendor and re-routes the
task to the in-harness head.**

**1. FIND THE SIGNAL FIRST, AND DO NOT GUESS ITS SHAPE.** Search the dispatch
logs and pi's own output for what a quota or rate-limit refusal actually looks
like. **If no such refusal has ever occurred on this machine, SAY SO** and
describe the signal you would match, marked INFERRED, with the evidence you
based it on. **A matcher written against an imagined error string is worse than
no matcher, because it will not fire on the day it is needed.**

**2. THE RE-ROUTE ITSELF.** `dispatch.py` cannot start an in-harness agent: an
in-harness dispatch passes through no tool. **So the fallback CANNOT launch the
replacement.** What it can do is **refuse loudly and tell the orchestrator
exactly what to run in-harness**, naming the task and the brief. **Say plainly
in your report that this is a hand-off and not an automatic re-route**, because
a design that claims to re-route and only prints a message is the escape hatch
C-43 describes.

**3. WHERE THE STATE LIVES.** If a refusal should stick, so the next dispatch
does not retry a dead vendor, say where that state goes and how it is CLEARED.
**`dispatch.py` already has `BLOCKED_MODELS` at `:81`, a dict from model to a
date, used by the dead-model refusal at `:631-636`.** **Read it. It may be the
right home, and re-using it beats inventing a second mechanism.**

## THE THREE QUESTIONS THE DESIGN MUST ANSWER

**A. DOES IT INTERACT WITH THE PIN?** `VERSION_IN_FORCE` is pinned to
`pi-subagent-mode` by the owner's word, daily. **A quota fallback that silently
overrides a pin is a rule fighting a ruling.** Say which wins and why. **My
reading, which you may overturn: the pin says which head LEADS, and a fallback
says that head is UNAVAILABLE. Those are different claims and both can be true.**

**B. WHAT HAPPENS TO THE ADVERSARIAL ROW?** DD17's invariant is that the critic
is never the author. Under `pi-subagent-mode` the default is `pi` and the
adversarial is in-harness `opus`. **If `pi` is exhausted and the default falls
back to in-harness, then a task and its DD25 review would both be in-harness,
and the invariant breaks.** **Say what the fallback does about that.** The
existing `fallback` row is `herdr`/`codex`, which may be the answer, and nobody
has used `--fallback` in any brief: `git grep --fallback agents/` returns zero.

**C. IS `codex` STILL REACHABLE?** The existing fallback row names it. **Check
whether `pi` and `codex` share the exhausted vendor**: `dev/vendors.toml` gives
`pi_provider = "zai"`, and the fallback row's model column also reads
`glm-5.3`. **If they share a quota, falling back to codex buys nothing and the
row is decorative. MEASURE IT and say so.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SIGNAL EXISTS AND YOU MATCH IT.** Report the matcher, the state, the
  three answers, and the tests. STOP.
- **NO REFUSAL HAS EVER BEEN SEEN.** **Say so.** Then the matcher is INFERRED,
  and it must be written so a wrong guess FAILS LOUDLY rather than silently not
  firing. **Say how you arranged that.**
- **THE FALLBACK CANNOT BE AUTOMATIC.** **That is the likely answer and it is a
  real one.** An in-harness dispatch passes through no tool, so the honest
  design is a loud refusal plus a hand-off. **Do not dress it up.**
- **THE INVARIANT BREAKS AND CANNOT BE SAVED.** Then the fallback needs a
  ruling, not code. Say what the owner would have to decide.

## CONSTRAINTS

- **`.claude/skills/codex-dispatch/dispatch.py` IS OUTSIDE YOUR WRITE SCOPE**
  and it is where this logic belongs. **So DESIGN it and write the exact patch
  as a diff in your report; I apply it.** **That file is untracked and mine.**
- Your write territory: `scripts/dispatch_policy.py`, `dev/vendors.toml`,
  `scripts/tests/`, and `agents/tasks/LJ-1-296/`. **NOT `AGENTS.md`, NOT
  `dev/PLAN.md`, NOT `src/`, NOT another task directory.**
- **A SIBLING IS MOVING `scripts/` RIGHT NOW** as `[LJ-1.295]`. **Check where
  `dispatch_policy.py` lives before you edit it**, and if the move is mid-flight,
  say so and stop rather than fighting it.
- **DO NOT RUN AGDA.** Siblings hold both slots.
- **Do not run `make check`**; I run it.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- **Create `agents/tasks/LJ-1-296/lj-1.296-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/lint-prose.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**C-48, written today. A policy that only a document states is not enforced,
and a tool that can read a condition must refuse on it.** **Here the condition
is the vendor's refusal and nothing else, because nothing else is readable.**

**C-43. An escape hatch is the shape a wrong choice hides in.** **A fallback
that silently swallows a quota error and proceeds is that shape. So is one that
claims to re-route and only prints.**

**C-44.** Every measurement in this brief is mine from today and you must
re-derive each one, especially the claim that `pi` exposes no usage.

**DD17's INVARIANT: the critic is never the same head as the author.** It is
not negotiable by a fallback.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. This task writes no mathematics. **Say in one
line whether your fallback would still work if the vendor changed again**, which
is the same question `dev/vendors.toml` exists to answer.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-288/lj-1.288-report.md`, the vendor config and its
`pi_wired` refusal, which is the nearest existing shape to what you are
building. `archive/dev/TASKS-archived.md`, taking SHAPE and never a claim.
Return an **ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on a quota fallback. Say so in one line and
return a **LITERATURE USED** section.

## SCOPE (read)

`.claude/skills/codex-dispatch/dispatch.py` lines 81 and 620 to 640 FIRST, the
existing dead-model refusal.

## SCOPE (write)

As listed under CONSTRAINTS.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS IS AN
EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **C-42.** A refutation measures the site it names.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **The residue here is「the limit is reachable」and its truth is what I
  measured as unobservable.**
- **C-22.** Write your deliverable incrementally.
- **P-l.** A judgement at one site is a hypothesis at another.
- **D-26.** It does not bear here and I say so rather than pretending.
- **C-32, C-36, C-38, C-39, C-40, C-43, C-44, C-45, C-46, C-48. I-5. DD0, DD4,
  DD8, DD17, DD18, DD19, DD24.**

## RETURN

**Lead with ONE line: what signal triggers the fallback, and whether you have
ever seen it.** Then the exact patch for `dispatch.py` as a diff. Then the three
answers: the pin, the invariant, and whether codex shares the exhausted vendor.
Then where the state lives and how it clears. **Mark every negative MEASURED or
INFERRED.**
