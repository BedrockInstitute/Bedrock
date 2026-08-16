# LJ-1.364: Fable RULING on two mathematical questions the owner has left open

tier: fable (pi-subagent-mode), **the EMERGENCY tier, taken on the owner's
EXPRESS authorisation of 2026-08-16: 「the other two rulings about mathematics,
dispatch fable to rule them. I have authorised it.」** **DD0 binds: this is a
ONE-OFF instruction and it is NOT a standing head choice. It does not make
fable the head for any other task.** In-harness, maximum effort.

## YOUR STANDING, and it is different from an ordinary agent's

**You are not reporting for the orchestrator to decide. You ARE the decision.**
The owner has delegated both rulings to you. **Give a RULING on each, in
words a landing brief can be written from, or give an explicit REFUSAL naming
what evidence is missing.** **A refusal is a legitimate ruling and it is
better than a guess.**

**Both questions were raised by agents who explicitly declined to answer them,
and both have sat unruled since.**

---

## RULING 1: seal `envSetAt` and `envOverAt`, or do not

### What was found

**`[LJ-1.283]` searched for seal candidates and found exactly one that sits in
BOTH closures**: `envSetAt` and `envOverAt` in `src/L/Coding/Model.lagda.md`
(`envSetAt` at `:1149-1150`). **A seal there is inherited by both proofs**,
which makes it the only candidate DD4 would call a shared win.

**MEASURED by me before writing this brief: `src/L/Coding/Model.lagda.md`
carries ZERO `abstract` and ZERO `opaque` blocks today.** Nothing has been
done. **Re-derive that.**

### The evidence AGAINST, and it is why nobody has ruled

**`[LJ-1.283]` put P-y's own recorded warning beside its own recommendation:**

> **P-y measured that a seal in shared upstream machinery made the AC side gain
> 41.7 percent against the GCH wing's 8 percent, and the DD24 ratio went 1.56x
> to 1.91x, so EVERY MASTER GOT FASTER AND THE VERDICT GOT WORSE.**

`dev/LESSONS.md:3840-3846`. **Read P-y's full entry, not this quotation.**

**Then `[LJ-1.283]` stopped: 「That is the owner's ruling to make, not mine.」**

### Why the tension is real and not an artefact

**DD24 sets a bar of 0.010514 seconds per line.** A seal that speeds the AC
closure more than the GCH closure moves the RATIO the wrong way even while it
moves every absolute number the right way. **So「faster」and「better」come
apart here, and which one the project is buying is a judgement rather than a
measurement.** **That judgement is what you are being asked for.**

### What to decide, and say which you are doing

**SEAL, DO NOT SEAL, or SEAL UNDER A NAMED CONDITION.** **If you rule for a
condition, state it so a checker or a brief can test it.**

**And answer the question under it, which nobody has asked:** **is DD24's
ratio the right instrument at all when a change helps both wings and helps one
more?** **If the instrument is wrong, say so; that is a larger finding than
this seal and the owner should hear it.** **You may rule the seal question and
REFER the instrument question upward. Say which you did.**

---

## RULING 2: retire `meet-suc`, or keep it

### What was found

**`[LJ-1.342]` measured that `meet-suc` has NO CODE CONSUMER.** Retiring it
costs **two `src/Everything.lagda.md` edits** and saves **4 lines**.

**MEASURED by me before writing this brief:** it is still live, at
`src/L/Choice/Stage.lagda.md:265`, and named in `src/Everything.lagda.md`
prose at `:667` and `:997`. **Re-derive the consumer count yourself; a
delivered chapter's English has twice this month held an answer nobody had
read against the question (C-57).**

### Why `[LJ-1.342]` refused to rule it

**「DD13 prices a retirement from the REWRITE SIDE, and I did not price that
rewrite.」** **DD13 is the rule and it is not optional: a consumer does not
prove a chapter must stay, and「we already paid for it」never decides the
question in either direction.** **The ideal form written fresh today must be
priced, then compared.**

### So your ruling has a precondition, and you must handle it honestly

**Either price the rewrite side yourself and rule**, or **rule that the
question cannot be settled without that price and say exactly what would have
to be measured.** **Do NOT rule on「no consumer」alone: that is precisely the
reasoning DD13 forbids.**

**A third outcome is open and you should consider it: `meet-suc` may be
consumed by PROSE rather than by code, and DD23 has now been restated by the
owner.** **MEASURED TODAY: `src/` carries NO mathematical prose; the two
masters that landed today were stripped to code and comments only, and
`src/L/GCH.lagda.md` has one prose line, its title.** **So a name held only by
`src/Everything.lagda.md`'s catalogue entries is held by a different kind of
text than it was when `[LJ-1.342]` looked. Say whether that changes the
answer.**

---

## WHAT BINDS YOU, AND WHAT DOES NOT

**The owner's authorisation is for these two rulings and nothing else.** **Do
not rule on the trophy statement, the route, or anything in DD2 or DD5.**

**DD23, restated by the owner TODAY:** **NO MATHEMATICAL PROSE until both
trophies land. Code and its own comments only.** **This binds anything you
recommend writing.** **I violated it in two briefs this morning and had to
strip 147 prose lines out of two masters an hour after landing them. Do not
recommend prose.**

## CONSTRAINTS

- **RULE, DO NOT BUILD.** Write only in `agents/tasks/LJ-1-364/`. **`src/` is
  forbidden** (I-5). **You may run Agda for a measurement.**
- **`[LJ-1.362]` and `[LJ-1.363]` are LIVE.** `[LJ-1.362]` holds ONE Agda slot
  and writes `src/FOL/Bernstein.lagda.md`; `[LJ-1.363]` writes
  `scripts/gate/` and `agents/tasks/LJ-1-363/`. **You may take the second Agda
  slot and no more.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-364/lj-1.364-ruling.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  Evidence is `file:line`. Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-two briefs carried a claim an agent measured FALSE,
and this morning `[LJ-1.359]` found two stale citations in a brief I had
written an hour before.** **The one at risk here: 「`envSetAt` and `envOverAt`
are the only candidate in BOTH closures」.** **That is `[LJ-1.283]`'s finding
from 2026-08-15, and the closures have MOVED since: `[LJ-1.323]`'s restatement
pushed `L.Absorption`, `L.InjChain` and `L.Axioms.Infinity` OUT of the GCH
closure.** **So the shared set is not what it was when the finding was made.**
**Re-run `.venv/bin/python scripts/measure/ledger.py --reuse` and check
whether `L.Coding.Model` is still in both. If it is not, ruling 1 changes
shape entirely.**

## THE RULES

**DD13 governs ruling 2 and it is not optional.** **P-y governs ruling 1 and
you must read its full entry.** **DD24's bar is 0.010514 s per line.**
**C-57, C-44, C-45, D-10, C-42, C-53, P-l, P-k, P-m.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD5, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and
`--grep seal`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**RULING 1 IS A DD4 QUESTION WEARING A PERFORMANCE COSTUME, and that is the
heart of it.** **The seal's whole appeal is that it sits in BOTH closures.**
**P-y's warning is that a shared-machinery win can move the ratio the wrong
way.** **So DD4's own no-metric ruling is live evidence for you: the owner
refused DD4 a threshold because a shared-line count would be gamed the moment
it gated anything. Ask whether DD24's ratio is exposed to the same objection
when the change is upstream of both wings.**

Today's reuse figures, MEASURED by me: AC closure 73 masters 17,186 lines;
GCH closure 48 masters 8,878; SHARED 43 masters 7,585; 41.0 percent of the
18,479-line union. **`dev/ledger.toml:200-206`: the GCH closure is read from a
STATEMENT whose proof is not wired, so it UNDERSTATES by about 1,027 lines.**
**A ratio computed on an understated wing is the thing you are being asked to
trust. Say whether you do.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED
2026-08-16** (`scripts/gate/check-archive-cited.py:26-27`). **Name each of the
four corpora, cited or declined in one line, and quote ONE line per archived
file you read.** That quote duty is DD18's amended return clause, ruled by the
owner today.

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route seal its
  coding substrate?** **That is direct evidence for ruling 1 and nobody has
  looked.** Grep it for `abstract` and `opaque`.
- **`archive/dev/JOURNAL-archived.md`**: the retired route's seal episodes.
  **P-y was measured somewhere; find where and read the episode, not the
  summary.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on sealing or on
  retirement pricing. **WHY NOT in one line if none bears.**
- **`archive/dev/TASKS-archived.md`**: **grep for a retired analogue of
  `meet-suc`.** **The retired route had its own stage machinery, so it may
  have priced this exact retirement.**

**Return an ARCHIVE USED section.**

## LITERATURE (DD18)

**`dev/literature/j-hierarchy.md`** for the stage machinery `meet-suc` serves.
**Say in ONE line whether the orthodox development needs a successor-stage
lemma of this shape at all.** **If it does not, that is evidence for
retirement that no consumer count can give.** Return a **LITERATURE USED**
section with WHY NOT.

## SCOPE (read)

`dev/LESSONS.md`, P-y's FULL entry at `:3840` and its surrounding measurement,
FIRST. It is the whole evidence base for ruling 1.

## SCOPE (write)

`agents/tasks/LJ-1-364/` only.

## RETURN

**Two rulings, each led by ONE word.**

**RULING 1: SEAL, NO-SEAL, or CONDITIONAL**, then the condition if any, then
whether `L.Coding.Model` is still in both closures, then your answer on
whether DD24's ratio is the right instrument.

**RULING 2: RETIRE, KEEP, or CANNOT-RULE-WITHOUT**, then the rewrite-side
price or exactly what must be measured to get it, then whether DD23's
restatement changes the answer.

**Mark every negative MEASURED or INFERRED. If you refuse a ruling, say so in
the first word and name the missing evidence.**
