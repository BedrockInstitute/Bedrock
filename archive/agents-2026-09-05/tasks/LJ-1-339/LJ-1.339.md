# LJ-1.339: sweep `src/L/Choice/Stage.lagda.md`, because two false negatives came from it

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY, and the agent that found them said so itself

**`[LJ-1.337]` found TWO delivered terms that three earlier briefs had called
absent, and BOTH were in one chapter:**

- **`ord-suc-inj`** at `src/L/Choice/Stage.lagda.md:239` is `sucV` injectivity,
  **top level, exported, and already consumed** at
  `src/L/Choice/Faithful.lagda.md:53`. **The search that missed it used
  `sucV-inj`; the delivered token order is reversed, so the pattern could not
  match.**
- **`isPropPredOf`** at `:249-252` is `isProp (IsSuc σ)` under another name,
  **the same `Σ≡Prop` and `isProp×` body**.

**Its own closing line:**

> **Two of my two false-negative finds were in `src/L/Choice/Stage.lagda.md`,
> which suggests that chapter is worth one sweep.**

**I verified both terms myself before writing this brief.**

## THE QUESTION

**What else does that chapter deliver that the rest of the tree does not know
about?**

## WHY THIS IS CHEAP AND WHY IT PAYS

**Three briefs on this leg funded work for things that already existed.**
`[LJ-1.328]` found a whole uniform family a predecessor had declared missing.
`[LJ-1.337]` found two more. **D-10 is the law: price the TRUTH of a recorded
residue before pricing its proof.**

**The cure is a NAME INDEX, not a proof.** **One chapter, read whole, and a
table of what it exports against what the rest of the tree searches for.**

## THE TASK

**1. READ THE CHAPTER WHOLE** and list every top-level exported name with a
one-line statement of what it gives.

**2. FOR EACH, ASK: would a natural search find it?** **Name the search a
reasonable agent would run and say whether it hits.** **`ord-suc-inj` failed
because the tokens are in the other order; look for that shape of miss
specifically.**

**3. CROSS-CHECK against what this leg's briefs called absent.** The claims to
test, each at `file:line` in its own report:

- `sucV` injectivity, called absent by `[LJ-1.335]` — **FOUND, verified**
- `isProp (Init δ)`, called absent by `[LJ-1.335]` — **`[LJ-1.337]` says still
  absent; CONFIRM or refute**
- a successor-or-limit dichotomy, called absent — **`[LJ-1.337]` found a
  TRUNCATED one in a live probe and built the untruncated one. Check the
  chapter holds neither**
- **any ordinal arithmetic fact this leg assumed missing.** **Read
  `agents/tasks/LJ-1-330/`, `LJ-1-332/`, `LJ-1-335/` and `LJ-1-337/` for their
  「MEASURED ABSENT」claims and test each against this chapter.**

**4. SAY WHETHER THE CHAPTER IS IN THE WRONG PLACE.** **`[LJ-1.337]` observed,
without pricing it, that ordinal facts are scattered across `L.Choice.Stage`
and `L.Ordinal.SquareLaw`.** **An ordinal fact in a CHOICE chapter is hard to
find by any search, and that may be the root cause rather than the naming.**
**Say whether a move is warranted; do not attempt one** (DD13 prices a
retirement from the rewrite side, and a move is the orchestrator's).

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE CHAPTER HOLDS MORE THAT THE TREE MISSES.** **Report each with the search
  that failed.** **That is the deliverable and every hit saves a future task.**
- **THE TWO WERE ALL OF IT.** **A real answer.** Then the chapter is fine and
  the naming was two accidents.
- **THE ROOT CAUSE IS PLACEMENT.** **Say so with the count**: how many ordinal
  facts live in a chapter whose name says choice.
- **A WALL.** Not expected: this is reading.

## WHAT YOU MUST NOT DO

- **RUN NO AGDA unless you need to confirm a term's type**, and count the slots
  first if you do. C-12 caps this machine at TWO and a sibling is live:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
  `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- **LAND NOTHING and MOVE NOTHING.** Write only in
  `agents/tasks/LJ-1-339/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-339/lj-1.339-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Seven of my last eleven briefs carried a claim an agent measured FALSE, and
this task exists because of that pattern.** **The one at risk here: 「the root
cause is naming」.** **`[LJ-1.337]` offered PLACEMENT as an alternative and did
not price it. Test both.**

## THE RULES

**D-10** is the whole task. **C-44, C-42, C-52** (a sweep names the
discriminating property, not a token, and this leg has now paid for that twice).
**C-45, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26. DD0, DD4, DD13, DD18.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`src/L/Choice/` is the AC trophy's own machinery, and this leg is the GCH
descent, which has now reused it twice**: `pullOrder` and `ord-suc-inj`. **So
this chapter is already a DD4 success nobody counted.** **Say how many of its
exports are used by the GCH side today, and how many MORE could be.** **That is
DD4's own axis and a real number for it.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-337/lj-1.337-report.md`, read WHOLE.** It funds you and
  its two finds are your starting point.
- **`agents/tasks/LJ-1-335/lj-1.335-report.md`**, whose absent-claims you test.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had ordinal arithmetic scattered too. **Say what would not
  transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on where a delivered lemma is named.** Say so
in one line and return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Choice/Stage.lagda.md` WHOLE, first.

## SCOPE (write)

`agents/tasks/LJ-1-339/` only.

## RETURN

**Lead with ONE number: how many delivered terms in that chapter the rest of the
tree would fail to find by a natural search.** Then each, with the failing
search. Then each absent-claim from this leg, CONFIRMED or REFUTED. Then whether
the root cause is naming or placement, with a count. Then how many of the
chapter's exports the GCH side uses today. **Mark every negative MEASURED or
INFERRED.**
