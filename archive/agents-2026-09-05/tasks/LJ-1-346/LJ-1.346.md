# LJ-1.346: land the tie supply, and settle the private access

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHAT IS BUILT AND WHERE IT GOES

**`[LJ-1.344]` supplied both repaired ties as TERMS**,
`agents/tasks/LJ-1-344/Supply344.agda`, exit 0 in 3.09 s. **25 code lines, NO
new `KFacts` field, NO new `BoundOver` lemma.**

**It named the site precisely:**

> One new module immediately after `KFactsCons`, which ends at
> `src/L/Condensation.lagda.md:6155`, and before `module ShapesAgree` at
> `:6157`. It holds `pair∈pr` (4 lines), `sglS` (7), and
> `module KTies (f : KFacts …)` with `sgltK`, `envK`, `defPairK` (25 code
> lines). Then at `:7207-7209` pass `KTies.envK` and `KTies.defPairK` and
> **delete both from the `LeafAgree` and `DefinesAgree` telescopes.**

**And a warning it gave that you must honour:** a supply written inside the
chapter sits **BEFORE** `KValue`, **so the wiring must stay at `KValue`'s site
or below.**

## THE INTERFACE QUESTION, and it is the reason this is a task and not an edit

**`[LJ-1.344]`:**

> The one thing the tree really lacks is an ACCESS, not a closure:
> `⁅ x , y ⁆ ∈ pr x y` is `inr∈⁅,⁆` at `src/V/Coding.lagda.md:149-150`, **inside
> a `private` block. Four tasks have now re-written those 4 lines.**

**I read the block. It starts at `src/V/Coding.lagda.md:136` and it holds more
than that one name**: `∈singl`, `singl∈`, `self∈singl`, `inl∈⁅,⁆`, `inr∈⁅,⁆`,
`mem⁅,⁆` and possibly more. **So「make it public」is not a one-word change; it
is a decision about a chapter's public interface.**

**DECIDE IT, with evidence:**

- **Which names in that block have been re-written outside the chapter, and how
  many times?** **Count, do not estimate** (C-57: say how many hits you read).
- **Which were made private on purpose?** **Read the chapter's own prose around
  `:130-136` before you move anything.**
- **Then propose the smallest interface change that stops the re-writing**, and
  say what it exposes that was hidden.

**If the honest answer is that the block should stay private and the four
re-writes are the correct cost, say that.** **A private block is a design
choice and the tree may have made it on purpose.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH LAND AND THE CHAPTER IS GREEN.** Report the diff, the cold check time
  past the cache, and every consumer. STOP.
- **THE INTERFACE SHOULD STAY PRIVATE.** **Say so with the count**, land the
  supply with its own 4-line copy, and the fifth re-write is then a measured
  decision rather than an accident.
- **THE SITE IS WRONG.** `[LJ-1.344]` named `:6155` to `:6157` and warned about
  the ordering against `KValue`. **If the ordering does not work, say where it
  breaks.**
- **A WALL.** **A plain re-check of this chapter is now a CACHE HIT at about
  2.4 s.** **`[LJ-1.345]` forced an honest cold figure by copying the chapter
  verbatim with only the module renamed, and got 132.93 s against a 2.37 s
  floor.** **Do the same; a cache hit is not a check.** 30 minutes on one
  invocation is a wall: interrupt, report ELAPSED SECONDS, bisect. **NEVER
  raise the cap.**

## WHAT YOU MUST NOT DO

- **You MAY edit `src/L/Condensation.lagda.md`, and `src/V/Coding.lagda.md`
  ONLY if you rule the interface should change.** **Nothing else in `src/`.**
- **Do not touch the four remaining construction ties.** `[LJ-1.344]` priced
  them and one is a refutation candidate it marked **INFERRED FALSE, not
  MEASURED**, after four interrupted runs. **That is a separate task.**
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-344/Supply344.agda` and its controls.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended:
  `[LJ-1.344]` measured its own delta UNDER the floor and called it
  UNMEASURABLE, which is the standard).
- **RUN A NEGATIVE CONTROL that MEASURES.** **`[LJ-1.344]`'s control A asked the
  supply for the PRE-repair unbounded hypothesis and got exit 42, which proves
  the repair is load-bearing in the PROOF and not only in the type.** **Keep
  that standard.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **Create `agents/tasks/LJ-1-346/lj-1.346-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `.venv/bin/python scripts/gate/lint-agda.py --check` and
  `.venv/bin/python scripts/site/weave-i18n.py --check` on anything you touch.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Nine of my last eighteen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the site at `:6155` to `:6157` works」.** **That is
`[LJ-1.344]`'s reading, and it also flagged an ordering hazard against `KValue`
in the same breath.** **Check the ordering before you write anything.**

## THE RULES

**C-45** is the law of this whole episode: `exit 0` is not a supply.
**C-40**: verify the CONSUMERS of a changed file, never the file alone. **Two
frozen probe records copy this chapter verbatim and your change makes them
staler; do NOT update them, name them.**
**C-57, C-53, C-44, C-42, D-10, P-l, C-22, C-32, C-36, C-39.** I-5.
**D-1, D-26. DD0, DD4, DD8, DD9, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for rewrite` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.344]` measured the supply is CLASS-FREE: the three terms name only
`fst`, `∈`, `lookup`, `pr`, `prʟ`, `numeralL`, the pair brace and four `KFacts`
fields, and not one mentions AC, GCH, a well-ordering or a cardinal.** **So the
same 25 lines serve both carriers because the record is already generic.**
**Confirm that survives landing**, and note `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** It funds you, it
  holds the terms and the site, and it corrected the two-line reading in the
  cheap direction.
- **`agents/tasks/LJ-1-345/lj-1.345-report.md`**, the review that upheld the
  refutation and caught the cache-hit trap.
- **`agents/tasks/LJ-1-343/lj-1.343-report.md`**, the landed repair whose
  telescopes you are about to shorten.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.344]` reported that its supply is
the port of a closure Devlin PROVES, where the repair's hypothesis was the port
of a premise he ASSUMES.** **Say in one line whether landing it puts the
chapter's dependency structure where his is.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-344/Supply344.agda:169-176` FIRST, the eight-line closure
that replaced a supposed two-line one.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/V/Coding.lagda.md` if you rule the
interface changes, and `agents/tasks/LJ-1-346/`.

## RETURN

**Lead with ONE line: does the supply land green, and what is the cold check
time past the cache.** Then the interface ruling with its count. Then the diff.
Then the telescopes shortened. Then every consumer. Then which frozen records
your change makes staler. Then the DD4 axis. **Mark every negative MEASURED or
INFERRED.**
