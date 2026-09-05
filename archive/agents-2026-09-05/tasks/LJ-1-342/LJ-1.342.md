# LJ-1.342: land the generic `μ` form, with its prose in three languages

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHAT IS ALREADY BUILT AND MEASURED

**`[LJ-1.340]` wrote the generic form and it typechecks.**
`agents/tasks/LJ-1-340/ProbeGeneric.agda:54-88`, 29 lines: `predOf` and
`carveAt`.

| claim | figure |
|---|---|
| lines saved | **10**, or 14 if `meet-suc` is retired |
| baseline it attacks | **74**, re-measured, not the 77 an earlier report gave |
| seconds delta | **ZERO, and unmeasurable**: the empty-file floor is 0.82 s |
| new imports | **ZERO**; `src/L/Choice/Stage.lagda.md:44-68` already has every name |
| edges | **RETIRES one**: `L.Choice.Step` drops `L.Ordinal.Stages` entirely |
| closure | **all 29 lines are SHARED by construction**, both chapters AC and GCH |
| delivered signatures | **all nine reproduced character for character**, checked mechanically |

**It refused an available import edge with a number:** reusing a delivered
adapter saves 2 lines and adds **2 masters to BOTH trophy closures**. **Do not
take that edge.**

## THE ONE THING IT DID NOT DO, and it is why this task exists

> **Not settled: the prose rewrite in three languages, which I neither wrote nor
> costed.**

**Both chapters are trilingual masters:** `src/L/Choice/Stage.lagda.md` carries
13 `<!--zh-->` markers and `src/L/Choice/Step.lagda.md` carries 24. **A landing
that moves code between them and leaves the prose describing the old shape is a
landing that lies.**

## THE TASK

**Produce the complete landing as a proposal: the code edits AND the prose, in
English, Chinese and Japanese, for both chapters.**

**Then verify it, and hand me a diff I apply.** **You do not land it.**

## THE PROSE RULES, and they are not optional

**`AGENTS.md`:** author every document in English first, then translate, **then
cross-check the Chinese and Japanese against each other for drift.**

- **The prose in a `.lagda.md` master is EXEMPT from ASD-STE100**: there,
  precision and voice decide the words. **Match the surrounding chapter's
  register.**
- **`dev/STYLE-i18n.md` governs the `<!--en--> <!--zh--> <!--ja-->` marker
  grammar.** **Read it.** **`weave-i18n.py --check` catches stray, unterminated
  and unknown-language markers, and it MISSES a mid-line marker and a fence
  inside a language group, so check those by eye.**
- **No em dash in any language. No half-width sentence punctuation in CJK
  prose.** `lint-prose.py --fix` handles most of it.
- **A term the glossary lacks is settled by DD19's two-agent pipeline, never by
  choosing.** **If you need a rendering `dev/glossary.toml` does not have, STOP
  and name it; do not invent one.**

## WHAT THE PROSE MUST SAY

**The generic form is a NEW shape in both chapters, so the prose is not a
translation of the old text.** **Say what `predOf` and `carveAt` are, why they
are one thing rather than two, and what each site's application does.**

**And say the thing `[LJ-1.340]` measured that the old prose got wrong:**

> **`src/L/Choice/Step.lagda.md:90` claims「The argument applies verbatim to a
> single set」.** **MEASURED HALF RIGHT AND POINTING THE WRONG WAY:** the split
> and the carve are verbatim, but the argument applies only **after the other
> chapter strips one truncation**, and Step's application is 4 lines against
> Stage's 7 to 11, **so Step's setting is the simple one, not the general one.**
> **Direct reuse was never available.**

**That sentence is delivered prose and it is wrong. Replace it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE LANDING VERIFIES.** Report the diff, the check time for both chapters,
  and the three-language prose. STOP. **I apply it.**
- **A GLOSSARY TERM IS MISSING.** **STOP and name it.** DD19's pipeline is two
  agents and it is not yours.
- **THE PROSE CANNOT DESCRIBE THE NEW SHAPE HONESTLY.** **If writing the prose
  reveals the form is harder to READ than the two originals, say so: DD9 admits
  machinery only where it makes code cheaper to read, and 10 saved lines do not
  buy an unreadable chapter.** **That would be a real refusal.**
- **A CHECK GOES RED.** Report it and stop; do not chase it into `src/`.

## WHAT YOU MUST NOT DO

- **DO NOT EDIT `src/`.** **Write the full proposed files in
  `agents/tasks/LJ-1-342/` as copies, verify them there, and give me the diff.**
- **Do not take the refused import edge.** It costs 2 masters in both closures.
- **Do not retire `meet-suc`** unless you measure that nothing needs it; the 10
  does not depend on it and the 14 does.
- **Do not edit another task directory.** You may READ and RE-RUN
  `agents/tasks/LJ-1-340/`'s four probes.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **C-53 as extended today: state the EMPTY-FILE FLOOR beside any seconds
  figure, and call a delta under the floor UNMEASURABLE rather than small.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-342/lj-1.342-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `.venv/bin/python scripts/gate/lint-agda.py --check` and
  `.venv/bin/python scripts/site/weave-i18n.py --check` on your copies.
- Evidence is `file:line`. **Your REPORT is ASD-STE100; the chapter PROSE is
  not.** Mark every negative **MEASURED** or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eight of my last fourteen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the prose is the only thing missing」.** **`[LJ-1.340]`
verified nine signatures character for character, but a landing also has to keep
every CONSUMER green, and it checked its probes rather than the tree.** **Check
the consumers** (C-40).

## THE RULES

**C-40** is the risk: verify the CONSUMERS of a changed file, never the file
alone. **DD9**: machinery is admissible only where it makes code cheaper to
READ. **DD19**: a missing glossary term is not yours to choose.
**C-57, C-53, C-44, C-45, C-22, C-32, C-36, C-39, C-42, P-l.** I-5.
**D-1, D-10, D-26. DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for rewrite` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This landing IS that rule, at a site where
`[LJ-1.340]` measured that all 29 lines are shared by construction.**

**NAME YOUR AXIS** (C-46), which is AC-against-GCH, fixed at
`scripts/measure/ledger.py:50`. **Report the closure after your edit and confirm
`[LJ-1.340]`'s zero-new-import figure**, noting `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

**And one thing it found that nothing demands today:** the form applies
unchanged at a THIRD site, `src/L/Reflect.lagda.md:175`, crossing a structure
boundary with no adapter, 10 lines typechecked. **It claimed no line for it and
neither should you. Mention it in the prose only if it reads naturally.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-340/lj-1.340-report.md`, read WHOLE.** It funds you and
  it holds the form, the baselines and the refused edge.
- **`agents/tasks/LJ-1-339/lj-1.339-report.md`**, whose baseline `[LJ-1.340]`
  corrected by one to three lines.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route landed generic forms too. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on writing an operation generic.** Say so in
one line and return a **LITERATURE USED** section.

## SCOPE (read)

`dev/STYLE-i18n.md` FIRST, then both chapters WHOLE.

## SCOPE (write)

`agents/tasks/LJ-1-342/` only.

## RETURN

**Lead with ONE line: does the landing verify, and what is the final line
delta.** Then the diff for both chapters. Then the three-language prose, and
confirm the Chinese and Japanese were cross-checked against each other. Then
every consumer, green or not. Then the closure. Then whether the new shape is
cheaper to READ than the two originals, which is DD9's question and yours to
answer honestly. **Mark every negative MEASURED or INFERRED.**
