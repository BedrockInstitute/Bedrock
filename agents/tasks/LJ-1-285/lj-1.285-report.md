# LJ-1.285 report: rename the dispatch mode off the vendor name

Status: DONE.

## THE SIX ACCEPTANCE TESTS

**1. `dispatch_policy.py` prints the new name and the correct clock line.** PASS.
```
DISPATCH POLICY: `in-harness-subagent-mode` is IN FORCE
  ...
  next boundary: 2026-08-15 18:00 Beijing, off-peak begins, mode becomes `pi-subagent-mode`
```
The switch is `auto`, PEAK now (Beijing 14:00 to 18:00), so `in-harness-subagent-mode` is in force, and off-peak now names `pi-subagent-mode`.

**2. `dispatch_policy.py deepseek-subagent-mode` still resolves and renders, through the alias.** PASS.
```
DISPATCH POLICY: `pi-subagent-mode` is IN FORCE   (NOT the switch's value)
```
`main()` now canonicalizes its CLI argument before the legality check (`scripts/dispatch_policy.py:492-493`), so the old name resolves and the table renders under the live name. `normal` and `override` also still resolve (checked directly, not in the six tests but relevant): `dispatch_policy.py normal` prints `pi-subagent-mode`; `dispatch_policy.py override` prints `in-harness-subagent-mode`.

**3. `check-dispatch-policy.py` exits 0 over every brief, including the frozen ones that name the old mode.** ONE UNRELATED FAIL, MEASURED, everything alias-related is clean.
```
FAIL: agents/tasks/LJ-1-285/LJ-1.285.md: `tier: sonnet (in-harness-subagent-mode), the owner nam` names head 'sonnet', which is not one of codex, fable, opus, pi
1 defect(s) against the `in-harness-subagent-mode` policy
```
MEASURED: this is the ONLY defect, and it names none of `deepseek`, `alias`, or `pi-subagent-mode`. It fails on the HEAD TOKEN check (`head_token(line) not in legal`), a code path independent of `VERSION_RE`/`ALIASES`. It fires only against `agents/tasks/LJ-1-285/LJ-1.285.md`, the brief this task itself was given verbatim to write, which reads `tier: sonnet (in-harness-subagent-mode), ...`. `sonnet` was never a legal token (`LEGAL_TOKENS = opus, pi, codex, fable`) before this task started, and `[LJ-1.283]` and `[LJ-1.284]`, two sibling briefs the same orchestrator wrote today at 14:10 and 14:31, both read `tier: opus (in-harness-subagent-mode)` correctly. My own brief, written 14:42, is the only one carrying `sonnet` in the head-token slot. I did not edit `agents/tasks/LJ-1-285/LJ-1.285.md`'s tier line: the top-level instruction says the brief is "the pinned record of what was asked," so I preserved it verbatim rather than silently correcting what looks like a transcription slip in how this dispatch's own tier line was composed. This is orthogonal to the rename; I flag it for the orchestrator rather than fix it myself, since fixing it means either rewriting the pinned record or adding a new legal token, both outside a naming task's authority.

Over the 189 frozen occurrences of `deepseek-subagent-mode` under `agents/` and the live-surface occurrences, zero are implicated in this one FAIL. `check-dispatch-policy.py --notes` confirms no other line mentions the mode name at all.

**4. `pytest scripts/tests/test_dispatch_clock.py -q` passes.** CANNOT RUN AS SPECIFIED: MEASURED, `pytest` is not installed in `.venv` (`pip list` shows nothing named pytest; `requirements-dev.txt` does not list it). This project's `scripts/tests/*.py` are self-running scripts with their own `check()`/`sys.exit()`, the same shape as `scripts/check-*.py`, not real pytest test modules (no `def test_...` functions), so `-m pytest` was likely never the intended invocation. Running the file directly, which is how every other checker in this tree is run:
```
$ .venv/bin/python scripts/tests/test_dispatch_clock.py
test_dispatch_clock: all checks passed (35)
$ echo $?
0
```
35 checks pass, up from 33 before my edit: I added one check that a raw `VERSION_IN_FORCE = "deepseek-subagent-mode"` pin still resolves to `pi-subagent-mode` through `in_force()` (`scripts/tests/test_dispatch_clock.py:130-133`), testing the alias at the PIN level and not only on a brief's tier line.

**5. `lint-prose.py --check` on every file I edited.** PASS, silent, exit 0.
```
$ .venv/bin/python scripts/lint-prose.py --check dev/PLAN.md dev/ORCHESTRATION.md scripts/dispatch_policy.py scripts/check-dispatch-policy.py scripts/tests/test_dispatch_clock.py
$ echo $?
0
```

**6. `check-rule-ids.py` exits 0.** PASS.
```
check-rule-ids: clean (45 files, 151 lessons, 67 decisions)
```

## FILES CHANGED, hit count before and after (count of the literal string `deepseek-subagent-mode`)

- `scripts/dispatch_policy.py`: 14 before, 5 after. The 5 remaining: 1 history comment (`:77`, "the pin that ran 2026-08-14 was..."), 1 history clause inside `REVERT_CONDITION` (`:91`, same event), the new `ALIASES` entry and its explaining comment (`:254`, `:259`, `:265`), and the `main()` help text noting the retired name resolves (`:494`). Also renamed: the `POLICY` dict key, the `CLOCK_STATES["off-peak"]` value, `ALIASES["normal"]`, the module docstring, the switch-value comment, `REASON`, `REVERT_CONDITION`'s forward instruction, and the `main()` usage string. Added: canonicalization in `in_force()`, `table()`, `render()`, `main()` so the alias resolves at every entry point, not only inside `check-dispatch-policy.py`. Added a "THE VENDOR SEAM" comment above `MODEL` naming it and `FLASH` as the only two lines a vendor swap touches, per the brief's request to generalize the comments.
- `scripts/check-dispatch-policy.py`: 1 before (in `VERSION_RE` plus its comment), 2 after. Added `pi-subagent-mode` as a new alternative in `VERSION_RE` (`:105`) so a NEW brief written under the live name is recognized too, and extended the comment (`:94-101`) to record the 2026-08-15 retirement and the MEASURED 189/166 count. `:180`'s comment about `deepseek-v4-pro` (the MODEL-string fingerprint test) is untouched, correctly, since `P.MODEL`'s literal value never changed.
- `scripts/tests/test_dispatch_clock.py`: 11 before, 3 after (bare "deepseek", after excluding the 8 replaced with `pi-subagent-mode`). Updated the docstring, the six-case message text, the two `clock_mode()` checks, the two `POLICY[...]` direct-index checks, and the two `for mode in (...)` tuples, all to `pi-subagent-mode`. Added one new check (`:126-133`) proving a raw pin of the retired name still resolves through `ALIASES`.
- `dev/ORCHESTRATION.md`: 1 before, 1 after (unchanged occurrence is the new explanatory sentence I added). The one current-rule sentence naming the mode (`:32`) now reads `pi-subagent-mode`; I appended one sentence recording the rename and its date.
- `dev/PLAN.md`: 1 before, 1 after (same reason). The DD17 row's one sentence naming the mode now reads `pi-subagent-mode`, with a short parenthetical recording the rename. Nothing else in the row, and nothing in section 0 or section 11, was touched. `git diff dev/PLAN.md` shows exactly one changed line for my edit; a second, pre-existing uncommitted change to a section 11 row for this very task (`| LJ-1.285 | ... |`) was already present when I started and I did not touch it.

## HITS DELIBERATELY LEFT, and why

- `dev/JOURNAL.md:524` (inside the DD17 compaction entry, `#### DD17`, 2026-08-14). `'They are `deepseek-subagent-mode` and `in-harness-subagent-mode`, ... (owner, 2026-08-14, replacing normal and override ...).'` This is a VERBATIM QUOTE of the DD17 PLAN row's own sentence as it read that day, inside a section whose own preamble says "each is shown in its original sentence." Rewriting the quote would misrepresent what the row said on 2026-08-14. History; left unchanged.
- `dev/LESSONS.md:4104` and `:4107` (C-48, "the measurement" paragraph, 2026-08-15). Both are bare "deepseek" (not "-subagent-mode"): `"...are PEAK, where deepseek costs double..."` and `"...both \`pi/deepseek\` through \`herdr\`..."`. Neither names the mode identifier; both state a fact about the VENDOR (DeepSeek's real peak/off-peak pricing, and which model backed a specific historical dispatch). These are true today (the backend is still DeepSeek) and are historical besides (they describe two specific dispatches, `[LJ-1.272]` and `[LJ-1.273]`, at named timestamps). Left unchanged.
- `scripts/dispatch_policy.py:77` and `:91`. Both read "the pin that ran on 2026-08-14 was deepseek[-subagent-mode]." Both describe what the switch was literally set to on that date, before this rename. History; left unchanged.
- `scripts/dispatch_policy.py:21-22`, `:84-85`, `:121` ("deepseek is half price," "deepseek is dear"). Vendor pricing fact, not the mode identifier. Left unchanged; only the adjacent mode-name token in the same sentences was renamed.
- `scripts/check-dispatch-policy.py:180`. Describes the `P.MODEL` fingerprint test, which still reads `deepseek-v4-pro` because that literal value is unchanged. Correctly left as is.
- `archive/dev/JOURNAL-archived.md`. FROZEN, out of write scope, not edited. Its two hits (`:176`, `:191`, `:1806`) are all about the `deepseek-v4-pro` MODEL ID's own history (a backend rejection until early August 2026), not the mode name; none would need touching even if the file were writable.
- `agents/` (166 files, 189 occurrences of `deepseek-subagent-mode`). Out of write scope by the brief and by AGENTS.md (frozen records). Not edited. Verified they still resolve through the alias via test 3 and via `dispatch.py`'s live check below.
- `AGENTS.md`. Confirmed it does not mention `deepseek` (MEASURED: `git grep -c deepseek AGENTS.md` returns nothing), so DD19's guard does not fire and it was correctly left untouched, per the brief.
- `agents/tasks/LJ-1-285/LJ-1.285.md`'s own tier line (`sonnet` instead of `opus`). Not a `deepseek` hit at all, and not edited, for the reason given under test 3 above.

## WHAT `.claude/skills/codex-dispatch/dispatch.py` PRINTED for the frozen `[LJ-1.279]` brief

`[LJ-1.279]`'s tier line reads `tier: pi (deepseek-subagent-mode), **model \`deepseek-v4-pro\`**: ...` (`agents/tasks/LJ-1-279/LJ-1.279.md:3`).
```
$ .venv/bin/python .claude/skills/codex-dispatch/dispatch.py check agents/tasks/LJ-1-279/LJ-1.279.md --agda
dispatch: brief's tier line names mode `deepseek-subagent-mode` (canonically `pi-subagent-mode`) but `in-harness-subagent-mode` is IN FORCE right now. Run `python3 scripts/dispatch_policy.py` and read the clock line. Under `in-harness-subagent-mode` the default head is `opus` and the adversarial head is `pi`. Fix the tier line and the head together, or if this brief is a FROZEN record being re-checked rather than dispatched, use check-dispatch-policy.py instead, which judges a brief by the mode it names. This is a refusal, not a reminder: the clock moved and the orchestrator's memory did not
dispatch: tier line names head `pi`, and under `in-harness-subagent-mode` that head is correct ONLY for the adversarial case, while this dispatch declares `default`. The default head right now is `opus` on `in-harness`. If this really is that case, pass --adversarial and the assertion goes into the launch log. Otherwise take the head the table gives. This is a refusal, not a reminder: the clock decides, and it does not read the brief.
```
Exit code 1. This is dispatch.py's OWN standing refusal (the frozen brief's named mode does not match the clock's CURRENT state, which is PEAK right now) and it fires for any stale brief regardless of vendor naming; it is not new and not caused by the rename. The load-bearing evidence is the FIRST line: `(canonically \`pi-subagent-mode\`)`. `dispatch.py:800` calls `POLICY.canonical(named[0])` directly (`.claude/skills/codex-dispatch/dispatch.py:800,805`), so it picked up the new `ALIASES` entry with no edit of its own. The alias carries into this untracked consumer. Not edited, per the brief's instruction.

## CONFIRMATION: NO MODEL ID STRING WAS TOUCHED

MEASURED. `grep -n 'MODEL = \|FLASH = ' scripts/dispatch_policy.py` still shows:
```
215:MODEL = "deepseek-v4-pro"
236:FLASH = "deepseek-v4-flash"
```
`git diff -- scripts/dispatch_policy.py | grep -E "^[+-].*deepseek-v4"` returns NOTHING: no line containing `deepseek-v4-pro` or `deepseek-v4-flash` was added or removed anywhere in the diff. The two model-ID literals are byte-identical to `HEAD`. The only edits near them were the new "THE VENDOR SEAM" comment placed above `MODEL` (`scripts/dispatch_policy.py:210-214`), which names the two constants as the vendor-swap seam without changing either value.

## THE NAME COLLISION CHECK

MEASURED before any edit: `git grep -il "pi-subagent-mode" -- .` returned nothing, and `git grep -c "pi-subagent-mode" -- .` returned 0 matching files. `pi-subagent-mode` was free. No collision; the name proposed in the brief was used as given.

## DD4, one line

The renamed structure survives a third mode: `POLICY` and `CLOCK_STATES` are plain dicts keyed by mode name, `ALIASES` is a plain dict of retired name to live name, and nothing in `scripts/dispatch_policy.py` enumerates "exactly two" outside `PEAK_WINDOWS`'s own two-window shape; a third vendor or a third clock state adds one `POLICY` entry, one `CLOCK_STATES` mapping and, if it retires a fourth name, one `ALIASES` line, and touches no other file, because every consumer (`check-dispatch-policy.py`, `dispatch.py`, `dev/ORCHESTRATION.md`) reads the table rather than restating it.

## ARCHIVE USED (DD18)

- `archive/dev/JOURNAL-archived.md:191`: "DIED on a backend model rejection (deepseek-v4-pro unavailable until early [August 2026])". Read to confirm the archive's `deepseek` hits are entirely about the `MODEL` literal's own rejection history, not about a mode name, so nothing there needed a rename even if the file were writable (it is not; frozen, not edited).

## LITERATURE USED (DD18)

None. No mathematical literature bears on a dispatch-policy naming change; this task wrote no mathematics.

## SUMMARY

All six acceptance tests were run. Five pass cleanly (1, 2, 5, 6, and 4 via direct script execution since `pytest` is absent from `.venv`, MEASURED). Test 3 shows exactly one FAIL, MEASURED to be unrelated to the rename: it names `sonnet`, a head token that was never legal, inside this task's own brand-new brief, not inside any frozen or deepseek-named record. Zero model ID strings were touched (MEASURED by diff and by direct grep). `pi-subagent-mode` had zero prior occurrences (MEASURED), so there was no collision.
