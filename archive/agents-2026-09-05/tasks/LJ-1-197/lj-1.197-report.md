# LJ-1.197 report: do `build-manifest.toml` and `rules.toml` actually FIRE when they should

tier: pi (deepseek-subagent-mode). Every answer
is marked MEASURED or INFERRED. No Agda ran. No agent was dispatched. No
commit, no push, nothing staged.

## 0. LEAD, the counts

**7 rules FIRE. 5 rules are SILENT. 1 rule is UNPROVOKABLE.**

The abort criterion was fixed before the run (D-1). It is: if any rule does
not fire, that is the finding. **Five rules do not fire. The finding is real,
and the silent rules sit in the file the brief says is the class that cost
this project a backlog.**

The summary in three sentences.

- `build-manifest.toml`'s checker NAMES an undeclared file, and nothing else.
  It is not in `make check`, not in the hook, not in CI. It runs only when a
  human runs it. The rule it serves, "never leave an undeclared file", has no
  enforcement point anywhere (MEASURED).
- `rules.toml`'s mechanical checks fire in the gate: the cap, the dangling
  ID, the imported-routing and the DD4 statement. The kind derivation fires,
  and it misfires on two measured shapes: a wildcarded probe path derives as
  recon, and the word "adversarial" in a sentence about ANOTHER task derives
  the smallest bundle (MEASURED).
- The two files disagree with their own briefs about who validates what.
  `check-rule-ids.py` does not scan `dev/rules.toml` at all. The gate
  validator is `rules.py --check`, which `make check` runs. DD4 is not routed
  in `rules.toml`; the brief's premise that it is "routed into the build
  bundle" is false (MEASURED).

## 1. THE PROVOCATION TABLE

One row per rule. Each row names the violation, the exact command, and the
verdict. The violation was undone after every run. The tree is back to its
audited state (section 11).

| Rule | The violation I constructed | The command I ran | Fired? |
|---|---|---|---|
| BM-1. `check-build-manifest.py` names an undeclared file | `_build/scratch-undeclared.txt` | `.venv/bin/python scripts/check-build-manifest.py` | **FIRES.** Prints `UNDECLARED, 1 file(s)` and the path, exit 0. With `--check`, exit 1 (MEASURED) |
| BM-2. "Never leave an undeclared file in `_build/`" stops something | the same file, plus a search of the whole gate | `grep -rn "check-build-manifest" Makefile scripts/git-hooks/ .github/` | **SILENT.** No match. `make check` (`Makefile:36`) has no manifest target. Nothing runs the checker. The default mode exits 0 while it names the violation (MEASURED) |
| BM-3. Each class's `delete_when` / `promote_when` conditions | a file in the `evidence` class, which the checker cannot identify | read `scripts/check-build-manifest.py:12-16` | **SILENT.** The checker "never deletes, never moves, and NEVER FAILS A GATE" by its own docstring. No lifecycle condition is enforced by anything (MEASURED) |
| BM-4. `evidence` promotes IMMEDIATELY when a document cites it | the same undeclared file, described as evidence | the BM-1 command | **SILENT.** The only firing is BM-1's naming. Nothing reacts to a citation of a measurement in `_build/` (MEASURED) |
| BM-5. `working` deletes when the task-index row stops saying live | none: no `_build/` file is `working` class today, and no glob points at it | read `dev/build-manifest.toml:58-78` and `scripts/check-probes.py`'s scope | **SILENT.** No sweep exists for `_build/` task scratch. `check-probes.py` covers `agents/tasks/`, never `_build/` (MEASURED) |
| BM-6. "Declare its class when you create it" | the same undeclared file, created | the BM-1 command | **SILENT at creation.** Nothing fires when a file is written. The naming fires later, by hand. The README regeneration (`--readme`) is manual too (MEASURED) |
| RT-1. A bundle holds at most `max_ids = 12` | a scratch copy of `rules.toml` with a 13th real ID in `bundle.build` | `rules.py --check` driven over the scratch (same code path, import reassign) | **FIRES.** `DEFECT: bundle.build holds 13 ids, over the cap of 12`, exit 1 (MEASURED) |
| RT-2. No dangling ID in a bundle or a trigger | a scratch copy with fake `R-999` in `bundle.review` and in a new trigger | the same `--check` path | **FIRES.** Two DEFECT lines, exit 1 (MEASURED) |
| RT-3. The kind is DERIVED from the write scope, and a brief missing its bundle is refused | three real briefs of different kinds, plus two provocation shapes | `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py check <brief>` and `.venv/bin/python scripts/rules.py --for-scope <path>` | **FIRES, and misfires.** See section 5.3 (MEASURED) |
| RT-4. A trigger resolves through `rules.py --grep` | none: every term must return something | `rules.py --grep <term>` for all 55 terms | **FIRES.** All 55 return non-empty. All IDs resolve, per `--check` (MEASURED) |
| RT-5. An imported LESSONS entry is routed | a scratch `rules_data` with empty routing | `check_imported_routing()` driven over the real LESSONS text | **FIRES.** Flags `P-i` as imported and unrouted. Clean on the real tree (MEASURED) |
| RT-6. A brief states DD4 | a scratch brief without a `## DD4` heading | `.venv/bin/python scripts/check-dd4-stated.py` and `dispatch.py check` on the scratch | **FIRES, both gates.** `check-dd4-stated` exits 1; `dispatch` refuses with the DD4 message (MEASURED) |
| RT-7. "Absence here means not routed, which is legal" | none: it is a design invariant, not a catchable violation | read `dev/rules.toml:62` | **UNPROVOKABLE.** Its enforcement is the cap, which is RT-1 (MEASURED) |

## 2. THE SILENT RULES, RANKED BY WHAT THEY GUARD

**First: the undeclared-file promise (BM-2).** This is the rule the whole file
exists to serve (`AGENTS.md:54-55`). The checker names a violation and exits
0. Nothing calls the checker. The brief's own account is confirmed: on
2026-08-14 the orchestrator recreated `_build/briefs/` to satisfy a stale
pinning check, the checker NAMED those files undeclared, nothing failed,
nothing blocked, and the owner caught the mistake, not the tool. The record is
`dispatch.py:644-661`, which calls the workaround "forbidden by AGENTS.md".
The checker's last line, "Advisory only. This is not a gate."
(`check-build-manifest.py:166`), is a true confession.

**Second: the evidence-promote rule (BM-4).** It guards the exact class that
produced the [LJ-1.132] backlog: a measurement cited by `dev/ledger.toml`
while sitting one `make clean` from deletion (`build-manifest.toml:44-57`).
The class worked once: its three cold profiles were promoted to
`dev/measurements/` (`l3.32-coldprofile-2026-08-06.txt`,
`l3.32-coldprofile-2026-08-09.txt`, `l3.32-t256-belowlim-profile.txt`).
Nothing would fire today if a fresh measurement was cited from `_build/`.

**Third: the working-delete rule (BM-5).** It guards stale task scratch in
`_build/`. It has no subject today and no glob. `check-probes.py` enforces the
probe half of the same rule for `agents/tasks/`, so a `_build/` working file
would sit until a human noticed it.

**Fourth: the class lifecycle conditions (BM-3).** Every class's
`delete_when` and `promote_when` are prose for a human. The checker cannot
tell evidence from exhaust and says so (`check-build-manifest.py:12-16`).
These rules fire only in review, which means they fire only when a reviewer
already suspects.

**Fifth: the declare-at-creation duty (BM-6).** The positive form of BM-2.
Nothing fires at the moment of creation, which is the moment the rule names.

## 3. THE MOMENT EACH RULE MUST FIRE, AND WHAT FIRES THEN

This is the owner's real question. A rule that fires only when somebody runs a
command by hand fires when that person already suspected something.

| Rule | The moment it must fire | What fires at that moment |
|---|---|---|
| BM-1, BM-6 | a file is written to `_build/` | nothing automatic. A human must run the checker later (MEASURED) |
| BM-2 | the same moment | nothing. Not in `make check` (MEASURED) |
| BM-3, BM-4, BM-5 | a lifecycle event: a citation, a task closure, a deletion | nothing. Review only (MEASURED) |
| RT-1, RT-2 | `rules.toml` is edited | the next `make check`. `rules.py --check` runs in the `ruleids` target (`Makefile:116-117`). This is the gate before any commit, so it fires at commit time, not edit time (MEASURED) |
| RT-3 | a brief is written | `dispatch.py` refuses, but ONLY on the codex path. The docstring says it in as many words: "THIS BINDS THE CODEX PATH ONLY. An in-harness dispatch does not pass through this file" (`dispatch.py:2049-2051`). The DD17 override sends every default dispatch in-harness, so the moment usually passes with no fire (MEASURED) |
| RT-4 | the orchestrator searches for a rule by term | `rules.py --grep`, by hand, at that moment. Nothing forces the search (MEASURED) |
| RT-5 | an imported lesson lands unrouted | the next `make check` (`devdocs` target) (MEASURED) |
| RT-6 | a brief is written | `dispatch.py` on the codex path and `check-dd4-stated.py` in `make check` (`Makefile:144-145`). The gate half fires for every brief (MEASURED) |

## 4. WHAT `dev/build-manifest.toml` CLAIMS, ANSWERED

**Q1. Does an undeclared file make the checker fire?** YES. It names the file
in both modes. Default mode exits 0. `--check` mode exits 1. (MEASURED)

**Q2. Is the checker a gate or a report?** A report. Its own last line says
"Advisory only. This is not a gate." (`check-build-manifest.py:166`). `make
check` does not run it at all: `Makefile:36` has no manifest target, and
`grep -rn "check-build-manifest" Makefile scripts/git-hooks/ .github/` finds
nothing. `AGENTS.md:49-55` promises the rule as a "Never", and the table that
names enforcement points has no row for it. So the promise has no enforcement
point, which `AGENTS.md` itself calls a wish. (MEASURED)

**Q3. The 2026-08-14 `_build/briefs/` account.** Confirmed. The sequence:
`dispatch.py`'s pinning check still demanded `_build/briefs/` after the briefs
moved to `agents/tasks/`; the orchestrator recreated the directory to satisfy
it; the checker listed the files as undeclared; nothing failed and nothing
blocked; the owner caught it. The record is `dispatch.py:644-661`, which says
the broken path "stays green while nothing walks it". `_build/briefs/` is gone
today. The meaning for enforcement: the checker's naming is the whole
deliverable, and it reaches a human only when that human runs it. (MEASURED)

**Q4. Are any classes dead?** No class is dead in the sense of unusable.
Measured today: `toolchain` 397 files, `protected` 23, `runtime` 2.
`exhaust` has entries but zero current files; it reappears on `make site`, so
it is dormant, not dead. `evidence` has no entry and its known members were
promoted to `dev/measurements/`. `working` has no entry, no glob, and no
member ever: it is a slot. `foreign` declares its own emptiness:
`members = "NONE today"` (`build-manifest.toml:95-100`), the owner deleted
its one member on 2026-08-13. The one class with no subject at all is
`working`, and its subject was obviated by [LJ-1.142] moving probes to
`agents/tasks/` (MEASURED).

## 5. WHAT `dev/rules.toml` CLAIMS, ANSWERED

### 5.1 Does the cap fire?

YES. A scratch copy with a 13th ID in `bundle.build` produces
`DEFECT: bundle.build holds 13 ids, over the cap of 12` and exit 1. The cap is
called "THE DESIGN" in the file's own header (`rules.toml:26-30`). The build
bundle sits exactly at 12 today. (MEASURED)

### 5.2 Does a dangling ID fire?

YES, in both places. A fake `R-999` in a bundle and in a trigger produces two
DEFECT lines and exit 1. (MEASURED)

**One attribution in the brief is wrong, and it matters.** The brief says
`rules.toml` is "validated by `scripts/check-rule-ids.py`". It is not.
`check-rule-ids.py`'s default scan is `dev/*.md` plus `AGENTS.md`
(`check-rule-ids.py:317-321`). `dev/rules.toml` is a `.toml` file and is
never scanned. I proved it. `rules.py --check` over the dangling scratch failed with two
defects, while the default `check-rule-ids.py` run reported clean without
ever opening the file. The gate validator of `rules.toml` is
`rules.py --check`, which `make check` runs at `Makefile:117`.
`check-rule-ids.py` catches a fake ID only if the file is handed to it
explicitly. (MEASURED)

### 5.3 Does the kind derivation work?

**It fires, and it misfires. There are two implementations, and they have
drifted.**

The derivation in force is `dispatch.py`'s `brief_kind`
(`dispatch.py:2077-2142`), used by `rule_bundle_defects`
(`dispatch.py:2146-2181`). The derivation documented in `rules.py` is
`kind_for_scope` (`rules.py:69-74`), reachable only through
`--for-scope`, which nothing calls automatically. Two copies of one rule is
the C-26 drift class the dispatch comment claims to have prevented
(`dispatch.py:2082-2084`).

Measured on real briefs:

| Brief | What a reader would say | `dispatch.py brief_kind` | `rules.py --for-scope` |
|---|---|---|---|
| LJ-1.103 (`src/L/BoundedSubset.lagda.md`) | build | build | build |
| LJ-1.105 (`src/L/Condensation.lagda.md`) | build | build | build |
| LJ-1.118 (`src/ProbeLJ1118*.agda` only, has ProbeLJ1118A.agda) | probe | **recon** | probe |
| LJ-1.121 (same shape) | probe | **recon** | probe |
| LJ-1.131 (pricing study, report only, "Do NOT make it") | recon | **review** | recon |
| LJ-1.197 (this audit) | recon | recon | recon |

Two misfires, both measured.

**Misfire 1: the wildcard.** A scope that writes `src/ProbeLJ1118*.agda`
contains the word "Probe", so `kind_for_scope` says probe. `brief_kind`'s
regex is `src/Probe[\w.-]*\.(?:agda|lagda\.md)` and the `*` in the brief's
path is not in `[\w.-]`, so the pattern fails and the brief falls to recon
(`dispatch.py:2126-2132`). `dispatch.py check` refused LJ-1.118 for C-42,
which is the recon bundle's rule, not the probe bundle's
(`bundle.probe` holds D-1, P-i, C-12, R-40). A probe brief demanded the wrong
bundle. (MEASURED)

**Misfire 2: the review keyword.** `brief_kind` returns review when the word
"adversarial" appears in the first 1200 characters (`dispatch.py:2141-2142`).
LJ-1.131 contains that word at line 21, describing `[LJ-1.129]`, a DIFFERENT
task's review. LJ-1.131 is a pricing recon. It derived the smallest bundle
(review holds 3 rules, recon holds 5) and passed. (MEASURED)

**The unreachable bundle.** No derivation can produce `rewrite`. Both
functions return only build, probe, recon or review. A rewrite brief (it
replaces delivered content, `rules.toml:51-54`) writes `src/` masters and so
derives as build, and receives the 12-rule build bundle instead of the
7-rule rewrite bundle. There is no live rewrite brief to test. This is
INFERRED from the code: the two functions have no branch that returns
`rewrite`.

**The refusal mechanism itself fires.** `dispatch.py check` refused LJ-1.118
and LJ-1.121 today for missing mandatory rules, and accepted LJ-1.103,
LJ-1.105, LJ-1.131, LJ-1.184, LJ-1.188 and LJ-1.197. The 2026-08-14 refusal
episode the brief names is recorded in `agents/tasks/LJ-1-188/lj-1.188-report.md:170-173`
and in `dispatch.py:644-661`: "it had refused EVERY dispatch since the briefs
moved into agents/tasks/". (MEASURED)

### 5.4 Do the triggers resolve?

YES. All 55 terms in `[triggers]` return a non-empty bundle from
`rules.py --grep`. Every ID they name resolves against `dev/LESSONS.md`, which
`rules.py --check` proves. A trigger that returns nothing does not exist here.
The limitation is the moment: `--grep` fires only when a human runs it.
(MEASURED)

### 5.5 Is any routed rule unreachable in practice?

93 of 145 LESSONS entries sit in no bundle and under no trigger. The file
calls that legal (`rules.toml:62`), and 92 of them are cited somewhere in the
corpus or a brief, so a brief can still reach them by name. **One entry is
truly unreachable**: `I-9` is unrouted and cited nowhere in the live corpus.
`check-dev-docs.py --sweep` reports it: "not routed in dev/rules.toml and
cited nowhere in the corpus or any brief". Its only mention is an archived
dossier as the string "P-I-9". No bundle, no trigger, no citation: no brief
would ever receive I-9. (MEASURED)

## 6. DD4: the gate versus the routing

The brief's premise is false. It says DD4 "is routed by `rules.toml` into the
build bundle". `grep -c "DD4" dev/rules.toml` returns 0. `rules.py --for
build` does not emit DD4. DD4 is a PLAN decision, and `rules.toml` routes
LESSONS entries only, so it structurally cannot carry DD4.

The two enforcement points that DO exist agree with each other, and both
gates fire. `check-dd4-stated.py` requires a `## DD4` heading in every live
brief (`check-dd4-stated.py:65`), grandfathered twelve frozen ones, and exits
1 on a brief without it. `dispatch.py`'s `dd4_defects` refuses every brief
without DD4 or without both halves of its statement (`dispatch.py:1982-2016`).
I provoked both with a scratch brief: `check-dd4-stated` reported it, and
`dispatch check` refused it with the DD4 message.

So the answer to the brief's question: the routing and the gate do NOT agree
about which briefs must carry DD4. The gate says every brief. The routing
says nothing, because it cannot say anything. An agent that obeys only
`rules.py --for <kind>` is never told about DD4 and is refused at dispatch
anyway. The gate is the moment that fires; the routing is silent. (MEASURED)

## 7. ARE THE PARTIAL MARKS STILL ACCURATE?

Yes. All four. The table is `AGENTS.md:94,97,99,100`.

- **Dispatch, slots, briefs, audits** (`AGENTS.md:94`). Accurate. I measured
  the admission: in-harness dispatches pass through no tool
  (`dispatch.py:2049-2051`), and `check-dispatch-policy.py` cannot see which
  head ran. (MEASURED)
- **Code and chapter style** (`AGENTS.md:97`). Accurate per
  `scripts/README.md`: `lint-agda.py` covers the OPTIONS header, import
  necessity and the forbidden constructs; the rest is review only.
  (INFERRED, from the README's own claim)
- **Literate Agda and i18n** (`AGENTS.md:99`). Accurate. I read the canonical
  implementation. `MARKER_RE` anchors the marker to the whole line
  (`i18n_markers.py:21`), so a mid-line marker is silently treated as prose.
  `lint_markers` (`i18n_markers.py:105-124`) has no check for a code fence
  inside a language group. Both "does NOT" claims hold. (MEASURED)
- **Term renderings** (`AGENTS.md:100`). Accurate per `scripts/README.md`:
  the glossary checker catches avoid-list renderings and opt-in coverage; the
  two-agent pipeline is review only. (INFERRED)

## 8. ARCHIVE USED

- `dev/rules.toml` WHOLE, header included. `dev/build-manifest.toml` WHOLE,
  header included. The two files are the subject of the audit.
- `scripts/rules.py` WHOLE. `scripts/check-build-manifest.py` WHOLE.
  `scripts/check-rule-ids.py` WHOLE. `scripts/check-dd4-stated.py` WHOLE.
  The four checkers the brief named.
- `scripts/check-dev-docs.py:169-243`, the imported-routing subcheck, a fifth
  consumer of `rules.toml`.
- `scripts/i18n_markers.py:21-124`, for the PARTIAL mark on literate Agda.
- `.claude/skills/codex-dispatch/dispatch.py:618-720,1982-2181`, the brief-time
  enforcement: `launch_defects`, `dd4_defects`, `brief_kind`,
  `rule_bundle_defects`, and the `_build/briefs/` episode record.
- `Makefile:36,114-117,144-145`, for what `make check` actually runs.
- `AGENTS.md:49-55,94,97,99,100`, the rule and the PARTIAL rows.
- `agents/tasks/LJ-1-188/lj-1.188-report.md:160-190`, the 2026-08-14 refusal
  episode.
- `dev/measurements/`, the promoted evidence-class files.
- The git history of `dev/build-manifest.toml` (`265bf0d` first version), for
  the class-entry history.

## 9. LITERATURE

Not this task's subject. Nothing in `dev/literature/` bears on a config
routing audit. DD18 is satisfied by this one line.

## 10. DD4

This task touches no shared proof code, and the audit itself is written
generic: every finding names the file and line it came from, so the same
provocation runs on any future routing file. The two proofs share nothing
here; the shared asset is the provocation method, and I used it on every rule
rather than reading any rule twice.

## 11. PROHIBITIONS, ANSWERED

- No edit to `dev/build-manifest.toml`, `dev/rules.toml`, any checker, any
  `dev/` document, `src/`, or any brief or report but my own. The scratch
  files lived in `agents/tasks/LJ-1-197/` and are deleted.
- No staging, no commit, no push. `git status` at the end shows only the
  sibling's `agents/tasks/LJ-1-196/` and this report, both untracked.
- No Agda run, no dispatch. `GHCRTS` was never needed.
- No `git checkout`, `stash`, `reset` or `clean`.

## 12. WORKING TREE STATE

The tree changed under me once, and not by my hand. At the start of the audit
`git status --short` showed `M dev/PLAN.md`, `?? agents/tasks/LJ-1-196/` and
`?? agents/tasks/LJ-1-197/`. At 10:58 a commit landed: `321693e [LJ-1.197]
Audit whether two config files FIRE, and a correction I owe`, which carried
the brief and its PLAN row. My own actions created and deleted only
`_build/scratch-undeclared.txt` and two scratch copies of `rules.toml`, all
removed. `_build/` is exactly as found: `.last-gate`, `2.8.0/`,
`literature/`, `README.md`, `tools/`. The final tree holds the sibling's
untracked `agents/tasks/LJ-1-196/` and my untracked report. Nothing of mine
is staged. I confirm the tree is as the audit left it, and I say plainly that
a commit by the orchestrator landed while I worked.
