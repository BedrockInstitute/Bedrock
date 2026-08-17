# AGENTS.md

The rulebook for AI coding agents on Bedrock. Every session loads it: Claude Code through the
root `CLAUDE.md`, other agents directly.

**This file is deliberately short.** It holds only what changes what you DO on a task. For
everything else, read one row in [Where the rules live](#where-the-rules-live).

> **This project is very early and this guide is incomplete.** No rule here does **not** mean no
> rule. When unsure, do **not** guess. Stop, ask the repository owner, and wait. A question
> always beats a confident wrong assumption.

## Boundaries

- **Always:** **write it generic**, so re-instantiation is nearly free; load the rules for your
  task with `rules.py --for <kind>` and read them **before** you write; run
  `make check` before committing; author every document in English first, then translate, then
  cross-check the Chinese and Japanese against each other for drift.
- **Always, DD4, the rule that has cost this project most:** **maximize the code the two proofs
  share, and write it generic.** One rule, two ends. It has **NO METRIC** by the owner's
  decision, because a shared-line count would be gamed the moment it gated anything. So it is
  stated in EVERY brief and answered in every return. **`check-dd4-stated.py` gates
  that a brief SAYS it**, reading the heading and never the content: the statement is
  mechanical, the substance is review. **A stop-line is never a reason to write fixed:** say so
  and stop for a re-price.
- **Always, write a controlled style, and the AUDIENCE picks it.** Each skill holds its full
  rule set; **Bedrock's own prose rules win over both.**
  - **To the repository owner: Chinese, in the Chinese Tech Doc Style.** Accuracy before
    rhetoric, one point per paragraph, one term per concept, conditions before the action they
    govern. **Never add a number, a date or a certainty the evidence does not give.** Skill:
    `.claude/skills/tech-doc-style-chinese/`, which is not a Chinese ASD-STE100.
  - **To everyone else: ASD-STE100 Simplified Technical English.** One meaning per word; one
    part of speech per word; active voice; simple tenses; one instruction per sentence; 20
    words or fewer for an instruction and 25 for a description; 3 words or fewer in a noun
    cluster; no ellipsis, so keep the subject, the verb and the article; 6 sentences or fewer
    in a paragraph. Skill: `.claude/skills/asd-ste100/`.
  - **ASD-STE100 applies to:** NEW developer documents under `dev/` and NEW per-directory
    `README.md` files; and all agent-to-agent text, so every brief and every report. **A
    dispatched agent writes ASD-STE100, never Chinese:** its reader is the orchestrator.
  - **Neither applies to:** mathematical prose; the documents under `docs/`; or the prose in
    a `.lagda.md` master. There, precision and voice decide the words.
  - **Nobody rewrites an existing document for this rule.** It binds new text only, so the
    written corpus costs nothing.
- **Ask first:** genuine architecture forks (surface them with a recommendation rather than
  charging ahead on one reading); adding a top-level directory (then add its `README.md`); a
  translation term not yet in `dev/glossary.toml`; **an edit to `AGENTS.md` itself** (DD19):
  show the owner the diff and the reason, get the ruling, then commit with a dated
  `AGENTS-diff-approved:` trailer, which `check-agents-guard.py` refuses to go
  without.
- **Never:** commit generated files (anything under `_build/`, woven mono-lingual `.lagda.md`)
  or a probe under `src/`; DELETE retired code (archive it); translate developer
  docs; use an em dash in any language; use half-width sentence punctuation in CJK prose;
  commit or print deployment secrets; add an unpinned or globally-installed dependency; add an
  in-file `SPDX-*` header.
- **Never leave an undeclared file in `_build/`.** Declare its class in
  `dev/build-manifest.toml` when you create it, or move it to a permanent home.

## Commands

- **`make check` is the gate before any commit.** It typechecks the masters, then runs the
  checkers wired into its `check:` target. **It does NOT run every checker in
  [scripts/](scripts/README.md)**, and several are deliberately outside it: `check-ratio.py`
  and `check-timing.py` because they cost minutes, and the advisory reports because a red gate
  would buy a pasted answer. **Read the `Makefile`'s `check:` line for the list that actually
  runs.** **Run it in the background, never in the foreground**: a cold typecheck takes about
  twelve minutes and must not block the session (`dev/PLAN.md` DD15). While you work, run the
  individual checks instead (`agda <file>`, `lint-prose.py <files>`).
- **`rules.py --for <kind>`** gives the mandatory rules for a build, probe,
  recon, rewrite or review, with each statement. `--grep <term>` finds the long tail by trigger
  word. **Never pick rules from memory.**
- **`ledger.py --brief`** is the only admissible source for a standing size
  figure. Never quote a number found in a paragraph.
- **`make venv`** once per clone, then **`make hooks`**. `make site` / `make serve` / `make gen`
  build the site. `lint-prose.py --fix <files>` auto-fixes most prose.

**Run every `python3` command as `.venv/bin/python`**, or run `make venv` first and let `make`
pick the interpreter.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11 or later.
[requirements-dev.txt](requirements-dev.txt) pins the dependencies and `make venv` installs
them into `.venv`.

## Where the rules live

Every rule has ONE canonical home, chosen by who enforces it. **A rule that no machine enforces
must name its enforcement point:** a gate, a brief section, a review step. A rule with no
enforcement point is a wish, and nothing is canonical twice. **Read the gloss column to decide
whether you need the file**, and believe the enforcement column when it says PARTIAL: a row
claiming more than its checker delivers is false safety.

| What it covers | Canonical home | Enforced by |
|---|---|---|
| **Measured engineering laws.** Performance, conversion, termination, inference, design, craft. Each exists because something cost time or died | `dev/LESSONS.md` | `rules.py` bundles; review |
| **Project rulings.** Architecture, process, retirement, numbered and dated. **The live series is `DD`**; a bare `D<n>` resolves only against the archive | `dev/PLAN.md` section 3; `archive/dev/DECISIONS-archived.md` | `check-rule-ids.py` resolves every code. **It cannot tell which series an author MEANT.** Dated records under `dev/` and `agents/` are exempt
| **Dispatch, slots, briefs, audits.** **RUN THE SWITCH, THEN TAKE THE HEAD IT GIVES. Never the reverse.** **This table names checkers by FILE NAME, never by path, so a directory move cannot make it wrong** (2026-08-15; `dispatch_policy.py` moved to `scripts/dispatch/` and this row survived it, `dev/PLAN.md:1177` did not). The brief's `tier:` line names the head and the model | Tables and modes: `dispatch_policy.py`, run it. Vendors: `dev/vendors.toml`. Operated by `dev/ORCHESTRATION.md` section 1. | **PARTIAL.** `check-dispatch-policy.py` **cannot see which head RAN**: an in-harness dispatch passes through no tool. **Only one case walks `dispatch.py`, so its refusals are live under one mode and dead under the other.**
| **Goal status and execution history.** **PLAN section 11 indexes every goal and every dispatch, one row each; JOURNAL holds what each dispatch found** | `dev/PLAN.md` section 11, `dev/JOURNAL.md` | PLAN section 6.0 rules 6 to 8 (register before starting, one row per code, 200-character cap); `check-task-index.py`; review |
| **Size ledger.** Standing, remaining, endpoint, check cost in seconds | `dev/ledger.toml`, whose header carries the caliber and why standing is never written down | `ledger.py --check` |
| **Code and chapter style.** OPTIONS header, import necessity, forbidden constructs | `dev/STYLE-agda.md` | **PARTIAL.** `lint-agda.py` covers the OPTIONS header, import necessity and the forbidden constructs. The rest of `dev/STYLE-agda.md` is review only |
| **Prose.** The em-dash ban, CJK full-width punctuation, `「」` quotes, CJK spacing and reflow, English-only inside ` ``agda ` fences | `dev/STYLE-i18n.md` | `lint-prose.py`, pre-commit hook; `--fix` handles most |
| **Literate Agda and i18n.** One master `.lagda.md` per module, the `<!--en--> <!--zh--> <!--ja-->` marker grammar, shared code fences, woven copies never committed | `dev/STYLE-i18n.md` | **PARTIAL.** `weave-i18n.py --check` catches stray, unterminated and unknown-language markers and markers inside fences; **it misses a mid-line marker and a fence inside a language group, and both pass green.** Agda enforces one master per module; `check-probes.py` catches woven copies
| **Term renderings.** A term the glossary lacks is settled by DD19's two-agent pipeline, never by choosing: a codex dossier, then an opus adversarial review. **Never add an entry yourself** | `dev/glossary.toml`, explained by `dev/GLOSSARY.md`; the protocol is `dev/ORCHESTRATION.md` section 8 | **PARTIAL.** `check-glossary.py` catches renderings on a term's `avoid` list and opt-in coverage. **The pipeline is enforced by review only:** nothing mechanical notices a term settled by choosing |
| **Documentation taxonomy.** User docs trilingual under `docs/<lang>/`, developer docs English only, `README.md` follows the user rule. Place a new document by audience; give every top-level directory a `README.md` | this row | review |
| **Licensing.** Three buckets declared centrally; a new file inherits AGPL-3.0 | `REUSE.toml`, texts in `LICENSES/` | `reuse lint` |
| **Deployment.** Automatic on merge to `main`; credentials are org secrets and contributors never handle them | `.github/workflows/` | n/a |
| **Route memos, digested literature** | `dev/memos/`, `dev/literature/` | n/a |
| **Agent reports and briefs.** Every dispatch writes one of each, and **both live in ONE directory per task, `agents/tasks/<CODE>/`, beside that task's probes**; retired tasks sit in `agents/tasks/archive/<CODE>/`. All tracked, all CC, all exempt from the prose linter because a record is never rewritten | `agents/README.md` | review |
| **What the project IS**: the theorem, the charter, the licences, who wrote it | [README.md](README.md), trilingual under `docs/` | n/a |
| **Where the work stands today**: the live status screen | `dev/PLAN.md` section 0; `ledger.py --brief` for the standing figures | n/a |

**`dev/LESSONS.md` BINDS NEW CODE.** Its entries are measurements, not opinions. When your work
discovers a new law, propose it with its measurement; **the orchestrator assigns the ID**
(owner's delegation, 2026-08-06). **A law is not admitted without its measurement**, whoever
numbers it.

## Working rules for dispatched agents

These bind an agent working against a pinned brief. The ORCHESTRATING agent writes the briefs,
audits the returns, wires the catalog and commits; it works to `dev/ORCHESTRATION.md`.

- **Never touch `src/Everything.lagda.md`.** The orchestrator wires it after auditing your work.
- **Never commit, never push.** Leave the working tree as your report describes it.
- **Run Agda under a heap cap**: `GHCRTS=-M8g agda <file>`, one process per agent. The quota is
  C-12's, never one machine-wide process (owner's correction, 2026-08-07). A task that measures
  check time gets a quiet machine. Report a heap exhaustion as a wall. Never raise the cap.
- **Write your deliverable incrementally.** Create the file early and fill it as answers land.
  Research held only in your head dies with your budget.
- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
- **A stop is a deliverable.** If the target is false, the price wrong, or the plan resting on a
  bad premise, give the evidence and stop. Refutations gave this project its best results.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site. An expected
  figure anchored on a comparable elsewhere is a hypothesis, not a price (`dev/LESSONS.md` P-l).

## Probes, gates and estimates

**Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work.** Build the
smallest decisive miniature and report GO or NO-GO with a price. A probe prices THIS setting; it
never re-proves what the literature or the delivered tree settles. **Write it in
`agents/tasks/<TASK>/`, beside your brief and your report, and run it there.** It is tracked, it
is never deleted, and **nothing typechecks it once your task closes, so run it while you can.**
**`src/` is forbidden**, and `check-probes.py` enforces that because `git add -f` walks past an
ignore rule. `dev/LESSONS.md` **D-1** is the rule.

**Gate every block before you fund it.** Measuring the widest unmeasured term is what turns a
projection into a price. **A build brief that cannot name that term, and the probe that measures
it, is not ready to send.**

**An estimate is ONE best-effort number, and it names its basis** (`dev/PLAN.md` DD8): a probe,
a delivered comparable or a survey. A size figure counts non-blank lines inside ` ``agda `
fences. Record an overage plainly and work it down where real compression exists.

**THE ROUTE is DD2 and DD5 and this file does not restate them.** **RULED:** both trophies,
`L ⊨ AC` and `L ⊨ GCH`, both stated in L, with a two-directional bridge. **CANDIDATE, ruled at
`[LJ-2.5]`:** the two towers and the bridge. **Say which is which in a brief**, because an agent
told the architecture is ruled will not report evidence against it.

**FOUR ARCHIVES, and surveying them is a brief section rather than a hope.** The retired route
left `archive/` for code and `archive/dev/` for the records, and `archive/dev/README.md` is the
table that says which of the four answers what. Every brief carries an **ARCHIVE** section
naming what may bear on the task; every return carries an **ARCHIVE USED** section naming what
it read and took, at `file:line`. **A brief that dispatches mathematics carries a LITERATURE
section too, and its return carries LITERATURE USED, including WHY NOT for anything it did not
use** (DD18); the dispatcher at `.claude/skills/codex-dispatch/dispatch.py` refuses a brief
missing either section. **That path is git-ignored, so a fresh clone does not have it and the
refusal is the orchestrator's to apply by hand.** `dev/LESSONS.md` is NOT
archived and still binds.

## Retiring code

Plan a retirement from the **rewrite side** (DD13). A consumer does not prove that a chapter must
stay: price the ideal form written fresh today, then compare. "We already paid for it" never
decides the question, in either direction.

**Archive retired code. Never delete it.** It goes to `archive/`, outside `src/`, so every gate is
blind to it by structure. Archived files are frozen; nothing imports across the boundary.
`dev/ARCHIVE.md` records for each module what it is, why it left, where it was last green,
**what it did right** (from measurement, not praise), and what would reopen it.
