# AGENTS.md

The rulebook for AI coding agents on Bedrock. Every session loads it: Claude Code through the
root `CLAUDE.md`, other agents directly.

**This file is deliberately short.** It holds only what changes what you DO on a task. For
everything else, read one row in [Where the rules live](#where-the-rules-live). A rulebook
nobody finishes reading binds nothing.

> **This project is very early and this guide is incomplete.** No rule here does **not** mean no
> rule. When unsure, do **not** guess. Stop, ask the repository owner, and wait. A question
> always beats a confident wrong assumption.

## Boundaries

- **Always:** **write it generic**, so re-instantiation is nearly free; load the rules for your
  task with `python3 scripts/rules.py --for <kind>` and read them **before** you write; run
  `make check` before committing; author every document in English first, then translate, then
  cross-check the Chinese and Japanese against each other for drift.
- **Always, DD4, the rule that has cost this project most:** **maximize the code the two proofs
  share, and write it generic.** One rule, two ends. It has NO metric and no checker by the
  owner's decision, so it is stated in EVERY brief and answered in every return, and that
  repetition is its only enforcement. **A stop-line is never a reason to write fixed:** say so
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
  `AGENTS-diff-approved:` trailer, which `scripts/check-agents-guard.py` refuses to go
  without.
- **Never:** commit generated files (anything under `_build/`, woven mono-lingual `.lagda.md`)
  or a probe under `src/`; DELETE retired code (archive it); translate developer
  docs; use an em dash in any language; use half-width sentence punctuation in CJK prose;
  commit or print deployment secrets; add an unpinned or globally-installed dependency; add an
  in-file `SPDX-*` header.
- **Never leave an undeclared file in `_build/`.** It is a temporary folder, not a rubbish bin.
  Declare its class in `dev/build-manifest.toml` when you create it, or move it to a permanent
  home.

## Commands

- **`make check` is the gate before any commit.** It typechecks the masters, then runs every
  checker in [scripts/](scripts/README.md). **Run it in the background, never in the
  foreground**: a cold typecheck takes about twelve minutes and must not block the session
  (`dev/PLAN.md` DD15). While you work, run the individual checks instead (`agda <file>`,
  `python3 scripts/lint-prose.py <files>`).
- **`python3 scripts/rules.py --for <kind>`** gives the mandatory rules for a build, probe,
  recon, rewrite or review, with each statement. `--grep <term>` finds the long tail by trigger
  word. **Never pick rules from memory.**
- **`python3 scripts/ledger.py --brief`** is the only admissible source for a standing size
  figure. Never quote a number found in a paragraph.
- **`make venv`** once per clone, then **`make hooks`**. `make site` / `make serve` / `make gen`
  build the site. `python3 scripts/lint-prose.py --fix <files>` auto-fixes most prose.

**Run every `python3` command as `.venv/bin/python`**, or run `make venv` first and let `make`
pick the interpreter.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11 or later.
[requirements-dev.txt](requirements-dev.txt) pins the dependencies and `make venv` installs
them into `.venv`.

## Where the rules live

Every rule has ONE canonical home, chosen by who enforces it. **A rule that no machine enforces
must name its enforcement point:** a gate, a brief section, a review step. A rule with no
enforcement point is a wish. Nothing is canonical twice: where this file restates a rule, the
other document rules and this one summarizes. **Read the gloss column to decide whether you need
the file, without opening it.** Most rows cost a red gate when broken; **the column says so where
enforcement is partial or absent**, because a row that claims more than its checker delivers
turns a rule into false safety.

| What it covers | Canonical home | Enforced by |
|---|---|---|
| **Measured engineering laws.** Performance, conversion, termination, inference, design, craft. Each exists because something cost time or died | `dev/LESSONS.md` | `scripts/rules.py` bundles; review |
| **Project rulings.** Architecture, process, retirement, numbered and dated. **The live series is `DD`**; the whole `D` series was archived on 2026-08-09 when the route changed, and a `D` citation still resolves against the archive | `dev/PLAN.md` section 3, and `archive/dev/DECISIONS-archived.md` for the retired series | `scripts/check-rule-ids.py`, which resolves every code AND refuses a bare `D<n>` where a `DD<n>` row exists, so the two series cannot be confused silently. **It cannot tell which series an author MEANT**; `dev/JOURNAL.md`, `dev/memos/` and `agents/` are exempt as dated records, and a file may declare its whole series once. The orchestrator; briefs |
| **Dispatch, slots, briefs, audits.** **DD17 has TWO versions and ONE switch picks between them:** `scripts/dispatch_policy.py`, which prints the version in force and why. The brief's `tier:` line names the head AND the version; if the justifying sentence will not write, take the head the table gives | `scripts/dispatch_policy.py`, operated by `dev/ORCHESTRATION.md` section 1 | **PARTIAL.** `check-dispatch-policy.py` reads every brief against the switch. It CANNOT see which head actually RAN: an in-harness dispatch passes through no tool |
| **Goal status and execution history.** **PLAN section 11 indexes every goal and every dispatch, one row each; JOURNAL holds what each dispatch found** | `dev/PLAN.md` section 11, `dev/JOURNAL.md` | PLAN section 6.0 rules 6 to 8 (register before starting, one row per code, 200-character cap); `scripts/check-task-index.py`; review |
| **Size ledger.** Standing, remaining, endpoint, check cost in seconds | `dev/ledger.toml`, whose header carries the caliber and why standing is never written down | `scripts/ledger.py --check` |
| **Code and chapter style.** OPTIONS header, import necessity, forbidden constructs | `dev/STYLE-agda.md` | **PARTIAL.** `lint-agda.py` covers the OPTIONS header, import necessity and the forbidden constructs. The rest of `dev/STYLE-agda.md` is review only |
| **Prose.** The em-dash ban, CJK full-width punctuation, `「」` quotes, CJK spacing and reflow, English-only inside ` ```agda ` fences | `dev/STYLE-i18n.md` | `scripts/lint-prose.py`, pre-commit hook; `--fix` handles most |
| **Literate Agda and i18n.** One master `.lagda.md` per module, the `<!--en--> <!--zh--> <!--ja-->` marker grammar, shared code fences, woven copies never committed | `dev/STYLE-i18n.md` | **PARTIAL.** `weave-i18n.py --check` catches stray, unterminated and unknown-language markers, and markers inside fences. It does NOT catch a mid-line marker, and does NOT catch a code fence inside a language group, which STYLE-i18n forbids: both pass green. Agda itself enforces one master per module; `check-probes.py` catches woven copies |
| **Term renderings.** A term the glossary lacks is settled by DD19's two-agent pipeline, never by choosing: a codex dossier, then an opus adversarial review. **Never add an entry yourself** | `dev/glossary.toml`, explained by `dev/GLOSSARY.md`; the protocol is `dev/ORCHESTRATION.md` section 8 | **PARTIAL.** `check-glossary.py` catches renderings on a term's `avoid` list and opt-in coverage. **The pipeline is enforced by review only:** nothing mechanical notices a term settled by choosing |
| **Documentation taxonomy.** User docs trilingual under `docs/<lang>/`, developer docs English only, `README.md` follows the user rule. Place a new document by audience; give every top-level directory a `README.md` | this row | review |
| **Licensing.** Three buckets declared centrally; a new file inherits AGPL-3.0 | `REUSE.toml`, texts in `LICENSES/` | `reuse lint` |
| **Deployment.** Automatic on merge to `main`; credentials are org secrets and contributors never handle them | `.github/workflows/` | n/a |
| **Route memos, digested literature** | `dev/memos/`, `dev/literature/` | n/a |
| **Agent reports and briefs.** Every dispatch writes one of each, and **both live in ONE directory per task, `agents/tasks/<CODE>/`, beside that task's probes**; retired tasks sit in `agents/tasks/archive/<CODE>/`. All tracked, all CC, all exempt from the prose linter because a record is never rewritten | `agents/README.md` | review |
| **What the project IS**: the theorem, the charter, the licences, who wrote it | [README.md](README.md), trilingual under `docs/` | n/a |
| **Where the work stands today**: the live status screen | `dev/PLAN.md` section 0; `scripts/ledger.py --brief` for the standing figures | n/a |

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
`agents/tasks/<TASK>/`, beside your brief and your report, and run it there.** It is tracked, it is never
deleted, and **nothing typechecks it once your task closes, so run it while you can.** **`src/`
is forbidden**, and `scripts/check-probes.py` enforces that because `git add -f` walks past an
ignore rule. `dev/LESSONS.md` **D-1** is the rule.

**Gate every block before you fund it.** Measuring the widest unmeasured term is what turns a
projection into a price. **A build brief that cannot name that term, and the probe that measures
it, is not ready to send.**

**An estimate is ONE best-effort number, and it names its basis** (`dev/PLAN.md` DD8): a probe,
a delivered comparable or a survey. A size figure counts non-blank lines inside ` ```agda `
fences. Record an overage plainly and work it down where real compression exists. Evidence can
move a technique; a number alone cannot.

**THE ROUTE** (`dev/PLAN.md` DD2 and DD5). **RULED:** both trophies, `L ⊨ AC` and `L ⊨ GCH`,
both stated in L, and a bridge goes BOTH ways. **CANDIDATE, ruled at `[LJ-2.5]`:** the L tower,
the J tower through rud, and the bridge. Say which is which in a brief; an agent told the
architecture is ruled will not report evidence against it. **DD4 above is the core constraint**,
and the total falls out of it, never from splitting or re-bucketing. **DD24** sets the quality
bar as cold seconds over in-fence lines. **DD23 freezes mathematical prose** until both trophies
land.

**FOUR ARCHIVES, and surveying them is a brief section rather than a hope.** The retired route
left `archive/` for code and `archive/dev/` for the records: `TASKS-archived.md` for what each
dispatch found, `JOURNAL-archived.md` for why, `DECISIONS-archived.md` for the rulings,
`STATUS-archived.md` for the goal table. Every brief
carries an **ARCHIVE** section naming what may bear on the task; every return carries an
**ARCHIVE USED** section naming what it read and took, at `file:line`. `dev/LESSONS.md` is NOT
archived and still binds.

## Retiring code

Plan a retirement from the **rewrite side**. A consumer does not prove that a chapter must stay.
First price the ideal form of the content, written fresh today, then compare. "We already paid
for it" never decides the question, in either direction.

**Archive retired code. Never delete it.** It goes to `archive/`, outside `src/`, so every gate
is blind to it by structure. Archived files are frozen and nothing imports across the boundary.
`dev/ARCHIVE.md` records for each module what it is, why it left, where it was last green,
**what it did right** (from measurement, not praise), and what would reopen it.
