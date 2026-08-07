# AGENTS.md

The rulebook for AI coding agents on Bedrock. Every session loads it: Claude Code through the
`@AGENTS.md` import in the root `CLAUDE.md`, other agents directly.

**This file is deliberately short.** It holds only what changes what you DO on a task. For
everything else, read one row in [Where the rules live](#where-the-rules-live). A rulebook
nobody finishes reading binds nothing.

> **This project is very early and this guide is incomplete.** No rule here does **not** mean no
> rule. When unsure, do **not** guess. Stop, ask the repository owner, and wait. A question
> always beats a confident wrong assumption.

## Boundaries

- **Always:** **write it generic** (structure-generic at full strength, so re-instantiation is
  nearly free; a stop-line is never a reason to write fixed: say so and stop for a re-price);
  load the rules for your task with `python3 scripts/rules.py --for <kind>` and read them
  **before** you write; run `make check` before committing; author every document in English
  first, then translate, then cross-check the Chinese and Japanese against each other for
  drift; verify a load-bearing assumption cheaply before heavy or hard-to-reverse work; state
  any size projection in both calibers.
- **Always, write ASD-STE100 Simplified Technical English.** The rules: one meaning per word;
  one part of speech per word; active voice; simple tenses; one instruction per sentence; 20
  words or fewer for an instruction and 25 for a description; 3 words or fewer in a noun
  cluster; no ellipsis, so keep the subject, the verb and the article; 6 sentences or fewer in
  a paragraph.
  - **It applies to:** every message to the repository owner, **in whatever language the owner
    writes to you**; NEW developer documents under `dev/` and NEW per-directory `README.md`
    files; the dashboard; and all agent-to-agent text, which means each brief this project
    sends and each report an agent returns.
  - **It does NOT apply to:** mathematical prose; the reader-facing documents under `docs/`;
    or the prose in a `.lagda.md` master. In those places precision and voice decide the
    words.
  - **Nobody rewrites an existing document for this rule.** It binds new text only. This keeps
    the cost at zero for the corpus that is already written.
  - The full rule set, with worked examples, is the skill at `.claude/skills/asd-ste100/`.
- **Ask first:** genuine architecture forks (surface them with a recommendation rather than
  charging ahead on one reading); adding a top-level directory (then add its `README.md`); a
  translation term not yet in `dev/glossary.toml`; **an edit to `AGENTS.md` itself** (D34):
  show the owner the diff and the reason, get the ruling, then commit with a dated
  `AGENTS-diff-approved:` trailer, which `scripts/check-agents-guard.py` refuses to go
  without.
- **Never:** commit generated files (anything under `_build/`, woven mono-lingual `.lagda.md`)
  or probe files (`src/Probe*.agda`); DELETE retired code (archive it); translate developer
  docs; use an em dash in any language; use half-width sentence punctuation in CJK prose;
  commit or print deployment secrets; add an unpinned or globally-installed dependency; add an
  in-file `SPDX-*` header.

## Commands

- **`make check` is the gate before any commit.** It typechecks the masters, then runs every
  checker in [scripts/](scripts/README.md): i18n markers, prose, Agda style, rule-citation
  resolution, glossary, size ledger, the never-commit rule, whole-tree invariants, and `reuse
  lint`. **Run it in the background, never in the foreground**: a cold typecheck takes about
  twelve minutes and must not block the session (`dev/PLAN.md` D28). While you work, run the
  individual checks instead (`agda <file>`, `python3 scripts/lint-prose.py <files>`).
- **`python3 scripts/rules.py --for <kind>`** gives the mandatory rules for a build, probe,
  recon, rewrite or review, with each statement. `--grep <term>` finds the long tail by trigger
  word. **Never pick rules from memory.** Memory drifted for five days while an imported
  playbook sat uncited in 102 of 112 briefs.
- **`python3 scripts/ledger.py --brief`** is the only admissible source for a standing size
  figure. Never quote a number found in a paragraph.
- **`make venv`** once per clone, then **`make hooks`**. `make site` / `make serve` / `make gen`
  build the site. `python3 scripts/lint-prose.py --fix <files>` auto-fixes most prose.

**Run every `python3` command as `.venv/bin/python`**, or run `make venv` first and let `make`
pick the interpreter. The scripts need `tomllib` from Python 3.11: with an older system
`python3` the FIRST command in this file dies, and `[L3.32-T120]` lost two runs to exactly
that.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11 or later.
[requirements-dev.txt](requirements-dev.txt) pins the dependencies and `make venv` installs
them into `.venv`.

## Where the rules live

Every rule has ONE canonical home, chosen by who enforces it. This table says where a rule is,
and where a new one goes. **A rule that no machine enforces must name its enforcement point:**
a gate, a brief section, a review step. A rule with no enforcement point is a wish. Nothing is
canonical twice: where this file restates a rule, the other document rules and this one
summarizes.

**Read the gloss column to decide whether you need the file, without opening it.** A checker in
`make check` enforces most rows, so you pay for a lapse with a red gate. **The column says so
where enforcement is partial or absent.** A row that claims more than its checker delivers is
worse than no row: it turns a rule into false safety.

| What it covers | Canonical home | Enforced by |
|---|---|---|
| **Measured engineering laws.** Performance, conversion, termination, inference, design, craft. Each exists because something cost time or died | `dev/LESSONS.md` | `scripts/rules.py` bundles; review |
| **Project rulings.** Architecture, process, retirement, numbered and dated | `dev/PLAN.md` section 3 | the orchestrator; briefs |
| **Dispatch, slots, briefs, audits.** How work is sent out and how a return is checked | `dev/ORCHESTRATION.md` | the orchestrator, at the points it names |
| **Goal status and execution history.** A ruling is a PLAN row, an episode is a JOURNAL entry. **PLAN section 11 is the complete index of goals and of dispatched tasks, one row each; JOURNAL holds what each dispatch actually found** | `dev/PLAN.md` section 11, `dev/JOURNAL.md` | PLAN section 6.0 rules 6 to 8 (register before starting, one row per code, 200-character cap); `scripts/check-task-index.py`; review |
| **Size ledger.** Standing, remaining, endpoint, check cost in seconds | `dev/ledger.toml`, whose header comment carries the caliber, how a row goes missing, and why standing is never written down | `scripts/ledger.py --check` |
| **Code and chapter style.** OPTIONS header, import necessity, forbidden constructs | `dev/STYLE-agda.md` | **PARTIAL.** `lint-agda.py` covers the OPTIONS header, import necessity and the forbidden constructs. The rest of `dev/STYLE-agda.md` is review only |
| **Prose.** The em-dash ban, CJK full-width punctuation, `「」` quotes, CJK spacing and reflow, English-only inside ` ```agda ` fences | `dev/STYLE-i18n.md` | `scripts/lint-prose.py`, pre-commit hook; `--fix` handles most |
| **Literate Agda and i18n.** One master `.lagda.md` per module, the `<!--en--> <!--zh--> <!--ja-->` marker grammar, shared code fences, woven copies never committed | `dev/STYLE-i18n.md` | **PARTIAL.** `weave-i18n.py --check` catches stray, unterminated and unknown-language markers and markers inside fences. It does NOT catch a marker embedded mid-line, and it does NOT catch a code fence inside a language group, which STYLE-i18n forbids: both pass green. One-master-per-module is enforced by Agda itself; woven copies are caught by `check-probes.py`, not by this checker |
| **Term renderings.** A term the glossary lacks is settled by the D35 pipeline, never by choosing: a codex dossier with literature provenance, then an opus adversarial review; a PASS lands the entry, a FAIL escalates it to the owner. Use it consistently, NAME it in your report, **never add an entry yourself** | `dev/glossary.toml`, explained by `dev/GLOSSARY.md`; the protocol is `dev/ORCHESTRATION.md` section 8 | **PARTIAL.** `check-glossary.py` catches renderings on a term's `avoid` list and opt-in coverage. **The dossier rule is enforced by review only** (`dev/ORCHESTRATION.md` section 6 step 7 dispatches the dossier): nothing mechanical notices a term settled by choosing |
| **Documentation taxonomy.** User docs trilingual under `docs/<lang>/`, developer docs English only, `README.md` follows the user rule. Place a new document by audience; give every top-level directory a `README.md` | this row | review |
| **Licensing.** Three buckets declared centrally; a new file inherits AGPL-3.0 | `REUSE.toml`, texts in `LICENSES/` | `reuse lint` |
| **Deployment.** Automatic on merge to `main`; credentials are org secrets and contributors never handle them | `.github/workflows/` | n/a |
| **Tooling.** What every script does and when to run it | [scripts/README.md](scripts/README.md) | n/a |
| **Route memos, digested literature, probe reports** and the briefs that produced them | `dev/memos/`, `dev/literature/`, `_build/` | n/a |
| **What the project IS**: the theorem, the charter, the licences, who wrote it | [README.md](README.md), trilingual under `docs/` | n/a |
| **Where the work stands today**: the live status screen | `dev/PLAN.md` section 0, and `make dashboard` for the owner's board | n/a |
| **What every contributing agent must know** | this file | loaded at session start |

**`dev/LESSONS.md` BINDS NEW CODE.** Its entries are measurements, not opinions. When your work
discovers a new law, propose it with its measurement; **the orchestrator assigns the ID**
(owner's delegation, 2026-08-06): the P series uses letters, the R, T, I, D and C series use
numbers, and the next free one is the ID. A law is not admitted without its measurement,
whoever numbers it.

## The one rule that has cost this project most

**Write content structure-generic rather than fixed to a carrier.** It is more expensive on the
first instance and cheaper from the second onward, which is exactly why it gets skipped under a
deadline. `dev/PLAN.md` D29 requires the question to be asked at three moments: when a recon is
dispatched, when a build is dispatched, and when a route is planned.

## Working rules for dispatched agents

These bind an agent that works against a pinned brief. The ORCHESTRATING agent writes the
briefs, audits the returns, wires the catalog and commits; it works to `dev/ORCHESTRATION.md`.

- **Never touch `src/Everything.lagda.md`.** The orchestrator wires it after auditing your work.
- **Never commit, never push.** Leave the working tree as your report describes it.
- **Run Agda under a heap cap**: `GHCRTS=-M8g agda <file>`, one process per agent. The
  concurrency quota is C-12's, never one machine-wide process (owner's correction,
  2026-08-07). A task that measures check time gets a quiet machine. Report a heap
  exhaustion as a wall. Never raise the cap.
- **Write your deliverable incrementally.** Create the file early and fill it as answers land.
  Research held only in your head dies with your budget.
- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
- **A stop is a deliverable.** If the target is false, or the price is wrong, or the plan rests
  on a bad premise, give the evidence and stop. Refutations gave this project some of its most
  valuable results.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site. An expected
  figure anchored on a comparable elsewhere is a hypothesis, not a price (`dev/LESSONS.md` P-l).

## Probes, gates and estimates

**Verify the load-bearing assumption cheaply before heavy or hard-to-reverse work.** Build the
smallest decisive miniature. Report GO or NO-GO with a price. Throw it away. A probe prices what
THIS setting costs; it never re-proves what the literature or the delivered tree settles. Nobody
commits a probe (`scripts/check-probes.py` enforces both halves, because `git add -f` walks past
an ignore rule).

**Gate every block before you fund it.** This is arithmetic, not caution: a green gate moves the
term from the 3x class to about 1.3x and lowers the top of the band, which decides whether a
projection fits. **A build brief that cannot name its widest unmeasured term, and the probe that
measures it, is not ready to send.**

**Every estimate carries two calibers.** A size figure counts non-blank lines inside ` ```agda `
fences. State each projection twice: **naive**, the component sum on delivered comparables, and
**calibrated**, with this project's measured underestimation (about 1.3x where a probe or
comparable reaches, 3x where only a survey does).

**An estimate is a measurement, not a decision procedure** (`dev/PLAN.md` D26). Record an
overage in both calibers, say plainly that it is an overage, and work it down where real
compression exists. Evidence can move a technique. A number alone moves nothing, and it never
puts the campaign route back on the table.

**An idle agent slot is a defect.** A slot stays empty only when a real block stops every
remaining task. An audit is not a reason to leave a slot idle.

## Retiring code

Plan a retirement from the **rewrite side**. A consumer does not prove that a chapter must
stay. First price the ideal form of the content, written fresh today. Then compare. "We already
paid for it" never decides the question, in either direction.

**Archive retired code. Never delete it.** It goes to `archive/` at the repository root,
outside `src/`, so every gate is blind to it by structure. Archived files are frozen and nothing
imports across the boundary. For each module, `dev/ARCHIVE.md` records what it is, why it left,
where it was last green, **what it did right** (from measurement, not praise), and what would
make it worth a second look.
