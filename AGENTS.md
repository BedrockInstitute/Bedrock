# AGENTS.md

Working rules for AI coding agents contributing to Bedrock. This is the canonical, agent-facing
rulebook, loaded at every session start (Claude Code reaches it through the root `CLAUDE.md`
`@AGENTS.md` import; other agents read it directly).

**This file is deliberately short.** It holds only what changes what you DO on an arbitrary
task. Everything else is one line in [The index](#the-index) pointing at its canonical home,
and almost all of that is machine-enforced by `make check`, so forgetting it is caught by a
gate rather than by review. A rulebook nobody finishes reading binds nothing.

> **This project is very early, and this guide is incomplete.** The absence of a rule here does
> **not** mean there is no rule. When unsure, do **not** guess: stop and ask the repository
> owner, and wait. Surfacing a question always beats a confident wrong assumption.

## Boundaries

- **Always:** **write it generic** (structure-generic at full strength, so re-instantiation is
  nearly free; a stop-line is never a reason to write fixed: say so and stop for a re-price);
  load the rules for your task with `python3 scripts/rules.py --for <kind>` and read them
  **before** you write; run `make check` before committing; author every document in English
  first, then translate; verify a load-bearing assumption cheaply before heavy or hard-to-reverse
  work; state any size projection in both calibers.
- **Ask first:** genuine architecture forks (surface them with a recommendation rather than
  charging ahead on one reading); adding a top-level directory (then add its `README.md`); a
  translation term not yet in `dev/glossary.toml`.
- **Never:** commit generated files (anything under `_build/`, woven mono-lingual `.lagda.md`)
  or probe files (`src/Probe*.agda`); DELETE retired code (archive it); translate developer
  docs; use an em dash in any language; use half-width sentence punctuation in CJK prose; commit
  or print deployment secrets; add an unpinned or globally-installed dependency; add an in-file
  `SPDX-*` header.

## Commands

- **`make check` is the gate before any commit.** It typechecks the masters, then runs every
  checker in [scripts/](scripts/README.md): i18n markers, prose, Agda style, rule-citation
  resolution, glossary, size ledger, the never-commit rule, whole-tree invariants, and `reuse
  lint`. **Run it in the background, never in the foreground**: a cold typecheck takes about
  twelve minutes and must not block the session (`dev/PLAN.md` D28). While you work, run the
  individual checks instead (`agda <file>`, `python3 scripts/lint-prose.py <files>`).
- **`python3 scripts/rules.py --for <kind>`** emits the rules mandatory for a build, probe,
  recon, rewrite or review, with each rule's statement. `--grep <term>` resolves the long tail
  by trigger word. **Do not select rules from memory**: that is what drifted for five days while
  an imported playbook sat uncited in 102 of 112 briefs.
- **`python3 scripts/ledger.py --brief`** is the only admissible source for a standing size
  figure. Never quote a number found in a paragraph.
- **`make venv`** once per clone, then **`make hooks`**. `make site` / `make serve` / `make gen`
  build the site. `python3 scripts/lint-prose.py --fix <files>` auto-fixes most prose.

Requirements: Agda 2.8.0 with cubical 0.9, and Python 3.11+. Dependencies are pinned in
[requirements-dev.txt](requirements-dev.txt) and installed into `.venv` by `make venv`.

## Where the rules live

Every rule has ONE canonical home, chosen by who enforces it. **A rule that is not
machine-enforced must name its enforcement point** (which gate, which brief section, which
review step): a rule with no enforcement point is a wish. Nothing is canonical in two places;
where this file restates a rule, the other document is canonical and this one is the summary.

| Kind of rule | Canonical home | Enforced by |
|---|---|---|
| Measured engineering law | `dev/LESSONS.md` | `scripts/rules.py` bundles; review |
| Project ruling (architecture, process, retirement) | `dev/PLAN.md` section 3, numbered | the orchestrator; briefs |
| Dispatch, slots, briefs, audits | `dev/ORCHESTRATION.md` | the orchestrator, at the points it names |
| Goal status and history | `dev/PLAN.md` section 11, `dev/JOURNAL.md` | the registration rule |
| Size ledger (standing, remaining, endpoint) | `dev/ledger.toml`, explained by `dev/LEDGER.md` | `scripts/ledger.py --check` |
| Code and chapter style | `dev/STYLE-agda.md` | `scripts/lint-agda.py` (a subset); review |
| Prose, CJK, i18n markers | `dev/STYLE-i18n.md` | `scripts/lint-prose.py`, the marker checker |
| Term renderings | `dev/glossary.toml`, explained by `dev/GLOSSARY.md` | `scripts/check-glossary.py` |
| Licensing | `REUSE.toml` | `reuse lint` |
| What every contributing agent must know | this file | loaded at session start |

A fact belongs in exactly one of them: a **ruling** is a PLAN row, an **episode** is a JOURNAL
entry, a **law** is a LESSONS entry.

**`dev/LESSONS.md` BINDS NEW CODE.** Its entries are measurements, not opinions, and each one
exists because something cost time or died. When your work discovers a new law, propose it with
its measurement; **the orchestrator assigns the ID** (owner's delegation, 2026-08-06): the P
series uses letters, the R, T, I, D and C series use numbers, and the next free one is the ID.
A law is not admitted without its measurement, whoever numbers it.

## The one rule that has cost this project most

**Write content structure-generic rather than fixed to a carrier.** It is more expensive on the
first instance and cheaper from the second onward, which is exactly why it gets skipped under a
deadline. `dev/PLAN.md` D29 requires the question to be asked at three moments: when a recon is
dispatched, when a build is dispatched, and when a route is planned.

## Working rules for dispatched agents

These bind an agent working against a pinned brief. The ORCHESTRATING agent, which writes the
briefs, audits returns, wires the catalog and commits, works to `dev/ORCHESTRATION.md` instead.

- **Never touch `src/Everything.lagda.md`.** The orchestrator wires it after auditing your work.
- **Never commit, never push.** Leave the working tree as your report describes it.
- **Run Agda under a heap cap, one process at a time**: `GHCRTS=-M8g agda <file>`. Concurrent
  typechecks thrash the machine and corrupt each other's measurements. A heap exhaustion is a
  wall event to report, never a reason to raise the cap.
- **Write your deliverable incrementally.** Create the file early and fill it as answers land.
  Research held only in your head dies with your budget.
- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
- **A stop is a deliverable.** If the target is false, the price wrong, or the plan built on a
  bad premise, say so with the evidence and stop. Several of this project's most valuable
  results were refutations.
- **A measured cure does not transfer by analogy.** Re-measure it at its own site. An expected
  figure anchored on a comparable elsewhere is a hypothesis, not a price (`dev/LESSONS.md` P-l).

## Probes, gates and estimates

**Before heavy or hard-to-reverse work, verify the load-bearing assumption cheaply**: build the
smallest decisive miniature, report GO or NO-GO with a price extrapolation, throw it away. A
probe prices only what THIS setting costs us; it never re-establishes what the literature or the
delivered tree already settles. Probes are never committed (`scripts/check-probes.py` enforces
both halves, since an ignore rule is a default and `git add -f` walks past it).

**Every block is gated before it is funded.** No block is built at the coarse estimate class
without first trying to measure it. This is arithmetic, not caution: a green gate moves its term
from the 3x class to about 1.3x and narrows the band's top, which is the edge that decides
whether a projection fits. **A build brief that cannot name its block's widest unmeasured term,
and the probe that would measure it, is not ready to be sent.**

**Estimates carry two calibers.** Size figures are non-blank lines inside ` ```agda ` fences.
Every projection is stated twice: **naive**, the component sum anchored on delivered
comparables, and **calibrated**, with this project's measured underestimation applied (about
1.3x for a part a probe or comparable reaches, 3x for a part only a survey could).

**An estimate is a measurement, not a decision procedure** (`dev/PLAN.md` D26). A projection
that exceeds the target is recorded in both calibers, stated plainly as an overage, and worked
down where real compression exists. Evidence may move a technique; a number alone moves nothing,
and never puts the campaign route back on the table.

**An idle agent slot is a defect.** A slot stays empty only when every remaining task is
genuinely blocked. Auditing a return is not a reason to leave slots idle.

## Retiring code

Retirement is planned from the **rewrite side**. Before concluding that a chapter must stay
because something consumes it, price what the ideal form of the needed content would cost
written fresh today, then compare. "We already paid for it" is never a deciding argument, in
either direction.

Retired code is **archived, never deleted**, into `archive/` at the repository root, outside
`src/`, so every gate is structurally blind to it. Archived files are frozen and nothing imports
across the boundary. `dev/ARCHIVE.md` records for each module what it is, why it went, where it
was last green, **what it did right** (from measurement, not praise), and what would make it
worth consulting again.

## The index

Everything below is real and binding; none of it is needed until you do that particular thing,
and all of it is enforced by a gate rather than by your memory.

| Topic | Where | Enforced by |
|---|---|---|
| Prose rules: the em-dash ban, CJK full-width punctuation, `「」` quotes, CJK spacing and reflow, English-only inside ` ```agda ` fences | `dev/STYLE-i18n.md` | `scripts/lint-prose.py`, pre-commit hook. `--fix` handles most of it |
| Literate Agda: one master `.lagda.md` per module, `<!--en--> <!--zh--> <!--ja-->` marker grammar, shared code fences, woven copies never committed | `dev/STYLE-i18n.md` | `scripts/weave-i18n.py --check` |
| Translation: English first, then both targets, then cross-check them against each other; meaning over calque. A term the glossary lacks is settled by a dossier, never by choosing: name it in your report | `dev/ORCHESTRATION.md` section 8, `dev/glossary.toml` | `scripts/check-glossary.py`; the dossier protocol |
| Documentation taxonomy: user docs are trilingual under `docs/<lang>/`, developer docs are English only, `README.md` follows the user rule. Place a new document by audience, and give every top-level directory a `README.md` | this table; `dev/README.md` | review |
| Licensing: three buckets declared centrally, a new file inherits AGPL-3.0 | `REUSE.toml`, texts in `LICENSES/` | `reuse lint` |
| Deployment: automatic on merge to `main`, credentials are org secrets, contributors do nothing | `.github/workflows/` | n/a |
| Tooling: what every script does and when to run it | [scripts/README.md](scripts/README.md) | n/a |
| Route memos, digested literature, probe reports and the briefs that produced them | `dev/memos/`, `dev/literature/`, `_build/` | n/a |
