# AGENTS.md

Working rules for AI coding agents contributing to Bedrock. This is the canonical,
agent-facing rulebook (and the one humans point their agent at). It is plain Markdown with no
required structure; every agent that loads `AGENTS.md` reads this. Claude Code loads it through
the root `CLAUDE.md` (`@AGENTS.md`); other agents read this file directly.

> **This project is very early, and this guide is incomplete.** The absence of a rule here
> does **not** mean there is no rule: it may simply not be documented yet. When you are unsure
> about anything, do **not** guess. Stop and ask the repository owner explicitly, and wait for
> an answer before proceeding. Surfacing a question is always preferred over a confident wrong
> assumption.

## Commands

- **`make check`** is the gate before any commit. It typechecks the masters
  (`agda src/Everything.lagda.md`, the single trusted invocation), validates i18n markers, runs
  the prose linter, runs the Agda code linter (`scripts/lint-agda.py` against the
  [dev/STYLE-agda.md](dev/STYLE-agda.md) rules: OPTIONS header, import necessity, no forbidden
  constructs), runs the glossary checker (`scripts/check-glossary.py` against the term data in
  [dev/glossary.toml](dev/glossary.toml), explained in [dev/GLOSSARY.md](dev/GLOSSARY.md)),
  validates the size-ledger declaration (`scripts/ledger.py --check` against
  [dev/ledger.toml](dev/ledger.toml), explained in [dev/LEDGER.md](dev/LEDGER.md)), enforces the
  never-commit rule (`scripts/check-probes.py --check`: no probe file, nothing generated),
  checks the whole-tree invariants (`scripts/check-tree.py --check`, chiefly that every master
  is in `Everything`'s import closure, since one that is not is never typechecked at all), and
  runs `reuse lint` for per-file licensing. It is expensive: run the individual checks while you
  work (`agda <file>`, `python3 scripts/lint-prose.py <files>`) and the full gate before the
  commit.
- **`make venv`** creates the project virtual environment (`.venv`) from Python 3.11+ and
  installs the pinned tooling in [requirements-dev.txt](requirements-dev.txt). Run it once per
  clone before `make check`.
- **`make site`** builds the multilingual hyperlinked site into `_build/site`; **`make serve`**
  previews it; **`make gen`** weaves the on-demand mono-lingual `.lagda.md` copies.
- **`make hooks`** activates the version-controlled pre-commit hook
  (`scripts/git-hooks/pre-commit`), which runs the prose linter and marker check on staged
  files. Run it once per clone.
- **`python3 scripts/lint-prose.py --fix <files>`** auto-fixes prose (CJK punctuation, quotes,
  paren spacing). Em dashes, single quotes, and quote nesting are reported but fixed by hand.

Requirements: Agda 2.8.0 + cubical 0.9 and Python 3.11+ for `make check`. Python tooling
dependencies (currently `reuse`) are pinned in [requirements-dev.txt](requirements-dev.txt) and
installed into the project `.venv` by `make venv`; `make` then uses that interpreter. The site
build also uses Node only at deploy time (KaTeX and fonts load from a CDN). Tooling:
[scripts/README.md](scripts/README.md).

## Boundaries

- **Always:** read the `dev/LESSONS.md` entries relevant to what you are about to write, before
  you write it; run `make check` before committing; author each document in English first, then
  translate; verify a load-bearing assumption cheaply before committing to heavy or
  hard-to-reverse work (large installs, forks, multi-hour builds, framework choices); state any
  size projection in both calibers; install Python tooling with `make venv` and pin any new
  dependency in `requirements-dev.txt`.
- **Ask first:** genuine architecture forks (surface them to the owner with a recommendation
  rather than charging ahead on one interpretation); adding a top-level directory (then add its
  `README.md`); a translation term not yet in [dev/glossary.toml](dev/glossary.toml) (choose by
  meaning and surface the choice).
- **Never:** commit generated files (anything under `_build/`, or woven mono-lingual
  `.lagda.md`) or probe files (`src/Probe*.agda`); DELETE retired code (archive it, see below);
  translate developer docs; use an em dash in any language; use half-width sentence punctuation
  in CJK prose; commit or print deployment secrets; add an unpinned or globally-installed
  dependency (pin it in `requirements-dev.txt`, installed into `.venv`).

## Where the rules live

Every rule has ONE canonical home, chosen by who enforces it. If you are
looking for a rule, this table says where it is; if you are adding one, it says
where it goes. **A rule that is not machine-enforced must name its enforcement
point** (which gate, which brief section, which review step): a rule with no
enforcement point is a wish.

| Kind of rule | Canonical home | Enforced by |
|---|---|---|
| Term renderings | `dev/glossary.toml` | `check-glossary.py` in `make check` |
| Code and chapter style | `dev/STYLE-agda.md` | `lint-agda.py` (a subset) plus review |
| Prose, CJK, i18n markers | `dev/STYLE-i18n.md` and the rules below | `lint-prose.py`, the marker checker |
| Licensing | `REUSE.toml` | `reuse lint` |
| Measured engineering law | `dev/LESSONS.md` | briefs point at it; review |
| Size ledger (standing, remaining, endpoint) | `dev/ledger.toml`, explained by `dev/LEDGER.md` | `scripts/ledger.py --check` in `make check` |
| Project ruling (architecture, process, retirement) | `dev/PLAN.md` section 3, as a numbered decision | the orchestrator; briefs |
| What every contributing agent must know | this file | loaded at session start |
| Dispatch, slots, briefs, audits | `dev/ORCHESTRATION.md` | the orchestrator, at the points it names |
| Goal status and history | `dev/PLAN.md` section 11, `dev/JOURNAL.md` | the registration rule |

Nothing is canonical in two places. Where this file restates a rule from
`dev/LESSONS.md` or `dev/PLAN.md`, the other document is canonical and this one
is the summary an agent reads first.

## The developer documents, and which of them bind

- **`dev/LESSONS.md` BINDS NEW CODE.** About a hundred measured entries in six series (P
  performance, R conversion and reduction, T termination, I inference, D design, C craft and
  process). They are measurements, not opinions, and each one exists because something cost
  time or died. Read the relevant entries before writing, not after a wall. When your work
  discovers a new law, propose it with its measurement; the owner assigns the ID.
- **`dev/PLAN.md` is the goal registry.** Section 0 says where the work stands today, section 3
  holds the ratified decisions, section 6 holds the goal tree and the coding rules, section 11
  is the master status table. Work is managed by goal codes and every commit carries one in
  brackets (`[L3.32-T8]`).
- **`dev/JOURNAL.md` is the execution record**: how each goal actually went, dispatch by
  dispatch, with the measurements and the refutations.
- **`dev/STYLE-agda.md`** is code and chapter style law (`scripts/lint-agda.py` enforces a
  subset). **`dev/STYLE-i18n.md`** is the marker grammar. **`dev/glossary.toml`** is the
  canonical term data, machine-checked, explained by `dev/GLOSSARY.md`.
- **`dev/ORCHESTRATION.md`** holds the dispatch, slot, brief and audit rules.
- **`dev/memos/`** holds route memos; **`dev/literature/`** holds the digested sources.
  Reconnaissance and probe reports live in `_build/*.md`, with the briefs that produced them
  archived in `_build/briefs/`.

A fact belongs in exactly one of them: a **ruling** is a PLAN row, an **episode** is a JOURNAL
entry, a **law** is a LESSONS entry.

## Working rules for dispatched agents

These bind an agent working against a pinned brief. The ORCHESTRATING agent,
which writes the briefs, audits the returns, wires the catalog and commits,
works to `dev/ORCHESTRATION.md` instead; where the two differ, the difference
is called out below.

- **Never touch `src/Everything.lagda.md`.** The orchestrator wires it after auditing your work.
- **Never commit, never push.** Leave the working tree as your report describes
  it. (This applies to DISPATCHED agents. The orchestrating agent does commit,
  with the goal code, after auditing and gating the return; nobody pushes
  without the owner's word.)
- **Run Agda under a heap cap and one process at a time**: `GHCRTS=-M8g agda <file>`. Several
  concurrent typechecks will thrash the machine, and a heap exhaustion is treated as a wall
  event, not a hiccup.
- **Write your deliverable incrementally.** If your output is a file, create it early and fill
  it as answers land. Research held only in your head dies with your budget.
- **Evidence is `file:line`.** A report that cannot be checked can only be believed.
- **A stop is a deliverable.** If the target turns out to be false, or the price wrong, or the
  plan built on a bad premise, say so with the evidence and stop. Two of this project's most
  valuable results were a refutation and a stop.

## Probes and gates

Before heavy or hard-to-reverse work, verify the load-bearing assumption cheaply: build the
smallest decisive miniature, report GO or NO-GO with a price extrapolation, and throw it away.
A probe prices only what THIS setting costs us; it never re-establishes what the literature or
the delivered tree already settles.

Probes are never committed, and `scripts/check-probes.py` enforces both halves of that: the
pre-commit hook refuses a staged probe (an ignore rule is a default, not a gate, and `git add
-f` walks past it), and `--stale` deletes probes whose verdict is recorded and which no live
agent is still writing. The verdict lives in a report under `_build/`; the file survives
only while it is the template for a chapter about to be written from it, and goes when that
chapter lands. A pattern worth keeping belongs in `dev/LESSONS.md` or in the chapter it seeded,
never in a stray file.

**An idle agent slot is a defect.** Whenever a slot is free, check for
parallelizable work and fill it. A slot stays empty only when every remaining
task is genuinely blocked: waiting on a ruling, on a sibling's write territory,
on a measurement that would make the work fundable, or on the concurrency and
heap ceilings. Auditing a return is not a reason to leave slots idle. At every
return, name what is unblocked, name what blocks the rest, and dispatch before
writing the report.

**Every block is gated before it is funded.** No block is built at the coarse (3x) estimate
class without first trying to measure it: each carries a paired probe aimed at its widest
unmeasured term, run before or alongside the build, and is funded at the band the probe leaves
rather than the band the survey guessed. This is arithmetic, not caution: a green gate moves its
term from the 3x class to about 1.3x and narrows the band's TOP, which is the edge that decides
whether a projection fits. A build brief that cannot name its block's widest term and the probe
that would measure it is not ready to be sent.

## Estimates carry two calibers

Size figures are non-blank lines inside ` ```agda ` fences. Any projection is stated twice:
**naive**, the component sum with each part anchored on a delivered comparable, and
**calibrated**, the naive figure with this project's measured underestimation applied (a part
anchored by a probe or a delivered comparable carries about 1.3x, a part that only a survey
could reach carries 3x). The split prices ignorance rather than pessimism, which is why a probe
converts money: every gate that goes green moves its part from the 3x class to the 1.3x class
and narrows the band.

The ledger that holds these figures is `dev/ledger.toml`, explained by
[dev/LEDGER.md](dev/LEDGER.md) and computed by `scripts/ledger.py`. **Standing is measured from
the tree and written down nowhere**, because a standing figure once written in prose was
re-quoted unchecked for nine dispatches while the tree moved under it. Quote
`python3 scripts/ledger.py --brief`, never a number you found in a paragraph.

**An estimate is a measurement, not a decision procedure.** The project's campaign route is
settled; how to walk it is not, and results decide that. The canonical statement is
`dev/PLAN.md` decision D26. A projection that exceeds the target line is recorded in both
calibers, stated plainly as an overage, and worked down wherever real compression exists.
Evidence may move a technique; a number alone moves nothing, and it may never put the campaign
route back on the table. A report that reasons from an overage to a route change is rejected at
review. This does not weaken the gates above: a probe asks which TECHNIQUE to use, and it
converts money exactly as before.

## Retiring code

Retirement is planned from the **rewrite side**, not the survivor side. Before concluding that
a chapter must stay because something still consumes it, price what the ideal form of the
needed content would cost written fresh today; only then compare. "We already paid for it" is
never a deciding argument, in either direction.

Retired code is **archived, never deleted**. The archive is `archive/` at the repository root,
outside `src/`, so every gate is structurally blind to it: it is not required to typecheck and
a red archive is not a defect. Archived files are frozen (a revival copies out, it never edits
in place) and nothing imports across the boundary. A registry under `dev/` records for each
archived module what it is, why it went, the commit where it was last green, and what would
make it worth consulting again. The archive and its registry are created at the first archival.

## Documentation taxonomy (user docs vs developer docs)

Bedrock separates documentation by audience, and the two follow different language rules:

- **User-facing docs** (the mathematics and the project itself) are **trilingual** in English,
  Chinese, and Japanese, and live under `docs/<lang>/` (e.g. `docs/{en,zh,ja}/CHARTER.md`).
- **Developer-facing docs** (how to contribute, conventions, specs) are **English only**. They
  live mostly in `dev/` (e.g. [dev/STYLE-i18n.md](dev/STYLE-i18n.md)), but the category is
  broader than that one directory: it also includes the two root developer docs (this
  `AGENTS.md`, the agent rulebook, and `CONTRIBUTING.md`, the human entry point), every
  per-directory `README.md` (listed below), and any other document written for contributors
  rather than readers. Do not translate developer docs.
- **`README.md` is the exception:** both audiences read it, so it follows the **user** rule and
  is trilingual (the English `README.md` at the repo root, with `docs/zh/README.md` and
  `docs/ja/README.md`). Any document that both audiences read is treated as a user doc.

This taxonomy is itself a rule, recorded here. If you add a document, place it by audience.

Developer docs are written **primarily for AI-agent readers** (humans second): favour explicit
structure and file-by-file description over narrative, so an agent can orient quickly. Every
top-level directory carries a short `README.md` to that end: [src/](src/README.md),
[docs/](docs/README.md), [dev/](dev/README.md), [site/](site/README.md),
[scripts/](scripts/README.md), and [.github/workflows/](.github/workflows/README.md). (The
`.github/` guide lives under `workflows/` because a `README.md` placed directly in `.github/`
would be shown as the repository homepage in place of the root `README.md`.) When you add a
top-level directory, add its README.

## Prose conventions (all languages)

Enforced by `scripts/lint-prose.py` and the pre-commit hook:

- **No em dash** anywhere (`—` U+2014, `―` U+2015, the Chinese `——`). Rewrite with a comma,
  colon, period, or parentheses, or split the sentence. The en dash `–` (numeric ranges) and
  the hyphen `-` are allowed. The Japanese long-vowel mark `ー` is not a dash and is fine.
- Inside ` ```agda ` code blocks: **English only**, no CJK and no full-width symbols. Agda's
  own Unicode operators (`≡ ℕ λ Δ₀ →` and the like) are fine. The CJK prose rules below do not
  apply inside code blocks.

### CJK prose (Chinese and Japanese)

- **Full-width sentence punctuation.** Chinese uses `，。；：！？`; Japanese uses the
  ideographic comma and period `、。` (and full-width `；：！？` where needed). Do not use
  half-width `, ; : ! ?` in CJK context (they are fine in code, URLs, and Latin fragments like
  `Cohen (1963)`). Do not "correct" a Japanese `、` to `，`.
- **Quotes** use the corner brackets `「」`. No `"…"`, no `'…'` as quotation marks, and no quote
  nesting. English apostrophes (`V's`) are kept.
- **Parentheses stay half-width `()`** (not full-width), with English-style outer spacing: one
  space before `(` and after `)` (e.g. `经典原理 (LEM、AC) 是…`), no space just inside.
- **No space between two CJK characters**; **no space adjacent to a full-width symbol**.
  Latin-to-CJK spacing elsewhere (`V 的`, `ZF 公理`) is normal and kept.
- **Reflow long CJK paragraphs onto one line.** A hard line break between two CJK characters
  renders as a stray space in Markdown, so write CJK paragraphs as single long lines; break
  only at a Latin word boundary where the space is wanted.

Most of the above is auto-fixable: run `python3 scripts/lint-prose.py --fix <files>`. Em
dashes, single quotes, and quote nesting are reported but must be rewritten by hand.

## Literate Agda and the i18n marker grammar

- Each module is **one master `.lagda.md`** under `src/`: the Agda code appears once, prose for
  every language lives in the same file wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->`
  markers, and code blocks are language-neutral (shared). The code can never drift between
  languages because it exists once. Full grammar: [dev/STYLE-i18n.md](dev/STYLE-i18n.md).
- Markers appear only in prose, never inside a ` ```agda ` fence.
- The initial site is **bilingual (en + zh)**; Japanese is **pre-supported** (add a `<!--ja-->`
  block and enable `ja` in the build). Adding a language never touches the code.
- **Woven mono-lingual `.lagda.md` are not committed.** They are an on-demand `make gen` output
  (for `agda --html` compatibility). Everything generated lives under `_build/` (git-ignored);
  never commit generated files.

## Translation workflow

Author each document **in English first**, then translate both the Chinese and the Japanese
from the English. Finally, **cross-check the Chinese and Japanese against each other** once more
for mistranslation, omission, addition, and term drift, and fix before finalizing. Prefer
**meaning over literal calque**.

Confirmed term renderings live in the **canonical glossary data
[dev/glossary.toml](dev/glossary.toml)** (explained in [dev/GLOSSARY.md](dev/GLOSSARY.md)), which
`scripts/check-glossary.py` machine-enforces via `make check` (so a wrong rendering is caught in
CI, not review). Consult it before translating.

**A term the glossary does not carry is NOT settled by choosing.** It is settled
by a terminology dossier: the literature is searched for the established
rendering first, candidates are drafted only where the literature is silent,
every guess is marked as a guess, and the owner rules. The full protocol,
including who dispatches it and when, is canonical in
[dev/ORCHESTRATION.md](dev/ORCHESTRATION.md) section 8. If you are a dispatched
agent and your chapter needs such a term, **use it consistently and NAME it in
your report** so the dossier can be dispatched; do not add a glossary entry
yourself.

## Licensing

Bedrock is multi-licensed under a three-bucket rule, declared per file in [`REUSE.toml`](REUSE.toml)
and enforced by `reuse lint` (part of `make check`):

- **CC BY-NC-SA 4.0**: the mathematical development and user prose (`src/`, `docs/`), the `README`,
  and the brand assets under `site/static/assets/`.
- **OFL-1.1**: the self-hosted third-party web fonts under `site/static/fonts/`.
- **AGPL-3.0-only** (the default): every other first-party file, the tooling, the site front-end,
  build and config, and the prose developer docs (`dev/`, this `AGENTS.md`, `CONTRIBUTING.md`).
  This folds in the front-end adapted from [the 1lab](https://1lab.dev) and the vendored
  `site/vendor/1lab/` tree, which are AGPL-3.0.

A newly added file inherits AGPL-3.0 automatically via the `**` default in `REUSE.toml`; the
carve-outs are the finite content/font set. Full texts are in [`LICENSES/`](LICENSES/) (mirrored as
root `LICENSE-*` files so GitHub's detector lists all three); attributions and the AGPL section 13
corresponding-source statement are in [NOTICE](NOTICE).

All per-file licensing is declared centrally in `REUSE.toml` and verified by `reuse lint`. **Do not
add in-file `SPDX-*` headers** to any file: licensing has one source of truth (like the glossary in
[dev/glossary.toml](dev/glossary.toml) and the i18n masters), so there is nothing per-file to keep
consistent. A new file inherits the `**` default (AGPL-3.0-only) automatically; if it should instead
be CC or OFL, add its path to the matching carve-out in `REUSE.toml`.

## Deployment

Deployment is automatic: on every merge to `main`, GitHub Actions builds the site and publishes
it to Cloudflare Pages (bedrock.institute) and GitHub Pages. Contributors need do nothing and
never handle deployment credentials.

The Cloudflare credentials live only as GitHub Actions encrypted organization secrets (on the
BedrockInstitute org, inherited by this repo); they are never committed, never printed in logs,
and not visible to contributors. The one-time owner
setup is documented in `.github/workflows/cloudflare.yml`.
