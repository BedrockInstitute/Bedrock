# [L3.32-T12] The geology corpus fetch (a mandatory gate, now) - ATTEMPT 2

## What attempt 1 established (do not rediscover this)

- **Direct network from the shell is BLOCKED (DNS fails).** Use the search and
  page-opening tools, which have their own access. Do not waste turns on curl.
- The papers are located: **Fuchs, Hamkins, Reitz, "Set-theoretic geology" =
  arXiv:1107.4776**; **Usuba = arXiv:1707.05132, whose real title is "The
  downward directed grounds hypothesis and very large cardinals"** (NOT "The
  mantle is a ground", which attempt 1 corrected); **Laver = Annals of Pure and
  Applied Logic 149 (2007)**; `jdh.hamkins.org` is reachable and indexes the
  rest. The `ar5iv.labs.arxiv.org/html/<id>` HTML renderings are the most
  fetchable form.
- Attempt 1 died with ZERO output because it researched for its whole budget
  and left the writing to the end. **THE BINDING FIX: write
  `dev/literature/geology.md` in your FIRST few actions as a skeleton with the
  five questions as empty headings, then fill it incrementally as each answer
  lands, saving after each.** A partial dossier is a real deliverable; an
  unwritten perfect one is not. Budget your turns so the file is always
  ahead of your research, never behind it.


tier: codex (default)

GOAL: the in-repo literature corpus contains ZERO set-theoretic geology
sources (`_build/l3.31-glprobe-report.md`: zero hits for mantle, grounds,
Hamkins, Usuba, Laver, approximation across all 13,645 lines of primary
sources), and PLAN's risk table makes fetching them a mandatory gate before
any geology funding. Do the fetch now, while it blocks nothing: it is
zero-Agda, it competes for no build resource, and having it in hand turns a
future gate into a formality.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `dev/literature/geology.md` and, if you obtain full texts,
the corresponding files under `_build/literature/` following the existing
naming convention there. Nothing else. Never touch `src/`, `.claude/`, or any
other `dev/` file.
SCOPE (read): `dev/literature/BIBLIOGRAPHY.md` and `digest.md` (the house
format and citation discipline you must match), `_build/literature/` (the
existing corpus and its file naming), `_build/l3.31-glprobe-report.md`
(what the POCs already measured and what questions the corpus must answer),
`dev/PLAN.md` section 6.1 `[L6]` (the meeting map: what geology is FOR here).

THE TARGETS, in priority order:
1. **Fuchs, Hamkins, Reitz, "Set-theoretic geology"** (the founding paper:
   grounds, the mantle, the generic mantle, the Ground Axiom).
2. **Laver, and Woodin, on ground model definability** (the theorem that
   makes the mantle first-order; its technical core is the approximation and
   cover properties, which is the first place inner-model-style argument
   appears inside geology).
3. **Usuba, on the bedrock theorem** (strongly compact implies the mantle is
   a ground; the downward directed grounds hypothesis).
4. Reitz on the Ground Axiom; Hamkins on the approximation and cover
   properties, if reachable.

THE QUESTIONS the dossier must answer, each with a citation:
- The exact definitions this development would have to formalize: ground,
  mantle, generic mantle, bedrock, the Ground Axiom. Give the definitions as
  stated, not as remembered.
- Ground model definability: the exact statement, its hypotheses, and what
  its proof needs (this is the mantle's universe-size wall the POC measured,
  arriving as a theorem: say precisely what it buys).
- Downward directed grounds: statement, status, what Usuba proved and under
  what hypotheses.
- The meeting theorem this book aims at, "L is a bedrock": is it stated
  anywhere in the literature, and if so where and in what form? If it is
  folklore, say so and give the nearest cited statement.
- What of this is FIRST-ORDER expressible and what needs a class-quantifier
  workaround, since that decides what our formalization can even state.

CONSTRAINTS: legitimate sources only. Paywalled material is REPORTED as
paywalled, never worked around. Every claim in the dossier carries its
source and location. No memory-sourced claims: if you cannot cite it, mark
it UNVERIFIED and say what would settle it. Zero Agda. No git commands. Match
the corpus's existing prose rules (no em dash; English only in this file).

RETURN (`dev/literature/geology.md`; final message = what was obtained, what
was paywalled, and the five questions' answers in compressed form).
