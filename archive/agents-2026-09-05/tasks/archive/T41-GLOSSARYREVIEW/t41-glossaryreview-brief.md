# [L3.32-T41] Review the 119 pre-existing glossary entries
tier: codex (default)

GOAL: `dev/glossary.toml` carries 133 entries. Fourteen were just settled by a
sourced dossier under the protocol in `dev/ORCHESTRATION.md` section 7. **The
other 119 predate that protocol**: most were added during the campaign without
a literature search, some by the orchestrator under time pressure. Review them
to the same standard, so the whole glossary rests on evidence rather than on
whoever happened to write the entry.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `dev/literature/glossary-review-2026-08.md` ONLY. **Do NOT edit
`dev/glossary.toml`**: this is a review for the owner's ruling, and the
orchestrator applies whatever the owner accepts. Nothing under `src/`.
SCOPE (read): `dev/glossary.toml` (the entries, their notes and their avoid
lists: the notes often record WHY a rendering was chosen, and a note that
already cites a source is itself evidence); `dev/GLOSSARY.md` (the field
meanings); `dev/literature/terms-2026-08.md` (**THE MODEL**: match its
structure, its evidence standard, and its habit of marking a guess as a guess);
`dev/ORCHESTRATION.md` section 7 (the protocol and the avoid-list caveat).

## Order of work, and it matters

Work in this order, finishing and SAVING each block before starting the next,
so a budget that runs out still leaves the valuable half done (C-22):

1. **Set theory, 58 entries.** The mathematical core and the highest risk: a
   wrong rendering here misleads a reader about mathematics.
2. **Logic, 7 entries, and Type theory, 25.** Technical, with established
   Chinese and Japanese literature in most cases.
3. **Logic and philosophy, 37, plus Other, 6.** Charter and project vocabulary;
   some of it is this project's own idiom and has no literature by nature, in
   which case say so rather than hunting.

## What to report per entry

Do NOT re-litigate settled ones. For each entry, one of four verdicts:

- **CONFIRMED**: an established rendering, and the entry matches it. Give the
  source. One line is enough.
- **CONFIRMED WITH A BETTER SOURCE**: the entry is right but its note cites
  nothing or something weak; supply the source so the entry can be strengthened.
- **CHALLENGED**: the literature says something else, or the rendering collides
  with another glossary term, or it reads as a different concept. Give the
  established rendering with its source, the collision, and what an `avoid`
  entry should say. **These are the report's whole value; put them first in
  your summary table.**
- **IDIOM, NO LITERATURE**: the project's own coinage or a metaphor. Say so
  plainly and stop; do not manufacture a source. Note whether it is at least
  internally consistent with the rest of the glossary.

Also flag, separately: entries whose `avoid` list bans a word that has innocent
uses (the ground ruling of 2026-08-05 taught this: an over-broad ban fires on
prose that never meant the term), and any entry whose Japanese looks like a
kanji transliteration rather than the term Japanese mathematics actually uses.

CONSTRAINTS: legitimate sources only; paywalled material reported as paywalled,
never worked around; every claim carries its source. **Write the dossier
incrementally, block by block, saving after each** (C-22: an agent that
researches for its whole budget and writes at the end returns nothing). Zero
Agda. No git. Never touch `.claude/`.

RETURN (`dev/literature/glossary-review-2026-08.md`; final message = the
CHALLENGED list in full, with the recommended change for each, then counts by
verdict and how far through the three blocks you got): a partial review that
covers set theory completely is a success; a complete review that cites nothing
is not.
