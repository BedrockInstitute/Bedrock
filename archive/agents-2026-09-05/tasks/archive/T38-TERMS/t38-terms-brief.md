# [L3.32-T38] The terminology dossier (fourteen renderings, for the owner's ruling)
tier: codex (default)

GOAL: fourteen load-bearing terms are already in use in the Chinese prose of
delivered chapters but are NOT in `dev/glossary.toml`, so nothing enforces them
and they can drift. Per `dev/ORCHESTRATION.md` section 6, the protocol is:
**search the Chinese literature for the established rendering first; only where
there is none, draft multiple candidates by analogy and present them with the
reasoning.** The owner rules; you do not choose. Deliver the dossier.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `dev/literature/terms-2026-08.md` ONLY (the dossier). **Do NOT
edit `dev/glossary.toml`**: the owner rules first, the orchestrator writes the
entries afterwards. Nothing under `src/`.
SCOPE (read): `dev/glossary.toml` (the 119 existing entries: match their
house style, their category vocabulary, and their avoid-list conventions);
`dev/GLOSSARY.md` (what the fields mean and how the checker uses them);
`dev/literature/` (the digested sources, which may already fix some of these);
the chapters where each term is used, to see the sense it carries here.

THE FOURTEEN, with where they are used and the orchestrator's provisional
suggestion (a suggestion is NOT a decision; refute it if the literature says
otherwise):

1. `face` (6 chapters) - provisional 面孔. The sense here: the side an object
   presents to a consumer, as in "the satisfaction face of Def". Check whether
   Chinese mathematical writing has a settled word; note that 面 alone collides
   with a polytope's face and 接口 collides with interface.
2. `initial segment` (2) - provisional 初段.
3. `presentation` (13) - provisional 呈现. The HIT sense: a set given as an
   index type plus an indexing map. Note 表示 collides with "representation",
   which is already a glossary entry.
4. `crossing` (10) - provisional 跨越. The sense: moving a statement between an
   ambient reading and an inner one, as in "Delta-0 is a crossing tax".
5. `decode` (17) - provisional 解码.
6. `order type` (3) - provisional 序型.
7. `canonical well-ordering` (3) - provisional 典范良序 (the glossary already
   fixes canonical and well-order; check the compound reads naturally).
8. `square law` (3) - provisional 平方律, for the cardinal identity. Check
   whether Chinese texts say 平方定理 and whether the distinction matters here,
   where it is cited as a bound rather than proved as a theorem.
9. `equinumerous` (1) - provisional 等势.
10. `initial ordinal` (1) - provisional 初始序数.
11. `count` (8) - provisional 计数, as the chapter subject "how many formulas
    there are".
12. `shape count` (1) - provisional 形状计数.
13. `square pairing` (2) - provisional 平方配对, the pairing function on the
    naturals. **Must be visibly distinct from 8**, since one is a pairing
    function and the other a cardinal law.
14. `pair atom` (1) - provisional 对子原子.

METHOD: for each term, report (a) what the established Chinese rendering is, if
there is one, WITH ITS SOURCE, (b) otherwise two or three candidates with the
analogy each rests on and the collision each avoids, (c) a recommended `avoid`
list of renderings that are actively wrong here, and (d) the Japanese
rendering if the sources give one, since the glossary carries a `ja` field.
**A term where the literature is silent must say so plainly** rather than
dressing a guess as a finding.

CONSTRAINTS: legitimate sources only; paywalled material is reported as
paywalled, never worked around; every claim carries its source. Write the
dossier INCREMENTALLY, filling each term as you settle it (C-22: an agent that
researches for its whole budget and writes at the end returns nothing). Zero
Agda. No git. Never touch `.claude/`.

RETURN (`dev/literature/terms-2026-08.md`; final message = a compact table of
the fourteen with your recommendation and its basis): the dossier, plus an
explicit list of any term where you could find no source and are guessing.
