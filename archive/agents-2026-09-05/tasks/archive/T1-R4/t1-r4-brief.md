# [L3.32-T1] The R4 corrective stop
tier: codex (default)

GOAL: remove the tree's one false hypothesis honestly. `Matching`
(Bridge.lagda.md:448) is classically FALSE (Devlin VI.2.4: J_alpha = L_{omega
times alpha} holds iff omega times alpha = alpha; the tree's claim is the
general equality). Record the falsity, record the true sandwich, retire the
dependence, keep every true asset.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): src/L/Rud/Bridge.lagda.md ONLY. Nothing else. Never
src/Everything.lagda.md.
SCOPE (read): _build/p2-fork-recon.md sections 1.1-1.5 and 2.1 row R4 (the
mandate, the citations, the counter-instance, what survives);
_build/literature/dev6.txt:1577-1582 and :1689-1695 (the source lines);
src/L/Rud/SatTable.lagda.md (the only importer of Bridge; keep it green);
dev/STYLE-i18n.md and dev/STYLE-agda.md.

THE FOUR ITEMS:
(a) State in the chapter's prose that `Matching` as recorded is false, with
    the Devlin citation and the counter-instance zeta = omega, gamma =
    omega times 2 (L_omega is a member of S_{omega times 2} yet no limit
    stage below omega times 2 holds it; the arithmetic truth set argument is
    the classical refutation). Prose in BOTH en and zh markers.
(b) Record the TRUE statement as a classical fact IN PROSE (not as a proof
    and NEVER as a postulate): Lset alpha is contained in Sset (omega times
    alpha) is contained in Lset (omega times alpha), with equality exactly at
    the omega-fixed points.
(c) Retire `module Bridged`'s dependence on `Matching`: the module and any
    export that exists only to consume the false hypothesis goes; the
    unconditional direction `bridge-isJ→isL`, which `p4` already supplies
    without `Matching`, STAYS and is stated unconditionally.
(d) Keep `p3`/`p4`/`RudBelow` untouched and re-export `p4` as the delivered
    half with prose naming it Devlin's P(alpha).

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, one agda process at a time (four
sibling agents run concurrently; do not exceed one process). Typecheck
Bridge AND SatTable green before reporting (SatTable imports Bridge; if the
re-typing breaks it, fix SatTable's import list ONLY, and say so). Run
`python3 scripts/lint-agda.py` and `python3 scripts/lint-prose.py` on every
file you touch, both clean. NO git commands at all; the orchestrator commits.
Do not touch .claude/ or generated files.
- Prose: no em dash in any language; CJK full-width sentence punctuation,
  half-width parentheses, corner-bracket quotes, no space between CJK
  characters; inside agda fences English only; markers never inside a fence.

RETURN (final message): what changed and why, the export-face diff (what
disappeared, what became unconditional), the two typecheck results, the lint
results, and any prose you were unsure of.
