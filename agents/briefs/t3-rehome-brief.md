# [L3.32-T3] The choice re-home probe (gate 5)
tier: codex (default)

GOAL: with the bridge standing, `hasChoice` on L is meant to flow from the
DELIVERED J-side well-order instead of the 6,046-line `L/Choice` tree. Probe
the pick: build the smallest honest version of the transversal-shaped choice
function over `Jset-order`, taking the bridge's isL-to-isJ step as a MODULE
HYPOTHESIS (the bridge is not built yet; that is the honest form). Measure.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): src/ProbeRehome.agda (untracked) and
_build/l3.32-t3-report.md ONLY. No master file, never Everything.
SCOPE (read): src/L/Rud/Order.lagda.md (the supplier: `Sset-order`:838,
`Jset-order`:1026-1028, `Sset-choice`:1042, `Jset-choice`:1059); the
delivered L-side shape it replaces, src/L/Choice/Transversal.lagda.md
(`hasChoiceL`) and src/L/Model.lagda.md:57,:99-101 (the consumer);
_build/l3.31-r5census.md section 3 (the choice leg as priced, 0.3-0.7k);
_build/l3.31-lt-report.md lever H2; dev/LESSONS.md (binding: D-21 the
approximation's target is the witness, R-37, I-4, C-6).

THE MINIATURE: a module taking (i) the bridge step as a hypothesis
(a is in L implies a is in Jset gamma for some limit gamma, in whatever
shape the delivered `Reduce`/`p4` machinery makes natural: state it and say
why), and (ii) the delivered order/choice exports; deliver the choice
function's pick and its two obligations (the pick is a member; the pick is
canonical/unique per the order). Then state, and check as far as the
miniature allows, the `Model:57` re-point's shape: what `L⊨ZFC`'s
`hasChoice` field would consume.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE agda process at a time (four
sibling agents run concurrently). STOP-LINE 200 probe lines. Wall protocol
per the law book. No git commands. Do not touch .claude/ or generated files.
Record every consumed hypothesis; a GO that consumed an unavailable
hypothesis is a false GO.

RETURN (_build/l3.32-t3-report.md; final message = compressed verdict):
GO/NO-GO; the pick's line count and its obligations; the exact bridge-step
hypothesis shape the re-home needs (this feeds the bridge's export design);
what `Model:57` would consume; the extrapolation to the re-home chapter's
band (currently 0.30-0.65k naive) and whether it moves to x1.3; walls by
LESSONS class.
