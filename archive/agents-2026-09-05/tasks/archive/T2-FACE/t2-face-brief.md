# [L3.32-T2] The fresh-generic Sigma-1 face probe (gates 1 and 2 fused)
tier: codex (default)

GOAL: measure the ruled architecture's central bet. The GCH wing's W1 IS a
fresh Sigma-1 face for the L-tower's level story, written CARRIER-GENERIC
from birth and instantiated where each consumer needs it (the wing at the
Def carrier, the bridge's L-sigma at a rud carrier, W5b at a collapsed
transitive set). Build the smallest honest version of that face generic,
instantiate it at TWO carriers, and measure.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): src/ProbeFace.agda (untracked) and
_build/l3.32-t2-report.md ONLY. No master file, never Everything.
SCOPE (read, in order): src/ProbeGenericRead.agda (THE PRECEDENT: the Ip
probe already wrote one reading generic in the carrier and instantiated at
two carriers, premium x1.36; build on its shape); _build/l3.31-ifip-report.md
(its measurements and method); _build/l3.31-r2lever-report.md facts 1-4 (why
the face is built FRESH as Devlin's initial-segment formula rather than as a
rewrite of LsetGraph; `full-switch-⊇` at SatSets:1650 is the limit case's
membership step); _build/literature/dev6.txt:1665-1678 (Devlin's phi, the
initial-segment formula); src/L/Rud/SatSets.lagda.md (the retained engine),
src/L/Rud/Realize.lagda.md (realize/realize-defSet), src/FOL/Absoluteness
.lagda.md (Single) and the Bounding.Relabel transport; dev/LESSONS.md
(binding: P-h, D-16, D-21, I-4, I-5, R-35, R-37, C-6).

THE MINIATURE (two arms over ONE generic definition):
Write the initial-segment story as an object-language formula GENERIC in the
carrier/structure (module parameters, P-h at full strength): "x is in the
range of some L-tower initial segment lying in the carrier". Keep it as
small as is honest: one Def-step clause with its K(u)-binding witness plus
the range read; do not build the whole tower story.
ARM A (gate 2, the face's statement layer): instantiate at the generic
carrier and prove ONE adequacy direction against the delivered defSet face.
ARM B (gate 1, the bridge's L-sigma): instantiate at a rud carrier
(⟪ Sset C ⟫) and check the TWO-WAY adequacy against `DefOf.defSet`.
Record which hypotheses each arm consumes (D-10: a GO that quietly consumed
an uninstantiable hypothesis is a false GO). C-6 perturbation controls on
any refutation-shaped claim.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE agda process at a time (four
sibling agents run concurrently). STOP-LINE 400 probe lines. Wall protocol:
isolate the minimal failing shape, try the law-book cures, two failed
distinct cures on one piece = record precisely and move on. No git commands.
Do not touch .claude/ or generated files. English only inside agda.

RETURN (_build/l3.32-t2-report.md; final message = compressed verdict):
GO/NO-GO per arm; the generic definition's line count and the per-arm
instantiation cost (the measured premium); every hypothesis consumed; walls
by LESSONS class with file:line; and the extrapolation: what this measures
for the face's statement layer (currently 400-750 naive at x3) and for the
bridge's L-sigma row (0.15-0.40k), i.e. whether each moves to x1.3.
