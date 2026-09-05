# [L3.31-IF-Ip] D-1 probe: one level-story reading, generic in the carrier
tier: codex (default)

GOAL: test the generic-cone architecture's central assumption at real scale:
write ONE reading of the L-level story GENERIC in the restriction class
(P-h style: the carrier/structure a module parameter), instantiate it at 𝒮ʟ
AND at a transitive set carrier, both green; measure the genericity premium
against the delivered monomorphic twin.

CWD: /Users/alsg/Agentic/Bedrock

SCOPE (read): _build/l3.31-ifrecon.md section 8.5 first bullet and section 3;
_build/l3.31-ivprobe-report.md:600-640 (the statement-layer instances:
FOL.Absoluteness.Single, Bounding.Relabel) and :632-634 (the named cheap
probe); src/L/Coding/Sequence.lagda.md:361-378 (LsetGraph and its readings;
pick ONE representative reading, a DefAt-class clause, as the subject);
src/L/Hierarchy.lagda.md exports; dev/LESSONS.md (binding: P-h, I-4, D-16,
I-5, R-35, R-37, C-6).
SCOPE (write): src/ProbeGenericRead.agda (untracked probe) and
_build/l3.31-ifip-report.md ONLY.

CONSTRAINTS: every agda run `GHCRTS=-M8g agda <file>`, ONE agda process at a
time (two sibling probes run concurrently on the same wide tier; never
exceed your own single process). STOP-LINE 400 probe lines. Wall protocol:
isolate, cure per the law book, two failed distinct cures on a piece =
record precisely and move on. No master edits, no Everything, no git
commands at all. Record every hypothesis the generic reading consumes (a GO
that quietly consumed an uninstantiable hypothesis is a false GO). C-6
perturbation controls on any refutation-shaped claim.

RETURN (_build/l3.31-ifip-report.md; final message = compressed verdict):
GO/NO-GO; the generic reading's line count vs the delivered monomorphic
twin's (the measured genericity premium); both instantiations' evidence;
walls by LESSONS class with file:line; the extrapolation: what this measures
for the I-ideal items I-6a/I-6f (600-1,350 naive) and whether they move from
x3 to x1.3.

- make check is the commit gate; you do not commit. Do not git push under
  any circumstances. Never touch .claude/ or generated files. Inside agda
  blocks English only.
