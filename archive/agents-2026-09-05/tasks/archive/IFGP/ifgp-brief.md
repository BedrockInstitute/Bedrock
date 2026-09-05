# [L3.31-IF-Gp] The b4e D-1 gate, run exactly as specified
tier: codex (default)

GOAL: run the three-arm D-1 gate that decides whether the Goedel-closure
architecture exists, EXACTLY as specified in
_build/b4e-feasibility-recon.md:47-53 (the three arms with their abort
budgets 240/120/120 s). Green cuts the G route's calibrated band by
2.6-5.4k; red ends the architecture. Either answer is a full success.

CWD: /Users/alsg/Agentic/Bedrock

SCOPE (read): _build/b4e-feasibility-recon.md IN FULL (the retry design and
the gate spec are the mandate; do not redesign them); _build/b4e-report.md
(the original wall trail: the shift image frame, the seek sentence's deep
satisfaction type); _build/r5d2-report.md (the stepForm zero-wall precedent
whose shape the retry mandates); src/L/Godel/Closure.lagda.md and
Levels.lagda.md (the walled region as committed); dev/LESSONS.md (binding:
I-4, I-5, R-36, R-37, the restricted-carrier and named-heads cures).
SCOPE (write): src/ProbeB4eGate.agda (untracked) and
_build/l3.31-ifgp-report.md ONLY.

CONSTRAINTS: every agda run `GHCRTS=-M8g agda <file>` with the specified
per-arm abort budgets enforced by watching wall time (kill and record on
budget breach; a breach IS the arm's result, not a failure of yours). ONE
agda process at a time (sibling probes run concurrently). No master edits,
no Everything, no git commands. The gate's arms are the spec's, verbatim:
do not substitute easier statements.

RETURN (_build/l3.31-ifgp-report.md; final message = compressed verdict):
per-arm result table (green/walled/aborted with wall-clock seconds), the
verdict GREEN/RED for the architecture per the recon's own criterion, the
LESSONS classes of any wall, and one paragraph on what the result does to
the G-ideal band (cite _build/l3.31-ifrecon.md section 4.3).

- Do not git push under any circumstances. Never touch .claude/ or
  generated files. Inside agda blocks English only.
