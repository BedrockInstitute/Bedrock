# [L3.32-T19] W3's gate, run
tier: codex (default)

GOAL: D22 says no block is funded at the coarse class without first trying to
measure it. `[T14]` designed W3's gate and did not run it. Run it, and report
what W3 should be funded at.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeW3.agda` (untracked) and `_build/l3.32-t19-report.md`
ONLY. No master, never `Everything`.
SCOPE (read): `_build/l3.32-t14-report.md` IN FULL, especially its gate design
(the exact target statements and stop-line are its, not yours to redesign) and
its band table with the class split; `src/L/Ordinal.lagda.md` and
`src/L/Ordinal/Linear.lagda.md`; `src/L/Rud/Order.lagda.md` (the delivered
producer order); `src/L/InitialSegment.lagda.md` (NEW, the face: if the order's
formula rides it, instantiate rather than rebuild); `src/V/Presentation.lagda.md`
(use the kit); `dev/LESSONS.md` (binding).

Run T14's gate exactly as designed. Where its spec is ambiguous, resolve by
the delivered code and SAY SO in the report rather than redesigning silently.
D-10 first: check each target's truth at the intended generality before
proving it, and record any correction beside the original.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (siblings
run). STOP-LINE as T14 set it; if T14 set none for a piece, 300 lines. No
postulate, no hole, no TERMINATING. C-6 controls on any refutation-shaped
claim. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t19-report.md`; final message = compressed verdict):
per-target green or red with sizes; the D-10 answers; **what W3 should now be
funded at in both calibers**, with which rows move from 3x to 1.3x; and the
walls by LESSONS class.
