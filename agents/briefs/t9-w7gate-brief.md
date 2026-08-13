# [L3.32-T9] The W7 cardinal gate (margin work: wave 2's first gate)
tier: codex (default)

GOAL: run the decisive gate T5 designed for W7's riskiest step. W7's
re-price put the endpoint's pessimistic corner on the owner's 25k line, so
this gate is literally margin work. Run it EXACTLY as specified in
`_build/l3.32-t5-report.md` section 4 (read that section first: the three
targets, the stop-line, and what green versus red imply are the mandate).

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeCard.agda` (untracked) and
`_build/l3.32-t9-report.md` ONLY. No master file, never `Everything`.
SCOPE (read): `_build/l3.32-t5-report.md` (sections 2-4 especially),
`_build/literature/dev2.txt` around the II.5 material T5 cites,
`src/FOL/Syntax.lagda.md` (the formula shape the count runs on),
`src/L/Axioms/Basic.lagda.md` (`Lset-suc`) READ-ONLY (a sibling agent is
editing it: read it, never write it, and if it is mid-edit, work from the
committed version via the git object store rather than the working file),
`src/L/Rud/Order.lagda.md`, `dev/LESSONS.md` (binding).

THE THREE TARGETS (T5's spec, verbatim in intent):
T1 the count: every formula over a carrier is a constant-free shape plus a
finite tuple of constants, as an injection.
T2 the product bound: for an infinite ordinal, finite tuples over it inject
into it (the kappa-times-kappa core; T5 flags this as having NO in-tree
precedent, so it is where the risk lives).
T3 the payoff: from the induction hypothesis plus T1 and T2 and `Lset-suc`,
the definable power of a stage injects into the stage's index.

CONSTRAINTS: `GHCRTS="-A64m -I0 -M12g" agda <file>`, ONE agda process at a
time (three sibling agents run concurrently; never exceed your own single
process). STOP-LINE 400 code lines. No postulate, no hole, no TERMINATING.
Wall protocol per the law book; C-6 controls on any refutation-shaped claim;
record every consumed hypothesis (D-10). No git commands. Never touch
`.claude/` or generated files.

RETURN (`_build/l3.32-t9-report.md`; final message = compressed verdict):
per-target GREEN or RED with line counts and wall times; which delivered
exports carried each; the walls by LESSONS class; and the band consequence
stated in T5's own terms (green moves the cardinal row to x1.3 and W7
calibrated to about 2.17-4.49k; red re-prices the cardinal row to about
0.75-1.30k naive). If T2 walls, say so plainly and price the ordinal-pairing
chapter it implies: that is a valid and important result.
