# [L3.32-T21] The square law's core (the cardinal row's dominant wall)
tier: codex (default)

GOAL: `[T16]` delivered the pairing chapter conditional on ONE named bound,
the square law (an infinite ordinal's product is equinumerous with it), and
priced its missing ordinal arithmetic at 300-460 naive / 500-950 calibrated.
Under D22 that band is a survey guess and must be measured before it is
funded. Probe its decisive core.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeSquareLaw.agda` (untracked) and
`_build/l3.32-t21-report.md` ONLY. No master, never `Everything`.
SCOPE (read, in order): `src/L/Ordinal/Pairing.lagda.md` (THE CONSUMER: its
`Pairing` module's `bound`/`bound-inj` is the exact shape you must aim at, and
its `col→τ` bijection is what you compose with), `_build/l3.32-t16-report.md`
(the route taken, what it prices and why), `_build/l3.32-t9-report.md` (target
T2, where the wall was first met), `src/L/Ordinal.lagda.md`,
`src/L/Ordinal/Linear.lagda.md`, `src/L/Ordinal/Stages.lagda.md` (the delivered
ordinal material and the house idiom), `_build/literature/jech13.txt` and
`dev2.txt` (the classical proof: Hessenberg's theorem and the induction it
runs; cite what you use), `dev/LESSONS.md` (binding).

D-10 FIRST, and it matters here: the classical theorem is true, so the
question is not its truth but **which formulation of it this tree can carry**.
The textbook route needs ordinal addition and multiplication as set recursions
plus a doubling lemma; ask whether the delivered material admits a cheaper
equivalent route to the SAME bound (an injection from the order type into the
ordinal), and say what each route costs. A cheaper route that reaches the
bound is worth more than a faithful reproduction of the textbook one.

THE MINIATURE: the decisive step of whichever route you judge cheapest, at the
smallest scale that settles the price. If the base case at omega and the
successor step are the risk, do those; if the limit case is, do that. Name what
you did not do and why.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time. STOP-LINE
350 probe lines. No postulate, no hole, no TERMINATING. C-6 controls. No git.
Never touch `.claude/`.

RETURN (`_build/l3.32-t21-report.md`; final message = compressed verdict): the
route chosen and why; what its decisive step measured; **what the square law
should now be funded at**, in both calibers, against T16's 300-460 naive; the
pieces of ordinal arithmetic it genuinely needs, named; and the walls by
LESSONS class.
