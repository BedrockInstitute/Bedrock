# [L3.32-T4] The retirement design recon (gate 6: the naive PASS's protector)
tier: codex (default)

GOAL: the ruled configuration's naive PASS (endpoint 17.24-22.85k against
the owner's 25k line) DEPENDS on retiring a 3,761-line Rud cluster
(`CodeSet` 193, `CodePred` 1,186, `StepInL` 1,989, `BaseBlock` 393). If that
cluster must be retained the naive top rises to about 26.6k and BREACHES.
The cluster contains `StepInL`'s `values∈L` and `stepSet∈L`, which are TRUE
delivered theorems currently feeding `Bridge.Reduce`'s telescope. Settle,
by design analysis on the delivered code, whether the RESHAPED bridge (the
R2' Q-induction over the index tower gamma(beta) = omega times (beta+1))
still needs them, and what a re-typed `SatTable` chain actually consumes.
Read-only; zero agda; the answer decides whether the ruled endpoint holds.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): _build/l3.32-t4-report.md ONLY (deliver the full report as
your final message too, in case the sandbox blocks the write).
SCOPE (read, in order): _build/l3.31-r2lever-report.md (the R2' composed
design: the closed-form tower, the element-level limit statement, the
fresh-Sigma-1 face, and `full-switch-⊇` as the limit case's membership
step); _build/p2-fork-recon.md section 2.0 (Q's three clauses: zero,
successor via BlockPowLim, limit); src/L/Rud/Bridge.lagda.md (`Reduce`'s
current telescope at :742 and its four hypotheses, `p3`/`p4`/`RudBelow`);
src/L/Rud/SatTable.lagda.md (the whole chain: `Pow`, `Coded`, `TwoLimit`,
`powFragment`, `defPow`, `fragment`, `BlockPow`/`BlockPowLim`, `+ω-fits`,
`block→general`, `slot-empty`, `Landing`, and its import list :62-69);
src/L/Rud/StepInL.lagda.md (what `values∈L` and `stepSet∈L` actually state
and what they are used by); src/L/Rud/BaseBlock.lagda.md (`baseDefPow`);
_build/l3.31-lt-report.md (the retirement table and gate 6);
dev/LESSONS.md (binding: D-10, D-15, D-19, D-24).

THE QUESTIONS, in order:
1. Under the reshaped Q induction, which of `Reduce`'s four current
   hypotheses survive as obligations at all? State Q's three clauses in the
   repo's vocabulary and, for each, name exactly which delivered export
   discharges it and from which chapter. `values∈L`/`stepSet∈L` are
   statements about the DEF tower's step being definable-in-L; the reshaped
   successor step is `BlockPowLim`. Do the two meet, or does one supersede
   the other?
2. What does a re-typed `SatTable` need to import once `BlockPow` becomes
   `BlockPowLim` proved on the fresh face and `P2`'s `SatRelation` is
   re-stated there? Walk its chain export by export and mark each RETAINED /
   RE-TYPED / DEAD, with the reason.
3. The honest verdict: is the 3,761-line retirement (a) fully available,
   (b) partially available (name the lines that must stay and why), or
   (c) unavailable? Re-state the naive endpoint under your verdict.
4. If any of the four files must partially survive, name the minimal
   surviving fragment and price it.

CONSTRAINTS: read-only; zero agda; no git. Evidence file:line on every
claim. Adversarial honesty: a verdict that the retirement is unavailable is
a fully valid and important result; do not shade toward the ruled plan.
Do not touch .claude/ or generated files.

RETURN: the four answers, the export-by-export table, the verdict, and the
re-stated endpoint.
