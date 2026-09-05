# [L3.32-T7] The wholesale-retirement recon (the retirement discipline applied)
tier: codex (default)

GOAL (owner-ordered 2026-08-04, a discipline raised to equal standing with
the sunk-cost rule): a partial retirement scoped to keep a surviving
consumer working is the WRONG SHAPE by default. Retirement is planned from
the REWRITE side: first price what the IDEAL-FORM version of the needed
content costs written fresh today, then retire the old chapter WHOLESALE.
Apply this to the ruled route's whole retirement ledger, starting with the
case that provoked the ruling.

CWD: /Users/alsg/Agentic/Bedrock

## The provoking case (do this one first and hardest)

`_build/l3.32-t4-report.md` concluded that `StepInL` (1,989 non-blank lines)
CANNOT retire, because `p4`/`RudBelow`'s successor clause calls `values∈L`
(Bridge.lagda.md:800) and `stepSet∈L` (Bridge.lagda.md:809) verbatim, and
their transitive closure inside the chapter is effectively the whole file.
It priced the alternative by quoting D-19 ("price a port against the
retiring chapter's transitive closure") and concluded a rebuild is dearer
than keeping.

**That reasoning is under review and you must test it, not inherit it.**
D-19 governs PORTS (re-proving the same shapes at a new carrier). The
question here is an IDEAL-FORM REWRITE: what does the content
`p4` actually needs cost if written fresh TODAY, with the current law book
and the delivered engine, in whatever shape is best rather than the shape
history produced? The nearest measurement on record cuts the other way: the
R5p probe measured 0.62x churn on a comparable re-founding, with whole
populations that DELETE rather than port (`_build/l3.31-r5probe-report.md`,
the per-declaration table).

Deliver, with evidence:
1. **The exact obligation.** What do `p4`/`RudBelow`'s two call sites need,
   stated minimally (not "these two theorems" but the propositions they
   supply and at what generality). Read Bridge.lagda.md:760-827 and
   StepInL.lagda.md's `values∈L` (:367-370) and `stepSet∈L` (:2419-2430).
2. **Why the delivered chapter is 1,989 lines.** Anatomise it: which parts
   are the mathematics, which are the sixteen-arm case bookkeeping, which
   are frames/readers that the fresh Sigma-1 face or the delivered
   Describe/Realize/Switch engine would now supply, and which exist only
   because of a formulation choice the law book has since superseded (the
   inner-world reading D-16, the carrier-level combinators I-4, the written
   branch types I-5, the small-index discipline R-35, the sealed reads
   R-36/R-38). Quantify each bucket in lines with ranges.
3. **The ideal-form price.** What would the same obligation cost written
   fresh today: both calibers, per-part, with a named delivered comparable
   anchoring each part. Say explicitly which parts DELETE (the R5p
   phenomenon: content that evaporates when the right former is used) and
   which genuinely port.
4. **The verdict.** Keep 1,989 standing, or rewrite at N lines and retire
   1,989 wholesale? State the standing-line arithmetic both ways against the
   ruled ledger (standing 14,726 with StepInL kept; 12,737 plus the rewrite
   without it) and the endpoint consequence (the naive band is 19.24-24.83k
   with it kept; the owner's line is 25k).
5. **The gate.** The cheapest decisive D-1 probe that would confirm your
   ideal-form price before any code moves: exact target statements, stop
   line, and what green vs red imply.

## Then generalise (the second half, do not skip)

Sweep the ruled route's ENTIRE retirement ledger
(`_build/l3.31-lt-report.md`'s retirement table, re-verified on today's
tree) for the same error class: every row whose retirement was trimmed, or
whose survival was justified, by "a survivor consumes it" rather than by an
ideal-form rewrite price. Candidates to examine explicitly: `L/Coding/Base`
(187, retained only because `Describe:58-59` uses two lemmas); `SatSets`
(1,289, retained on three warrants: is the retained SHAPE the ideal one, or
is it retained because it happens to exist?); the retained Rud trunk core
(5,372) against what the ruled configuration actually consumes; and any
retained shared-foundation module whose survival rests on a single
consumer. For each: is this a genuine keep, or a keep-because-someone-uses-
it that an ideal-form rewrite would dissolve? Price the ones that qualify.

## Method (binding)

- Every claim `file:line`; every size measured, not remembered.
- Both calibers (naive; calibrated by the R5p split: probed x1.3, unprobed
  x3). Every price anchored on a NAMED delivered comparable.
- Adversarial honesty in BOTH directions: this brief argues for wholesale
  retirement, so the failure mode to guard against is over-optimism about
  rewrite costs. If the honest answer for a row is "keeping really is
  cheaper", say so with the arithmetic; the owner wants the discipline
  applied, not a predetermined answer.
- Blast radius per candidate, and whether it can be staged behind the wing.
- No collision with work in flight: `src/L/Rud/Bridge.lagda.md` is being
  edited right now by a sibling agent; read it but never write it.

## Deliverable

`_build/l3.32-t7-report.md` (deliver the full report as your final message
too): the StepInL anatomy and verdict with the arithmetic both ways; the
ledger sweep table; the ranked list of rows that should convert from
"partial/keep" to "rewrite and retire wholesale"; the named gates.

CONSTRAINTS: read-only; zero agda; no git; never touch `.claude/` or
generated files. dev/LESSONS.md binds (D-10, D-16, D-19, D-24, P-h, I-4,
I-5, R-35, R-36, R-38, C-14).
