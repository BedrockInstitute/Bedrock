# [L3.32-T28] The code-set supplier, ideal form (so the coded cluster retires whole)
tier: codex (default)

GOAL: D17, applied. `[T25]` found the successor step still needs a CODE SET AS
A MEMBER of the level, which today only the delivered coded machinery supplies,
and concluded that CodeSet plus CodePred, 1,379 lines, must stay. Under D17
that conclusion is the WRONG SHAPE BY DEFAULT: a keep justified by a survivor
consuming it is exactly what the discipline forbids taking at face value. The
move is not to measure whether to keep, it is to **write, from actual need, the
minimal fresh module that supplies what the successor step consumes, so the old
1,379 lines retire wholesale.** Build that module.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/Rud/` (named by subject) plus
`_build/l3.32-t28-report.md`. Never `src/Everything.lagda.md`. Do not edit any
existing master; NAME any `private` export you need instead of un-privating it.
SCOPE (read, in order): `_build/l3.32-t25-report.md` IN FULL, especially its
statement of exactly what the successor step consumes and its two mechanized
reasons the face cannot supply it; `src/ProbeSatRel.agda` (the re-stated
interface it built: your module must satisfy that consumer, not a new one);
`src/L/Rud/CodePred.lagda.md` and `src/L/Rud/CodeSet.lagda.md` (THE INCUMBENT:
read what `At.codeSet∈J` proves and, more importantly, **how much more than
that it proves**, because the gap between "what is needed" and "what is
delivered" is the whole thesis of this dispatch); `_build/k2-report.md` and
`_build/l3.31-p1-report.md` (WHY the general form is unreachable: block
membership forces a uniform offset bound, and the codes are cofinal at a
successor index) and `_build/k4-report.md` section 3 (**THE KEY**: at a LIMIT
index the codes are ALREADY members, which is what `blockPow-at-limit` used;
the corrected target lives at a limit and the successor step's index is a
limit by construction of the extension); `src/L/Rud/SatSets.lagda.md`,
`src/L/Rud/OrdBlocks.lagda.md`, `src/L/InitialSegment.lagda.md`,
`src/L/PairAtoms.lagda.md` (the delivered engine the fresh module should stand
on); `dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding).

THE THESIS TO TEST BY BUILDING: the incumbent is large because it proves the
code set's membership AT EVERY ARITY OVER A TWO-LIMIT TELESCOPE, and the
successor step needs it at ONE index, a limit, at the arity its consumer
actually uses. Build only what is needed. D-10 first: state precisely what the
consumer needs, check that statement's truth at the intended index before
proving it, and record any correction beside the original.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (siblings
run). **STOP-LINE 500 non-blank in-fence lines.** If the fresh module cannot
supply the consumer inside it, STOP and report what is built, what remains, and
what the remainder would cost: that outcome means the incumbent's size is
justified and the keep genuinely wins, which is a valid and important result.
No postulate, no hole, no TERMINATING. Trilingual prose (en and zh), no em
dash, English only inside fences. Both linters clean. Do NOT run `make check`.
No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t28-report.md`; final message = the verdict): the
exports and the exact consumer obligation they discharge; **the measured size
against the incumbent's 1,379**, with an honest account of what the incumbent
proves that the fresh module deliberately does not; whether CodeSet and
CodePred can now retire wholesale; the walls by LESSONS class; and the fact
that the file needs `Everything` wiring.
