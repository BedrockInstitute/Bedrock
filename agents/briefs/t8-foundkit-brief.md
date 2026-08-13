# [L3.32-T8] The foundation kit batch (C3, C1, C4, C5; plus C2's gate only)
tier: codex (default)

GOAL: execute the four accepted foundation candidates from
`_build/l3.32-t6-report.md` (read its sections 2 and 5 FIRST: the priced
table and the per-candidate D-1 gates are your mandate and your stop-lines),
in one batch because they share edit surfaces. Then run C2's gate as a probe
only. Every item has a stop-line; a stop-line trip means REVERT that item
and report, not push through.

CWD: /Users/alsg/Agentic/Bedrock

## The four items, in this order (each one green before the next starts)

**C3 (1 line).** `src/V/Coding.lagda.md:339-372`: delete `private` on the
eight pair/singleton helpers so consumers stop re-deriving them (C-14's
third instance was measured at `src/ProbeForce.agda:49-59`). Export-only:
no name changes, no behaviour changes.

**C1 (about 50 new, about 94 deleted).** Add a `defSet` computation table to
`src/L/Definability.lagda.md` (`defSet-⊥`, `defSet-pair`, `defSet-union`,
`defSet-fin` in the shapes T6 section 5 specifies), then delete the four
`defSet≡` proofs in `src/L/Axioms/Basic.lagda.md` (`:494-502`, `:562-585`,
`:673-711`, `:308-350`) and re-derive `∅∈𝒟ₒ`, `pair∈𝒟ₒ`,
`UnionOf.union∈𝒟ₒ`, `FinOf.finSet∈𝒟ₒ` from the table.
STOP-LINE: if the table plus the four re-derivations exceed 57 lines
(60 percent of the 94 replaced), the table does not pay: revert C1 and
report. Also revert if any table entry needs resizing or LEM (the small
reading at the carrier is the whole point).

**C4 (about 20 new).** New module `src/V/Presentation.lagda.md` exporting
`member`, `fiber`, `↪-inj`, `∈ₛ↪`; then re-derive the measured consumers as
one- or two-line calls: `src/L/Axioms/Separation.lagda.md:131-134` and
`:276-279`, `src/L/Axioms/Basic.lagda.md:103-109`, and the other inline
fiber sites you find by grep in `L/Axioms/*` and `L/Definability`.
STOP-LINE: kit over 30 lines, or any re-derivation failing to drop to two
lines or fewer, or any change to an existing site's small-to-big membership
transport DIRECTION (P-d/R-37 watch): revert C4 and report.
NOTE: a new master needs trilingual prose per `dev/STYLE-i18n.md` (en and zh
marker blocks; ja optional) and must NOT be added to `src/Everything.lagda.md`
(the orchestrator wires it; say in your report that it needs wiring).

**C5 (about 20 new).** Add the uniqueness frame to `src/FOL/ZFModel.lagda.md`
(additive: `℩-fst-eq` plus the uniqueness aliases T6 section 5 names), then
re-derive `src/L/Axioms/Numerals.lagda.md:492-505` and `:517-522` from it.
STOP-LINE: if those two re-derivations do not shrink from 14 lines to six or
fewer, the kit's immediate value is not there: revert C5 and report (its
continuation value alone does not justify it).

## Then C2's GATE ONLY (probe, 60 lines, do not ship the module)

In `src/ProbeFold.agda` (untracked): define the `Formula` algebra and ONE
generic fusion lemma, then re-express THREE delivered pairs as instances:
`renameFo`+`⊨-rename` (`FOL/Manipulation/Renaming.lagda.md:235-247`,
`:304-324`), `mapFo`+`⊨-map` (`Relabelling.lagda.md:54-67`, `:154-169`),
`relativize`+`relativize-correct` (`Relativize.lagda.md:48-60`, `:142-159`).
STOP-LINE 60 probe lines. RED if any re-expression costs more lines than the
original, or the fusion lemma fails to typecheck inside the stop-line, or a
re-expressed walk changes definitional behaviour on a concrete sample (check
`refl` on one instance: P-a/P-d/R-23 watch). Report the verdict; the module
itself is NOT built in this batch.

## Constraints

- `GHCRTS=-M8g agda <file>`, ONE agda process at a time. Typecheck every
  master you touch, in dependency order, after each item.
- NEVER touch `src/Everything.lagda.md` (orchestrator-only), `.claude/`, or
  generated files. NO git commands at all.
- After the last item: `python3 scripts/lint-agda.py` and
  `python3 scripts/lint-prose.py` on every file you touched, both clean.
- EXPORTS FROZEN except the named additions (C3 publicizes, C1/C4/C5 add).
  No renames, no signature changes to anything that already exists.
- Prose rules: no em dash in any language; CJK full-width sentence
  punctuation, half-width parentheses, corner-bracket quotes, no space
  between CJK characters; inside agda fences English only; markers never
  inside a fence. Translation terms come from `dev/glossary.toml`.
- `dev/LESSONS.md` binds (P-h, D-10, I-4, I-5, R-35, R-36, R-37, C-11,
  C-14).
- A sibling read-only agent is running; `src/L/Rud/*` is not your territory
  and you have no reason to touch it.

## Report (`_build/l3.32-t8-report.md`; final message = the summary)

Per item: measured lines before and after (non-blank in-fence), whether the
stop-line held, the export-face delta, the typecheck result. Then C2's gate
verdict with its measurements. Then the batch total: lines written, lines
deleted, net standing delta, measured against T6's predictions (C3 1/0/8-16,
C1 50/25-40/50-110, C4 20/20-35/40-60, C5 20/20-35/20-50) with any
divergence explained. Name every file that needs `Everything` wiring.
