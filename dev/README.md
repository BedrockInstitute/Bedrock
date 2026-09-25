# Development workspace

This directory holds working research notes, active investigations and temporary
plans. It is not a configuration or permanent-specification directory.

Long-lived book/site configuration and authoring contracts live under
[site/](../site/README.md): the reading catalog, glossary, styles, teaching
architecture, toolchain policy and lint inventories. Shared implementation and
renderer contracts belong to Outcrop.

Reusable commands and tests belong in [scripts/](../scripts/README.md) or
Outcrop, not in permanent copies of one-off scripts here. This directory is not
a build input or a record that a past test still certifies the current revision.

## Active editorial review

[INLINE-LATEX-REVIEW.md](INLINE-LATEX-REVIEW.md) lists existing inline LaTeX for
human decisions grouped by source paragraph; all formulas in a paragraph share
one review ID, while translations and separate list items remain separate.
No formula is implicitly approved. Figure-reference paragraphs conforming to
the fixed-wording rule are mechanically allowed and labeled separately.
Regenerate it with
`.venv/bin/python -m outcrop lint --config site/project.json --project-root . --inline-math-inventory markdown`.
Approved decisions belong in `site/inline-latex-approvals.json`; rejected cases
are revised in the source book. Explicit temporary allowances for later chapters
are displayed separately and end when `human_reviewed` becomes true, not when
chapter text changes. Regenerating this report changes neither approvals nor
review flags. Once review is complete, delete this temporary
inventory and its README references, retaining the durable policy and decisions.

## Research evidence

`literature/` contains source digests, bibliography and investigations cited by
the book's editorial work. Start with [BIBLIOGRAPHY.md](literature/BIBLIOGRAPHY.md)
and [primary-sources.md](literature/primary-sources.md). These are research notes,
not additional authoring rules or proof certificates. Check their citations and
current consumers before promoting or removing material; the directory's
temporary role does not make referenced evidence disposable.

## Lifecycle

- Give new working material a clear purpose and current status.
- On completion, promote lasting decisions into the relevant site specification
  or source exposition, then delete the one-off plan, migration or report.
- Keep generated experiments, logs, downloads and screenshots under ignored
  `_build/` or a task-specific temporary directory, not in Git.
- Review `literature/` as research working material. Notes cited by the glossary
  or an active investigation must not be removed until their necessary evidence
  is preserved in the consuming document or an authoritative source reference.
- Git history retains deleted task records; do not create a second archive of
  finished tasks inside this directory.
