# Development workspace

This directory holds working research notes, active investigations and temporary
plans. It is not a configuration or permanent-specification directory.

Long-lived book/site configuration and authoring contracts live under
[site/](../site/README.md): the reading catalog, glossary, styles, teaching
architecture, toolchain policy and lint inventories. Shared implementation and
renderer contracts belong to Outcrop.

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
