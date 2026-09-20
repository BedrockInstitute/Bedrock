# Research material recovered from the main worktree

This import removes forcing research leftovers from the main worktree without
changing the production source tree or overwriting the research branch's
current documents. The manifest records the original path, byte size, SHA-256,
and exact retained location for every one of 211 files.

* 11 literature files concern Boolean-valued models, Cohen forcing, or geology.
  Five already have byte-identical tracked copies. Six differ from the current
  research documents and are preserved verbatim under `files/dev/literature/`.
  These are historical snapshots, not replacements for the current roadmap.
  Their original relative links are retained as source bytes; resolve literature
  references against the current `dev/literature/` directory when necessary.
* 76 historical check logs already have byte-identical tracked report copies.
  They are historical verification evidence, not newly executed checks.
* 124 generated historical dependency files match the immutable source archive.
  Their content-addressed gzip objects and original manifest paths are recorded;
  `archive.py prepare` regenerates them in the research worktree.

Only exact byte matches are deduplicated. Source copies are removed only after
all retained bytes have been verified and the import committed. Existing
archive objects and original manifests are unchanged.

The untracked `scripts/refactor/rewrite-quantifier-wrappers.py` rewrites generic
quantifier syntax throughout production `src`; it is unrelated to the forcing
research and remains in the main worktree. The existing tracked modification
to `src/Base/Classical.lagda.md` is outside this import and is left untouched.
