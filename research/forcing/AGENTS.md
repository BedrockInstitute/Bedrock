# Forcing continuation

This directory is the forcing research workspace on branch `research/forcing`. Read
`STATUS.md`, `reports/VALIDATION.md`, and `notes/cohen-implementation-roadmap-2026-09.md`
before making completion claims. K10 and the full K11 integration remain open.

* Edit research proofs in `active/`. Do not change `objects/`, `manifest.json`,
  `containers.json`, or `provenance.json`; they preserve original external bytes.
* Run `python3 archive.py prepare` to restore historical source dependencies.
  Never repair a proof by modifying `active/reference-production/` unnoticed.
* Preserve current main's `src/` and its L ZFC/GCH Milestones.
* Every accepted Agda file keeps `--safe`. No holes, postulates, unsafe
  termination pragmas, or added host choice principles.
* Use `GHCRTS='-A64m -I0 -M8g' agda <file>` from `active/`, counting machine-wide
  Agda processes before launch. At most two may run concurrently.
* Drafting agents are read-only. Follow the root model guidance; the most recent
  GLM request failed because its subscription expired. Do not retry in a loop.
* Distinguish conditional theorem endpoints, supplied capabilities, actual
  suppliers, historical checks, and fresh checks. A typechecked conditional
  theorem does not discharge its inputs.
* `NameKernel.MemberImage` is not an established consequence of ordinary ZFC.
  Read its definition and `LInstanceImage.memberImage→subclass` before trying to
  instantiate the general Cohen theorem at a countable ground or at L.
