# Forcing research

The `forcing` branch starts at main commit `4cb54fa4`. The independent research
worktree starts at `cbd1510efd048c77a7c3e7af972166f44f7b9338`. Its older production
foundation is retained under `active/reference-production/src`; the current
book and its two Milestones remain unchanged.

## Reproducible preservation

`manifest.json` records each original path, byte count and SHA-256. `objects/`
stores gzip-compressed, content-addressed bytes. Repeated historical snapshots
share objects. Origins:

* `archive`: source files, reports and logs from `bedrock-proofs-archive`.
* `worktree`: `src`, `dev`, AGENTS and library configuration from the external
  `bedrock-forcing-cohen-k0` worktree, including uncommitted research reports.
* `soft-pause-tar`: research files extracted from the historical pause tarball.

Build caches, Agda interfaces, Git internals and macOS resource forks are excluded.
The original tarball's checksum is in `containers.json`; its research contents
are preserved individually, rather than storing its large build caches. The
external originals have not been modified. File contents are preserved; original
permissions and timestamps are not part of this source archive.

```
python3 research/forcing/archive.py verify
python3 research/forcing/archive.py prepare
python3 research/forcing/archive.py list
python3 research/forcing/archive.py restore --origin archive --destination /tmp/forcing-archive-restored
```

`active/` is the editable continuation of `k10-k11-resume-2026-09-18`, initially
copied byte-for-byte except generated caches/logs. `archive.py prepare` restores
the ignored historical production foundation from verified archive objects.
It has its own library file and archived source dependencies, so it does not depend on either
external directory. Historical logs remain available through the object store.

```
cd research/forcing/active
sh verify-k10-k11.sh
```

This gate checks the listed endpoint modules and four expected-failure controls.
It is not a claim that the mathematical completion contract is satisfied: a safe,
typechecked theorem can still take substantial unconstructed hypotheses.
See `STATUS.md` for the current assumption and completion audit.
