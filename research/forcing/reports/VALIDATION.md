# Verification record, 2026-09-20

## Completed

* `python3 research/forcing/archive.py verify`: exit 0, 12,461 manifest entries
  and 1,090 distinct SHA-256 objects verified.
* Restore round trip for origin `soft-pause-tar`: exit 0, all 1,539 restored
  files match their recorded hashes.
* `python3 research/forcing/archive.py prepare`: exit 0, 124 historical
  production dependency files verified/restored.
* `GHCRTS='-A64m -I0 -M8g' agda K11/CountableCohen.agda`: exit 0.
* `GHCRTS='-A64m -I0 -M8g' agda K11/Corollary.agda`: exit 0, including the
  changed `CohenGeneric` compatibility wrapper.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanPowerTop.agda`: exit 0 after
  narrowing module aliases to the actual suppliers. The first broader-alias
  attempt was stopped after more than eight minutes near the heap limit;
  no mathematical assumption, theorem statement or memory limit changed.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanInjKPairFwd.agda`: exit 0
  after correcting the inherited transport direction described below.
* `GHCRTS='-A64m -I0 -M8g' agda K10/CohenBooleanCHBot.agda`: exit 0,
  including the new `omega-part-top` supplier. The accepted check uses narrow
  aliases and an explicit `Σ≡Prop` path between the two presentations of the
  checked omega name. No proof-bearing name components need to be unfolded
  to establish that path. Both `omega-top` and `power-top` are now proved.
* `GHCRTS='-A64m -I0 -M8g' agda src/Milestones.lagda.md`: exit 0.
* `make lint`: exit 0 after generating the historical dependency source in an
  ignored directory, separately from the current textbook.
* `make test`: exit 0.
* Complete `make check` using the installed Agda frontend: exit 0, including
  the full Milestones closure, all lint/framework gates and 175 passing tests:

```
make check -o typecheck-stage -o /opt/homebrew/bin/agda \
  BEDROCK_AGDA=/opt/homebrew/bin/agda AGDA=/opt/homebrew/bin/agda \
  TYPECHECK_ROOT=. AGDA_DIR=/Users/alsg/.agda
```

The two `-o` options avoid rebuilding the installed compiler and copying `src`
to the private staging directory. The actual typecheck runs against current
`src/Milestones.lagda.md`; none of the proof, lint or test gates is omitted.

## Environment and interrupted checks

Plain `make check` returned exit 2 while building the custom frontend:
`FileNotFoundError: [Errno 2] No such file or directory: 'cabal'`. This is an
environment failure before typechecking. The installed-Agda run above provides
the proof and gate validation, not validation of the custom frontend build.

The first serial endpoint run was cold. Completed module logs are preserved
under `cold-endpoints/`. It was intentionally stopped during
`CohenBooleanLeastEmpty` (exit 143), then restarted after reusing 211 missing
interfaces from the original checkpoint. The restarted run is an incremental
check, not a complete cold benchmark. Agda rechecks changed sources/dependencies.

An overlapping named omega check was also intentionally terminated to avoid
duplicating expensive dependency checks. Its partial log is `omega-part.log`;
it is not successful evidence. Final acceptance depends on the resumed gate.

The GLM drafting request returned HTTP 429/code 1309 (expired subscription),
producing no draft. There was no approval rejection or retry loop.
The coordinator authored the changes; GPT 5.6 Sol supplied read-only source
review of endpoint assumptions, dependent types and proof orientations.

## Discovered historical source error

The resumed endpoint run returned exit 42 at
`K10/CohenBooleanInjKPairFwd.agda:308.26-45`:

```
error: [UnequalTerms]
4 != 2 of type ℕ
when checking that the expression sgl-unique s x σ hs has type
```

The open goal is
`val kpairSglφ (env4 σ p x y) ≤ᴮ eq (fst σ) (check s)`.
`sgl-match` identifies that four-slot formula value with the two-slot singleton
formula value. The inherited substitution used the path forward while supplying
a proof at its destination; it needs `sym (sgl-match σ p x y)`.
The original diagnostic is retained in `kpair-original-error.log`.

## Final endpoint regression

`sh verify-k10-k11.sh`: exit 0. All 69 positive endpoint modules passed.
`MissingFunction`, `MissingValueFunction`, `MissingCheckReading`, and
`MissingOnto` each returned the expected exit 42 and the required
`[UnequalTerms]` diagnostic. Final logs are in `endpoint-regression/`.
`checks.json` records the checked source hashes and exit codes.

Two intermediate launches returned exit 1 because all Agda slots were occupied.
The runner now waits in two-second intervals for a slot before each check.
Earlier overlapping CHBot attempts were intentionally stopped; the accepted
named log is `chbot-transport.log`, and the final regression checks it again.

`make lint` after the final prose changes: exit 0. No pending compiler process
belongs to this research verification. The remaining work is mathematical,
as listed in `../STATUS.md`, not a claim of completed K10/K11 acceptance.

The final pre-commit run of the installed-Agda `make check` command above also
returned exit 0; its complete log is `final-main-check.log`.
