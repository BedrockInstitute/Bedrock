# Bedrock's Agda environment

The reusable compiler instrumentation, build, dependency installer and parallel
scheduler belong to [Outcrop](../outcrop/docs/AGDA.md). This repository supplies
the mathematics and the choices with which those mechanisms are invoked.

| Choice | Authority |
| --- | --- |
| Compiler source, adapter, Happy and tested host versions | `outcrop/src/outcrop/adapters/agda/resources/manifest.json` |
| Cubical dependency version and archive checksum | `dev/agda-libraries.json` |
| Library name, source root, dependencies and project flags | `bedrock.agda-lib` |
| Entry module, explicit compiler flags and resource budget | `Makefile` |
| Proof obligations | Actual Agda sources and project gates |
| Deployment and cache policy | `.github/workflows/ci.yml` |

After initializing the submodule, install Python 3.11+, GHC/Cabal, `make`, `patch`
and a native C toolchain, then run:

```sh
make bootstrap
_build/outcrop-agda/bin/outcrop-agda --outcrop-version
make check
make site
make serve
```

`make bootstrap` installs Outcrop into `.venv`, invokes its optional compiler
builder and installs the explicit Cubical lock. The compiler stays under
`_build/outcrop-agda`; dependencies stay under `_build/dependencies`, with their
project-local registry under `_build/agda-home`. Global Agda settings are not
changed. Only the build process needs Haskell. Rendering an already generated
backend does not.

The pinned Outcrop submodule identifies the compiler overlay and version adapter
as well as the website implementation. The legacy `bedrock-agda` source and
private scheduler have no copies here. Their replacement executable is
`outcrop-agda`; trace activation uses `OUTCROP_AGDA_TYPES`/`OUTCROP_AGDA_RUN`.
Existing old generated caches are not authoritative and can be removed manually
after verifying the replacement build. No migration changes any mathematical
source, declaration, `--safe` option or proof assumption.

## Modes and budgets

`make typecheck` is a pure incremental proof check. Interfaces live under
`_build/typecheck`; they never warm the traced HTML cache. `make typecheck-cold`
is the comparable single-process benchmark, retaining Cubical interfaces and
timing Agda alone. `typecheck-cold-parallel` is an operational build, not that
baseline. Both retain their timing reports under `_build/benchmarks`.

`make html` produces official highlighting and expression traces.
`html-cold` times the single-process combined traversal;
`html-cold-parallel` schedules imports with Outcrop's driver, using one trace per
worker and a final official HTML pass over completed interfaces. `make site`
extracts name/expression types and renders all editions. No second elaboration
is needed merely to write HTML from compatible interfaces.

`typecheck-ci` and `site-backend-ci` choose cached or cold paths explicitly. Keep
`GHCRTS="-A64m -I0 -M8g"` and at most two Agda processes on this machine. Local
parallel checks may run independent prose/unit gates alongside the proof gate.
Do not compare full CI duration, dependency installation or compiler compilation
against the pure single-process baseline.

## CI and deployment

Every job sets up Python before installing Outcrop into that interpreter. The
proof job owns the compiler cache; the site-backend job restores its exact key,
without another Haskell installation. Cache identities include the Outcrop
producer resources/code and Bedrock's dependency lock. Source interface and site
backend caches stay separate. After the proof gate and backend succeed, GitHub
Pages and Cloudflare independently render, validate and deploy the same backend
artifact for their respective base URLs.

Hostnames, credentials, project IDs, branch policy and deployment jobs remain
Bedrock choices. Outcrop's independent CI tests its mechanisms without importing
Bedrock content. See [the workflow guide](../.github/workflows/README.md).
