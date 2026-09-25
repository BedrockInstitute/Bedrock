# Bedrock's Agda environment

The reusable compiler instrumentation, build, dependency installer and parallel
scheduler belong to [Outcrop](../outcrop/docs/AGDA.md). This repository supplies
the mathematics and the choices with which those mechanisms are invoked.

| Choice | Authority |
| --- | --- |
| Compiler source, adapter, Happy and tested host versions | `outcrop/src/outcrop/adapters/agda/resources/manifest.json` |
| Cubical dependency version and archive checksum | `site/agda-libraries.json` |
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

`typecheck-ci` chooses cached or cold proof checks explicitly. `site-backend`
uses the same content-aware backend cache locally and in CI. Keep
`GHCRTS="-A64m -I0 -M8g"` and at most two Agda processes on this machine. Local
parallel checks may run independent prose/unit gates alongside the proof gate.
Do not compare full CI duration, dependency installation or compiler compilation
against the pure single-process baseline.

## Build entry points

`make` defaults to `help`, not an installation. Public setup commands are
`bootstrap`, `venv`, `toolchain`, `outcrop-agda` and `hooks`. Bootstrap sequences
Python installation before toolchain setup even with `make -j`.

| Command | Cache and execution contract |
| --- | --- |
| `check` | Pure typecheck, shared textbook lint plus instance extras, both unit suites |
| `lint`, `test`, `milestone-lint` | Independent source gates, unit tests and Origin reachability respectively |
| `typecheck` | Synchronize the isolated source mirror, including deletions/renames, then check incrementally |
| `typecheck-ci` | Select warm or cold parallel proof path |
| `typecheck-cold`, `typecheck-cold-parallel` | Serial baseline versus parallel operational timing; keep separate |
| `html` | Timestamp-managed low-level compiler highlighting/trace producer |
| `html-cold`, `html-cold-parallel` | Explicit serial/parallel compiler-evidence benchmarks |
| `types` | Prepare `html`, then extract both semantic products once |
| `site` | Content-aware backend plus rendering, identical entry locally and in CI |
| `site-backend` | Same content-aware backend preparation, no rendering |
| `site-render` | Force a complete render of existing evidence, without invoking Agda |
| `site-render RENDER_INCREMENTAL=1` | Validate the backend artifact and reuse unchanged render output; CI uses this mode |
| `site-cold` | One explicit parallel cold backend build, semantic extraction and rendering |
| `gen` | Produce per-language source copies, not required by the website build |
| `serve`, `deploy` | Preview existing output; build and explicitly deploy, respectively |
| `clean`, `distclean` | Remove generated website/cache files; additionally remove toolchain, dependencies and interfaces |

`types-refresh`, `site-ci` and `site-backend-ci` are removed. Use `types`, `site`
and `site-backend`. Diagnostic `*-gate` targets remain available for focused
checks; `typecheck-stage`, `_types` and `types-local-*` are internal stages.
The raw extraction stages require prepared compiler evidence and never invoke
`html`: the content-cache owner, not downstream timestamps, decides freshness.

`LOCAL_JOBS` controls independent lint/check tasks. `AGDA_JOBS` controls Agda
module workers, normally two; serial benchmarks remain serial. Extraction uses
up to two tasks (one Agda name loader plus one Python trace normalizer), or one
with `LOCAL_PARALLEL=0` or `LOCAL_JOBS=1`. Run only one compiler workflow at a time
against a given cache; independently launched Make processes do not share a
machine-wide Agda resource semaphore.

Normal overrides are `PY`, `PYTHON`, `LOCAL_PARALLEL`, `LOCAL_JOBS`, `AGDA_JOBS`,
`SITE_OUT`, `LANGS`, `BASE_URL`, `PORT`, and `CF_PROJECT`. Advanced backend path
overrides `HTML_DIR`, `AGDA_TRACE`, `AGDA_DIR` and `SITE_IFACES` cross the
Make/Python boundary explicitly. `SITE_IFACES` must name a dedicated cache below
`_build`. Compiler installation and normalized type-file locations remain fixed
instance internals, not alternative toolchain selectors.

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
