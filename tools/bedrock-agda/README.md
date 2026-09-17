# bedrock-agda

Bedrock records elaborated Agda expression types while Agda performs the same
traversal that writes `.agdai` files and HTML. The official backend API runs
after type checking and exposes modules and definitions, so it cannot observe
the local application and binder nodes required by the site. A small source
adapter is therefore still necessary.

The implementation is divided at a deliberate compatibility boundary:

- `src/Bedrock/Agda/TypeTrace.hs` is the stable overlay. It owns activation,
  ranges, delayed closures, deduplication, JSONL output and buffering. It lives
  outside the `Agda.*` namespace and is copied into an unpacked source tree.
- `adapters/Agda-2.8.0.patch` is the version-specific adapter. It registers the
  overlay as one Cabal module and adds calls at five semantic sites in upstream
  Agda. It contains no tracing policy or output implementation.
- `manifest.json` is the complete version lock: source URL and checksum,
  adapter path, and temporary Cabal bound overrides. The build fingerprint
  covers the manifest, adapter and entire overlay.
- `environment.json` pins the cubical release, its checksum, the tested GHC
  version and the minimum Python version without changing the compiler identity.

Ordinary Agda behavior is unchanged unless `BEDROCK_AGDA_TYPES` names a JSONL
file. With tracing enabled, records are formatted after complete declarations,
when local metavariables have been solved. Variable occurrences continue to use
Agda's own HTML links to their binding sites.

## Version identity

The patched compiler is versioned with this repository. Its exact identity is
the upstream source checksum plus the adapter and overlay hashes. Inspect the
installed identity with:

```sh
_build/bin/bedrock-agda --bedrock-version
```

Do not commit unpacked Agda source, executables, cubical sources, interfaces or
generated HTML. They remain under the ignored `_build` directory. A Bedrock Git
commit or release tag therefore identifies both the mathematics and the
compiler instrumentation used to check and render it.

Keep old version adapters when upgrading. Add
`adapters/Agda-VERSION.patch`, change `manifest.json`, and retain the previous
adapter for rollback and `git bisect`.

## Fresh-clone setup

Supported environments are macOS, Linux, and WSL2. Install these host tools:

- Python 3.11 or later;
- GHC and Cabal, with GHC 9.4.8 as the currently tested version;
- `make`, `patch`, a C toolchain, and standard system development libraries.

The recommended GHC and Cabal installer is
[GHCup](https://www.haskell.org/ghcup/). Agda itself need not be installed. From
a fresh clone run:

```sh
make bootstrap
_build/bin/bedrock-agda --bedrock-version
make check
```

`make bootstrap` creates `.venv`, builds the patched compiler, downloads the
checksummed cubical release from `environment.json`, and writes a project-local
Agda library registry under `_build/agda-home`. It never writes to `~/.agda`.
Re-running it is safe and uses the local caches. `make distclean` removes the
generated compiler and library environment for a clean deployment rehearsal.

Build and preview the website with:

```sh
make site
make serve
```

## Check and backend modes

The Makefile keeps the proof benchmark and the website backend as separate
Agda modes:

```sh
make typecheck       # pure incremental type checking
make typecheck-cold  # timed pure check with cold Bedrock interfaces
make html            # cached interfaces + HTML + expression trace
make html-cold       # timed cold combined traversal
make site            # cached combined traversal, then render the site
make site-cold       # cold combined traversal, then render the site
```

Pure checks run from `_build/typecheck`, which has its own Agda interface tree.
The source files copied there preserve their timestamps. This isolation matters:
loading an interface made by a prior pure check would skip the elaboration events
from which the website records local expression types. Both cold targets retain
the pinned cubical interfaces, so their times measure the Bedrock closure rather
than dependency installation. `/usr/bin/time -p` reports real, user and system
seconds for the Agda process; source staging and final site rendering are outside
that timed region. The same timing output is retained in
`_build/benchmarks/typecheck-cold.time` or
`_build/benchmarks/html-cold.time` for later comparison.

`html-cold` is the direct benchmark for the optimized backend path requested by
the site: one Agda invocation checks the Bedrock closure, writes `.agdai`, runs
the official HTML backend, and writes the expression-type trace. `site-cold`
uses those products and then runs the Python normalizers and renderer. Run
`typecheck-cold` and `html-cold` independently when comparing their costs; each
clears only its own Bedrock cache.

## CI and website deployment

The typecheck, GitHub Pages, and Cloudflare workflows all call `make toolchain`,
the non-virtualenv subset of `make bootstrap`. Their cache keys include
`tools/bedrock-agda/**`, so a manifest, overlay, adapter, or environment change
invalidates the relevant cache. The typecheck workflow caches only the isolated
pure-check interfaces. The deployment workflows cache the combined HTML and
type-trace products.

Pushing `main` runs the formal checks and builds both hosted sites. GitHub Pages
uses `.github/workflows/pages.yml`. The canonical Cloudflare deployment uses
`.github/workflows/cloudflare.yml` and requires `CLOUDFLARE_API_TOKEN` and
`CLOUDFLARE_ACCOUNT_ID`; its Pages project is named `bedrock`. An owner can also
deploy an already configured checkout with `make deploy`.

To upgrade Agda, first update the version, archive URL and checksum in
`manifest.json`. Copy the existing overlay unchanged, then rebase only the
adapter calls against the new source. The adapter test enforces the allowed
upstream files and rejects embedded implementation code or dependency-bound
edits. Finally build the compiler and run the strict expression-type
normalizer; a missing node is an error rather than a request for a second Agda
probing pass. If Agda gains a public elaborator-event API, replace the adapter
with that API and keep the overlay protocol.
