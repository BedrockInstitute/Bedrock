# .github/workflows

CI and deployment for Bedrock. English developer doc; see
[AGENTS.md](../../AGENTS.md). This guide lives here rather than at
`.github/README.md` on purpose: GitHub renders a `.github/README.md` as the repository
homepage in place of the root [README.md](../../README.md), so the `.github/` folder is
documented one level down instead.

## Workflow

`ci.yml` starts on every push and pull request, without workflow-level path
filters. The existing `typecheck` job always runs lint, both unit-test suites and
the Origin closure gate. Agda work is conditional on the changed-file scope.
For non-documentation pushes to `main`, or any manual dispatch, it subsequently
builds and deploys the multilingual site. Its full job graph is:

```text
typecheck -> site-backend -> pages
                           -> cloudflare
```

The graph gives the proof gate first use of the runner and makes its result independent
of the website. Pure-check interfaces remain isolated from HTML and expression-type products.

## Documentation-only shortcut

`site/ci-docs.json` is an explicit allowlist of reference documents, including
READMEs, authoring guides and Markdown under `docs/` and `dev/`. Literate
`.lagda.md` files are never documentation-only. Unknown paths, code, assets,
machine-readable configuration, CI policy and workflow changes select the full
pipeline. Do not expand the allowlist to cover inputs consumed by the website.

| Change / event | Always-run checks | Agda and website |
| --- | --- | --- |
| Only allowlisted documents | Lint, both test suites, Origin closure | Skip compiler/dependency caches and setup, typechecking, backend, rendering and deployment |
| Any other path, including mixed documentation/code changes | Same checks | Typecheck; build/deploy on `main` pushes |
| Manual dispatch | Same checks | Full pipeline, preserving the existing manual deployment behavior |
| Missing baseline/history or invalid policy | Same checks | Conservatively use the full pipeline |

The shared `outcrop.adapters.ci_scope` helper compares the whole push's `before`
revision to the checked-out event revision, or the PR base's merge base to that
revision. Initial pushes with no usable baseline run fully. Classification uses
the complete NUL-delimited Git diff, not an API's truncated changed-file list;
renames check both old and new paths. Checkout fetches full history for this job.

An Outcrop gitlink change is inspected between its old and new commits using
Outcrop's own `.github/docs-only.json`. Documentation-only framework updates can
therefore skip Bedrock's expensive work too. An added/removed submodule, unavailable
commit, policy change or any framework implementation change selects full CI.
The helper never fetches a branch or replaces the pinned framework revision.

The job summary records the decision. Keep `typecheck` present even for documents:
[skipping a whole required workflow can leave its check pending](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax).
Lightweight gates still fail normally; the shortcut is not an unconditional green
check. Local `make check` remains full and unchanged. The first push introducing
this optimization runs fully because it changes implementation and workflows.

## Caches and deployment

Every job checks out submodules recursively, selects Python 3.11 first, and then installs the pinned local Outcrop
package with `python3 -m pip install ./outcrop`. Outcrop Core and Outcrop Site are
the shared renderer, complete website and lint implementation; Bedrock supplies
content, configuration and mathematical gates. Tests are split between
`outcrop/tests/` and Bedrock's `scripts/tests/`; `make test` runs both.
Do not fetch an unpinned framework branch during deployment.

The optional compiler producer also comes from Outcrop; it is not a Bedrock-owned
fork. Its source/build resources participate in cache keys, while the Cubical
version is explicitly selected by `site/agda-libraries.json`. Do not switch Python
interpreters after installing Outcrop: that leaves later gates unable to import
the package. A repository integration test pins this ordering in all four jobs.

The `typecheck` job restores and validates the patched-Agda cache before Haskell setup,
then refreshes the verified wrapper timestamp so checkout times cannot trigger a false
rebuild. A normal cache hit therefore skips GHC and Cabal setup entirely. When the
compiler must be rebuilt, a separate Cabal cache reuses the package index and compiled
dependency store. The
project-interface key separates the stable toolchain fingerprint from the source-tree
fingerprint, allowing `restore-keys` to supply a useful incremental starting point after
source edits. Cache, Python, artifact and deployment actions use their Node 24 releases.

After `typecheck` succeeds, `site-backend` restores the exact patched-Agda and cubical
caches that job created, including cubical's pinned source archive. It does not install
GHC or redownload cubical. The combined backend cache stores interfaces, highlighted
HTML, expression types and a source/code inventory. A partial restore compares the
Agda fences of each chapter. If only prose changed, it reuses the compiler-produced
code blocks and updates the surrounding text without running Agda or extracting types.
Code or backend changes still run the combined Agda traversal. The host-neutral
HTML/type-data artifact also carries the inventory for deployment jobs.
The backend job invokes `make site-backend PY=python3 LOCAL_PARALLEL=1`;
deployment jobs invoke `make site-render PY=python3 RENDER_INCREMENTAL=1`
with their existing base URLs. These are wrappers around the same cache driver.
Plain `make site-render` is deliberately a forced local render.

### Content identities and archive restoration

`site-cache.py --cache-keys backend|render` prints the same content identities
used by the local driver as `name=value` output for Actions. Compute backend keys
after installing the toolchain/registry, and render keys after downloading the
validated backend artifact. The command is read-only and never starts Agda.

| Layer | Identity and invalidation |
| --- | --- |
| Compiler and pure-check interfaces | Existing toolchain/library/source keys and isolated paths, unchanged |
| Site backend (`bedrock-site-v5`) | Producer identity, extractor identity, then source inventory |
| Producer compatibility | Installed compiler identity, compiler integration sources/resources, source grammar, library lock and project library descriptor; not the whole Makefile or cache orchestration script |
| Extractor compatibility | The two extraction implementations and their Bedrock invocation adapters; changes rerun extraction without recompiling compatible evidence |
| Pages/Cloudflare render (`v2`, separate prefixes) | Render build key plus source inventory; key covers producer/code/type products, actual renderer Python dependencies, packaged resources, configured catalog/glossary/icons, project config, language and base URL |

Renderer Python inputs are found through a conservative static import closure,
including package initializers and deferred imports. A dynamically imported
package falls back to its complete Python source set. Unused lint modules,
reference Markdown, unrelated policy registries and Make orchestration are not
renderer dependencies. Figure checks invoked by rendering remain dependencies.
Changing compiler invocation semantics or the cache protocol requires updating
its producer inputs/schema; never silently reinterpret an existing receipt.

Restoration tries the closest compatible prefix first, then a same-layer/OS
fallback, including the prior backend `v4` and host render `v1` archives. This
allows existing evidence to survive the key migration. A recovered archive is
only a candidate: the driver always validates producer, source and extractor
identities, even on an exact Actions hit. Incompatible producer evidence loses
its traced interfaces and trace before recompilation. A failed extractor leaves
an uncertified receipt; render-only jobs reject it. Trace timestamps are refreshed
only inside the driver after compatibility is established, not blindly by CI.
CI never adopts an archive without a valid content receipt using timestamps;
the timestamp-based adoption path is only for local manual pre-receipt builds.

GitHub caches are immutable. A fallback restore is saved under the new complete
key after success; a primary-key hit is not saved again. The explicit output
fingerprints allow this without including an unrelated commit SHA or build-script
hash in every key. See [GitHub's cache reference](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching).
Logs distinguish archive restoration from actual compiler, extraction and render
reuse. Do not infer a fully warm build solely from an Actions cache step succeeding.

The `pages` and `cloudflare` jobs consume that artifact independently and may run in
parallel. Each has a separate rendered-site cache keyed by source and renderer inputs.
On a prose-only change, a restored site updates the affected chapters, the overview,
and global search, while reusing the compiler-derived code context. A cold cache or
code/renderer change triggers a complete render, without forcing a compatible
Agda backend to rebuild. The transition to the narrower render identity can
require one full render of restored backend data; it does not require a cold
Agda check. Each job checks its own links and
deploys its own output.
Neither job depends on the other, so a rendering, link-check, deployment or concurrency
failure in one host does not prevent the other. GitHub Pages is the mirror; Cloudflare
Pages at [bedrock.institute](https://bedrock.institute) is the canonical deployment.
The Cloudflare job pins Wrangler and caches npm's content-addressed download store; the
repository has no Node dependency tree, so it deliberately does not cache
`node_modules`.

The host-specific render uses Bedrock's thin `scripts/site/render-site.py` adapter
and the installed Outcrop resources, not a copied `site/` shell. Link validation
is `python3 -m outcrop check-links <output>`. Shared templates, JavaScript, worker,
fonts and vendor assets are packaged under `outcrop/src/outcrop/site/resources/`; runtime
modules publish together under one content digest. The backend cache fingerprint
includes Outcrop's compiler-data adapters. These workflow steps do not replace
actual browser acceptance of a changed interface.

## Local checks and changes across repositories

The [scripts index](../../scripts/README.md) documents the local gates and hooks.
`make check` does not include a site build or browser tests; `make milestone-lint`
is a separate local target. Link checks in deployment likewise do not replace
search-target validation or browser acceptance of an interaction change.

Outcrop is a separate repository. Publish its commit before pushing a Bedrock
commit that references the new submodule revision, so recursive CI checkout can
resolve it. Do not substitute a framework branch for the recorded commit. A
successful local check or push does not by itself mean either deployment job
has completed; inspect the workflow and each host's result separately.

## Secrets

The Cloudflare deploy uses organization secrets `CLOUDFLARE_API_TOKEN` and
`CLOUDFLARE_ACCOUNT_ID`. They are owner-configured encrypted secrets inherited from the
BedrockInstitute organization and are never committed or printed. The owner creates a
Cloudflare Pages project named `bedrock` and points `bedrock.institute` at it. GitHub
Pages must use GitHub Actions as its source; `actions/configure-pages` enables it when
needed.
