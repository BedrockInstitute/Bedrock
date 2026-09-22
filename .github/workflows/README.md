# .github/workflows

CI and deployment for Bedrock. English developer doc; see
[AGENTS.md](../../AGENTS.md). This guide lives here rather than at
`.github/README.md` on purpose: GitHub renders a `.github/README.md` as the repository
homepage in place of the root [README.md](../../README.md), so the `.github/` folder is
documented one level down instead.

## Workflow

`ci.yml` runs the proof gate on every push and pull request. On a push to `main`, or a
manual dispatch, the same workflow subsequently builds and deploys the multilingual
site. Its job graph is:

```text
typecheck -> site-backend -> pages
                           -> cloudflare
```

The graph gives the proof gate first use of the runner and makes its result independent
of the website. `typecheck` performs the pure Agda check, all source and prose gates, the
unit tests, and `make milestone-lint`. Pure-check interfaces remain isolated from HTML
and expression-type products.

The `typecheck` job restores and validates the patched-Agda cache before Haskell setup,
then refreshes the verified wrapper timestamp so checkout times cannot trigger a false
rebuild. A normal cache hit therefore skips GHC and Cabal setup entirely. When the
compiler must be rebuilt, a separate Cabal cache reuses the package index and compiled
dependency store. The
project-interface key separates the stable toolchain fingerprint from the source-tree
fingerprint, allowing `restore-keys` to supply a useful incremental starting point after
source edits.

After `typecheck` succeeds, `site-backend` restores the exact patched-Agda and cubical
caches that job created, including cubical's pinned source archive. It does not install
GHC, redownload cubical or compile Agda again. Its combined backend cache uses the same
two-part key, so source changes can reuse compatible interfaces and HTML as an
incremental starting point. A single combined
Agda traversal produces project interfaces, highlighted HTML and expression-type data,
which are uploaded as one short-lived, host-neutral artifact.

The `pages` and `cloudflare` jobs consume that artifact independently and may run in
parallel. Each renders its own base URL, checks its own links and deploys its own output.
Neither job depends on the other, so a rendering, link-check, deployment or concurrency
failure in one host does not prevent the other. GitHub Pages is the mirror; Cloudflare
Pages at [bedrock.institute](https://bedrock.institute) is the canonical deployment.
The Cloudflare job pins Wrangler and caches npm's content-addressed download store; the
repository has no Node dependency tree, so it deliberately does not cache
`node_modules`.

## Secrets

The Cloudflare deploy uses organization secrets `CLOUDFLARE_API_TOKEN` and
`CLOUDFLARE_ACCOUNT_ID`. They are owner-configured encrypted secrets inherited from the
BedrockInstitute organization and are never committed or printed. The owner creates a
Cloudflare Pages project named `bedrock` and points `bedrock.institute` at it. GitHub
Pages must use GitHub Actions as its source; `actions/configure-pages` enables it when
needed.
