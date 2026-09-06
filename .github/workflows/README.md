# .github/workflows

CI and deployment for Bedrock. English developer doc; see
[AGENTS.md](../../AGENTS.md). This guide lives here rather than at
`.github/README.md` on purpose: GitHub renders a `.github/README.md` as the repository
homepage in place of the root [README.md](../../README.md), so the `.github/` folder is
documented one level down instead.

## Workflows

`typecheck.yml` runs on every push and every pull request; the two deploy workflows run on
push to `main`:

- `typecheck.yml`: the **proof gate**. It typechecks the masters with an interface cache, then
  runs `make lint` (the four gates plus the i18n marker check) and `make test` (their unit
  tests). Together those are `make check`, split so the typecheck can use its cache.
- `cloudflare.yml`: builds the site (root base URL) and deploys to **Cloudflare Pages**, the
  primary host ([bedrock.institute](https://bedrock.institute)).
- `pages.yml`: builds the site (base URL `/Bedrock`) and deploys the **GitHub Pages** mirror.

## Secrets

The Cloudflare deploy uses organization secrets `CLOUDFLARE_API_TOKEN` and
`CLOUDFLARE_ACCOUNT_ID` (owner-configured GitHub Actions encrypted secrets on the BedrockInstitute
org, inherited by this repo, never committed or printed). Deployment is automatic and contributors handle no credentials. The one-time owner
setup is documented at the top of `cloudflare.yml`.
