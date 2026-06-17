# Contributing to Bedrock

Bedrock's working rules (prose style, the trilingual layout, the literate-Agda and i18n
conventions, the build gate) live in [AGENTS.md](AGENTS.md), written for AI coding agents.

You do not need to read them all. Open the repository in an AI coding agent (Claude Code,
Codex, Cursor, and the like). It loads `AGENTS.md` and will:

- **explain** any convention when you ask why,
- **apply** the rules as it edits, and
- **check** your contribution against them before you submit.

In other words: to understand a rule, ask the agent; let the agent tell you, and let the agent
be the gatekeeper. `make check` plus the pre-commit hook (`make hooks`) are the machine
backstop, and CI re-runs `make check` on every push.

If a rule is missing or the agent cannot answer, do not guess. Ask the repository owner.

## License and contribution terms

Bedrock is multi-licensed (see the [README](README.md#license), [`REUSE.toml`](REUSE.toml), and
[`LICENSES/`](LICENSES/)). Contributions are accepted under the license of the area you touch
(inbound = outbound):

- **Content** (the mathematics and prose under `src/` and `docs/`, and the README): CC BY-NC-SA 4.0.
- **Code and configuration** (everything else, the default): AGPL-3.0-only.

By opening a pull request you agree to license your contribution under those terms. Note the AGPL
expectation up front: some employers restrict contributing to AGPL-licensed code, so check whether
that applies to you. There is no separate CLA or DCO sign-off.
