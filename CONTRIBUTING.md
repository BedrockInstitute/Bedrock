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
