# AGENTS.md

Bedrock proves, in Cubical Agda, that the constructible universe `L` satisfies ZFC and
GCH. Both are proved and both are registered in `src/Milestones.lagda.md`: `L⊨ZFC` and
`L⊨GCH`, each on `LEM (ℓ-suc ℓ)` and nothing else.

Requirements: Agda 2.8.0, cubical 0.9, Python 3.11 or later.
`src/Milestones.lagda.md` reaches every module, and `dev/reading-catalog.json` stores the
reading order and multilingual chapter metadata. `make check` is the ordinary gate: it
typechecks the tree, checks code/prose boundaries, terminology, reading routes and the
trilingual chapter framework, and runs the gate tests. The push/CI-only
`make milestone-lint` gate additionally verifies that every source definition outside
`Milestones` lies in its transitive import closure.

## Current goal: complete the trilingual mathematics textbook

The chapter framework, module organization, glossary audit and first prose review
are complete. The current phase writes the full English, Chinese and Japanese
literate exposition throughout the book, including later English-only scaffolding.
Preserve the established chapter and subsection structure and parallel routes.

Use GLM 5.3 Flash through Herdr / pi for drafting. Drafting agents work read-only:
they may freely inspect complete modules, relevant imports and real consumers,
and return prose to the conversation. The coordinator mechanically validates and
applies their output. Supply the project and technical background, the fixed
glossary, the full chapter context and the exact code range in every task. When a
claim depends on another definition, read that definition; a prose summary or a
translation is not mathematical evidence. Use GPT 5.6 Sol for scoped verification
and sampling; reserve GPT 6 Astra for difficult mathematical judgment.

Aim for a substantive paragraph per 1–5 lines of code, splitting existing fences
at readable token boundaries while preserving the complete Agda code-line stream.
Write a mathematics textbook: organize prose around mathematical questions,
intuition, definitions, examples and arguments. Adjacent paragraphs must develop
a continuous explanation, with code providing the formal expression. Do not
substitute an import inventory, file-order narration, or developer comments for
teaching. Explain language syntax only where it helps the learner, and avoid
repeating compiler-option or module-declaration lessons in later chapters.
Review each subsection as a connected argument before reviewing individual
paragraphs. Reading with code hidden should reveal that argument's structure;
it does not require restating every displayed formula. Prose density and short
code blocks measure presentation, not mathematical accuracy or teaching quality.
The coordinator may mechanically move existing natural-language code comments
into trilingual prose, recording each exact removed suffix and checking that no
Agda token changes. Preserve the machine-readable `lint-agda: keep` directives
explicitly allowed by `dev/STYLE-agda.md`.
Explain local purpose, dependent types, proof steps and connections in context,
not merely what the syntax spells. Long definitions can have several interleaved
paragraphs. Do not compress code, repeat explanations, or add filler to inflate
the literary proportion. Measure prose/code ratios separately in each language,
not by adding three translations together; also measure short-block coverage and
remaining untranslated prose. Document necessary indivisible-token exceptions.

The glossary remains authoritative. Search literature before introducing or
revising terminology, centralize decisions and evidence in `dev/glossary.toml`,
and never allow parallel authors to invent competing translations. Preserve all
mathematical statements, hypotheses, code, safety and opacity boundaries. The
finished prose is for learners; replace development scaffolding with accurate
exposition rather than retaining a developer-facing voice.

Preserve the established parallel reading architecture in `dev/TEACHING.md`.
The module and interface refinement is complete; this writing phase does not
rename, split, merge or migrate code. Preserve `L⊨ZFC`, `L⊨GCH`, their statements
and their single `LEM (ℓ-suc ℓ)` hypothesis.

The former line-reduction run is closed. Code size, build time and peak memory
are costs to measure, not optimization targets for this task. Modest increases
are acceptable when a concrete improvement in comprehension or modularity
justifies them. The coordinating agent is authorized to make these tradeoffs.
Do not compress proofs or merge unrelated material to reduce the module count.

The current architecture plan and acceptance criteria live in `dev/TEACHING.md`.
The previous closed run's record remains in `dev/REFACTOR.md`.

## Rules for a dispatched agent

1. **Write only the files your brief names.** Do not touch any other file. Never commit,
   never push, never run `git` commands that change state.
2. **Every Agda file must keep `--safe`.** No `postulate`, no `TERMINATING` or
   `NON_TERMINATING` pragma, no `trustMe`, no unsolved metas or holes in a file you call
   done. If you cannot close a goal, leave the hole and say so.
3. **Memory.** Run Agda only as `GHCRTS="-A64m -I0 -M8g" agda <file>`. Two Agda processes
   at most on this machine, so count them before you start one. Never typecheck
   the full `src/Milestones.lagda.md` closure unless the brief says so.
4. **Deliverable.** For a prose-only brief, preserve the concatenated Agda code lines exactly
   (fences may be split; only the coordinator may perform the documented legacy
   comment migration), run the
   scoped prose, glossary and chapter-framework gates, and report their exit codes;
   the coordinator runs the final whole-tree typecheck. For proof changes, either
   the named file typechecks with exit 0, or provide a stop report. A stop
   report quotes the exact Agda error, the file and line, and the type of the goal that
   stands open. Nothing else counts as a result. **A measured negative is a result**: if
   the plan in your brief does not hold, say so with the evidence and stop.
5. **Report short.** State the outcome in the first line. Then the checked command and
   its exit code. Then anything the next person must know, with `file:line`. No history,
   no speculation, no restating the brief.
6. **Code style.** Follow the surrounding module. `dev/STYLE-agda.md` is the law for code
   and `dev/STYLE-i18n.md` for prose. **No comment inside an ```agda fence**: split the
   fence and write the comment as prose between the halves. Never an em dash. Do not
   rename or restructure existing definitions unless the brief asks.
7. **Trust grep, not prose.** A comment claiming a thing is proved once, or that a lemma
   has one consumer, has been wrong three times in this tree. Check before you rely on it.
