# STYLE-agda: Agda code and literate-chapter style

Binding style rules for every master under `src/`. This is a developer doc (English
only). It inherits the source project's finalized code-style spec
(`../fol-reification/docs/governance/STYLE.md`, finalized 2026-06-12 and proven over
70k lines) and adapts it to Bedrock's textbook mission; where the two differ, this
document wins. Process context (goal codes, phases, Frontier) lives in
[PLAN.md](PLAN.md); the i18n marker grammar lives in [STYLE-i18n.md](STYLE-i18n.md).

Rules marked **(provisional)** are expected to harden after real porting experience
(PLAN §8 T1). Changing any rule is legislation: open an `[L0.x]` item, do not
improvise silently.

The mechanical subset of these rules (the OPTIONS header, the import discipline of
§2, and the forbidden constructs of §1) is machine-enforced by `scripts/lint-agda.py`
as part of `make check` and the pre-commit hook `[L0.3]`.

## 0. Meta-principles

1. **Notation aligns with set-theoretic LaTeX tradition.** If it can look like the
   textbook, it looks like the textbook (`γ ⊨ φ`, `𝒮 ↾ M`, `𝒫 x`).
2. **One symbol, one layer.** A symbol never serves both a meta-level and an
   object-level role; collisions are resolved by layer markers (§3).
3. **Role determines form.** Whether an identifier is a symbol, a full word, a
   kebab phrase, or a single letter is decided by its role (§1), not by taste.
4. **No invented symbols.** Only symbols with mathematical tradition; a concept
   without a traditional symbol gets an English word. Invented symbols are written
   once and read never.
5. **Strictness over convenience.** Code here is written by agents; typing burden is
   never a reason for a style decision. Of two candidates separated only by
   engineering convenience, take the stricter.
6. **The reader is a beginner.** Bedrock-specific: where a stricter and a more
   teachable option genuinely conflict (rare), surface the conflict to the owner
   instead of deciding locally.

## 1. Options and assumptions

- Every module's first line is exactly
  `{-# OPTIONS --cubical --safe --guardedness #-}`. No other flag may be added
  without an `[L0.x]` ruling. Library-wide flags live in `bedrock.agda-lib`.
- **No `postulate`, no holes, no `{-# TERMINATING #-}`, ever.** The Frontier record
  (PLAN §5) is the only sanctioned form of "not proven yet".
- **Classical principles are module parameters, never axioms** (PLAN D2). The
  canonical packaging (validated by the L0.2 spike):

  ```agda
  LEM : ∀ ℓ → Type (ℓ-suc ℓ)
  LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥)
  ```

  defined once in `Base.Classical`; a module in the classical cone takes
  `(lem : ∀ {ℓ} → LEM ℓ)` in its telescope, after the level parameters, and applies
  it when importing other classical-cone modules
  (`open import L.Stage {ℓ} lem using (...)`). The same pattern governs any future
  assumption interface (set choice, resizing).

## 2. Modules and files

- One chapter = one master `.lagda.md`; module name = file path; namespaces = the
  book parts fixed in PLAN §4.
- Module names: full English words, PascalCase (`Constructible`, `WellOrder`).
  **Never** iteration numbers, primes, or provenance flavor (`Foo2`, `FooFinal`,
  `isL'`); PLAN D7.
- Telescope order: levels first, then assumption parameters, then subject
  parameters (`module L.Model {ℓ : Level} (lem : ∀ {ℓ'} → LEM ℓ') (F : Frontier ℓ)`).
- Imports needed by the telescope go **before** the module header; everything else
  after it.
- **Just-in-time introduction** (owner ruling, 2026-07-17): every definition lives in
  the chapter where it is first motivated, never earlier. The hubs in particular are
  **pure re-export surfaces** and define nothing of their own (so `_^_` belongs to
  the semantics chapter that needs environments, and `absurd` to the syntax chapter
  whose closed constant domain it serves; neither belongs to `Base.Prelude`).
- **Hub admission** (owner question, 2026-07-17): a name enters `Base.Prelude` only
  if it is **statement-ambient**, needed to read definitions and theorem statements
  throughout the book (universes, paths, h-levels, `hProp` with `⟨_⟩`, pairs, the
  indexing data `ℕ`/`Vec`/`Fin`, `⊥*`), and its statement-level role is not already
  played by one of the book's own abstractions (logic connectives belong to the
  truth algebra; truncated existence reaches statements as its `⋁`, which is why
  even the near-ubiquitous propositional truncation stays chapter-local).
  Proof-side machinery stays chapter-local however common (`⊎` decisions,
  `Empty.⊥` refutations, equivalence assembly, `⇔toPath`): every admission enlarges
  the set of untraceable names, and a local import line is information. When in
  doubt keep it local; promotion is one cheap change, demotion touches every
  chapter.
- `open import` always carries a `using`/`renaming` list (audit-friendly), and every
  imported name must actually be used: imports are **necessary** (the linter checks
  this) as well as sufficient (the typechecker checks that). Exceptions: `Everything`,
  whose bare import block is the site's module list, and the designated **hub
  modules** `Base.Prelude` and `Base.Truth`, curated re-export preludes designed to
  be opened wholesale (the hubs' own `public` re-exports stay curated with `using`
  lists). A genuine exception the linter cannot see (an instance-only import) is
  marked `-- lint-agda: keep`.
- Every module is imported by `Everything` in reading order (enforced by the
  L5-ported audit; a module outside `Everything` is unchecked and unlisted). Its
  reading position is where its first consumer needs it; thematic grouping is the
  derived structure catalog's job (PLAN §5), never a reason to move a chapter
  forward.

## 3. Naming

Decision tree (in order):

```
Type / record / module / chapter?
  → full English word, PascalCase (Formula, ZFStructure, TruthAlgebra).
Theorem / axiom / lemma / property name?
  → kebab phrase, topic symbols allowed (encode-inj, Δ₀-absolute, ∩-spec).
Operation or relation (returns data / Ω / Type)?
  → traditional symbol + layer marker if any (∩, ↾, ⊨, ∈ˢ, ∈̇);
    no traditional symbol → English word, camelCase (embed, numeral, lookup).
Local variable / module parameter?
  → single letter per the table below.
High-frequency concept too long for signatures?
  → only entries in the registered abbreviation list.
```

Registered suffixes for theorem names: `-rep` (combinator families), `-spec`
(specifications), `-inj` (injectivity), `-ax` (axiom instances, library tradition),
`-map` (functoriality). Registered abbreviations: `Rep` (representation), library
names (`Fin`, `Vec`, `ℕ`), and the affixes `inj`/`comm`/`assoc`. Anything else needs
registration here first. Forbidden: pinyin, ASCII two-character operators (`=>`,
`<=`), unregistered abbreviations.

**Qualified-import aliases are full words** (`import Cubical.Functions.Logic as
Logic`), never single letters: single capital letters (`L`, `V`, ...) are the book's
mathematical subjects, and an alias must not collide with them.

**Primes are forbidden in principle.** No public name (anything importable:
definitions, record fields, constructors, module names) carries a prime. The single
sanctioned use is strictly local: inside one definition or proof, a primed twin `x'`
may accompany `x` when the two appear **as a pair within eyeshot**, in the same
telescope or the same `where`/`let` block (an updated value derived from `x`, the
level pair `ℓ ℓ'`). A prime never crosses the definition boundary; a primed name
with no unprimed partner in sight is a naming failure even locally. Ported source
names like `isL'` are renamed on entry (PLAN D7).

Record fields: **operation fields are symbols** (`_∈ˢ_`, `_≈ˢ_`, `⊓`, `⋁`),
**property/axiom fields are words**; property-shaped fields are bare
adjectives/nouns (`extensional`, `foundation`), existence-shaped fields take `has-`
(`hasEmpty`, `hasPair`, `hasSep`, `hasPower`).

Fixed variable conventions:

| Variable | Role |
|---|---|
| `φ ψ θ` | formulas |
| `t u` | terms |
| `γ` | environment (never `env`) |
| `x y z` | sets (quantified or generic) |
| `A B C` | set parameters |
| `K` | constant domain |
| `ι` | constant interpretation `K → S` |
| `n m k` | free-variable counts, naturals |
| `i j` | de Bruijn indices (`Fin`) |
| `ℓ ℓ'` | universe levels |
| `P Q` | meta-level predicates/propositions |
| `M` | class (`S → hProp`) |

Locals and bound variables are single letters, matching mathematical text. Module
parameters for structures use script/blackboard single letters (`𝕋`, `𝒮`, `ℳ`);
top-level named instances use searchable English words (`hPropAlgebra`) or subscripted
symbols mirroring the mathematical object (`𝒮ᵥ`, `𝒮ʟ`).

## 4. The layer-marking system

Four semantic layers, one marking each:

| Layer | Marking | Examples |
|---|---|---|
| ① host/meta (Agda, cubical) | none (library names) | `≡` (path), `Σ ×`, `isSet`, library `_∈_` |
| ② truth algebra Ω | none + scope discipline | `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁` |
| ③ structure fields | `ˢ` superscript | `_∈ˢ_ _≈ˢ_` |
| ④ object syntax | dot mark | `_∈̇_ _≐_ ∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇ ∃̇ ∀̇ ∀̇∈ ∃̇∈` |

- **Scope discipline for layer ②:** `Base.Prelude` re-exports no logic operations;
  the symbols `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁` come only from opening a truth algebra, so each
  logic symbol has exactly one meaning in any scope.
- Object-language constructors always carry exactly one dot; the dot marks the
  token, not its components (`∀̇∈`, not `∀̇∈̇`).
- Superscript = layer marker (`ˢ ᶜ ᵗ`); subscript = variant or index (`∈ₛ`, `Δ₀`,
  `𝒮ᵥ`). Prefer precomposed characters (`≐`, not `=` plus combining dot).
- Orientation families, quoted in the syntax chapter's prose: membership
  `∈` (① V) / `∈ₛ` (① small) / `∈ˢ` (③) / `∈̇` (④) / `∈ᶜ` (class) / `∈ᵗ`
  (Type-valued); equality `≡` (①) / `≈ˢ` (③) / `≐` (④); implication `→` (①) /
  `⇒` (②) / `⇒̇` (④).

Reserved symbols (future milestones; do not occupy): `_[_]` substitution, `⊢` proof
systems, `⊩` forcing, `∈ᴮ ≈ᴮ` and the `ᴮ` family for Boolean-valued structures,
postfix `↑` weakening. `⌜_⌝` belongs to the coding chapters.

Fixity is centralized: one table in the syntax chapter, quoted in its prose.
Baseline: ④ atoms `≐ ∈̇` = 18, `∧̇ ∨̇` = 12, `⇒̇` = 10, `¬̇` = 13; ③ `∈ˢ ≈ˢ` = 20.
Corresponding operations across layers share a level (`∧̇` with `⊓`, `⇒̇` with `⇒`).

## 5. Symbol introduction discipline

At a symbol's definition site, the prose gives its **reading**, in each language
block (for example `⊨` reads "satisfies" in English and 满足 in Chinese). **Input
methods and LaTeX counterparts never appear in reader-facing prose** (owner ruling,
2026-07-17): readers read, they do not type. The place contributors look up how to
type a symbol is the master symbol table in `src/README.md` (a developer doc):
symbol / reading / layer / defining chapter / input sequence.

## 6. Layout and proof organization

- Type signatures aligned on `:`; constructors carry single-line comments to the
  right where a gloss helps.
- Record instances prefer record literals (`record { ... }`) over copatterns unless
  field dependencies force an order.
- Proofs prefer `where` with **named, type-annotated** sub-terms over nested `let`.
- Implicit-argument discipline: implicits passed through `⟨_⟩`/`fst` projections are
  given explicitly in hProp-instance proofs (a known unification trap).
- **Mixfix operators are used mixfix** (owner ruling, 2026-07-19). Applying an
  underscored operator name to its operands in prefix form (`_∈ᵗ_ 𝒮 y x`,
  `At._⊨_ ι γ φ`) is banned. When the operator lives in a parameterized module,
  open the module and write the operator infix (`y ∈ᵗ x`, `γ ⊨ φ`); when two
  instances must coexist in one scope, open both with `renaming` under marked
  names (`_⊨ᵛ_`/`_⊨ᵐ_`, `_⊨∘_`), or hold one behind a module alias and pass it
  qualified as a value (`Acc Vmem._∈ᵗ_ u`). Passing an operator **as a value**
  (`WellFounded _∈ᵗ_`, `cong₂ _⊓_ p q`), sections (`(x ∈ˢ_)`), and the
  left-hand side of the operator's own defining clause (`_↾_ {ℓ} 𝒮 M = …`) are
  all fine: the ban is on application. Application cannot be told from
  value-passing by a regex, so this rule is enforced in review, not by
  `lint-agda`.

## 7. Performance idioms (provisional)

Conversion-blowup countermeasures are legitimate but must stay visible and
skippable:

- Allowed: `opaque` seals with `unfolding` blocks, explicitly-spelled implicit
  arguments (`{φ = ...}`), extracted continuation helpers, Π-parameterized
  assumption bundles.
- Every such use carries a marker comment on its first line: `-- perf: <trigger>`,
  one line, naming what blew up (for example `-- perf: implicit {φ} metas on a huge
  formula; explicit spelling cuts 74min to 66s`). Narration never explains these;
  the marker is the whole story, and readers are told once (in the Base part) that
  `-- perf:` lines are engineering, not mathematics.
- When a module exceeds the PLAN §7 budgets (roughly 120 s cold or its heap cap),
  triage against the source playbook (`../fol-reification/docs/WORKLOG.md` §5,
  cases 1 to 20) before merging.

## 8. The literate chapter template (provisional)

Every master follows this shape (prose in `<!--en--> / <!--zh-->` markers per
STYLE-i18n; code fences are language-neutral and English-only):

1. `# Title`, then an opening block: what this chapter proves, why the reader
   should care, and where it sits in the part's arc (one to three paragraphs).
2. **Prose leads, code follows** (owner ruling, 2026-07-17, reversing the same-day
   code-first ruling): each code block is immediately preceded by the passage that
   explains it, one passage per block (one import statement per block in a hub).
   Follow-up remarks may trail a block, but a block never appears unannounced.
3. `##` sections in the order: motivation and informal picture, definitions,
   statements, proof development, recap. Small chapters may merge sections; the
   recap (what was established, what it feeds) is never skipped.
   **No forward jargon** (owner ruling, 2026-07-17): prose argues only from notions
   the reader already has at that point of the book. A forward pointer may name a
   destination ("Part 1 makes this concrete"), never lean on its terminology.
   **Prose teaches, it never defends** (owner ruling, 2026-07-17): compliance
   arguments, replies to review questions, and self-justifications ("this does not
   violate rule X") stay out of the text, exactly as such comments stay out of code.
4. Inline code references use `` `name`{.Agda} ``; section headings are stable
   anchors for cross-references.
5. New symbols follow §5; new terms enter `dev/glossary.toml` in the same change.
6. Authoring order per PLAN D6: English first, then Chinese, cross-checked; the
   Japanese block may be added later without touching code.

## 9. Commits

Commits touching planned work carry the goal code in brackets (`[L1.4] port
ZF.Structure ...`), per PLAN §6.0. `make check` before every commit, as always.
