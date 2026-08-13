# R1a report: the rud operations layer, F0-F7 and F9

Task `[L3.31-R1a]` (wave-1 batch, `[L3.31]`). Deliverables: the operations
module `src/L/Rud/Ops.lagda.md` (with the new `src/L/Rud/` directory) and this
report. Nothing else was created or modified in the repo; `git status` shows
only the two deliverable paths plus the parallel agents' own files.

## Verdict

**GO.** Nine operations with extension specifications typecheck cleanly:
452 non-blank Agda lines, no postulates, no holes, no `TERMINATING` pragmas,
no LEM spent anywhere, `lint-agda` and `lint-prose` green. Cold module check
(own interface regenerated, dependency interfaces from cache): 1.76 s wall /
1.62 s user; warm: 1.03 s wall / 0.94 s user. The 180 s wall protocol was not
approached. Stop-line 700 code lines: 452 used.

## Per-operation table

Line anchors are into `src/L/Rud/Ops.lagda.md`; definition lines are the
operation's defining clauses, spec lines are the extension specification
(statement plus both directions, the exported interface). The whole module is
one typecheck, so the timing column is the module's cold check; per-operation
timings are not separately measurable.

| op | reused or built | def lines | spec lines | anchors (def / spec) |
|---|---|---:|---:|---|
| F0 = {x,y} | reused: library pairing `⁅_,_⁆` + `pairing-ax` (Constructions.agda:138) | 2 | 9 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:114) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:117) |
| F1 = x ∖ y | built: `sett` over a member-type subtype | 2 | 33 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:147) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:150) |
| F2 = x × y | built: `sett` over `⟪ x ⟫ × ⟪ y ⟫` with `pr` | 5 | 44 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:204) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:211) |
| F3 = {<u,z,v> : z ∈ x, <u,v> ∈ y} | built: `sett` over `⟪ ⋃⋃ y ⟫ × ⟪ x ⟫ × ⟪ ⋃⋃ y ⟫` with pair-in-y condition | 11 | 64 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:277) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:290) |
| F4 = {<u,v,z> : z ∈ x, <u,v> ∈ y} | built: F3's index with the two middle coordinates exchanged | 11 | 64 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:374) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:387) |
| F5 = ⋃ x | reused: library union `⋃_` + `union-ax` (Constructions.agda:113) | 4 | 19 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:468) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:474) |
| F6 = dom(x) | built: `sett` over `⟪ ⋃⋃ x ⟫ × ⟪ ⋃⋃ x ⟫` with pair-in-x condition | 10 | 47 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:513) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:525) |
| F7 = ∈ ↾ x | built: `sett` over `⟪ x ⟫ × ⟪ x ⟫` cut to `u ∈ v` | 10 | 53 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:592) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:604) |
| F9 = <x,y> | reused: Kuratowski pair `pr` (V.Coding.lagda.md:175) | 2 | 11 | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:675) / [spec](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:678) |
| imports + helpers (private) | | 39 | | [Ops.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Ops.lagda.md:26) |

Every spec is exported as `Fᵢ-spec : (… x y t : V ℓ) → (⟨ t ∈ˢ Fᵢ … ⟩ → ⟨ R ⟩) × (⟨ R ⟩ → ⟨ t ∈ˢ Fᵢ … ⟩)`, the two
directions of the membership iff, hProp-valued and `⟨_⟩`-wrapped per I-2. The
realization layer consumes exactly these names and the operations themselves.

## Reuse-first accounting

- **F0** wraps the library's unordered pair; `F0-spec` is `pairing-ax` restated in
  the structure membership `_∈ˢ_` (converted via `∈∈ₛ`).
- **F5** wraps the library union; `F5-spec` is `union-ax` restated in `_∈ˢ_`.
- **F9** wraps `pr` from `V.Coding`; `F9-spec` is `pairing-ax` on the two members
  of the Kuratowski pair (`⁅ x ⁆s`, `⁅ x , y ⁆`).
- **F1, F2, F3, F4, F6, F7** are built as direct `sett`s (P-b: union-free at the
  definition level; `⋃` appears only inside index types, never under a membership
  obligation). Their membership laws are proved from `pairing-ax`, `union-ax`,
  the singleton/pair classification through raw sett membership, and
  `∈-asFiber`.

### The F3/F4/F6 bound

The components of a Kuratowski pair in `y` live in `⋃⋃ y` (not `⋃ y`): `u` is a
member of `{u,v}`, and `{u,v}` is a member of `pr u v ∈ y`. The private helper
`pair-member-in-⋃⋃` proves this once, and F3/F4/F6 index over the small member
types of the double union. The first draft bound with `⋃ y` was wrong; the
correction is recorded in the module prose and costs no LEM.

### Triple convention

`<u,z,v>` is `<u,<z,v>>`, i.e. `pr u (pr z v)`, stated in the module prose and
kept consistent across F3, F4, and F9. F3 emits `pr u (pr z v)`, F4 emits
`pr u (pr v z)`, F9 is `pr x y`. No other tuple kit exists in the committed
tree (`V.Coding` carries only `pr`), so this is the tree's own convention.

## LESSONS applied

- **P-c** (seal `⋃`-tower indices opaque at birth): F3, F4, F6 (double union in
  the index) are sealed `opaque`; F1, F2, F7 are also sealed because their sett
  images would otherwise unfold into the nested brace expressions the coding
  chapter warns against. Each seal carries a `-- perf:` marker.
- **P-b** (union-free definitions): every built operation is one direct `sett`;
  no membership obligation mentions `⋃`.
- **I-2** (hProp expressions cannot sit in type positions): every signature
  codomain is `⟨_⟩`-wrapped; the small-level negation in index conditions is
  taken qualified from the library (`Logic.¬_`) because the opened truth algebra
  lives at `hProp (ℓ-suc ℓ)`.
- **C-11** (parameterized module bodies indent deeper): observed in the strong
  form that bites inside `opaque` blocks, see surprises below.
- **R-34** (pin implicit universe levels): all `⋁` applications name their index
  type explicitly (`⋁ (V ℓ) …`) and all spec types spell `V ℓ`, so no
  level-typed meta search can open.
- **D-7** honored by absence: no LEM is spent; the operations algebra is fully
  constructive. The intersection debt D-7 names belongs to F15 and to the
  realization leg (R3), not to this file.

## Surprises and lesson candidates

1. **`opaque` where-bindings are opaque definitions.** Inside an `opaque` block,
   `where`-bound names require explicit type signatures (Agda warns
   `MissingTypeSignatureForOpaque` and postulates the type as a meta otherwise),
   and forward references within one `where` clause fail with `NotInScope`:
   definitions must appear in dependency order. This is a sharpening of C-11
   for the opaque case; candidate C-series entry "opaque-block where-bindings
   need signatures and dependency order".
2. **`PT.rec (snd _) …` leaves unsolved metas under opaque.** When the target
   proposition is a compound hProp, name it (`RHS : hProp (ℓ-suc ℓ)`, one alias
   per operation) and pass `snd RHS` explicitly; `snd _` fails. Extends I-2.
3. **`x ∈ˢ ⋃ (⋃ y)` does not parse** (prefix operator directly after the infix
   `_∈ˢ_`), while `x ∈ˢ (⋃ (⋃ y))` does. Parser-level oddity; workaround
   parenthesized and noted.
4. **subst-direction discipline**: with `q : w ≡ x`, transporting `P w` to `P x`
   uses `q`, not `sym q`; the first draft had both directions flipped in two
   places and the probe caught it. Craft, not a new lesson.
5. **Nested `⋁` witnesses**: the content of `⋁ (V ℓ) P` is a truncation, so a
   three-variable RHS needs one `∣_∣₁` per level on the way in and one
   `PT.rec` per level on the way out; the elimination chain must be ordered
   dependency-first inside `opaque` where-clauses (see surprise 1).

## Walls

None. Every obligation resolved on the first or second formulation in a scratch
probe (outside the repo, `/tmp/r1a-probe`) before the module was written; the
module itself typechecked on the fifth file-level iteration (four errors:
one parse, one out-of-scope spelling, a small-level connective level mismatch,
and one subst direction), never approaching the 180 s wall or
three-failed-formulation stop.

## Protocol compliance

- Created only `src/L/Rud/` (+ `Ops.lagda.md`) and `_build/r1a-report.md`.
- Never touched `src/Everything.lagda.md`, the parallel agents' files
  (`Images`, `OrdArith`, `Realize`), `.claude/`, git, or `make check`.
- Typechecked only `agda src/L/Rud/Ops.lagda.md`; ran `lint-agda.py --check`
  and `lint-prose.py --check` on the file only.
- Prose: English first, then Chinese, bilingual section headings, full-width CJK
  punctuation, half-width parens with outer spacing, no em dash anywhere;
  code blocks English-only; i18n marker counts balanced (23/23/23).
- No postulates, no holes, no `TERMINATING`; OPTIONS header exact.
