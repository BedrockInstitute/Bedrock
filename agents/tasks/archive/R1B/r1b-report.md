# R1b report: the image half of the rud operations (F8, F10-F15)

**Date:** 2026-08-02. **Scope:** one new literate master
`src/L/Rud/Images.lagda.md` plus this report. Nothing else touched: no
`src/Everything.lagda.md`, no parallel agents' files (`L.Rud.Ops`,
`L.Rud.OrdArith`, `L.Rud.Realize`), no git, no postulates, no holes, no
`TERMINATING`. **State:** the module is green standalone
(`agda src/L/Rud/Images.lagda.md`, exit 0, zero unsolved constraints,
~55 s wall), and `lint-agda`, `lint-prose --check`, `weave-i18n --check`,
and `check-glossary --check` all pass on/against the file. Every agda
invocation ran under `GHCRTS=-M10g`, one typecheck at a time (C-12).

## 1. Delivered

All seven operations of the brief, as total `V`-operations with
two-direction extension specifications:

- `F10 x y = x"{y}`: `v ∈ F10 x y` iff `pr y v ∈ x` (`F10-spec`).
- `F8 x y = { x"{z} : z ∈ y }`: `w ∈ F8 x y` iff there is an index
  `m : ⟪ y ⟫` with `w = F10 x (⟪ y ⟫↪ m)` (`F8-spec`, the small-index
  form of the classical reading, see section 4).
- `F11`-`F14`: the pair-decomposition specs
  `y ≡ pr a b → F11 x y ≡ pr a (pr x b)` etc., with the right-nested
  triple convention `⟨a, b, c⟩ = pr a (pr b c)` stated in prose.
- `F15 A x = A ∩ x` in the parameterized module `F15Of (A : V ℓ)`
  (`u ∈ F15 x` iff `(u ∈ x) ⊓ (u ∈ A)`), matching Devlin VI.1.12's
  `F9 = A ∩ x`; the unrelativized trunk instantiates `A := ∅` at
  assembly, never here.
- Support: `left`/`right` projections with `left (pr a b) ≡ a`,
  `right (pr a b) ≡ b`; both total, junk off pairs, no pairhood guard.

## 2. Per-operation table

Measured on the final file: nonblank Agda lines inside fences; the module
is one file, so the typecheck column is the whole-module time (the per-op
share is subsumed, not isolated).

| operation | reused-or-built | agda lines | spec lines | typecheck |
|---|---|---:|---:|---|
| `left` | built on `⋂` (new); `pr` reused | 5 | 3 (`left-spec`) | 54.6 s module |
| `right` | built on `sndExtract` (new); `pr-inj` reused | 50 | 4 (`right-spec`) | 54.6 s module |
| `F10` | built: `sett` over `⟪ x ⟫`, family `right ∘ ⟪ x ⟫↪`, filter `pr y · ∈ₛ x` | 25 | 23 (`F10-spec`) | 54.6 s module |
| `F8` | built: `sett` over `⟪ y ⟫` of `F10` slices | 12 | 11 (`F8-spec`) | 54.6 s module |
| `F11` | built: `pr (left y) (pr x (right y))` | 26 (block) | 4 | 54.6 s module |
| `F12` | built: `pr (left y) (pr (right y) x)` | " | 4 | " |
| `F13` | built: `⁅ left y , pr (right y) x ⁆` | " | 4 | " |
| `F14` | built: `⁅ left y , pr x (right y) ⁆` | " | 4 | " |
| `F15` | built: separation `⁅ x ∶ (λ u → u ∈ₛ A) ⁆`, module-parameterized | 14 | 10 (`F15-spec`) | 54.6 s module |

Whole module: 298 fence lines (263 nonblank), stop-line 700 respected;
typecheck 54.6 s wall (fresh interface, `GHCRTS=-M10g`), exit 0, no
`UnsolvedConstraints`. Reused rather than built: `pr`, `pr-inj`
(`V.Coding`); `sett`, `_∈ₛ_`, `∈∈ₛ`, `⟪_⟫`, `⟪_⟫↪`, `∈ₛ⟪_⟫↪_`,
`extensionality`, `identityPrinciple`, `ix∈ₛ`; `⁅_,_⁆`, `pairing-ax`,
`⋃_`, `union-ax`, `⁅_⁆s`, `SingletonPackage`/`SetPackage`,
`⁅_∶_⁆`, `separation-ax`; `⇔toPath`, `∃[]-syntax`. Nothing imported from
`L.Rud.Ops` (parallel) or any not-yet-committed module.

## 3. LESSONS applied

- **C-12 / P-i:** every agda run under `GHCRTS=-M10g`; the three
  conversion walls (section 5) were hunted by deletion-bisection to the
  guilty definitions and fixed by restructuring, not by sealing: the
  union-representation extraction is gone from every proof.
- **Wall protocol:** one wall event (the OOM crash) plus two further
  wall-class failures are recorded with their trails in section 5; each
  got a genuinely different formulation before the fix, and the trail
  would have been reported as a NO-GO deliverable had the third
  formulation failed.
- **STYLE-agda:** exact OPTIONS header, using-lists on every import,
  no postulates/holes/`TERMINATING`, mixfix usage, `-- perf`/keep
  markers where the linter needs them.
- **i18n:** `<!--en--> / <!--zh--> / <!--/-->` groups, prose leads code,
  zh with full-width punctuation, half-width parens with outer spacing,
  no em dash anywhere, long zh paragraphs on one line; the zh rendering
  for the rudimentary class is 初步函数 per the ruling (fixed from the
  interim form mid-task).

## 4. Surprises and lesson candidates

1. **The representation of a nested union of an open term is
   meta-poisoned.** `⟪ ⋃ (⋃ x) ⟫` for a variable `x` (a set-quotient
   over a Σ over another quotient) cannot compute indices or paths:
   extraction leaves unsolved constraints (exit 42) or OOMs. The
   representation of a concrete pair (`⟪ pr a b ⟫`, a quotient over
   `Lift Bool`) computes fine. **Lesson candidate:** index setts by
   `⟪ x ⟫` or by members with total families plus filters, never by the
   representation of unions of open terms; prove pair facts over
   concrete pairs.
2. **`separation-ax` over a union of a concrete pair explodes** (its
   repack runs `identityPrinciple` on the union's quotient); over a
   concrete pair it is cheap. Same fix: avoid separating on unions.
3. **Unsolved constraints report as `error: [UnsolvedConstraints]` with
   exit 42** while the log tail otherwise looks like a clean check.
   Always read the exit code, not the tail.
4. **The `⋃`-of-member trick:** `⋂ z` as the sett of the unions
   `⋃ (⟪ z ⟫↪ m)` of the members, filtered by membership in every member,
   gives the correct pair behavior (`⋂ (pr a b) = ⁅ a ⁆s`) with no
   union-representation machinery at all.
5. **`where` blocks do not see later declarations** in this codebase
   (B4 lesson re-confirmed): `⋃singl` had to precede its consumer
   `⋂pair`.
6. **Spec shape affects the cost of the proof.** `F8`'s classical
   `∃ z ∈ y` shape forces a fiber extraction from a big membership over
   `⟪ y ⟫` (the first wall); the small-index form
   `∃[ m ] (F10 x (⟪ y ⟫↪ m) ≡ₕ w)` is definitionally the sett's fiber
   and both directions are one-liners. The two are extensionally the
   same (every member of `y` is `⟪ y ⟫↪ m`), stated in the prose.

## 5. Walls (all resolved)

- **Wall 1 (OOM crash, observed past 5.8 GB, machine rebooted):** the
  original `F8-spec` bwd via `∈-asFiber` on `z ∈ y`. Trail: bisection to
  `F8-bwd`; fix = restate the spec over the small index (no fiber
  extraction); both directions then definitional. This is the wall the
  session recovery message refers to.
- **Wall 2 (210 s hang, then OOM on retry):** `rightSlice-pair` with
  `separation-ax` over `⋃ (pr a b)` (repack explosion, surprise 2).
  Fix: `rightSlice` as a `sett` over `⟪ z ⟫` with the equality-based
  second-component extraction `sndExtract` at the concrete-pair level.
- **Wall 3 (unsolved metas, exit 42):** `∈ₛ→fiber`-style extraction over
  `⟪ ⋃ (pr a b) ⟫` in `⋂pair` sub₂ and `rightSlice-pair` sub₂ (surprise
  1). Fix: `⋂` over members' unions (`⋃ (⟪ z ⟫↪ m)` family) and
  `rightSlice` over members via `sndExtract`; every remaining index or
  path lives over a stuck term (`⟪ x ⟫` with `x` a variable) or a
  concrete pair, both of which compute cheaply.

## 6. Honest notes

- `⋂` is engineered for its pair behavior (`⋂ (pr a b) ≡ ⁅ a ⁆s`), the
  only place it is used; its value on arbitrary sets is a total junk
  convention, in line with the brief's discipline for the projections.
- `F8-spec` is the small-index form; the classical `∃ z ∈ y` reading is
  equivalent and is what the prose states.
- The `zh` prose was audited for the ruling rendering: no substitute for
  初步函数 (rud 函数, 初等函数, 初始函数) remains.
