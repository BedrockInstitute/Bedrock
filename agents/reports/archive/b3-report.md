# B3 report: the kinded levels, the invariant, and terms-to-levels

Repository `/Users/alsg/Agentic/Bedrock`, branch `godel-route`. Batch B3 per
the task brief `b3-brief.md`, the meta heart of option B: the kinded level
family `slice`, the kinded invariant replacing the certificate's honesty
induction, terms-to-levels, and the productionized cut theorem. Only
`src/L/Godel/Closure.lagda.md` and this report were touched; no git
operations, no postulates, holes, or TERMINATING/NON_TERMINATING pragmas
anywhere in the new code.

## Status

`agda src/L/Godel/Closure.lagda.md` is green; the whole tree
(`agda src/Everything.lagda.md`) is green; the four linters (i18n markers,
prose, Agda code, glossary) pass on the file explicitly; `make check`'s five
stages pass (typecheck, markers, prose lint, Agda code lint, glossary), with
the `reuse` stage run through the same one-line `os.sysconf` fallback wrapper
the B1/B2 reports recorded (the sandbox blocks that syscall; with a fallback
of 32000 the stage reports 197/197 files, zero read errors, three used
licenses). No definition crossed the 180 s wall: the whole chapter cold-checks
in seconds (see Timings).

## Delivered

1. **The kinded levels.** `slice : (A : V ℓ) → ℕ → ℕ → V ℓ` (stated inside
   the chapter's `module _ (A : V ℓ)` as `slice : ℕ → ℕ → V ℓ`), an
   arity-indexed, level-cumulative family:
   `slice A 0 0 = singletons A`, `slice A 0 (suc k) = ∅`, and
   `slice A (suc n) k = slice A n k ∪ step A n k`. The step is one direct
   `sett` over a tag-indexed sum of presentations of the previous level, with
   one tag per clause: `tagInter`/`tagUnion`/`tagDiff` and the two selections
   stay inside the slice; `tagAll` writes `allTuples A k` from the numeral
   alone; `tagExt` moves a slice up by one arity and draws its first argument
   from a **positive**-arity slice and its second from the seeded arity-zero
   shelf; `tagShift` moves a slice down by one; `tagValues` reads the arity-one
   slice and writes the arity-zero shelf. Membership laws: one `slice-in` per
   clause (`slice-∩-in`, `slice-∪-in`, `slice-∖-in`, `slice-selM-in`,
   `slice-selE-in`, `slice-allTuples-in`, `slice-extendFamily-in`,
   `slice-shiftDown-in`, `slice-values-in`), each building the image's fiber
   from the arguments' memberships, and `slice-out` as the disjunctive
   inversion (old member or a tagged image with its payload), direction-paired;
   `slice-old`/`slice-addR`/`slice-addL` are the old-member inclusion and its
   iteration on either side of addition.
2. **The kinded invariant.** `slice-inv : (n k : ℕ) (u : V ℓ) →
   ⟨ u ∈ slice A n (suc k) ⟩ → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ (suc k) ] (u ≡ satSet φ) ∥₁`,
   by plain induction on the level, one case per clause, each discharged by an
   equation run backward: `sat-∧`, `sat-∨`, `sat-¬`, `sat-⊤`, `sat-∃`, the B1
   selection equations `sat-∈vv-sel`/`sat-≐vv-sel`, and the B2 extension
   equation `extendFamily-pin-eq`, with `satSet⊆` and `satSet-∖`
   (conjunction-with-negation for the difference clause) proved membership-wise
   in this chapter. The arity-zero shelf is deliberately outside the
   invariant's scope (it is the value shelf, where `values` lands and the
   seed's singletons sit). No codes, no annotation table: this replaces the
   certificate's honesty induction.
3. **Terms-to-levels.** `levelOf` computes a level witness by term induction
   (leaves at one, two, and four; binary nodes at the sum of the children's
   levels plus one; the shift at the child's level plus one), and
   `terms-in-levels : (t : KT ⟪ A ⟫ k) → ⟨ ⟦_⟧ᴷ A t ∈ slice A (levelOf t) k ⟩`
   is the **untruncated** form (the witness is computable, per the brief's
   preference). One term induction; each constructor's case is the
   corresponding `slice-in` law. The binary cases lift both children to the
   summed level via `slice-addR`/`slice-addL`; the constant-atom composite
   draws its extension argument from the seed via `slice-singleton-seed` and
   `slice-addR`.
4. **The cut theorem, productionized.** From `CutProbe.agda`'s validated
   statements, against `𝒟ₒ A` with the sanctioned openings:
   `cut-sound : {n} {u} → ⟨ u ∈ slice A n 1 ⟩ → ⟨ values u ∈ 𝒟ₒ A ⟩` by the
   invariant, the values bridge `sat-defSet`, and `𝒟ₒ-intro`; and
   `cut-complete`, under the chapter's own `module WithLEM (lem : LEM (ℓ-suc ℓ))`
   matching how `Terms` scopes its classical half, by `𝒟ₒ-inv`,
   `Terms.WithLEM.termDef≡Def`, and `terms-in-levels`, giving
   `∥ Σ[ n ] Σ[ u ] (⟨ u ∈ slice A n 1 ⟩ × (values u ≡ v)) ∥₁` for every
   `v ∈ 𝒟ₒ A`. The probe's `⊆ allTuples A 1` guard is absorbed by the kinded
   design: `slice1⊆allTuples` derives it from the invariant and `satSet⊆`, so
   the cut is stated against the slices alone.

## The seed discipline chosen, and why

**The carrier's own members seed slice zero, as their singletons, via the B2
singleton family: `slice A 0 0 = singletons A`; every higher shelf starts
empty.** The constant-atom composite `selEqConK i a` feeds `⁅ κ a ⁆s` (a
member of the singleton family) to the family extension, and the B2 singleton
family exists precisely to supply that argument, so the seed is exactly the
piece of the B2 machinery the constant-atom clause consumes. Two constraints
fix the shape. First, soundness: a raw member of `A` is not generally a subset
of `A`, and the probe's escape case shows that seeding the cut with raw
carrier members lets `values (A ∩ allTuples A 1)` escape `𝒟ₒ A` on
non-transitive carriers; the kinded seed keeps raw members out of every shelf,
so the values-cut never reads them. Second, the shelf discipline: seeding
slice zero with the singletons puts the extension arguments on the value
shelf, and `slice-extendFamily-in` draws its second argument from that shelf
(`⟨ ⁅ κ a ⁆s ∈ slice n 0 ⟩`, discharged at level zero by `slice-singleton-seed`
via `singletons-in` and maintained by cumulativity). The singleton family
itself, as a set, is not a slice member; what enters are its members. Slices at
arity one and above seed empty, and the tuple families enter at level one from
the numeral alone (`allTuples A k ∈ slice A 1 k` by `slice-allTuples-in`), so
the invariant's base case is vacuous.

## The mixed-arity junk cases: impossible by construction

The probe's §2.2 table, re-examined against the slice discipline:

| case | probe verdict | here | why |
|---|---|---|---|
| 1. `allTuples A 1 ∩ allTuples A 2` | lands inside (`∅ ∈ Def`) | **impossible** | `slice-∩-in` requires both arguments in one slice; arities 1 and 2 are different shelves, and no clause crosses shelves |
| 2. `allTuples A 1 ∩ allTuples A 1` | lands inside | possible, and definable | the same-arity intersection is a clause image; the invariant makes it `satSet (⊤̇ ∧̇ ⊤̇)`, so its values-cut lands in `𝒟ₒ A` by `cut-sound` (this is the invariant's job, not an argument) |
| 3. `allTuples A 2 ∖ allTuples A 1` | lands inside (`A ∈ Def`) | **impossible** | `slice-∖-in` is inside a slice; mismatched arities cannot be its inputs |
| 4. `A ∩ allTuples A 1` (seed cut) | **escapes** in general | **impossible** | `A` is not a slice member at any arity (raw members seed only as singletons, and `A` itself is only ever a values-image in slice zero, arity zero); the intersection clause cannot take one slice-zero and one slice-one argument |

No clause as written crosses arities. The only arity-moving clauses are the
sanctioned ones: `tagExt` (positive arity to one higher, first argument from a
positive-arity slice only, which is what keeps the arity-one invariant
honest), `tagShift` (one lower), and `tagValues` (arity one to arity zero).
The `tagExt` arity-0 crossing that would break the invariant at arity one was
caught during design against the probe's table: drawing the extension's first
argument from the arity-zero value shelf would put non-satisfaction sets into
slice one, so the clause is fixed to draw from `slice A n (suc k)`.

## Prose

Section pairs (en then zh) added for: the kinded levels (the shelf
discipline, the pedagogical heart of option B: different arities on different
shelves, operations shop only on their own shelf, which is what makes the junk
impossible by construction), the kinded invariant, terms-to-levels, and the
cut theorem. The chapter intro and the Recap (en and zh) are updated to the
completed state. No em dash anywhere; the CJK rules hold (linters verify).

## Terms

- 层 for "level" (the brief's suggestion; also the established "layer"
  rendering in `dev/glossary.toml`, where `layer` = 层 for the L-tower stages;
  the closure chapter uses 层 exclusively for the ℕ-indexed level and never for
  stages, so no ambiguity arises in context; "level" is not a tracked glossary
  term, so nothing is machine-flagged. Surfaced per `AGENTS.md`; a glossary
  entry can be added when the closure chapter lands).
- 片 for "slice" (the brief's suggestion; adopted; `slice` appears in code
  identifiers verbatim).
- 架位 for "shelf" (the shelf-discipline metaphor; rendered as 架位 in the
  discipline sentence and 片 elsewhere).
- 单例族 for "singleton family", established in B1, used unchanged.

## LESSONS IDs that shaped choices

- **P-b** (union-free operation definitions): each clause image is one direct
  `sett` over a tag-indexed sum of presentations; the only union that is a
  membership obligation is the cumulative level, which is exactly the brief's
  sanctioned exception.
- **P-c** (seal `⋃`-tower indices at birth): the level union sits at the top
  of `slice`, never under a sealed index, and the step's index is a sum of
  presentations of the previous level with no `⋃`-tower, so no seal is needed
  at the birth site; this is the adopted P-b/P-c reading, recorded in the
  chapter prose as well.
- **P-d** (reductions travel as direction pairs): every satisfaction-set
  identity used by the invariant (`sat-∨`, `sat-¬`, `sat-⊤`, `sat-∃`,
  `sat-defSet`, `satSet-∖`) is a membership-wise extensionality of two
  directions, and the invariant consumes the equations by `sym`/`cong` at a
  variable member `u`, never by pointwise paths between satisfactions.
- **P-g / B2 surprise 1** (no `cong` with a function lambda at concrete
  presentation-carrying types; spell `satSet`'s arity where not forced):
  `cong (λ W → selectMember W …)` and the extension's `cong₂` run over the
  sealed heads `selectMember`/`selectEqual`/`extendFamily`, and every
  `satSet` arity in the new code is either forced by the formula or spelled
  explicitly (`sat-⊤ {n = suc k}`); no wall occurred, so no path-lambda
  rewrite was needed beyond the sealed-head discipline.
- **B2 surprise 2** (explicit implicits on `singletons-out`): the new code
  consumes only `singletons-in`, with `{X}` and `{x}` spelled explicitly in
  `slice-singleton-seed`; `singletons-out` is not consumed by this batch.
- **Rule 1** (discharge substitutions at variable arguments): every `subst`
  in the invariant and the cut is at a variable member (`u`, `w`, `v`, `x`),
  never at a concrete set.
- **Rule 8** (name the `PT.rec` payload): the invariant's `split`/`step'`
  payloads and the case helpers' sigma types are written down.
- **Rule 10** (case splits concluding in a membership hProp are named
  helpers): each invariant clause is a named helper (`inter-case`, …,
  `shift-case`) with its conclusion written down.
- **Rule 20** (composites consumed factor by factor): `cut-complete` consumes
  `termDef≡Def` as one factor and `terms-in-levels` as another; the invariant
  consumes one equation per clause.
- **D-2** (junk excluded by construction, not by decoration): the kinded
  level table is the D-2 remedy for the naive closure; the probe's escape case
  is impossible by the shelf discipline, as tabulated above.
- **C-8** (the gate has blind spots): the file is git-tracked, but the end of
  the file and the marker balance were verified explicitly, and the linters
  were run on the file before the full gate.

## Surprises

1. **`Satisfaction`'s stock is not reusable by import, even where the
   definitions look identical.** `Satisfaction.satSet` is not definitionally
   equal to this chapter's locally restated `satSet`: the private `tab`/`vec`
   of each module are distinct stuck names at variable assignments, so
   importing `sat-∨`/`sat-¬`/`sat-⊤`/`sat-∃`/`sat-defSet` fails with
   `L.Godel.Satisfaction.tab … != tab …`. B1's "restated locally" precedent is
   therefore load-bearing, and the five missing equations were restated
   locally (~170 lines) against this chapter's machinery. The brief's "read
   its stock; B1 restated some locally" is exactly the right reading.
2. **`ext-case` could not conclude in the shared `T`.** The where-block
   conclusion `T = Σ[ φ ∈ Formula (suc k) ] …` is defined at the unrefined
   arity, and the `tagExt` branch refines `k` to `suc k'` inside `step'` but
   not inside the separately typechecked helper; the fix was to state
   `ext-case`'s conclusion explicitly at `suc (suc k')`.
3. **Agda where-blocks have no forward references** (B2's surprise 3
   recurred): the invariant's `split` had to be declared after `step'`, which
   had to be declared after the case helpers.
4. **`n + zero` and `n + suc m` are not definitionally `n`/`suc (n + m)`** for
   the built-in `_+_` (it recurses on the first argument), so `slice-addR`
   needs `+-zero`/`+-suc` transports; this is why the level merge is stated on
   either side of the addition (`slice-addR`/`slice-addL`), avoiding any
   commutativity lemma.
5. **`_+_` is not in scope through `Base.Prelude`** in practice (the chapter
   needed an explicit `open import Cubical.Data.Nat using ( _+_; +-zero; +-suc )`,
   matching the explicit imports in `Name`/`Tower`).
6. **`module WithLEM` collides with `Terms.WithLEM`**: the local classical
   module is named `WithLEM` per the brief, so `Terms` is imported qualified
   (`import L.Godel.Terms as Terms`) and the mirror half is reached as
   `Terms.WithLEM A lem`.
7. **Where-block names cannot shadow module-level helpers**: `sat-defSet`'s
   local `fwdV`/`bwdV` clashed with B1's top-level `fwdV`/`bwdV` in the values
   generalization, renamed to `fwdVal`/`bwdVal`.

## Choices worth recording

- The level witness for binary nodes is the **sum** of the children's levels
  plus one, not the brief's suggested max: with addition, `slice-addR`/
  `slice-addL` lift either child to the summed level without any `≤`/max
  machinery or truncation, and the witness stays computable (an upper bound,
  exactly what the statement needs). This is a deliberate deviation from the
  brief's parenthetical, recorded here rather than papered over.
- The `slice-out` payload for the extension clause returns the presentation
  and the constant but not the premise `⟨ ⁅ κ a ⁆s ∈ slice n 0 ⟩`: that
  premise is derivable from the constant alone (seed plus cumulativity), and
  no consumer needs it; the premise stays in the `slice-in` law where it
  states the shelf discipline.
- The bounded-quantifier and remaining atom reductions of `Satisfaction`
  (`red-∃∈`, `red-∀∈`, …) are not consumed by this batch: the closure's
  clause set is exactly the operations' arities, and the bounded quantifiers
  enter the cut through the mirror (`termDef≡Def`), not through closure
  clauses. Nothing is deferred; they simply belong to the other side of the
  cut.
- The level recursion is fully meta: `slice` is an Agda ℕ-recursion, the
  invariant a meta induction on the level, `terms-in-levels` a meta term
  induction. Nothing here quantifies tables internally; that is the next batch
  (the internal closure chapter), as the brief requires.

## Timings

- `agda src/L/Godel/Closure.lagda.md`: cold (interface absent) about 3 to 4 s
  per run during development; warm 1.5 s (measured 2026-08-02).
- `agda src/Everything.lagda.md`: 2.7 s warm.
- No definition crossed the 180 s wall; no LESSONS countermeasure beyond the
  recorded ones was needed.
- `make check` stages: typecheck, markers, prose lint, Agda code lint,
  glossary all green; `reuse lint` green with the recorded `os.sysconf`
  fallback wrapper (197/197 files).

## Accounting for every brief item

- Kinded levels, meta: **delivered** (item 1), with the seed discipline
  pinned (carrier's members seed slice zero as singletons via the B2 singleton
  family), the P-b/P-c reading recorded, `slice-in` per clause and `slice-out`
  as the disjunctive inversion in both directions.
- Kinded invariant: **delivered** (item 2), level induction, one case per
  clause, each discharged by an equation run backward, replacing the
  certificate's honesty induction.
- Terms-to-levels: **delivered** (item 3), untruncated computable form with
  `levelOf`, one term induction, each case the corresponding `slice-in` law.
- Cut theorem, productionized: **delivered** (item 4), `cut-sound` and
  `cut-complete` under the chapter's `WithLEM`, stated against `𝒟ₒ A` via
  `𝒟ₒ-intro`/`𝒟ₒ-inv`.
- Mixed-arity junk impossible by construction: **delivered**, tabulated
  above; the `tagExt` arity-0 crossing was caught and the clause fixed.
- P-d directions, `satSet` arity implicits, `singletons-out` implicits:
  **delivered** as recorded under LESSONS IDs.
- Level recursion fully meta: **delivered**, recorded.
- Prose pairs and Recap update: **delivered**.
- Terms: 层/片/架位/单例族, chosen and surfaced.
- Verification: `agda` green, four linters green, `make check` green once
  (reuse via the recorded wrapper). Nothing is deferred.
