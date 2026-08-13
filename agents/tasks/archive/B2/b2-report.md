# B2 report: closing B1's deferrals

Repository `/Users/alsg/Agentic/Bedrock`, branch `godel-route`. Batch B2 per
the task brief `b2-brief.md`, closing the three deferrals B1 recorded in the
commit message of `5cd66e2`: the reverse pinning direction, the full
family-extension equation, and the singleton family's `At`-description and
constructibility. Only `src/L/Godel/Closure.lagda.md` and this report were
touched; no git operations, no postulates, holes, or
TERMINATING/NON_TERMINATING pragmas anywhere in the new code.

## Status

All four deliverables land green. `agda src/L/Godel/Closure.lagda.md` checks
clean; the four linters (i18n markers, prose, Agda code, glossary) pass on the
file explicitly (per C-8); `make check` passes once at the end (see the
Verification section for the tree timings). The chapter stays in the
seconds-per-chapter class: cold check of `Closure` alone about 2.6 s, warm
about 1.9 to 2.7 s against the B1 baseline of about 1.7 s warm.

## Delivered

1. **The reverse pinning direction** `extendFamily-pin-rev`, completing
   `extendFamily-pin` into the full inclusion pair:
   `(w : V ℓ) → ⟨ w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s ⟩ → ⟨ w ∈ satSet (var zero ≐ con a) ∩ extendFamily (satSet φ) A ⟩`.
   A member of the singleton extension is the graph of an assignment extended
   by the constant itself; `singleton-out` reads the constant off the head,
   `tuple-extend` re-assembles the graph as the tuple of the consed assignment,
   and `sat-in` with the lookup specification re-builds the pinned formula's
   satisfaction, while the extension membership stays in the full family.
2. **The full family-extension equation** `extendFamily-pin-eq`:
   `extendFamily (satSet φ) ⁅ κ a ⁆s ≡ satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)`,
   assembled from the renaming law (`satSet-rename-shift`) and the two pinning
   inclusions, in the exact shape `Terms.sound`'s `selEqConK` case reads
   backward. The assembly is membership-wise (see below).
3. **The singleton family's `At`-description** `singletonsAt k i` with both
   readers `singletonsAt-out` and `singletonsAt-in` at variable slots and
   environments, in the `Describes` frame of `L.Godel.Definable`. The body is
   `∃̇∈ (var (suc i)) (sglAt′ (suc zero) zero)`: the bound member is the
   singleton of a member of the carrier slot. The singleton atom class
   `sglAt′` is private in `L.Godel.InL`, so it is restated locally, exactly as
   B1 restated its satisfaction machinery; the report says so, per the brief.
4. **The singleton family's constructibility** `singletonsL : ⟨ isL X ⟩ → ⟨ isL (singletons X) ⟩`
   by the InL pattern: one stage from directedness (`isL-directed X X lX lX`),
   the defining formula over the next stage
   (`∃̇∈ (con mX) (sglAt′ (suc zero) zero)` over `⟪ Lset (sucV σ) ⟫`), and
   `defSet→isL (sucV σ) (suc-ord oσ)`. The fixed climb (`sglUp-mini`: a stage
   member's singleton lies in the next stage) is restated locally after the
   `sglUp`-class precedent in `L.Godel.InL`, since that chapter's climbs are
   private and no other file may be touched.

## Which attack formulation cracked the reverse pinning

Attack (a), the brief's mandated first formulation, cracked it: **direct path
lambdas per P-g, with named helpers carrying spelled payloads**. The reverse
proof is written as one `PT.rec` over `extendFamily-out` with a named `build`
continuation (payload spelled, per Rule 8), a named `step` over `sat-out`, and
a `let`-block of small named equations (`y≡`, `g'`, `w≡`, `hw`, `w∈S`,
`y∈A`, `w∈F`) rather than inline `cong` chains or single `subst` megasteps.
The graph-to-tuple rewrite is `eγ ∙ cong₂ extendGraph y≡ (sym eg) ∙ sym (tuple-extend A g')`
over `extendGraph`'s sealed head (P-c), never a `cong` with a function lambda
at a concrete presentation-carrying type. No wall occurred: no formulation
crossed the 180 s tripwire, so the abstract-set formulation (attack (b),
P-e/Rule-5) and the `opaque` seal (attack (c), P-c/Rule 2) were not needed;
that is recorded rather than papered over. Two supporting choices mattered
for the typechecker: the `satSet {n = suc n}` arity is passed explicitly
wherever the pinned formula is not determined by an assignment (see
Surprises), and the full equation is assembled membership-wise (see below)
rather than by `cong₂ _∩_` over concrete satisfaction sets.

## How the full equation's statement matches the invariant's selEqConK clause

`Terms.sound`'s `selEqConK` case reads
`⟦ selEqConK i a ⟧ᴷ = shiftDown (selectEqual (extendFamily (allTuples A n) ⁅ κ a ⁆s) ⁅ # (suc (toℕ i)) ⁆s ⁅ # 0 ⁆s)`
with `sound (selEqConK i a) = sym (sat-≐vc A i a)`: the constant-atom
composite is a selection over the family extended by the constant, then a
shift. The kinded invariant's constant-atom clause will consume
`extendFamily-pin-eq` to rewrite the selection's `extendFamily (satSet φ) ⁅ κ a ⁆s`
endpoint into `satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)`, so the selection
over the extended family becomes a selection over the conjunction's
satisfaction set; the selection equations of this chapter then read that
selection as one more conjunction, and the shift is met by the renaming law's
direction, discharging the clause. The statement is exactly the shape the
clause needs: the pinned formula's fresh first variable records the constant
and the remaining variables are the original ones shifted up by one.

## LESSONS IDs that shaped choices

- **P-g** (no `cong` with a function lambda at concrete presentation-carrying
  types): the reverse pinning was written with direct path lambdas and named
  `let`-equations; the brief's attack order (a) is the one that landed.
- **Rule 8** (name the `PT.rec` payload): `build` and `step` are named with
  their sigma payloads written down.
- **P-d / Rule 20** (reductions travel as direction pairs; composites
  consumed factor by factor): the full equation is assembled membership-wise,
  `extensionalV λ w → ⇔toPath (to w) (fro w)`, each direction a single
  `subst (λ z → ⟨ w ∈ z ⟩)` at a variable `w` along one law (`sat-∧`,
  `satSet-rename-shift`) per step (Rule 1's variable-argument pattern),
  never `cong₂ _∩_` over concrete satisfaction sets.
- **P-c** (seal `⋃`-tower indices at birth): `extendGraph` arrives sealed, so
  `cong₂ extendGraph` in the graph-to-tuple rewrite is cheap; the chapter
  never unfolds it.
- **C-8** (the gate has blind spots): the four linters were run explicitly on
  the file, since new-file handling and end-of-file placement are not
  self-checking.

## Surprises

1. The B1-recorded P-g-class wall did not recur under attack (a). The reverse
   direction typechecked in seconds once the `satSet {n = suc n}` arity was
   explicit in every occurrence; whether the arity-meta churn contributed to
   B1's measured hang cannot be recovered from the record, but spelling the
   arity plus keeping every `PT.rec` payload named dissolved the wall outright
   in this batch.
2. `singletons-out`'s implicit `{X}`/`{w}` must be passed explicitly: with
   `singletons`' unsealed body (`sett ⟪ X ⟫ …`), unifying `singletons ?X ≡
   singletons X` normalizes the presentation `⟪ ?X ⟫` and blocks on a
   metavariable, leaving an unsolved milestone. This was the longest bisect of
   the batch (the blocked constraint survives even with the consuming code
   replaced by holes; explicit implicits remove it).
3. Agda forbids `where` clauses inside `let` bindings, and a `where` block
   attached to an equation cannot see the equation body's `let`-bound names;
   every helper had to be attached at clause level with the variables it needs
   either as pattern variables or as explicit arguments.
4. Inside `module _ (A : V ℓ)`, the outer `hPropStructure 𝒮ᵥ` opening shadows
   `S` and `_∈ˢ_`, so the description section spells its carrier directly as
   `Σ[ x ∈ V ℓ ] ⟨ isL x ⟩` (definitionally `𝒮ʟ`'s) and takes the inner
   satisfaction qualified from `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`,
   avoiding the name clash without touching the existing opening.
5. The `Describes` frame's conversions needed both directions of `∈∈ₛ`
   (`∈ₛ` ↔ `∈`) at the subset witnesses and none at the semantics' own
   membership, which arrives already unfolded; several one-line fixes of this
   kind were the bulk of the iteration.

## Verification

- `agda src/L/Godel/Closure.lagda.md`: green (cold about 2.6 s, warm about
  1.9 to 2.7 s).
- Four linters on the file: markers, prose, Agda code lint, glossary all
  clean.
- `make check`: run once at the end; typecheck (the whole tree via
  `agda src/Everything.lagda.md`, about 2.7 s warm), markers, prose, Agda code
  lint, and glossary all green; the `reuse` stage needs the same one-line
  `os.sysconf` fallback wrapper the B1 report recorded, as the sandbox blocks
  that syscall (with the wrapper, `reuse lint` passes: 197/197 files with
  license information, three used licenses, zero read errors). Licensing is
  declared centrally in `REUSE.toml` (`src/**` → CC-BY-NC-SA-4.0), no in-file
  SPDX headers.

## Accounting for every brief item

- Reverse pinning direction: **delivered** (item 1), attack (a) cracked it,
  no walls, (b)/(c) not exercised.
- Full family-extension equation: **delivered** (item 2), assembled from the
  renaming law and the two pinning inclusions; the report states how the
  kinded invariant's `selEqConK` clause will consume it.
- Singleton family `At`-description: **delivered** (item 3), `Describes`
  frame, both readers at variable slots and environments, `sglAt′` restated
  locally and said so.
- Singleton family constructibility: **delivered** (item 4), InL pattern with
  the fixed climb restated locally.
- Prose: **delivered**. One paragraph pair extends the family-extension
  section (the equation now whole) and one the singleton family's internal
  face (description and constructibility, consumed by the closure recursion in
  the next batch); the chapter intro and the Recap are updated to the
  completed state; no em dash anywhere; CJK rules followed; terms registered
  as B1 did (`单例族` established there; no new glossary entry needed, the
  glossary checker flags only known-wrong renderings and none occur).
- Verification and report: **delivered** (this file).
